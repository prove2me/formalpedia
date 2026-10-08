-- Prove2me | solution 1 for GomoryGroup.Rel.ip_le_lp_add_group
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:22:35.572575+00:00
-- url     : https://prove2.me/submissions/5c2a2b78-d70d-42d3-92d3-0c88ada4c0c1

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting



namespace GomoryGroup.Rel

open Matrix

theorem ipfgf_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ),
      IsIPFeasible B N b xB xN → IsGroupFeasible B N b xN := by
  intro xB xN h
  refine ⟨fun i => (xB i : ℤ), ?_⟩
  unfold IsIPFeasible at h
  rw [← h]; abel

theorem periodic_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) :
    ∀ i : Fin m,
      (∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y) ∧
        groupValues B N cB cN (b + fun r => B r i) = groupValues B N cB cN b := by
  intro i
  have hcol : (fun r => B r i) = B *ᵥ (Pi.single i 1 : Fin m → ℤ) := by
    ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : ∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y := by
    intro y
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k - Pi.single i 1, ?_⟩
      rw [Matrix.mulVec_sub, ← hk, hcol]; abel
    · rintro ⟨k, hk⟩
      refine ⟨k + Pi.single i 1, ?_⟩
      rw [Matrix.mulVec_add, ← hk, hcol]; abel
  refine ⟨key, ?_⟩
  ext z
  simp only [groupValues, Set.mem_setOf_eq, key]

theorem fund_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0) :
    ∀ (xB : Fin m → ℝ) (xN : Fin n → ℝ),
      Br B *ᵥ xB + Nr N *ᵥ xN = (fun i => (b i : ℝ)) →
        cB ⬝ᵥ xB + cN ⬝ᵥ xN =
          cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + ∑ j, reducedCost B N cB cN j * xN j := by
  intro xB xN h
  have hdet : IsUnit (Br B).det := by
    have : (Br B).det = ((B.det : ℤ) : ℝ) := by
      unfold Br
      have := (Int.castRingHom ℝ).map_det B
      simpa using this.symm
    rw [this]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hB)
  have hx : xB = (Br B)⁻¹ *ᵥ ((fun i => (b i : ℝ)) - Nr N *ᵥ xN) := by
    rw [← h, add_sub_cancel_right, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
  have hcol : ∀ j, ((cB ᵥ* (Br B)⁻¹) ᵥ* Nr N) j = cB ⬝ᵥ ((Br B)⁻¹ *ᵥ fun r => (N r j : ℝ)) := by
    intro j
    rw [dotProduct_mulVec]
    rfl
  have hsum : cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (Nr N *ᵥ xN)) =
      ∑ j, (cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun r => (N r j : ℝ)))) * xN j := by
    rw [dotProduct_mulVec, dotProduct_mulVec]
    conv_lhs => unfold dotProduct
    exact Finset.sum_congr rfl (fun j _ => by rw [hcol j])
  rw [hx, Matrix.mulVec_sub, dotProduct_sub, hsum]
  have : cN ⬝ᵥ xN = ∑ j, cN j * xN j := rfl
  rw [this]
  simp only [reducedCost, sub_mul, Finset.sum_sub_distrib]
  ring

theorem ip_real {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (xB : Fin m → ℕ) (xN : Fin n → ℕ) (h : IsIPFeasible B N b xB xN) :
    Br B *ᵥ (fun i => (xB i : ℝ)) + Nr N *ᵥ (fun j => (xN j : ℝ)) = (fun i => (b i : ℝ)) := by
  ext i
  have h1 := congrFun h i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply] at h1
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Br, Nr, Matrix.map_apply]
  exact h2

theorem ip_cost_eq {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0)
    (xB : Fin m → ℕ) (xN : Fin n → ℕ) (h : IsIPFeasible B N b xB xN) :
    ipCost cB cN xB xN = cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + groupObj B N cB cN xN := by
  have := fund_core B N cB cN b hB _ _ (ip_real B N b xB xN h)
  unfold ipCost groupObj
  exact this

theorem ip_le_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) :
    ∀ φ : ℝ, IsGreatest (groupValues B N cB cN b) φ →
      ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ), IsIPFeasible B N b xB xN →
        ipCost cB cN xB xN ≤ cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + φ := by
  intro φ hφ xB xN h
  rw [ip_cost_eq B N cB cN b hB xB xN h]
  have : groupObj B N cB cN xN ≤ φ :=
    hφ.2 ⟨xN, ipfgf_core B N b xB xN h, rfl⟩
  linarith

theorem extend_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) :
    ∀ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y →
      ∃ k : Fin m → ℤ, B *ᵥ k = b - N *ᵥ (fun j => (y j : ℤ)) ∧
        (0 ≤ k →
          IsIPOptimal B N cB cN b (fun i => (k i).toNat) y ∧
            ipCost cB cN (fun i => (k i).toNat) y =
              cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + groupObj B N cB cN y) := by
  intro y hy
  obtain ⟨k, hk⟩ := hy.1
  refine ⟨k, hk.symm, fun hk0 => ?_⟩
  have hfeas : IsIPFeasible B N b (fun i => (k i).toNat) y := by
    unfold IsIPFeasible
    have : (fun i => (((k i).toNat : ℕ) : ℤ)) = k := by
      ext i; exact Int.toNat_of_nonneg (hk0 i)
    rw [this, ← hk]; abel
  have hcost := ip_cost_eq B N cB cN b hB _ _ hfeas
  refine ⟨⟨hfeas, ?_⟩, hcost⟩
  intro xB' xN' h'
  rw [hcost, ip_cost_eq B N cB cN b hB _ _ h']
  have := hy.2 xN' (ipfgf_core B N b xB' xN' h')
  linarith

theorem euclNorm_eq' {m : ℕ} (v : Fin m → ℝ) :
    euclNorm v = ‖(EuclideanSpace.equiv (Fin m) ℝ).symm v‖ := by
  simp [euclNorm, EuclideanSpace.norm_eq]

theorem basic_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hB : B.det ≠ 0)
    (hb : (fun i => (b i : ℝ)) ∈ reducedCone B (ell N * ((detD B : ℝ) - 1))) :
    ∀ y : Fin n → ℕ, ∑ j, y j ≤ detD B - 1 →
      euclNorm (Nr N *ᵥ (fun j => (y j : ℝ))) ≤ ((detD B : ℝ) - 1) * ell N ∧
        0 ≤ (Br B)⁻¹ *ᵥ ((fun i => (b i : ℝ)) - Nr N *ᵥ (fun j => (y j : ℝ))) := by
  intro y hy
  have hD : 1 ≤ detD B := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hB)
  have hell : 0 ≤ ell N := Real.iSup_nonneg (fun j => by rw [euclNorm_eq']; exact norm_nonneg _)
  have hcolle : ∀ j, euclNorm (fun r => (N r j : ℝ)) ≤ ell N := fun j =>
    le_ciSup (f := fun j : Fin n => euclNorm (fun r => (N r j : ℝ))) (Set.finite_range _).bddAbove j
  have hmul : Nr N *ᵥ (fun j => (y j : ℝ)) = ∑ j, (y j : ℝ) • (fun r => (N r j : ℝ)) := by
    ext r
    simp [Matrix.mulVec, dotProduct, Nr, Finset.sum_apply, mul_comm]
  have hnorm : euclNorm (Nr N *ᵥ (fun j => (y j : ℝ))) ≤ ((detD B : ℝ) - 1) * ell N := by
    rw [euclNorm_eq', hmul, map_sum]
    calc ‖∑ j, (EuclideanSpace.equiv (Fin m) ℝ).symm ((y j : ℝ) • (fun r => (N r j : ℝ)))‖
        ≤ ∑ j, ‖(EuclideanSpace.equiv (Fin m) ℝ).symm ((y j : ℝ) • (fun r => (N r j : ℝ)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j, (y j : ℝ) * ell N := by
          apply Finset.sum_le_sum
          intro j _
          rw [map_smul, norm_smul, Real.norm_natCast, ← euclNorm_eq']
          exact mul_le_mul_of_nonneg_left (hcolle j) (Nat.cast_nonneg _)
      _ = ((∑ j, y j : ℕ) : ℝ) * ell N := by rw [← Finset.sum_mul]; push_cast; rfl
      _ ≤ ((detD B : ℝ) - 1) * ell N := by
          apply mul_le_mul_of_nonneg_right _ hell
          have : ((∑ j, y j : ℕ) : ℝ) ≤ ((detD B - 1 : ℕ) : ℝ) := by exact_mod_cast hy
          rw [Nat.cast_sub hD] at this
          simpa using this
  refine ⟨hnorm, ?_⟩
  have hmem := hb ((fun i => (b i : ℝ)) - Nr N *ᵥ (fun j => (y j : ℝ))) (by
    rw [sub_sub_cancel_left, euclNorm_eq', map_neg, norm_neg, ← euclNorm_eq']
    rw [mul_comm]; exact hnorm)
  exact hmem

end GomoryGroup.Rel

open GomoryGroup.Rel
open Matrix

theorem solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) :
    ∀ φ : ℝ, IsGreatest (groupValues B N cB cN b) φ →
      ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ), IsIPFeasible B N b xB xN →
        ipCost cB cN xB xN ≤ cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + φ := by
  exact ip_le_core B N cB cN b hB
