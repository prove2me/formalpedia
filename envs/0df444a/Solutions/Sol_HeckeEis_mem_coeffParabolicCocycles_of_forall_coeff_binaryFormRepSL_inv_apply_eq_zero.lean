-- Prove2me | solution 1 for HeckeEis.mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/014086f9-c754-51d0-84a6-10d648a42079

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Theorems.Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm
import Theorems.Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

namespace A2BCR

open MvPolynomial CongruenceSubgroup HeckeEis

section Prelim

variable (K : Type*) [Field K] (n : ℕ)

abbrev V : Type _ := ↥(BinaryForm K n)

noncomputable abbrev R : SL(2, ℤ) →* (V K n →ₗ[K] V K n) := binaryFormRepSL K n

omit [Field K] in

theorem eval_binarySubst {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval x (binarySubst K M P)
      = MvPolynomial.eval (fun j => ∑ i : Fin 2, x i * ((M i j : ℤ) : K)) P := by
  unfold binarySubst
  rw [MvPolynomial.aeval_eq_bind₁]
  change MvPolynomial.eval₂Hom (RingHom.id K) x (MvPolynomial.bind₁ _ P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => MvPolynomial.eval x _) P = _
  congr 2
  funext j
  simp [Fin.sum_univ_two, mul_comm]

noncomputable def top (P : V K n) : K := MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) K)

theorem top_eq_eval (P : V K n) : top K n P = MvPolynomial.eval ![0, 1] (P : MvPolynomial (Fin 2) K) :=
  coeff_single_one_eq_eval_of_mem_binaryForm P.2

noncomputable def topLin : V K n →ₗ[K] K where
  toFun := top K n
  map_add' P Q := by simp [top]
  map_smul' c P := by simp [top]

@[scoped simp] theorem topLin_apply (P : V K n) : topLin K n P = top K n P := rfl

theorem top_add (P Q : V K n) : top K n (P + Q) = top K n P + top K n Q := (topLin K n).map_add P Q
theorem top_neg (P : V K n) : top K n (-P) = -top K n P := (topLin K n).map_neg P
theorem top_zero : top K n 0 = 0 := (topLin K n).map_zero

theorem top_T_zpow (m : ℤ) (P : V K n) : top K n (R K n (ModularGroup.T ^ m) P) = top K n P := by
  rw [top_eq_eval, top_eq_eval, binaryFormRepSL_apply_coe, eval_binarySubst, ModularGroup.coe_T_zpow]
  have h : (fun j : Fin 2 => ∑ i : Fin 2, (![0, 1] : Fin 2 → K) i * (((!![1, m; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : K))
      = ![0, 1] := by
    funext j
    fin_cases j <;> simp [Fin.sum_univ_two]
  rw [h]

theorem binarySubst_neg_one : binarySubst K (-1 : Matrix (Fin 2) (Fin 2) ℤ) = MvPolynomial.aeval fun j => -X j := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [binarySubst_X, MvPolynomial.aeval_X, Fin.sum_univ_two]
  fin_cases j <;> simp

omit [Field K] in

theorem sum_support_eq_of_isHomogeneous {K : Type*} [CommRing K] {φ : MvPolynomial (Fin 2) K} {m : ℕ}
    (hφ : φ.IsHomogeneous m) {d : Fin 2 →₀ ℕ} (hd : d ∈ φ.support) : ∑ i ∈ d.support, d i = m := by
  have h := hφ (MvPolynomial.mem_support_iff.mp hd)
  simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum, Finsupp.linearCombination, Finsupp.lsum] using h

theorem aeval_neg_X_of_isHomogeneous {φ : MvPolynomial (Fin 2) K} (hφ : φ.IsHomogeneous n) :
    MvPolynomial.aeval (fun j => -X j) φ = (-1 : K) ^ n • φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  have hdeg := sum_support_eq_of_isHomogeneous hφ hd
  have hprod : (d.prod fun i e => (-X i : MvPolynomial (Fin 2) K) ^ e)
      = (-1 : MvPolynomial (Fin 2) K) ^ n * d.prod fun i e => (X i : MvPolynomial (Fin 2) K) ^ e := by
    simp only [Finsupp.prod, neg_pow (X _ : MvPolynomial (Fin 2) K), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [hdeg]
  rw [hprod, MvPolynomial.algebraMap_eq, MvPolynomial.smul_eq_C_mul, map_pow, map_neg, map_one]
  ring

theorem R_neg_one (P : V K n) : R K n (-1) P = (-1 : K) ^ n • P := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    binarySubst_neg_one, Submodule.coe_smul]
  exact aeval_neg_X_of_isHomogeneous K n ((mem_homogeneousSubmodule n _).mp P.2)

end Prelim

section Main

variable {K : Type*} [Field K] {N : ℕ} {n : ℕ}

noncomputable abbrev ρK (K : Type*) [Field K] (N n : ℕ) : Representation K (Gamma0 N) (V K n) :=
  (binaryFormRepSL K n).comp (Gamma0 N).subtype

theorem ρK_apply (g : Gamma0 N) : ρK K N n g = R K n (g : SL(2, ℤ)) := rfl

variable {z : Gamma0 N → V K n}

theorem cocycle_one (hz : z ∈ coeffCocycles (ρK K N n)) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.mp h

theorem cocycle_inv (hz : z ∈ coeffCocycles (ρK K N n)) (g : Gamma0 N) : z g⁻¹ = -(ρK K N n g⁻¹ (z g)) := by
  have h := hz g g⁻¹
  rw [mul_inv_cancel, cocycle_one hz] at h
  have h2 : ρK K N n g⁻¹ (ρK K N n g (z g⁻¹)) = z g⁻¹ := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← h2, eq_neg_iff_add_eq_zero, ← map_add, add_comm, ← h, map_zero]

def negOne (N : ℕ) : Gamma0 N := ⟨-1, by rw [Gamma0_mem]; simp⟩

@[scoped simp] theorem coe_negOne : ((negOne N : Gamma0 N) : SL(2, ℤ)) = -1 := rfl

theorem ρK_negOne (hn : Even n) (P : V K n) : ρK K N n (negOne N) P = P := by
  rw [ρK_apply, coe_negOne, R_neg_one, hn.neg_one_pow, one_smul]

theorem cocycle_negOne [CharZero K] (hn : Even n) (hz : z ∈ coeffCocycles (ρK K N n)) : z (negOne N) = 0 := by
  have h := hz (negOne N) (negOne N)
  have hsq : negOne N * negOne N = 1 := Subtype.ext (by simp)
  rw [hsq, cocycle_one hz, ρK_negOne hn] at h
  have h2 : (2 : K) • z (negOne N) = 0 := by rw [two_smul]; exact h.symm
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem coe_pow_of_eq_conj (δ : SL(2, ℤ)) (m : ℤ) (x : Gamma0 N) (hx : (x : SL(2, ℤ)) = δ * ModularGroup.T ^ m * δ⁻¹)
    (j : ℕ) : ((x ^ j : Gamma0 N) : SL(2, ℤ)) = δ * ModularGroup.T ^ (m * j) * δ⁻¹ := by
  rw [Subgroup.coe_pow, hx, conj_pow, ← zpow_natCast, ← zpow_mul]

theorem top_pow (hz : z ∈ coeffCocycles (ρK K N n)) (δ : SL(2, ℤ)) (m : ℤ) (x : Gamma0 N)
    (hx : (x : SL(2, ℤ)) = δ * ModularGroup.T ^ m * δ⁻¹) (j : ℕ) :
    top K n (R K n δ⁻¹ (z (x ^ j))) = j * top K n (R K n δ⁻¹ (z x)) := by
  induction j with
  | zero => rw [pow_zero, cocycle_one hz, map_zero, top_zero, Nat.cast_zero, zero_mul]
  | succ j ih =>
    rw [pow_succ, hz, map_add, top_add, ih, ρK_apply, coe_pow_of_eq_conj δ m x hx j]

    have hcomm : R K n δ⁻¹ (R K n (δ * ModularGroup.T ^ (m * j) * δ⁻¹) (z x))
        = R K n (ModularGroup.T ^ (m * (j : ℤ))) (R K n δ⁻¹ (z x)) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [hcomm, top_T_zpow]
    push_cast
    ring

variable [CharZero K] [NeZero N]

theorem apply_mem_range (hz : z ∈ coeffCocycles (ρK K N n))
    (h : ∀ (σ : SL(2, ℤ)) (γ : Gamma0 N), (γ : SL(2, ℤ)) = σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ →
      top K n (R K n σ⁻¹ (z γ)) = 0)
    (δ : SL(2, ℤ)) (hh : ℤ) (hh0 : hh ≠ 0) (u : Gamma0 N) (hu : (u : SL(2, ℤ)) = δ * ModularGroup.T ^ hh * δ⁻¹) :
    z u ∈ LinearMap.range (ρK K N n u - 1) := by

  have hgmem : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma0 N := by

    have hT : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
      have hc : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] :=
        ModularGroup.coe_T_zpow _
      rw [Gamma_mem, hc]
      simp
    have hconj : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma N := (Gamma_normal N).conj_mem _ hT δ
    rw [Gamma_mem] at hconj
    rw [Gamma0_mem]
    exact hconj.2.2.1
  set g : Gamma0 N := ⟨δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹, hgmem⟩ with hgdef
  have hg : (g : SL(2, ℤ)) = δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ := rfl

  have hc0 : top K n (R K n δ⁻¹ (z g)) = 0 := h δ g hg

  have hgpow : ∀ j : ℕ, top K n (R K n δ⁻¹ (z (g ^ j))) = 0 := fun j => by
    rw [top_pow hz δ (N : ℤ) g hg j, hc0, mul_zero]
  have hgzpow : ∀ j : ℤ, top K n (R K n δ⁻¹ (z (g ^ j))) = 0 := by
    intro j
    rcases Int.eq_nat_or_neg j with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast]; exact hgpow m
    · rw [zpow_neg, zpow_natCast, cocycle_inv hz, map_neg, top_neg, ρK_apply, neg_eq_zero]
      have hcoe : (((g ^ m)⁻¹ : Gamma0 N) : SL(2, ℤ)) = δ * ModularGroup.T ^ (-((N : ℤ) * m)) * δ⁻¹ := by
        rw [Subgroup.coe_inv, coe_pow_of_eq_conj δ (N : ℤ) g hg m]
        group
      rw [hcoe]
      have hcomm : R K n δ⁻¹ (R K n (δ * ModularGroup.T ^ (-((N : ℤ) * m)) * δ⁻¹) (z (g ^ m)))
          = R K n (ModularGroup.T ^ (-((N : ℤ) * m))) (R K n δ⁻¹ (z (g ^ m))) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hcomm, top_T_zpow]
      exact hgpow m

  have hupow : u ^ N = g ^ hh := by
    refine Subtype.ext ?_
    rw [coe_pow_of_eq_conj δ hh u hu N, Subgroup.coe_zpow, hg, conj_zpow, ← zpow_mul, mul_comm]

  have hcu : top K n (R K n δ⁻¹ (z u)) = 0 := by
    have h1 := top_pow hz δ hh u hu N
    rw [hupow, hgzpow] at h1
    have hN : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    exact (mul_eq_zero.mp h1.symm).resolve_left hN

  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp
    (mem_range_binaryFormRepSL_T_zpow_sub_one (K := K) n hh0 (R K n δ⁻¹ (z u)) hcu)
  refine LinearMap.mem_range.mpr ⟨R K n δ w, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, ρK_apply, hu]
  rw [LinearMap.sub_apply, Module.End.one_apply] at hw

  have hzu : z u = R K n δ (R K n (ModularGroup.T ^ hh) w - w) := by
    rw [hw, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hgrp : δ * ModularGroup.T ^ hh * δ⁻¹ * δ = δ * ModularGroup.T ^ hh := by group
  rw [hzu, map_sub, ← Module.End.mul_apply, ← map_mul, hgrp, map_mul, Module.End.mul_apply]

theorem main (hn : Even n) (hz : z ∈ coeffCocycles (ρK K N n))
    (h : ∀ (σ : SL(2, ℤ)) (γ : Gamma0 N), (γ : SL(2, ℤ)) = σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ →
      top K n (R K n σ⁻¹ (z γ)) = 0) :
    z ∈ coeffParabolicCocycles (ρK K N n) := by
  refine ⟨hz, fun γ hγ => ?_⟩
  obtain ⟨ε, δ, hh, hε, hγε⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ

  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have humem : δ * ModularGroup.T ^ hh * δ⁻¹ ∈ Gamma0 N := by
    have : δ * ModularGroup.T ^ hh * δ⁻¹ = ε * (γ : SL(2, ℤ)) := by
      rw [hγε, ← mul_assoc, hεsq, one_mul]
    rw [this]
    rcases hε with rfl | rfl
    · rw [one_mul]; exact γ.2
    · exact Subgroup.mul_mem _ (negOne N).2 γ.2
  set u : Gamma0 N := ⟨δ * ModularGroup.T ^ hh * δ⁻¹, humem⟩ with hudef
  have hu : (u : SL(2, ℤ)) = δ * ModularGroup.T ^ hh * δ⁻¹ := rfl

  have hγu : γ = u ∨ γ = negOne N * u := by
    rcases hε with rfl | rfl
    · left; exact Subtype.ext (by rw [hγε, one_mul])
    · right; exact Subtype.ext (by rw [hγε]; rfl)
  have hzγ : z γ = z u := by
    rcases hγu with rfl | rfl
    · rfl
    · rw [hz, cocycle_negOne hn hz, ρK_negOne hn, zero_add]
  have hργ : ρK K N n γ = ρK K N n u := by
    rcases hγu with rfl | rfl
    · rfl
    · rw [map_mul]
      refine LinearMap.ext fun P => ?_
      rw [Module.End.mul_apply, ρK_negOne hn]
  rw [hzγ, hργ]

  rcases eq_or_ne hh 0 with rfl | hh0
  · have hu1 : u = 1 := Subtype.ext (by rw [hu, zpow_zero, mul_one, mul_inv_cancel]; rfl)
    rw [hu1, cocycle_one hz]
    exact Submodule.zero_mem _
  · exact apply_mem_range hz h δ hh hh0 u hu

end Main

end A2BCR
p2m_reactivate "P2MW.S_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero.A2BCR"

theorem solution
    {K : Type*} [Field K] [CharZero K] (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n)
    {z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (h : ∀ (σ : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N),
      (γ : SL(2, ℤ)) = σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ →
        MvPolynomial.coeff (Finsupp.single 1 n)
          ((HeckeEis.binaryFormRepSL K n σ⁻¹ (z γ) : ↥(HeckeEis.BinaryForm K n)) : MvPolynomial (Fin 2) K) = 0) :
    z ∈ HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) :=
  A2BCR.main hn hz h

end S_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero
end P2MW
export P2MW.S_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero (solution)
