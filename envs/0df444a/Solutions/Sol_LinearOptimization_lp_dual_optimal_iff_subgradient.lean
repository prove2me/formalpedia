-- Prove2me | solution 1 for LinearOptimization.lp_dual_optimal_iff_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T22:09:13.316488+00:00
-- url     : https://prove2.me/submissions/1e843d6f-5dd0-4420-8e8f-eded93fac099

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_OptimalCostFunction
import Definitions.Def_LinearOptimization_Subgradient
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
import Mathlib.Tactic.Linarith

open Matrix

private lemma weak_duality_std {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (b : Fin m → ℝ) (p : Fin m → ℝ)
    (hp : p ∈ LinearOptimization.dualFeasibleStd A c)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.stdPolyhedron A b) :
    p ⬝ᵥ b ≤ c ⬝ᵥ x := by
  calc
    p ⬝ᵥ b = p ⬝ᵥ A.mulVec x := by rw [hx.1]
    _ = Aᵀ.mulVec p ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec]
      congr 1
      funext j
      simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
    _ ≤ c ⬝ᵥ x := Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (hp j) (hx.2 j)

private lemma dual_certificate_of_real_value {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (b : Fin m → ℝ) (v : ℝ)
    (hfeas : (LinearOptimization.stdPolyhedron A b).Nonempty)
    (hv : ((v : ℝ) : EReal) = LinearOptimization.lpOptimalCostRhs A c b) :
    ∃ q ∈ LinearOptimization.dualFeasibleStd A c, v ≤ q ⬝ᵥ b := by
  classical
  let C : Matrix ((Fin m ⊕ Fin m) ⊕ Fin n) (Fin n) ℝ
    | Sum.inl (Sum.inl i), j => A i j
    | Sum.inl (Sum.inr i), j => -A i j
    | Sum.inr k, j => -((Pi.single k (1 : ℝ) : Fin n → ℝ) j)
  let rhs : ((Fin m ⊕ Fin m) ⊕ Fin n) → ℝ
    | Sum.inl (Sum.inl i) => b i
    | Sum.inl (Sum.inr i) => -b i
    | Sum.inr _ => 0
  have hC (x : Fin n → ℝ) : C.mulVec x ≤ rhs ↔
      x ∈ LinearOptimization.stdPolyhedron A b := by
    constructor
    · intro hx
      constructor
      · funext i
        have h₁ := hx (Sum.inl (Sum.inl i))
        have h₂ := hx (Sum.inl (Sum.inr i))
        simp [C, rhs, Matrix.mulVec, dotProduct] at h₁ h₂
        change (∑ j, A i j * x j) = b i
        exact le_antisymm h₁ h₂
      · intro j
        have hj := hx (Sum.inr j)
        simpa [C, rhs, Matrix.mulVec, dotProduct, Pi.single_apply] using hj
    · rintro ⟨hAx, hx⟩ s
      rcases s with ⟨i | i⟩ | j
      · simpa [C, rhs, Matrix.mulVec] using congrFun hAx i |>.le
      · simpa [C, rhs, Matrix.mulVec, dotProduct] using congrFun hAx i |>.ge
      · simpa [C, rhs, Matrix.mulVec, dotProduct, Pi.single_apply] using hx j
  have hvalid : ∀ x : Fin n → ℝ, C.mulVec x ≤ rhs → (-c) ⬝ᵥ x ≤ -v := by
    intro x hx
    have hx' := (hC x).mp hx
    have hi : ((v : ℝ) : EReal) ≤ ((c ⬝ᵥ x : ℝ) : EReal) := by
      rw [hv, LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
      exact iInf_le_of_le x (iInf_le_of_le hx' le_rfl)
    have := EReal.coe_le_coe_iff.mp hi
    simpa [dotProduct] using neg_le_neg this
  obtain ⟨μ, hμ, hstat, hobj⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype C rhs (-c) (-v)
      ⟨hfeas.choose, (hC hfeas.choose).mpr hfeas.choose_spec⟩).mp hvalid
  let q : Fin m → ℝ := fun i ↦ μ (Sum.inl (Sum.inr i)) - μ (Sum.inl (Sum.inl i))
  refine ⟨q, ?_, ?_⟩
  · intro j
    have hj := congrFun hstat j
    simp [C, Matrix.mulVec_apply_eq_sum, Matrix.transpose, Matrix.of_apply, dotProduct, Fintype.sum_sum_type, Pi.single_apply, q] at hj
    have hnonneg : 0 ≤ μ (Sum.inr j) := by simpa using hμ (Sum.inr j)
    change (∑ i, A i j * (μ (Sum.inl (Sum.inr i)) -
      μ (Sum.inl (Sum.inl i)))) ≤ c j
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    linarith
  · simp [rhs, dotProduct, Fintype.sum_sum_type, q] at hobj
    change v ≤ ∑ i, (μ (Sum.inl (Sum.inr i)) -
      μ (Sum.inl (Sum.inl i))) * b i
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    linarith

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (bstar : Fin m → ℝ)
    (F : (Fin m → ℝ) → ℝ) (p : Fin m → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (hfeas : (LinearOptimization.stdPolyhedron A bstar).Nonempty)
    (hfin : LinearOptimization.lpOptimalCostRhs A c bstar ≠ ⊥)
    (hF : ∀ b ∈ LinearOptimization.feasibleRhsSet A,
      ((F b : ℝ) : EReal) = LinearOptimization.lpOptimalCostRhs A c b) :
    LinearOptimization.IsLpDualOptimal bstar
      (LinearOptimization.dualFeasibleStd A c) p ↔
      LinearOptimization.IsSubgradientOn F
        (LinearOptimization.feasibleRhsSet A) p bstar := by
  classical
  have hbstar : bstar ∈ LinearOptimization.feasibleRhsSet A := hfeas
  obtain ⟨q, hq, hvq⟩ := dual_certificate_of_real_value A c bstar (F bstar)
    hfeas (hF bstar hbstar)
  have hqv : q ⬝ᵥ bstar ≤ F bstar := by
    obtain ⟨x, hx⟩ := hfeas
    have hweak := weak_duality_std A c bstar q hq x hx
    have hlower : ((q ⬝ᵥ bstar : ℝ) : EReal) ≤
        LinearOptimization.lpOptimalCostRhs A c bstar := by
      rw [LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      exact EReal.coe_le_coe_iff.mpr (weak_duality_std A c bstar q hq y hy)
    rw [← hF bstar hbstar] at hlower
    exact EReal.coe_le_coe_iff.mp hlower
  have hqeq : q ⬝ᵥ bstar = F bstar := le_antisymm hqv hvq
  constructor
  · rintro ⟨hp, hpopt⟩
    have hpeq : p ⬝ᵥ bstar = F bstar := by
      apply le_antisymm
      · have hlower : ((p ⬝ᵥ bstar : ℝ) : EReal) ≤
            LinearOptimization.lpOptimalCostRhs A c bstar := by
          rw [LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
          apply le_iInf; intro x; apply le_iInf; intro hx
          exact EReal.coe_le_coe_iff.mpr (weak_duality_std A c bstar p hp x hx)
        rw [← hF bstar hbstar] at hlower
        exact EReal.coe_le_coe_iff.mp hlower
      · simpa [hqeq] using hpopt q hq
    refine ⟨hbstar, ?_⟩
    intro b hb
    have hlower : p ⬝ᵥ b ≤ F b := by
      rw [show p ⬝ᵥ b ≤ F b ↔
        ((p ⬝ᵥ b : ℝ) : EReal) ≤ (F b : EReal) by simp]
      rw [hF b hb, LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
      apply le_iInf; intro x; apply le_iInf; intro hx
      exact EReal.coe_le_coe_iff.mpr (weak_duality_std A c b p hp x hx)
    rw [dotProduct_sub, hpeq]
    linarith
  · rintro ⟨_, hsub⟩
    have hzero : (0 : Fin m → ℝ) ∈ LinearOptimization.feasibleRhsSet A := by
      exact ⟨0, by simp [LinearOptimization.stdPolyhedron]⟩
    have hFzero : F 0 ≤ 0 := by
      have hi : LinearOptimization.lpOptimalCostRhs A c 0 ≤ ((0 : ℝ) : EReal) := by
        rw [LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
        exact iInf_le_of_le 0 (iInf_le_of_le (by simp [LinearOptimization.stdPolyhedron]) (by simp))
      rw [← hF 0 hzero] at hi
      exact EReal.coe_le_coe_iff.mp (by simpa using hi)
    have hvp : F bstar ≤ p ⬝ᵥ bstar := by
      have := hsub 0 hzero
      simp [dotProduct] at this
      change F bstar ≤ F 0 + p ⬝ᵥ bstar at this
      linarith
    have hpfeas : p ∈ LinearOptimization.dualFeasibleStd A c := by
      intro j
      by_contra hnot
      have hlt : c j < Aᵀ.mulVec p j := lt_of_not_ge hnot
      let t : ℝ := (p ⬝ᵥ bstar - F bstar + 1) / (Aᵀ.mulVec p j - c j)
      have ht : 0 < t := by dsimp [t]; positivity
      let xx : Fin n → ℝ := t • Pi.single j 1
      let bb := A.mulVec xx
      have hxx : xx ∈ LinearOptimization.stdPolyhedron A bb := by
        refine ⟨rfl, ?_⟩
        intro k
        by_cases h : k = j <;> simp [xx, Pi.single_apply, h, le_of_lt ht]
      have hbb : bb ∈ LinearOptimization.feasibleRhsSet A := by
        exact ⟨xx, hxx⟩
      have hs := hsub bb hbb
      have hFb : F bb ≤ c ⬝ᵥ xx := by
        have hi : LinearOptimization.lpOptimalCostRhs A c bb ≤ ((c ⬝ᵥ xx : ℝ) : EReal) := by
          rw [LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
          exact iInf_le_of_le xx (iInf_le_of_le hxx le_rfl)
        rw [← hF bb hbb] at hi
        exact EReal.coe_le_coe_iff.mp hi
      have hpb : p ⬝ᵥ bb = t * (Aᵀ.mulVec p j) := by
        dsimp [bb, xx]
        rw [Matrix.dotProduct_mulVec]
        simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.single_apply,
          mul_comm, mul_left_comm]
      have hcx : c ⬝ᵥ xx = t * c j := by
        dsimp [xx]
        simp [dotProduct, Pi.single_apply, mul_comm]
      rw [dotProduct_sub, hpb] at hs
      rw [hcx] at hFb
      have hdenne : Aᵀ.mulVec p j - c j ≠ 0 := by linarith
      have hkey : t * (Aᵀ.mulVec p j - c j) =
          p ⬝ᵥ bstar - F bstar + 1 := by
        dsimp [t]
        rw [div_mul_cancel₀ _ hdenne]
      nlinarith
    refine ⟨hpfeas, ?_⟩
    intro q' hq'
    have hweaklower : q' ⬝ᵥ bstar ≤ F bstar := by
      have hl : ((q' ⬝ᵥ bstar : ℝ) : EReal) ≤
          LinearOptimization.lpOptimalCostRhs A c bstar := by
        rw [LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
        apply le_iInf; intro x; apply le_iInf; intro hx
        exact EReal.coe_le_coe_iff.mpr (weak_duality_std A c bstar q' hq' x hx)
      rw [← hF bstar hbstar] at hl
      exact EReal.coe_le_coe_iff.mp hl
    exact hweaklower.trans hvp
