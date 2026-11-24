-- Prove2me | solution 1 for GlobalTheory.LowestWeight.exists_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:23.643893+00:00
-- url     : https://prove2.me/submissions/3e03f0da-d2d7-4700-91de-fa5ca761cd76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
open GlobalTheory.LowestWeight
variable {r : ℕ}
namespace GlobalTheory.LowestWeight
theorem _root_.solution (Y : Matrix (Fin r) (Fin r) ℂ) (hY : ∀ i, lminor Y i ≠ 0) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, (∀ a, B a a = 1) ∧ (∀ a c, c < a → B a c = 0) ∧
      ∀ a c, a < c → (Y * B) a c = 0 := by
  have key : ∀ c : Fin r, ∃ u : Fin r → ℂ, u c = 1 ∧ (∀ a, c < a → u a = 0) ∧
      ∀ a, a < c → (Y *ᵥ u) a = 0 := by
    intro c
    have hc : (c : ℕ) ≤ r := c.isLt.le
    set A := Y.submatrix (Fin.castLE hc) (Fin.castLE hc) with hA
    have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 (hY c.castSucc)
    set w : Fin c → ℂ := A⁻¹ *ᵥ fun a => -Y (Fin.castLE hc a) c with hw
    have hAw : A *ᵥ w = fun a => -Y (Fin.castLE hc a) c := by
      rw [hw, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hne : ∀ (j : Fin c) (a : Fin r), c ≤ a → a ≠ Fin.castLE hc j := by
      intro j a ha h
      have := j.isLt
      have h' : (a : ℕ) = j := by rw [h]; rfl
      have : (c : ℕ) ≤ a := ha
      omega
    refine ⟨Pi.single c 1 + ∑ j : Fin c, w j • Pi.single (Fin.castLE hc j) 1, ?_, ?_, ?_⟩
    · simp [Finset.sum_apply, Pi.single_eq_of_ne (hne _ c le_rfl)]
    · intro a ha
      simp [Finset.sum_apply, Pi.single_eq_of_ne (hne _ a ha.le), Pi.single_eq_of_ne ha.ne']
    · intro a ha
      have h := congrFun hAw ⟨a, ha⟩
      rw [mulVec_add, mulVec_sum]
      simp only [mulVec_smul, mulVec_single_one, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.col_apply]
      simp only [mulVec, dotProduct, hA, submatrix_apply] at h
      have e : Fin.castLE hc ⟨a, ha⟩ = a := rfl
      rw [e] at h
      rw [Finset.sum_congr rfl fun j _ => mul_comm (w j) _, h]
      ring
  choose u h1 h2 h3 using key
  exact ⟨Matrix.of fun a c => u c a, h1, fun a c h => h2 c a h, fun a c h => h3 c a h⟩
end GlobalTheory.LowestWeight
