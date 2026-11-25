-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.exists_zmod_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:43.291798+00:00
-- url     : https://prove2.me/submissions/7e6de537-71e5-4561-ab84-69f19a9fbb51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix
namespace GlobalTheory.TorsionMatrix
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod l) V] (hc1 : Nat.card V = l ^ m) :
    ∃ b : Fin m → V, ∀ x : V, ∃! t : Fin m → ZMod l, x = ∑ j, (t j).val • b j := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hc1]; exact pow_ne_zero _ hl.out.ne_zero)
  have hr : Module.finrank (ZMod l) V = m := by
    have := Module.natCard_eq_pow_finrank (K := ZMod l) (V := V)
    rw [hc1, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hl.out.two_le this).symm
  let b := Module.finBasisOfFinrankEq (ZMod l) V hr
  have hs : ∀ t : Fin m → ZMod l, ∑ j, (t j).val • b j = b.equivFun.symm t := by
    intro t
    rw [b.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul (ZMod l), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hs, LinearEquiv.symm_apply_apply]
  · simp only [hs] at ht
    rw [ht, LinearEquiv.apply_symm_apply]
end GlobalTheory.TorsionMatrix
