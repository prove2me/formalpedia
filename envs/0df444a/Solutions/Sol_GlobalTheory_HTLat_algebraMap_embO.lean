-- Prove2me | solution 1 for GlobalTheory.HTLat.algebraMap_embO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:09.979603+00:00
-- url     : https://prove2.me/submissions/2d7559ba-df0b-406c-bbd5-657a2ed7bfd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
omit [NumberField E]
namespace GlobalTheory.HTLat
namespace _root_.GlobalTheory.HTLat
theorem _root_.solution (φ : E →+* C) (a : 𝓞 E) :
    algebraMap O C (_root_.GlobalTheory.HTLat.embO hv φ a) = φ a := by
  have hb : Function.Bijective (algebraMap O C).rangeRestrict :=
    ⟨fun _ _ hab => hv.hom_inj (congrArg Subtype.val hab), (algebraMap O C).rangeRestrict_surjective⟩
  have hm : ∀ x, (φ.comp (algebraMap (𝓞 E) E)) x ∈ (algebraMap O C).range := fun x =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1
      ((map_isIntegral_int φ (NumberField.RingOfIntegers.isIntegral_coe x)).tower_top))
  exact congrArg Subtype.val
    ((RingEquiv.ofBijective (algebraMap O C).rangeRestrict hb).apply_symm_apply
      ((φ.comp (algebraMap (𝓞 E) E)).codRestrict _ hm a))
end _root_.GlobalTheory.HTLat
end GlobalTheory.HTLat
