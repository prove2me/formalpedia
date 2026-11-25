-- Prove2me | solution 1 for GlobalTheory.HL.DivisibleGauss.index_span_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:35:05.382101+00:00
-- url     : https://prove2.me/submissions/75e2297e-0dac-4121-afaf-a55b7cc3f9bb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DivisibleGauss
namespace GlobalTheory.HL.DivisibleGauss
theorem _root_.solution {A : Type*} [CommRing A] (c : A →+* A) (hc : ∀ x, c (c x) = x)
    (x : A) :
    (Ideal.span {c x}).toAddSubgroup.index = (Ideal.span {x}).toAddSubgroup.index := by
  have hs : Function.Surjective c.toAddMonoidHom := fun z => ⟨c z, hc z⟩
  rw [← AddSubgroup.index_comap_of_surjective _ hs]
  congr 1
  ext z
  simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
  constructor
  · intro h
    have h' : c x ∣ c z := h
    simpa only [hc] using map_dvd c h'
  · exact fun h => map_dvd c h
end GlobalTheory.HL.DivisibleGauss
