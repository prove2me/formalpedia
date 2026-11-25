-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.trel_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:58:28.656094+00:00
-- url     : https://prove2.me/submissions/1fa4b76f-be91-4799-8388-931b177b4199

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_img_mul
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_img_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution (P : FPair H r) : Equivalence (TRel P) where
  refl t := ⟨1, P.St.one_mem, (img_one _).symm⟩
  symm := by
    rintro t t' ⟨s, hs, h⟩
    refine ⟨s⁻¹, P.St.inv_mem hs, ?_⟩
    rw [h, ← img_mul, inv_mul_cancel, img_one]
  trans := by
    rintro t t' t'' ⟨s, hs, h⟩ ⟨s', hs', h'⟩
    exact ⟨s' * s, P.St.mul_mem hs' hs, by rw [h', h, img_mul]⟩
end GlobalTheory.NonGenericLocalCheck
