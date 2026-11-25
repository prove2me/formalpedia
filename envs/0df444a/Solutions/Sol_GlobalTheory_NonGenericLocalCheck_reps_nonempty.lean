-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.reps_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:41.240112+00:00
-- url     : https://prove2.me/submissions/40531ffb-5c34-4d05-99bd-7c80e7f037d4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_exists_transv
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_trel_equiv
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_rel_equiv

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
theorem _root_.solution (P : FPair H r) : Nonempty (Reps P) := by
  choose RT hRT using fun d : Datum P =>
    exists_transv (TRel P) (trel_equiv P) {t | IsTermOver P d t}
  obtain ⟨RD, hRD⟩ := exists_transv (Datum.Rel (P := P)) (rel_equiv P) Set.univ
  exact ⟨⟨RD, RT, hRD, hRT⟩⟩
end GlobalTheory.NonGenericLocalCheck
