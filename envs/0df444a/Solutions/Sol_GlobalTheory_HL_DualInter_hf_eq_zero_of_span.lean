-- Prove2me | solution 1 for GlobalTheory.HL.DualInter.hf_eq_zero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:37.95924+00:00
-- url     : https://prove2.me/submissions/a911708b-f8ba-4ec5-826d-df8a61d194f7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm}
namespace GlobalTheory.HL.DualInter
theorem _root_.solution {S : Set (Fin n → E)} {y : Fin n → E} (hy : ∀ x ∈ S, hf L Hm x y = 0) :
    ∀ x ∈ Submodule.span E S, hf L Hm x y = 0 := fun x hx =>
  (Submodule.span_le (p := LinearMap.ker (hfL L Hm y))).2 hy hx
end GlobalTheory.HL.DualInter
