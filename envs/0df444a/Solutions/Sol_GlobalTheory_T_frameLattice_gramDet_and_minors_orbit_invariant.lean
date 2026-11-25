-- Prove2me | solution 1 for GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:44.68311+00:00
-- url     : https://prove2.me/submissions/8d9a862c-d27c-4d30-a9ad-29a465d92cb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameGram_main


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', (∃ c : F, c ≠ 0 ∧ vE L S.ϖ (algebraMap F E c) = S.a ∧ (Matrix.of fun a b => S.h (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) b) (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) a)).det = algebraMap F E c) ∧ (∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l) ∧ Submodule.span E (Set.range (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))))) = S.ME := by
  first | exact @GlobalTheory.FrameGram.main | exact GlobalTheory.FrameGram.main | (intros; apply GlobalTheory.FrameGram.main <;> assumption)
end _root_.GlobalTheory.T
