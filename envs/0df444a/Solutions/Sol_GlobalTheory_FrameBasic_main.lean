-- Prove2me | solution 1 for GlobalTheory.FrameBasic.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:09.243852+00:00
-- url     : https://prove2.me/submissions/51924a4a-9c8d-4dfc-9b90-56654e264a10

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_frames_basic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), LinearIndependent E (Sum.elim S.f S.f') ∧ IsCompl S.ME S.W0 ∧ (∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c) ∧ IsUnit (S.D (Fin.last (r + 1))) ∧ (∀ l, S.D l ≠ 0 → IsUnit (S.D l)) ∧ S.th ≠ 0 ∧ S.th ∈ 𝒪[F] ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.W0 = Submodule.span E (Set.range b) :=
  fun L r k S => frames_basic L r k S
end GlobalTheory.FrameBasic
