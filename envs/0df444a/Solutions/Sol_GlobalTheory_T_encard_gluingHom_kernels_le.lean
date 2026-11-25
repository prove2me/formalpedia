-- Prove2me | solution 1 for GlobalTheory.T.encard_gluingHom_kernels_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:23.307179+00:00
-- url     : https://prove2.me/submissions/f08f7f4e-66f3-422a-8f90-de0d1d73f3a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardGluingHomKernelsLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardGluingHomKernelsLeStatement
import Theorems.Thm_GlobalTheory_HL_GluingKernels_encard_kernels_le


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  first | exact @GlobalTheory.HL.GluingKernels.encard_kernels_le | exact GlobalTheory.HL.GluingKernels.encard_kernels_le | (intros; apply GlobalTheory.HL.GluingKernels.encard_kernels_le <;> assumption)
end _root_.GlobalTheory.T
