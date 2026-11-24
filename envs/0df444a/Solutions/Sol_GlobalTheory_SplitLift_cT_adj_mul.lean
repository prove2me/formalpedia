-- Prove2me | solution 1 for GlobalTheory.SplitLift.cT_adj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:36.072324+00:00
-- url     : https://prove2.me/submissions/bf8a0d7f-cf9c-4bb1-8543-67586468a835

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
import Theorems.Thm_GlobalTheory_SplitLift_cT_cT
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.SplitLift
theorem _root_.solution (s : A →+* A) (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hH : IsHerm s J) (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) : cT s (adj s J X) * J = J * X := by
  have hH' : cT s J = J := hH
  have h1 : cT s J⁻¹ * J = 1 := by
    have := congrArg (cT s) (Matrix.mul_nonsing_inv _ hJ)
    rwa [cT_mul, cT_one, hH'] at this
  simp only [adj, cT_mul, cT_cT s hs, hH', Matrix.mul_assoc, h1, Matrix.mul_one]
end GlobalTheory.SplitLift
