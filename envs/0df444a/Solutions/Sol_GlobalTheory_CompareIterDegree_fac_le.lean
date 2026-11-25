-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.fac_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:00.582271+00:00
-- url     : https://prove2.me/submissions/56981655-a4b0-49a5-b5f0-88e998b3d987

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
namespace GlobalTheory.CompareIterDegree
theorem _root_.solution {x y t : ℝ} (hxy : 0 < x * y) (h : t * y ≤ t * x) : (x + t) / x ≤ (y + t) / y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy.ne'
  have hy : y ≠ 0 := right_ne_zero_of_mul hxy.ne'
  have : (y + t) / y - (x + t) / x = (t * x - t * y) / (x * y) := by field_simp; ring
  have h2 := div_nonneg (sub_nonneg.2 h) hxy.le
  linarith
end GlobalTheory.CompareIterDegree
