-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.mContDiffAt_orthCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:30.236872+00:00
-- url     : https://prove2.me/submissions/bc473eb0-dcb6-4f83-b34a-6c61d54d82b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype l] [DecidableEq l]
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthCoeff (H x)) z :=
  (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose
end GlobalTheory.HermFrame.Model
