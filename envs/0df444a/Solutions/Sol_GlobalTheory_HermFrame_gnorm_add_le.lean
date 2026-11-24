-- Prove2me | solution 1 for GlobalTheory.HermFrame.gnorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:51.633515+00:00
-- url     : https://prove2.me/submissions/a5a4d790-61aa-452d-810f-167747511a0f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
namespace GlobalTheory.HermFrame
theorem _root_.solution {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    gnorm H (v + w) ≤ gnorm H v + gnorm H w := by
  obtain ⟨R, -, h2⟩ := exists_root hH
  rw [h2, h2, h2, map_add]; exact norm_add_le _ _
end GlobalTheory.HermFrame
