-- Prove2me | solution 1 for GlobalTheory.LFunction_one_eq_classNumber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:18.908793+00:00
-- url     : https://prove2.me/submissions/cdce8786-265d-47eb-8220-2a7837ff4bf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_exists_isIdealClassPoint
import Theorems.Thm_GlobalTheory_LFunction_one_and_mean_log_eta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
  {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ)
include h2 hD hd hχ
include σ
namespace GlobalTheory
theorem _root_.solution : χ.LFunction 1 = (π * classNumber K / √d : ℝ) := by
  choose τ hτ using exists_isIdealClassPoint h2 hD σ
  exact (LFunction_one_and_mean_log_eta h2 hD hd hχ σ hτ).1
end GlobalTheory
