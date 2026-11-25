-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCount.casG_polar_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:08.738675+00:00
-- url     : https://prove2.me/submissions/6e971d27-6cea-4839-889d-10831f4e36f5

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CountingBound
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_casG_polar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCount
namespace GlobalTheory.CompanionTheory.ZuckCount
theorem _root_.solution {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    (casG (addSet μ J) : ℂ) + (casG (μ + Pi.single s 1) : ℂ) + (2 - (casG μ : ℂ))
      - (casG (addSet μ J + Pi.single s 1) : ℂ) = if s ∈ J then 0 else 2 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (casG_polar μ J s)
  split_ifs at h ⊢ <;> (push_cast at h; exact h)
end GlobalTheory.CompanionTheory.ZuckCount
