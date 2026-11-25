-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.isOpen_alt_bis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:53.1666+00:00
-- url     : https://prove2.me/submissions/c89662ed-e7f7-443e-a320-4276082218e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_mem_src_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
theorem _root_.solution (p : (k : K) → ι k) : IsOpen (src P p) := by
  have : src P p = ⋂ k, {x : Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x; simp [mem_src_iff]
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
