-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.mem_src_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:45:40.030411+00:00
-- url     : https://prove2.me/submissions/f4572184-5392-4a16-b853-68ea862447f6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_normSq_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_proj_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_rep_mem


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
theorem _root_.solution (p : (k : K) → ι k) (x : Pts P) :
    x ∈ src P p ↔ ∀ k, x.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
  refine forall_congr' fun k => ?_
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  rw [← proj_rep x]
  simp only [proj, ne_eq, div_eq_zero_iff, h, or_false, mul_eq_zero, map_eq_zero, or_self]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
