-- Prove2me | solution 1 for GlobalTheory.sigmaSign_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:15.694018+00:00
-- url     : https://prove2.me/submissions/cfe8d8b0-5b00-478b-a9d1-50c95985c3b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_conj_latticeForm
import Theorems.Thm_GlobalTheory_canonicalSigma_eq_zero_iff
import Theorems.Thm_GlobalTheory_canonicalSigma_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {a b : ℂ} (ha : a ∈ L.lattice) (hb : b ∈ L.lattice) :
    sigmaSign L (a + b) =
      sigmaSign L a * sigmaSign L b * cexp (π * I * (latticeForm L a b).im) := by
  set x := L.ω₁ / 2
  have hx : canonicalSigma L x ≠ 0 :=
    (canonicalSigma_eq_zero_iff L).not.2 L.ω₁_div_two_notMem_lattice
  have h1 := canonicalSigma_add L (add_mem ha hb) x
  rw [← add_assoc, canonicalSigma_add L hb, canonicalSigma_add L ha] at h1
  have h2 : cexp (π * latticeForm L (x + a) b + π * latticeForm L b b / 2) *
      cexp (π * latticeForm L x a + π * latticeForm L a a / 2) =
      cexp (π * I * (latticeForm L a b).im) *
      cexp (π * latticeForm L x (a + b) + π * latticeForm L (a + b) (a + b) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have h3 := sub_conj (latticeForm L a b)
    rw [conj_latticeForm] at h3
    push_cast at h3
    simp only [latticeForm, map_add] at h3 ⊢
    linear_combination (π / 2 : ℂ) * h3
  refine mul_right_cancel₀ (mul_ne_zero (exp_ne_zero
    (π * latticeForm L x (a + b) + π * latticeForm L (a + b) (a + b) / 2)) hx) ?_
  linear_combination sigmaSign L a * sigmaSign L b * canonicalSigma L x * h2 - h1
end GlobalTheory
