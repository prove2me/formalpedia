-- Prove2me | solution 1 for GlobalTheory.Chow.isPrime_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:02.057841+00:00
-- url     : https://prove2.me/submissions/21998bd6-5411-4edc-93f6-6925cf9d5af7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_mem_elimIdeal_iff_of_generic
import Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint_eq_zero_iff
import Theorems.Thm_GlobalTheory_Chow_genericPoint_ne_zero
import Theorems.Thm_GlobalTheory_isPrime_span_linForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]
namespace GlobalTheory.Chow
theorem _root_.solution {p : Ideal (MvPolynomial σ K)} [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    (elimIdeal β p).IsPrime := by
  have hne := genericPoint_ne_zero hp
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have h := isPrime_span_linForm (ι := β) (genericPoint p) (Ne.isUnit hj) Set.univ
  rw [Set.image_univ] at h
  have : elimIdeal β p = (Ideal.span (Set.range (linForm (genericPoint p) : β → _))).comap
      (map (algebraMap K _)) :=
    Ideal.ext fun f => mem_elimIdeal_iff_of_generic (aeval_genericPoint_eq_zero_iff p) hne
  rw [this]
  exact Ideal.comap_isPrime _ _
end GlobalTheory.Chow
