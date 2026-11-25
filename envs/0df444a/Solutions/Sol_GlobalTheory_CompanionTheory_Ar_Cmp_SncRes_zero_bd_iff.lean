-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.zero_bd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:10.020413+00:00
-- url     : https://prove2.me/submissions/68dc8812-8297-4358-b523-a390102f89c5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_lift_vec
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_lift_mem_conePts
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_isMultiHomogIdeal_sup
import Theorems.Thm_ReciprocityTheory_AnForm_R_conePts_of_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_renPt_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (∀ h ∈ bd P D p, eval (coord P p x) h = 0) ↔
      (fun q => eval (coord P p x) (lift p q)) ∈ conePts D := by
  have hmem := lift_mem_conePts hP p x hx
  rw [lift_vec p x hx] at hmem ⊢
  have hone : ∀ k, affCoord p (rep x) ⟨k, p k⟩ = 1 := fun k => by
    simp [affCoord, hx k]
  constructor
  · intro h
    have hz : ∀ f ∈ chartIdeal (P ⊔ D) p, eval (affCoord p (rep x)) f = 0 := by
      intro f hf
      rw [← eval_renC]
      exact h _ (Ideal.le_radical (Ideal.mem_map_of_mem _ hf))
    have := (conePts_of_chartIdeal (isMultiHomogIdeal_sup hP hD) p _ hz).1
    exact ⟨this.1, fun f hf => this.2 f (Ideal.mem_sup_right hf)⟩
  · intro hDm g hg
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval (affCoord p (rep x))) := by
      refine sup_le (sup_le (fun f hf => hmem.2 f hf) (fun f hf => hDm.2 f hf)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval _ _ = 0
      simp [hone k]
    obtain ⟨n, hn⟩ := hg
    have h0 := renPt_zero (chartIdeal (P ⊔ D) p) (affCoord p (rep x)) (fun f hf => hle hf) _ hn
    rw [map_pow] at h0
    exact eq_zero_of_pow_eq_zero h0
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
