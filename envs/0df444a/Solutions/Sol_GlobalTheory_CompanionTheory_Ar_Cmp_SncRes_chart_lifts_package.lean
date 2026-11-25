-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:58.930414+00:00
-- url     : https://prove2.me/submissions/31ed9e30-1fc4-49a8-ba45-d4684fc866f5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_sameOrbit_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_sameOrbit_trans
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_proj_eq_of_sameOrbit
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_sameOrbit_of_proj_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_orbit_rep_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_lift_mem_conePts
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_zero_bd_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_proj_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_rep_mem
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ReciprocityTheory.AnForm.R.IsMultiHomogIdeal D → (∀ x : SncRes.Pts P, ∃ p : (k : K) → ι k, x ∈ SncRes.src P p) ∧ (∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts P) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x) (SncRes.lift p' q))) ∧ (∀ z ∈ ReciprocityTheory.AnForm.R.conePts P, ∃ p : (k : K) → ι k, ∃ x ∈ SncRes.src P p, ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) z) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ x' ∈ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x') (SncRes.lift p' q)) → x = x') ∧ ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ((∀ h ∈ SncRes.bd P D p, eval (SncRes.coord P p x) h = 0) ↔ (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts D) := by
  intro K _ ι _ P D hP hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart (rep x) (rep_mem x).1
    exact ⟨p, hp⟩
  · exact fun p x hx => SncRes.lift_mem_conePts hP p x hx
  · intro p p' x hx
    exact SncRes.sameOrbit_trans (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx.1))
      (SncRes.orbit_rep_lift p' x hx.2)
  · intro z hz
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z hz.1
    let x : SncRes.Pts P := ⟨SncRes.proj z, z, hz, rfl⟩
    have hrz : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) z :=
      SncRes.sameOrbit_of_proj_eq (SncRes.rep_mem x).1 hz.1 (SncRes.proj_rep x)
    have hx : x ∈ SncRes.src P p := by
      obtain ⟨c, hc, he⟩ := hrz
      intro k
      rw [he]
      exact mul_ne_zero (hc k) (hp k)
    exact ⟨p, x, hx, SncRes.sameOrbit_trans
      (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx)) hrz⟩
  · intro p p' x hx x' hx' h
    have h1 : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) (SncRes.rep x') :=
      SncRes.sameOrbit_trans (SncRes.orbit_rep_lift p x hx)
        (SncRes.sameOrbit_trans h (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p' x' hx')))
    apply Subtype.ext
    rw [← SncRes.proj_rep x, ← SncRes.proj_rep x']
    exact SncRes.proj_eq_of_sameOrbit h1
  · exact fun p x hx => SncRes.zero_bd_iff hP hD p x hx
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
