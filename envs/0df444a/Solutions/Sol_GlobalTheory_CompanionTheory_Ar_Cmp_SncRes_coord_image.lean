-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.coord_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:20:08.043652+00:00
-- url     : https://prove2.me/submissions/bd681930-ed96-4499-a2b4-77c01afb0d27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomial
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_proj_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_rep_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_sameOrbit_of_proj_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_affCoord_eq_of_sameOrbit
import Theorems.Thm_ReciprocityTheory_AnForm_R_conePts_of_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_conePts_iff_chartIdeal
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
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact renPt_zero (chartIdeal P p) (affCoord p (rep x))
      ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))
  · intro ht
    obtain ⟨w, hwd⟩ : ∃ w, w = t ∘ Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
    have hren : renPt w = t := by
      subst hwd
      funext l
      simp [renPt]
    have hw : ∀ h ∈ chartIdeal P p, eval w h = 0 := by
      intro h hh
      rw [← eval_renC w h, hren]
      exact ht _ (Ideal.mem_map_of_mem _ hh)
    obtain ⟨hc, h1, ha⟩ := conePts_of_chartIdeal hP p w hw
    let x : Pts P := ⟨proj w, w, hc, rfl⟩
    have ho : SameOrbit (rep x) w := sameOrbit_of_proj_eq (rep_mem x).1 hc.1 (proj_rep x)
    refine ⟨x, fun k => ?_, ?_⟩
    · obtain ⟨c, hcn, hcz⟩ := ho
      have hk : rep x ⟨k, p k⟩ = c k * w ⟨k, p k⟩ := congrFun hcz ⟨k, p k⟩
      rw [hk, h1 k, mul_one]
      exact hcn k
    · show renPt (affCoord p (rep x)) = t
      rw [affCoord_eq_of_sameOrbit p ho, ha, hren]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
