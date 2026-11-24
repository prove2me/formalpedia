-- Prove2me | solution 1 for GlobalTheory.KTypeSteps.pfil_one_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:03.809221+00:00
-- url     : https://prove2.me/submissions/bdb02f57-dc28-4ce7-8510-21e74fa398d2

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_KtypesWithinSteps
import Theorems.Thm_GlobalTheory_KTypeSteps_kSpan_le_ker
import Theorems.Thm_Formalism_REAL_arrModule
import Theorems.Thm_Formalism_REAL_compact_span_le_of_stable
import Theorems.Thm_Formalism_REAL_compact_span_stable_general
import Theorems.Thm_Formalism_REAL_glRel_kRel
import Theorems.Thm_Formalism_REAL_hVCoeff
import Theorems.Thm_Formalism_REAL_kDecomp
import Theorems.Thm_Formalism_REAL_mem_compact_span_self_general
import Theorems.Thm_Formalism_REAL_noncompact_arr_finite_dimensional
import Theorems.Thm_Formalism_REAL_noncompact_arr_one_compact_stable
import Theorems.Thm_Formalism_REAL_pfilFacts
import Theorems.Thm_Formalism_REAL_thetaFil


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.KTypeSteps
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace GlobalTheory.KTypeSteps
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hfd : FiniteDimensional ℂ (kSpan ε E y))
    (hne : μ ≠ ν) (hne' : ∀ a b, ε a ≠ ε b → μ ≠ ν + root a b) :
    pfil ε E y 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  refine le_trans ((thetaFil V n ε E y hg).2.1 0) (sup_le ?_ ?_)
  · obtain ⟨hA, hθ⟩ := (arrModule V n ε E 1).1 hg
    have hKU := (arrModule V n ε E 1).2 hu
    have := noncompact_arr_finite_dimensional (j := 1) hfd
    obtain ⟨m, F, lam, hF, -, hsup⟩ := kDecomp (Arr V n 1) n ε (arrE E 1) (arrV0 ε E y 1)
      inferInstance (glRel_kRel ε _ hA) hKU noncompact_arr_one_compact_stable
    change (arrV0 ε E y 1).map (thetaA E 1) ≤ _
    rw [← hsup, Submodule.map_le_iff_le_comap]
    refine iSup_le fun i => ?_
    obtain ⟨hmem, h0, hhi⟩ := hF i
    obtain ⟨a, b, hab, hlam⟩ := hVCoeff V n ε E ν (lam i) y (F i) hg hu hy hmem hhi h0
    have hθhi : KHighest ε E (lam i) (thetaA E 1 (F i)) := by
      refine ⟨fun c => ?_, fun c d hcd he => ?_⟩
      · rw [← hθ, hhi.1 c, map_smul]
      · rw [← hθ, hhi.2 c d hcd he, map_zero]
    have hle : kSpan ε (arrE E 1) (F i) ≤ (kSpan ε E (thetaA E 1 (F i))).comap (thetaA E 1) := by
      refine compact_span_le_of_stable ?_ (mem_compact_span_self_general _)
      intro c d hcd G hG
      rw [Submodule.mem_comap] at hG ⊢
      rw [hθ]
      exact compact_span_stable_general _ c d hcd _ hG
    exact hle.trans (Submodule.comap_mono
      (kSpan_le_ker hg hu hx hθhi (hlam ▸ hne' a b hab)))
  · rw [(pfilFacts V n ε E y hg).1]
    exact kSpan_le_ker hg hu hx hy hne
end GlobalTheory.KTypeSteps
