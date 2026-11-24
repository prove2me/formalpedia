-- Prove2me | solution 1 for GlobalTheory.entire_antilinear_periods_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:37.482932+00:00
-- url     : https://prove2.me/submissions/853c2bd3-a5a6-4cf4-891d-8fdc459ee5de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConst
import Theorems.Thm_GlobalTheory_entire_sub_conj_bounded_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by
  intro g Λ hdisc hspan v t hv hper
  have : IsZLattice ℝ Λ := ⟨hspan⟩

  have hcont : Continuous (fun z => v z - t ⬝ᵥ star z) :=
    hv.continuous.sub (continuous_const.dotProduct continuous_star)
  have hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z := by
    intro z w hw
    simp only
    rw [hper ⟨w, hw⟩ z, star_add, dotProduct_add]
    ring
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded

  have hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0 := by
    intro d
    have hd : Differentiable ℂ (fun s : ℂ => v (s • d)) :=
      hv.comp (differentiable_id.smul_const d)
    have hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M := by
      intro s
      have e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d) := by
        rw [star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
      rw [e]
      exact hM _ ⟨s • d, rfl⟩
    obtain ⟨h1, h2⟩ := entire_sub_conj_bounded_const hd hb
    exact ⟨h1, fun s => by simpa using h2 s⟩
  refine ⟨?_, fun z => by simpa using (hline z).2 1⟩
  funext i
  have hi := (hline (Pi.single i 1)).1
  rw [← Pi.single_star, star_one, dotProduct_single, mul_one] at hi
  simpa using hi
end GlobalTheory
