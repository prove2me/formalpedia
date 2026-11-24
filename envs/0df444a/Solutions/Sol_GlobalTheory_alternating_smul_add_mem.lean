-- Prove2me | solution 1 for GlobalTheory.alternating_smul_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:23.116626+00:00
-- url     : https://prove2.me/submissions/d4543245-f44c-427c-9024-d4ecdf556087

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (ω : M [⋀^ι]→ₗ[R] N) (P : Submodule R N) (θ : M) (a : ι → R)
    (w : ι → M) (h₀ : ω w ∈ P) (h₁ : ∀ i, ω (Function.update w i θ) ∈ P) :
    ω (fun i => a i • θ + w i) ∈ P := by
  have e := ω.toMultilinearMap.map_add_univ (fun i => a i • θ) w
  change ω (fun i => a i • θ + w i) = ∑ s : Finset ι, ω (s.piecewise (fun i => a i • θ) w) at e
  rw [e]
  refine Submodule.sum_mem _ fun s _ => ?_
  have e₂ : s.piecewise (fun i => a i • θ) w
      = fun i => (s.piecewise a (fun _ => 1) i) • (s.piecewise (fun _ => θ) w i) := by
    funext i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [e₂, ω.map_smul_univ]
  refine P.smul_mem _ ?_
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simpa using h₀
  by_cases hs : s = {i}
  · subst hs
    rw [Finset.piecewise_singleton]
    exact h₁ i
  · obtain ⟨j, hj, hji⟩ : ∃ j ∈ s, j ≠ i := by
      by_contra hc
      push Not at hc
      exact hs (Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, hc⟩)
    rw [ω.map_eq_zero_of_eq _ (i := j) (j := i) (by simp [hi, hj]) hji]
    exact P.zero_mem
end GlobalTheory
