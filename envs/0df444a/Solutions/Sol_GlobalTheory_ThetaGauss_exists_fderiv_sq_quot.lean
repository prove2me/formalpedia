-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.exists_fderiv_sq_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:25.424548+00:00
-- url     : https://prove2.me/submissions/c0cb9eb7-ef0c-4619-b0d9-b715442faf86

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_entire_quot
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_bound_on_line
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_entire_quot_of_lines
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (v : Fin g → ℂ) (hD : Differentiable ℂ fun z => fderiv ℂ θ z v)
    (hm : ∀ a, θ a = 0 → fderiv ℂ θ a v = 0) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ ∀ z, ψ z * θ z = fderiv ℂ θ z v ^ 2 := by
  refine exists_entire_quot_of_lines hθ (hD.pow 2) h0 fun z w hw => ?_
  have hl : Differentiable ℂ fun s : ℂ => z + s • w := by fun_prop
  refine exists_entire_quot (N := fun s => fderiv ℂ θ (z + s • w) v ^ 2) ((hD.comp hl).pow 2)
    (hθ.comp hl) hw fun s₀ _ => ?_
  have e : ∀ s : ℂ, z + s₀ • w + (s - s₀) • w = z + s • w := fun s => by
    rw [sub_smul]; abel
  obtain ⟨s₁, hs₁⟩ := hw
  obtain ⟨C, hC⟩ := bound_on_line hθ v hm (z + s₀ • w) w ⟨s₁ - s₀, by rwa [e]⟩
  have ht : Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun s hs => sub_ne_zero.2 hs⟩
    exact ((continuous_sub_right s₀).tendsto' s₀ 0 (sub_self _)).mono_left nhdsWithin_le_nhds
  exact ⟨C, (ht.eventually hC).mono fun s hs => by rwa [e] at hs⟩
end GlobalTheory.ThetaGauss
