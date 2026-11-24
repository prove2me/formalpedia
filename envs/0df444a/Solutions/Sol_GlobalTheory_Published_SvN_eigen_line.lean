-- Prove2me | solution 1 for GlobalTheory.Published.SvN.eigen_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:21.466503+00:00
-- url     : https://prove2.me/submissions/9a0fc1f4-09c7-44ac-9692-32774bd50655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Alt_sq_swap
import Theorems.Thm_GlobalTheory_Published_SvN_Ops_comm
import Theorems.Thm_GlobalTheory_Published_SvN_eq_zero_of_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution (h : Alt c) (hρ : Ops c ρ) (hα : Splits c A α) (hA : h.perp A ≤ A) {e : M}
    (he : ∀ a ∈ A, ρ a e = α a • e) {v : M} (hv : v ∈ Submodule.span ℂ (Set.range fun x => ρ x e))
    (hva : ∀ a ∈ A, ρ a v = α a • v) : ∃ r : ℂ, v = r • e := by
  classical
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  rw [Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ A)] at hva ⊢
  have h1 : ∑ x ∈ f.support with x ∈ A, f x • ρ x e = (∑ x ∈ f.support with x ∈ A, f x * α x) • e := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun x hx => by rw [he x (Finset.mem_filter.1 hx).2, smul_smul]
  rw [h1] at hva ⊢
  refine ⟨_, add_eq_left.2 ?_⟩
  have h2 : ∑ x ∈ f.support with x ∉ A, f x • ρ x e = ∑ x ∈ f.support.subtype (· ∉ A), f x.1 • ρ x.1 e :=
    (Finset.sum_subtype_eq_sum_filter fun x => f x • ρ x e).symm
  rw [h2] at hva ⊢
  refine eq_zero_of_sum (ρ := ρ) (A := A) (α := α) _ (fun x a => c a x.1 ^ 2 * α a) (fun x => ?_) _ (fun x a ha => ?_) fun a ha => ?_
  · by_contra hc
    push Not at hc
    exact x.2 (hA fun a ha => h.sq_swap ((mul_eq_right₀ (hα.ne a ha)).1 (hc a ha)))
  · rw [map_smul, hρ.comm h, he a ha, map_smul, smul_smul, smul_smul, smul_smul]
    congr 1; ring
  · have := hva a ha
    rwa [map_add, map_smul, he a ha, smul_add, smul_comm, add_right_inj] at this
end GlobalTheory.Published.SvN
