-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_irr_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:59:52.283414+00:00
-- url     : https://prove2.me/submissions/b82bafb3-738e-4042-ab0f-810171565308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_apply_eq
import Theorems.Thm_GlobalTheory_Published_SvN_ops_of_central
import Theorems.Thm_GlobalTheory_Published_SvN_irr_of_span

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
open Heisenberg
variable {F W M : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (Heisenberg B) M}
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [TopologicalSpace W]
  [IsModuleTopology F W]
variable (hB : B.IsAlt) {A : AddSubgroup W} {α : W → ℂ} (hα : Splits (fun x y => ψ (B x y / 2)) A α)
  (hA : (alt_psi hB ψ).perp A ≤ A) (h1 : ∀ᶠ u in 𝓝 (0 : W), u ∈ A ∧ α u = 1)
  (h2 : ∀ N ∈ 𝓝 (0 : W), ∃ T, ((alt_psi hB ψ).perp T : Set W) ⊆ N ∧ Finite (A ⧸ ((alt_psi hB ψ).perp T).addSubgroupOf A))
  (h3 : ∀ w, ∀ᶠ u in 𝓝 (0 : W), ψ (B u w / 2) ^ 2 = 1)
include hα hA h1 h2 h3
namespace GlobalTheory.Published.SvN
theorem _root_.solution (hψ : Continuous ψ) (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) {e : M} (he0 : e ≠ 0)
    (he : ∀ a ∈ A, π ⟨a, 0⟩ e = α a • e) :
    ∃ P : Subrepresentation π, e ∈ P.toSubmodule ∧ IsIrrSmoothOf ψ P.toRepresentation := by
  let N := Submodule.span ℂ (Set.range fun x => π ⟨x, 0⟩ e)
  have hN : ∀ g, ∀ v ∈ N, π g v ∈ N := by
    intro g v hv
    have : N.map (π g) ≤ N := by
      rw [Submodule.map_span_le]
      rintro _ ⟨y, rfl⟩
      beta_reduce
      rw [← Module.End.mul_apply, ← map_mul, apply_eq hπ]
      exact N.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    exact this ⟨v, hv, rfl⟩
  have heN : e ∈ N := Submodule.subset_span ⟨0, (ops_of_central hπ).zero e⟩
  refine ⟨⟨N, fun g v hv => hN g v hv⟩, heN, irr_of_span hB hα hA h1 h2 h3 hψ (fun t v => Subtype.ext (hπ t v.1)) (e := ⟨e, heN⟩)
    (fun h => he0 (congrArg Subtype.val h)) (fun a ha => Subtype.ext (he a ha)) ?_⟩
  apply Submodule.map_injective_of_injective N.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl
end GlobalTheory.Published.SvN
