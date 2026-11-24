-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_eigen_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:46.388483+00:00
-- url     : https://prove2.me/submissions/85820819-cc98-4959-a649-4a35fb4806e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_exists_eigen
import Theorems.Thm_GlobalTheory_Published_SvN_ops_of_central
import Theorems.Thm_GlobalTheory_Published_SvN_eventually_fix

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
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [IsModuleTopology F W]
include hα h1 h2
namespace GlobalTheory.Published.SvN
theorem _root_.solution (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) (hs : PRep.IsSmooth π) (P : Subrepresentation π) (hP : P ≠ ⊥) :
    ∃ e ∈ P.toSubmodule, e ≠ 0 ∧ ∀ a ∈ A, π ⟨a, 0⟩ e = α a • e := by
  have : P.toSubmodule ≠ ⊥ := fun h => hP (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
  obtain ⟨T, hT, hfin⟩ := h2 _ (h1.and (eventually_fix hs v))
  exact exists_eigen (alt_psi hB ψ) (ops_of_central hπ) hα T (fun u hu => (hT hu).1.2) P.toSubmodule
    (fun x m hm => P.apply_mem_toSubmodule _ hm) v hv hv0 fun u hu => (hT hu).2
end GlobalTheory.Published.SvN
