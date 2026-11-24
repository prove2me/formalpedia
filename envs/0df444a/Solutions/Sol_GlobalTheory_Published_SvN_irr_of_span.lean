-- Prove2me | solution 1 for GlobalTheory.Published.SvN.irr_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:39.493931+00:00
-- url     : https://prove2.me/submissions/83532e7a-4d48-4d8a-942e-e1706fe94386

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Ops_comm
import Theorems.Thm_GlobalTheory_Published_SvN_eigen_line
import Theorems.Thm_GlobalTheory_Published_SvN_ops_of_central
import Theorems.Thm_GlobalTheory_Published_SvN_isSmooth_of_eventually
import Theorems.Thm_GlobalTheory_Published_SvN_exists_eigen_mem

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
    (he : ∀ a ∈ A, π ⟨a, 0⟩ e = α a • e) (hsp : Submodule.span ℂ (Set.range fun x => π ⟨x, 0⟩ e) = ⊤) : IsIrrSmoothOf ψ π := by
  have hs : PRep.IsSmooth π := by
    refine isSmooth_of_eventually hψ hπ fun v => ?_
    have hv : v ∈ Submodule.span ℂ (Set.range fun x => π ⟨x, 0⟩ e) := hsp ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨x, rfl⟩ := hx
      filter_upwards [h1, h3 x] with u hu hu'
      have := (ops_of_central hπ).comm (alt_psi hB ψ) u x e
      beta_reduce at this ⊢
      rw [this, hu', he u hu.1, hu.2, one_smul, one_smul]
    | zero => simp
    | add a b _ _ ha hb => filter_upwards [ha, hb] with u ha hb using by rw [map_add, ha, hb]
    | smul r a _ ha => filter_upwards [ha] with u ha using by rw [map_smul, ha]
  refine ⟨hs, ?_, hπ⟩
  have : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun h => he0 (by
    have : e ∈ (⊥ : Subrepresentation π).toSubmodule := h ▸ Submodule.mem_top
    exact this)⟩
  refine ⟨fun P => or_iff_not_imp_left.2 fun hP => ?_⟩
  obtain ⟨e', hP', he0', he'⟩ := exists_eigen_mem hB hα h1 h2 hπ hs P hP
  obtain ⟨r, rfl⟩ := eigen_line (alt_psi hB ψ) (ops_of_central hπ) hα hA he (v := e') (hsp ▸ Submodule.mem_top) he'
  have heP : e ∈ P.toSubmodule := (Submodule.smul_mem_iff _ (left_ne_zero_of_smul he0')).1 hP'
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 ?_)
  rw [← hsp, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact P.apply_mem_toSubmodule _ heP
end GlobalTheory.Published.SvN
