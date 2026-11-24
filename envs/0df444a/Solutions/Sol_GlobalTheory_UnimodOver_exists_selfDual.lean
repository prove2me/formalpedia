-- Prove2me | solution 1 for GlobalTheory.UnimodOver.exists_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:49:50.424634+00:00
-- url     : https://prove2.me/submissions/3d500eca-9b99-45de-a825-d3dac4874485

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Theorems.Thm_GlobalTheory_UnimodOver_discrete_dual
import Theorems.Thm_GlobalTheory_UnimodOver_span_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.UnimodOver
theorem _root_.solution (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ M : Submodule ℤ V, Λ ≤ M ∧ M ≤ B.dualSubmodule Λ ∧ B.dualSubmodule M = M := by
  haveI := discrete_dual B hB Λ hs
  set D := B.dualSubmodule Λ with hD
  haveI : IsZLattice ℝ D := ⟨span_of_le hs hint⟩
  haveI : IsNoetherian ℤ D := inferInstance
  have anti : ∀ {L M : Submodule ℤ V}, L ≤ M → B.dualSubmodule M ≤ B.dualSubmodule L :=
    fun h _ hy x hx => hy x (h hx)
  obtain ⟨M, ⟨h1, h2⟩, hmax⟩ := (set_has_maximal_iff_noetherian.2 this)
    {M : Submodule ℤ D | Λ ≤ M.map D.subtype ∧
      M.map D.subtype ≤ B.dualSubmodule (M.map D.subtype)}
    ⟨Λ.comap D.subtype, by
      simp only [Set.mem_setOf_eq, Submodule.map_comap_subtype, inf_eq_right.2 hint]
      exact ⟨le_rfl, hint⟩⟩
  refine ⟨M.map D.subtype, h1, Submodule.map_subtype_le _ _, le_antisymm ?_ h2⟩
  intro w hw
  have hwD : w ∈ D := anti h1 hw
  have hle : M ≤ M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := le_sup_left
  have heq : M = M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := by
    by_contra hne
    refine hmax _ ⟨h1.trans (Submodule.map_mono hle), ?_⟩ (lt_of_le_of_ne hle hne)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
    have e1 := h2 ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
    have e2 := hw _ ⟨y₁, hy₁, rfl⟩
    have e3 := hw _ ⟨x₁, hx₁, rfl⟩
    have e4 : B (x₁ : V) w = - B w (x₁ : V) := (hA.neg_eq _ _).symm
    have e5 : B w w = 0 := hA w
    have e6 : B (D.subtype (x₁ + a • ⟨w, hwD⟩)) (D.subtype (y₁ + c • ⟨w, hwD⟩)) =
        B (D.subtype x₁) (D.subtype y₁) + a • B w (D.subtype y₁) - c • B w (D.subtype x₁) := by
      simp only [Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_zsmul,
        LinearMap.add_apply, LinearMap.smul_apply, e4, e5, smul_zero, smul_neg, add_zero]
      ring
    rw [e6]
    exact sub_mem (add_mem e1 (Submodule.smul_mem _ _ e2)) (Submodule.smul_mem _ _ e3)
  have : (⟨w, hwD⟩ : D) ∈ M := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact ⟨_, this, rfl⟩
end GlobalTheory.UnimodOver
