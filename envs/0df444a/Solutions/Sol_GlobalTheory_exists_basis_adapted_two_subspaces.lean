-- Prove2me | solution 1 for GlobalTheory.exists_basis_adapted_two_subspaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:38.753807+00:00
-- url     : https://prove2.me/submissions/b609a69b-7b20-4563-a317-ab8c52333474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedTwoSubspaces
import Theorems.Thm_GlobalTheory_exists_relCompl_submodule
import Theorems.Thm_GlobalTheory_exists_fin_independent_span_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W₁ W₂ : Submodule K V) :
    ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → V), LinearIndependent K w ∧
      Submodule.span K (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧
      Submodule.span K (Set.range w) = W₁ ⊔ W₂ := by
  obtain ⟨C₁, hd₁, hs₁⟩ := exists_relCompl_submodule (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
  obtain ⟨C₂, hd₂, hs₂⟩ := exists_relCompl_submodule (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
  obtain ⟨a, u, hu, hus⟩ := exists_fin_independent_span_eq (W₁ ⊓ W₂)
  obtain ⟨b, v₁, hv₁, hvs₁⟩ := exists_fin_independent_span_eq C₁
  obtain ⟨c, v₂, hv₂, hvs₂⟩ := exists_fin_independent_span_eq C₂
  have hC₁ : C₁ ≤ W₁ := hs₁ ▸ le_sup_right
  have hC₂ : C₂ ≤ W₂ := hs₂ ▸ le_sup_right
  have h12 : Disjoint C₁ C₂ := by
    rw [Submodule.disjoint_def]
    intro x hx₁ hx₂
    exact (Submodule.disjoint_def.1 hd₁) x ⟨hC₁ hx₁, hC₂ hx₂⟩ hx₁
  have hU : Disjoint (W₁ ⊓ W₂) (C₁ ⊔ C₂) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hz1 : z ∈ W₁ := by
      have := W₁.sub_mem hx.1 (hC₁ hy)
      simpa using this
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd₂) z ⟨hz1, hC₂ hz⟩ hz
    subst hz0
    rw [add_zero] at hx ⊢
    exact (Submodule.disjoint_def.1 hd₁) y hx hy
  have hv : LinearIndependent K (Sum.elim v₁ v₂) :=
    hv₁.sum_type hv₂ (by rw [hvs₁, hvs₂]; exact h12)
  have hvs : Submodule.span K (Set.range (Sum.elim v₁ v₂)) = C₁ ⊔ C₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hvs₁, hvs₂]
  refine ⟨a, b, c, Sum.elim u (Sum.elim v₁ v₂),
    hu.sum_type hv (by rw [hus, hvs]; exact hU), ?_, ?_, ?_, ?_⟩
  · rw [Sum.elim_comp_inl, hus]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inl = Sum.elim u v₁ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₁, hs₁]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inr = Sum.elim u v₂ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₂, hs₂]
  · rw [Set.Sum.elim_range, Submodule.span_union, hus, hvs, sup_sup_distrib_left, hs₁, hs₂]
end GlobalTheory
