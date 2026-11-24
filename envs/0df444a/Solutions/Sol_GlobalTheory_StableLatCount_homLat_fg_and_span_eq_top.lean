-- Prove2me | solution 1 for GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:31.366573+00:00
-- url     : https://prove2.me/submissions/e42166a3-4468-4e78-8c66-47a04804b33e

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTop
import Theorems.Thm_GlobalTheory_StableLatCount_exists_smul_mem_finset_of_span_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
noncomputable section
open GlobalTheory GlobalTheory.StableLatCount
namespace GlobalTheory.StableLatCount
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁]
    [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂]
    [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) :
    IsLat O E M₁ → IsLat O E M₂ →
      (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  classical
  intro h₁ h₂
  obtain ⟨h₁fg, h₁sp⟩ := h₁
  obtain ⟨h₂fg, h₂sp⟩ := h₂
  obtain ⟨s, hs⟩ := h₂fg
  have hsE : Submodule.span E (s : Set A₂) = ⊤ := by
    rw [eq_top_iff, ← h₂sp, Submodule.span_le, ← hs]
    exact fun x hx => Submodule.span_le_restrictScalars O E _ hx
  have memH : ∀ ψ ∈ homLat E M₁ M₂, ∀ x ∈ M₂, ψ x ∈ M₁ := fun ψ hψ => hψ
  refine ⟨?_, ?_⟩
  · haveI : Module.Finite O M₁ := Module.Finite.iff_fg.mpr h₁fg
    let f : homLat E M₁ M₂ →ₗ[O] (s → M₁) :=
      { toFun := fun ψ x => ⟨ψ.1 x, memH ψ.1 ψ.2 x (hs ▸ Submodule.subset_span x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro ψ φ h
      apply Subtype.ext
      apply LinearMap.ext_on hsE
      intro x hx
      exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
    haveI := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.mp this
  · rw [eq_top_iff]
    intro ψ _
    obtain ⟨d, hd, hdψ⟩ := exists_smul_mem_finset_of_span_eq_top O E M₁ h₁sp (s.image ψ)
    have hmem : d • ψ ∈ homLat E M₁ M₂ := by
      show ∀ x ∈ M₂, (d • ψ) x ∈ M₁
      intro x hx
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => rw [LinearMap.smul_apply]; exact hdψ _ (Finset.mem_image_of_mem _ hy)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact M₁.add_mem hy hz
      | smul o y _ hy => rw [LinearMap.map_smul_of_tower]; exact M₁.smul_mem o hy
    have hd' : algebraMap O E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hψ : ψ = (algebraMap O E d)⁻¹ • (d • ψ) := by
      rw [← algebraMap_smul E d ψ, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end GlobalTheory.StableLatCount
