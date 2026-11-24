-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExtTensorFixed.fixed_le_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:25.540454+00:00
-- url     : https://prove2.me/submissions/81a4ecfd-ba2b-4f42-b552-879e160bc466

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalFixedTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_ExtTensorFixed_mem_fixed_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_ExtTensorFixed_mem_range_lTensor_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExtTensorFixed
variable {G H V W X ι : Type} [DecidableEq ι] [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
namespace GlobalTheory.CompanionTheory.ExtTensorFixed
theorem _root_.solution (ρ : Representation ℂ G V) (σ : Representation ℂ H W)
    (K₁ : Subgroup G) (K₂ : Subgroup H) :
    fixed (extTensor ρ σ) (K₁.prod K₂) ≤
      LinearMap.range (TensorProduct.map (fixed ρ K₁).subtype (fixed σ K₂).subtype) := by
  intro x hx
  have hx' := (mem_fixed_iff _ _ _).1 hx
  have act : ∀ (g : G × H) (z : V ⊗[ℂ] W),
      extTensor ρ σ g z = TensorProduct.map (ρ g.1) (σ g.2) z := by
    intro g z
    induction z with
    | zero => simp
    | add a c ha hc => simp [ha, hc]
    | tmul v w => simp

  have h1 : ∀ k : K₁, (ρ (k : G)).lTensor W (TensorProduct.comm ℂ V W x) =
      TensorProduct.comm ℂ V W x := by
    intro k
    have hk := hx' ⟨((k : G), 1), ⟨k.2, one_mem _⟩⟩
    rw [act] at hk
    conv_rhs => rw [← hk]
    simp only [map_one]
    generalize x = z
    induction z with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v w => simp
  obtain ⟨y', hy'⟩ := mem_range_lTensor_fixed ρ K₁ _ h1
  let y : (fixed ρ K₁) ⊗[ℂ] W := TensorProduct.comm ℂ W (fixed ρ K₁) y'
  have hy : (fixed ρ K₁).subtype.rTensor W y = x := by
    have : (fixed ρ K₁).subtype.rTensor W y =
        TensorProduct.comm ℂ W V ((fixed ρ K₁).subtype.lTensor W y') := by
      simp only [y]
      generalize y' = z
      induction z with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]
      | tmul v w => simp
    rw [this, hy']
    simp

  have hinj : Function.Injective ((fixed ρ K₁).subtype.rTensor W) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have h2 : ∀ k : K₂, (σ (k : H)).lTensor (fixed ρ K₁) y = y := by
    intro k
    apply hinj
    have hk := hx' ⟨(1, (k : H)), ⟨one_mem _, k.2⟩⟩
    rw [act] at hk
    rw [hy]
    conv_rhs => rw [← hk, ← hy]
    simp only [map_one]
    generalize y = z
    induction z with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v w => simp
  obtain ⟨z, hz⟩ := mem_range_lTensor_fixed σ K₂ y h2
  refine ⟨z, ?_⟩
  rw [← hy, ← hz]
  generalize z = t
  induction t with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v w => simp
end GlobalTheory.CompanionTheory.ExtTensorFixed
