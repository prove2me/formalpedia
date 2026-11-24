-- Prove2me | solution 1 for GlobalTheory.UnimodOver.dualSubmoduleToDual_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:49:48.441009+00:00
-- url     : https://prove2.me/submissions/94189d69-4d98-4321-9ee2-b957af409f04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Theorems.Thm_GlobalTheory_UnimodOver_exists_basis

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
theorem _root_.solution (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    Function.Surjective (B.dualSubmoduleToDual Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  have hbmem : ∀ i, b i ∈ Λ := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  intro φ
  set y : V := ∑ i, (φ ⟨b i, hbmem i⟩ : ℤ) • B.dualBasis hB b i with hy
  have hymem : y ∈ B.dualSubmodule Λ := by
    rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hLI : LinearIndependent ℤ b := b.linearIndependent.restrict_scalars' ℤ
  let bΛ : Module.Basis (Fin n) ℤ Λ := (Module.Basis.span hLI).map (LinearEquiv.ofEq _ _ hb)
  have hbΛ : ∀ i, (bΛ i : V) = b i := fun i => by simp [bΛ, Module.Basis.span_apply]
  refine ⟨⟨y, hymem⟩, bΛ.ext fun j => ?_⟩
  apply Int.cast_injective (α := ℝ)
  have hspec := LinearMap.BilinForm.dualSubmoduleParing_spec B ⟨y, hymem⟩ (bΛ j)
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hspec
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply, hspec]
  simp only [hbΛ, hy, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    LinearMap.BilinForm.apply_dualBasis_left, smul_ite, smul_zero, zsmul_eq_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 2
  exact Subtype.ext (hbΛ j).symm
end GlobalTheory.UnimodOver
