-- Prove2me | solution 1 for GlobalTheory.exists_finite_separable_compositum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:20.939567+00:00
-- url     : https://prove2.me/submissions/c1090de0-4eed-4e62-b066-c5c33b0ff02f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K K' k : Type) [Field K] [Field K'] [Field k] [Algebra K k]
    [FiniteDimensional K k] [Algebra.IsSeparable K k] (φ : K →+* K') :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra K' k') (g : k →+* k'), FiniteDimensional K' k' ∧
      Algebra.IsSeparable K' k' ∧ g.comp (algebraMap K k) = (algebraMap K' k').comp φ := by
  let Ω := AlgebraicClosure K'
  let _ : Algebra K K' := φ.toAlgebra
  let σ : k →ₐ[K] Ω := IsAlgClosed.lift
  let bs := Module.finBasis K k
  let k' := IntermediateField.adjoin K' (Set.range fun i => σ (bs i))
  have sepσ : ∀ z : k, IsSeparable K' (σ z) := fun z =>
    ((Algebra.IsSeparable.isSeparable K z).map σ σ.injective).tower_top _
  have h₁ : FiniteDimensional K' k' :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact (sepσ _).isIntegral)
  have h₂ : Algebra.IsSeparable K' k' :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).2 (by rintro _ ⟨i, rfl⟩; exact sepσ _)
  have hmem : ∀ z : k, σ z ∈ k' := fun z => by
    rw [← bs.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply K K' Ω]
    exact mul_mem (k'.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  refine ⟨k', inferInstance, inferInstance, σ.toRingHom.codRestrict k'.toSubring hmem, h₁, h₂, ?_⟩
  ext z
  exact σ.commutes z
end GlobalTheory
