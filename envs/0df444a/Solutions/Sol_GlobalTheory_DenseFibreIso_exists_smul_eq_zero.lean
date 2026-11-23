-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.exists_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:08.33626+00:00
-- url     : https://prove2.me/submissions/42dc45e8-42c7-4f0b-b13d-490f3c777f6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {A : Type} [CommRing A]
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution {N : Type} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (A' : Type) [CommRing A'] [Algebra A A'] [Subsingleton (A' ⊗[A] N)] (m : PrimeSpectrum A') :
    ∃ a : A, algebraMap A A' a ∉ m.asIdeal ∧ ∀ n : N, a • n = 0 := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A A') m
  have hp : p ∉ Module.support A N := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    let k := p.asIdeal.ResidueField
    let L := m.asIdeal.ResidueField
    let : Algebra k L := (Ideal.ResidueField.map p.asIdeal m.asIdeal (algebraMap A A') rfl).toAlgebra
    have : IsScalarTower A k L := .of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap p.asIdeal m.asIdeal (algebraMap A A') rfl r).symm
    have h1 : Subsingleton (L ⊗[A] N) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' L L N).symm.toEquiv.subsingleton
    have h2 : Subsingleton (L ⊗[k] (k ⊗[A] N)) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A k L L N).toEquiv.subsingleton
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k L).1 h2
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hp
  obtain ⟨a, ha, ha'⟩ := hp
  exact ⟨a, ha', Module.mem_annihilator.1 ha⟩
end GlobalTheory.DenseFibreIso
