-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7177c529-31a3-5951-9e27-05ff9ed34131

import Mathlib
import Theorems.Thm_CoalgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
import Theorems.Thm_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {H : Type u} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (M : Type v) [AddCommGroup M] [Finite M]
    (ψ₀ : ResidueField R ⊗[R] H →ₐc[ResidueField R] AddMonoidAlgebra (ResidueField R) M) :
    ∃ ψ : H →ₐc[R] AddMonoidAlgebra R M,
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ : H →ₐ[R] AddMonoidAlgebra R M) =
        ((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) M).restrictScalars R).comp
          Algebra.TensorProduct.includeRight := by
  classical
  haveI : Module.Free R H := Module.free_of_flat_of_isLocalRing

  obtain ⟨f, hf⟩ := CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing (B := H) M ψ₀.toCoalgHom

  have hfx : ∀ x : H, AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (f x) = ψ₀ ((1 : ResidueField R) ⊗ₜ[R] x) := by
    intro x
    have := congrArg (fun g => g x) hf
    simp at this
    exact this

  have hone : f 1 = 1 := by
    have key := CoalgHom.addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq (B := R) M
      (f.comp (Bialgebra.unitBialgHom R H).toCoalgHom) (Bialgebra.unitBialgHom R (AddMonoidAlgebra R M)).toCoalgHom (by
        apply LinearMap.ext; intro r
        change AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (f (Bialgebra.unitBialgHom R H r)) =
          AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (Bialgebra.unitBialgHom R (AddMonoidAlgebra R M) r)
        have h1 : (Bialgebra.unitBialgHom R H) r = algebraMap R H r := rfl
        have h2 : (Bialgebra.unitBialgHom R (AddMonoidAlgebra R M)) r = algebraMap R (AddMonoidAlgebra R M) r := rfl
        rw [h1, h2, Algebra.algebraMap_eq_smul_one, map_smul, map_smul, hfx, AlgHom.commutes,
          Algebra.algebraMap_eq_smul_one, ← Algebra.TensorProduct.one_def, map_one])
    have := congrArg (fun g => g (1 : R)) key
    have h1 : (Bialgebra.unitBialgHom R H) (1 : R) = 1 := map_one _
    have h2 : (Bialgebra.unitBialgHom R (AddMonoidAlgebra R M)) (1 : R) = 1 := map_one _
    change f ((Bialgebra.unitBialgHom R H) 1) = (Bialgebra.unitBialgHom R (AddMonoidAlgebra R M)) 1 at this
    rwa [h1, h2] at this

  have hmul : ∀ x y : H, f (x * y) = f x * f y := by
    have key := CoalgHom.addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq (B := H ⊗[R] H) M
      (f.comp (Bialgebra.mulCoalgHom R H))
      ((Bialgebra.mulCoalgHom R (AddMonoidAlgebra R M)).comp (Coalgebra.TensorProduct.map f f)) (by
        apply TensorProduct.ext'; intro x y
        change AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (f (Bialgebra.mulCoalgHom R H (x ⊗ₜ[R] y))) =
          AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))
            (Bialgebra.mulCoalgHom R (AddMonoidAlgebra R M) (Coalgebra.TensorProduct.map f f (x ⊗ₜ[R] y)))
        simp only [Bialgebra.coe_mulCoalgHom, LinearMap.mul'_apply, Coalgebra.TensorProduct.map_tmul, map_mul, hfx]
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul])
    intro x y
    have := congrArg (fun g => g (x ⊗ₜ[R] y)) key
    simpa using this
  refine ⟨BialgHom.mk f hone hmul, ?_⟩
  apply AlgHom.ext
  intro x
  simpa using hfx x

end S_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing (solution)
