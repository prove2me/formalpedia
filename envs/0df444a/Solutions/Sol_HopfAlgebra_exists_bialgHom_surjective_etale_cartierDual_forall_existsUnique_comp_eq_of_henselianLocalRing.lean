-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/412f8382-071e-5e63-af9e-bd57c570a512

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
p2m_attr_erase "instance" "HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul"
p2m_attr_erase "simp" "CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Flat R H] :
    ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra R M) (_ : Coalgebra.IsCocomm R M)
      (_ : Module.Free R M) (_ : Module.Finite R M) (π : H →ₐc[R] M),
      Function.Surjective π ∧

      Algebra.Etale R (CartierDual R M) ∧

      (∀ (M' : Type v) [CommRing M'] [HopfAlgebra R M'] [Coalgebra.IsCocomm R M']
          [Module.Free R M'] [Module.Finite R M'] [Algebra.Etale R (CartierDual R M')]
          (f : H →ₐc[R] M'), ∃! g : M →ₐc[R] M', g.comp π = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : M →ₐc[R] M, ψ.comp π = π.comp φ) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (CartierDual R' (R' ⊗[R] M)) ∧
          ∀ (N : Type v) [CommRing N] [HopfAlgebra R' N] [Coalgebra.IsCocomm R' N]
            [Module.Free R' N] [Module.Finite R' N] [Algebra.Etale R' (CartierDual R' N)]
            (f : R' ⊗[R] H →ₐc[R'] N),
              ∃! g : R' ⊗[R] M →ₐc[R'] N,
                g.comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f) := by
  haveI : Module.Free R H := Module.free_of_flat_of_isLocalRing
  obtain ⟨E, _i1, _i2, _i3, _i4, _i5, ι, hι, hE, huniv, _hEnd, hsplit, hbc⟩ :=
    HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing R (CartierDual R H)
  exact
    HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
      R H E ι hι hE huniv hsplit hbc

end S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing (solution)
