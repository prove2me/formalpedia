-- Prove2me | solution 1 for HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1bf5c101-b956-5a4a-8dd0-ff5a4a144938

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field
import Theorems.Thm_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing
p2m_attr_erase "instance" "HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Flat R H] :
    ∃ (E : Type v) (_ : CommRing E) (_ : HopfAlgebra R E) (_ : Coalgebra.IsCocomm R E)
      (_ : Module.Free R E) (_ : Module.Finite R E) (ι : E →ₐc[R] H),
      Function.Injective ι ∧

      Algebra.Etale R E ∧

      (∀ (E' : Type v) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
          [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
          (f : E' →ₐc[R] H), ∃! g : E' →ₐc[R] E, ι.comp g = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : E →ₐc[R] E, ι.comp ψ = φ.comp ι) ∧

      Module.Free R (H ⧸ LinearMap.range (ι : E →ₐ[R] H).toLinearMap) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (R' ⊗[R] E) ∧
          ∀ (E' : Type v) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
            [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
            (f : E' →ₐc[R'] R' ⊗[R] H),
              ∃! g : E' →ₐc[R'] R' ⊗[R] E,
                (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f) := by
  obtain ⟨E₀, _, _, _, _, ι₀, hι₀, hE₀, huniv₀, hbc₀⟩ :=
    HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] H)
  exact HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
    R H E₀ ι₀ hι₀ hE₀ huniv₀ hbc₀

end S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing
end P2MW
export P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing (solution)
