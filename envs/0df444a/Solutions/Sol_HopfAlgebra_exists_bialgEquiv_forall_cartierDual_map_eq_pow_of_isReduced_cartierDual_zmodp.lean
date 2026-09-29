-- Prove2me | solution 1 for HopfAlgebra.exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7a4a08db-543c-5482-849c-44ab0d26aebb

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp

set_option autoImplicit false

open scoped TensorProduct

open HopfAlgebra in

theorem solution
    (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A] [Module.Free (ZMod p) A]
    (hred : IsReduced (CartierDual (ZMod p) A)) :
    ∃ V : A ≃ₐc[ZMod p] A, ∀ χ : CartierDual (ZMod p) A, CartierDual.map (V : A →ₐc[ZMod p] A) χ = χ ^ p := by
  classical
  haveI : Nontrivial (CartierDual (ZMod p) A) := by
    refine ⟨⟨(Coalgebra.counit (R := ZMod p) (A := A) : Module.Dual (ZMod p) A), 0, ?_⟩⟩
    intro h
    have := LinearMap.congr_fun h (1 : A)
    rw [Bialgebra.counit_one] at this
    exact one_ne_zero this
  haveI : CharP (CartierDual (ZMod p) A) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (CartierDual (ZMod p) A)).injective p
  obtain ⟨V, -, -, hV⟩ := PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp p A

  have hpin : ∀ χ : CartierDual (ZMod p) A, CartierDual.map V χ = χ ^ p := by
    intro χ
    apply LinearMap.ext
    intro a
    exact hV χ a
  have hinjT : Function.Injective (CartierDual.map V) := by
    intro χ χ' h
    rw [hpin, hpin] at h
    exact frobenius_inj (CartierDual (ZMod p) A) p h

  have hdual : Function.Injective ((V : A →ₐ[ZMod p] A).toLinearMap.dualMap) := by
    intro χ χ' h
    exact hinjT h
  have hsurj : Function.Surjective V := by
    have := LinearMap.dualMap_injective_iff.1 hdual
    exact this
  have hbij : Function.Bijective V :=
    ⟨(LinearMap.injective_iff_surjective (f := (V : A →ₐ[ZMod p] A).toLinearMap)).2 hsurj, hsurj⟩
  refine ⟨BialgEquiv.ofBijective V hbij, fun χ => ?_⟩
  exact hpin χ

end S_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp (solution)
