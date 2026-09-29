-- Prove2me | solution 1 for HopfAlgebra.natCard_algHom_dvd_natCard_algHom_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/41750b5e-4301-56a7-8730-79d512a14ae8

import Mathlib
import Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_natCard_algHom_dvd_natCard_algHom_of_surjective

set_option autoImplicit false

theorem solution
    (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (H₀ : Type) [CommRing H₀] [HopfAlgebra R H₀]
    (π : H →ₐc[R] H₀) (hπ : Function.Surjective π) [Finite (H →ₐ[R] K)] :
    Nat.card (H₀ →ₐ[R] K) ∣ Nat.card (H →ₐ[R] K) := by
  classical

  have hu : ∀ f : WithConv (H →ₐ[R] K), IsUnit f := fun f => HopfAlgebra.isUnit_withConv_algHom f
  have hu₀ : ∀ f : WithConv (H₀ →ₐ[R] K), IsUnit f := fun f => HopfAlgebra.isUnit_withConv_algHom f

  let ψ : WithConv (H₀ →ₐ[R] K) →* WithConv (H →ₐ[R] K) :=
    { toFun := fun f => WithConv.toConv (f.ofConv.comp (π : H →ₐ[R] H₀))
      map_one' := by
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro x
        rw [WithConv.ofConv_toConv, AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
        congr 1
        exact CoalgHomClass.counit_comp_apply π x
      map_mul' := fun f g => by
        have h := AlgHom.convMul_comp_bialgHom_distrib f g π
        rw [h, WithConv.toConv_ofConv] }
  have hψ : ∀ f, ψ f = WithConv.toConv (f.ofConv.comp (π : H →ₐ[R] H₀)) := fun f => rfl
  have hψinj : Function.Injective ψ := by
    intro f g hfg
    rw [hψ, hψ] at hfg
    have h1 := congrArg WithConv.ofConv hfg
    rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv] at h1
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact congr($h1 x)

  haveI : Finite (WithConv (H →ₐ[R] K)) := Finite.of_equiv _ (WithConv.equiv (H →ₐ[R] K)).symm

  have eM : Nat.card (WithConv (H →ₐ[R] K))ˣ = Nat.card (H →ₐ[R] K) := by
    rw [← Nat.card_congr (WithConv.equiv (H →ₐ[R] K))]
    exact Nat.card_congr (Equiv.ofBijective (Units.val : (WithConv (H →ₐ[R] K))ˣ → _)
      ⟨fun _ _ h => Units.ext h, fun f => hu f⟩)
  have eM₀ : Nat.card (WithConv (H₀ →ₐ[R] K))ˣ = Nat.card (H₀ →ₐ[R] K) := by
    rw [← Nat.card_congr (WithConv.equiv (H₀ →ₐ[R] K))]
    exact Nat.card_congr (Equiv.ofBijective (Units.val : (WithConv (H₀ →ₐ[R] K))ˣ → _)
      ⟨fun _ _ h => Units.ext h, fun f => hu₀ f⟩)

  let Ψ : (WithConv (H₀ →ₐ[R] K))ˣ →* (WithConv (H →ₐ[R] K))ˣ := Units.map ψ
  have hΨinj : Function.Injective Ψ := Units.map_injective hψinj
  have hS : Nat.card Ψ.range ∣ Nat.card (WithConv (H →ₐ[R] K))ˣ := Subgroup.card_subgroup_dvd_card _
  have hR : Nat.card Ψ.range = Nat.card (WithConv (H₀ →ₐ[R] K))ˣ := by
    rw [← Nat.card_range_of_injective hΨinj]
    rfl
  rw [← eM, ← eM₀, ← hR]
  exact hS

end S_HopfAlgebra_natCard_algHom_dvd_natCard_algHom_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_natCard_algHom_dvd_natCard_algHom_of_surjective (solution)
