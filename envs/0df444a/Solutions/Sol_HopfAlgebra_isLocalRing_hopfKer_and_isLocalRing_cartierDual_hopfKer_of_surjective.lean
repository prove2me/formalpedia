-- Prove2me | solution 1 for HopfAlgebra.isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6a3930b3-5634-56c7-b6b0-64b68f0b7581

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective

set_option autoImplicit false

open scoped TensorProduct

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (HV : Type) [CommRing HV] [HopfAlgebra R HV] [Module.Finite R HV] [Module.Free R HV]
    [Coalgebra.IsCocomm R HV] [Nontrivial HV]
    (π : H →ₐc[R] HV) (hπ : Function.Surjective π)
    [Module.Finite R ↥(HopfAlgebra.hopfKer π)] [Module.Free R ↥(HopfAlgebra.hopfKer π)]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual R H)) :
    IsLocalRing ↥(HopfAlgebra.hopfKer π) ∧ IsLocalRing (CartierDual R ↥(HopfAlgebra.hopfKer π)) := by
  classical
  haveI := hloc
  haveI := hdual
  haveI : Nontrivial R := Module.nontrivial R HV

  haveI : Algebra.IsIntegral ↥(HopfAlgebra.hopfKer π) H :=
    ⟨fun a => (Algebra.IsIntegral.isIntegral (R := R) a).tower_top⟩
  have h1 : IsLocalRing ↥(HopfAlgebra.hopfKer π) := by
    apply IsLocalRing.of_unique_max_ideal
    obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal ↥(HopfAlgebra.hopfKer π)
    refine ⟨𝔫, h𝔫, fun 𝔫' h𝔫' => ?_⟩
    have hker : RingHom.ker (algebraMap ↥(HopfAlgebra.hopfKer π) H) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective
    haveI := h𝔫
    haveI := h𝔫'
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := H) 𝔫 (by rw [hker]; exact bot_le)
    obtain ⟨Q', hQ'max, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := H) 𝔫' (by rw [hker]; exact bot_le)
    have hQQ' : Q = Q' := by
      rw [IsLocalRing.eq_maximalIdeal hQmax, IsLocalRing.eq_maximalIdeal hQ'max]
    rw [← hQ, ← hQ', hQQ']
  refine ⟨h1, ?_⟩

  set ι := HopfAlgebra.hopfKerVal π with hι
  have hnat : ∀ (φ ψ : Module.Dual R H) (x : ↥(HopfAlgebra.hopfKer π) ⊗[R] ↥(HopfAlgebra.hopfKer π)),
      TensorProduct.dualDistrib R H H (φ ⊗ₜ[R] ψ)
          (TensorProduct.map (ι : ↥(HopfAlgebra.hopfKer π) →ₐc[R] H).toLinearMap
            (ι : ↥(HopfAlgebra.hopfKer π) →ₐc[R] H).toLinearMap x) =
        TensorProduct.dualDistrib R ↥(HopfAlgebra.hopfKer π) ↥(HopfAlgebra.hopfKer π)
          ((φ ∘ₗ (ι : ↥(HopfAlgebra.hopfKer π) →ₐc[R] H).toLinearMap) ⊗ₜ[R]
            (ψ ∘ₗ (ι : ↥(HopfAlgebra.hopfKer π) →ₐc[R] H).toLinearMap)) x := by
    intro φ ψ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  let t : CartierDual R H →+* CartierDual R ↥(HopfAlgebra.hopfKer π) :=
    { toFun := fun φ => CartierDual.ofDual R ↥(HopfAlgebra.hopfKer π)
        ((CartierDual.toDual R H φ) ∘ₗ (ι : ↥(HopfAlgebra.hopfKer π) →ₐc[R] H).toLinearMap)
      map_one' := by
        apply CartierDual.ext; intro a
        simp only [CartierDual.ofDual_apply, LinearMap.comp_apply, CartierDual.toDual_apply, CartierDual.one_apply]
        exact CoalgHomClass.counit_comp_apply ι a
      map_mul' := fun φ ψ => by
        apply CartierDual.ext; intro a
        simp only [CartierDual.ofDual_apply, LinearMap.comp_apply, CartierDual.toDual_apply, CartierDual.mul_apply]
        rw [show (ι : ↥(HopfAlgebra.hopfKer π) →ₐc[R] H).toLinearMap a = ι a from rfl,
          ← CoalgHomClass.map_comp_comul_apply ι a]
        exact hnat _ _ _
      map_zero' := by apply CartierDual.ext; intro a; rfl
      map_add' := fun φ ψ => by apply CartierDual.ext; intro a; rfl }
  have ht : ∀ φ a, t φ a = φ (ι a) := fun φ a => rfl

  obtain ⟨⟨r, hr⟩, -, -, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  have hsurj : Function.Surjective t := by
    intro ψ
    refine ⟨CartierDual.ofDual R H ((CartierDual.toDual R ↥(HopfAlgebra.hopfKer π) ψ) ∘ₗ (r.restrictScalars R)), ?_⟩
    apply CartierDual.ext; intro c
    rw [ht]
    simp only [CartierDual.ofDual_apply, LinearMap.comp_apply, CartierDual.toDual_apply, LinearMap.restrictScalars_apply]
    rw [hι, HopfAlgebra.hopfKerVal_apply, hr c]
  haveI : Nontrivial (CartierDual R ↥(HopfAlgebra.hopfKer π)) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : (1 : CartierDual R ↥(HopfAlgebra.hopfKer π)) 1 = 0 := by rw [← h]; rfl
    rw [CartierDual.one_apply, Bialgebra.counit_one] at h1
    exact one_ne_zero h1
  exact IsLocalRing.of_surjective' t hsurj

end S_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective (solution)
