-- Prove2me | solution 1 for HopfAlgebra.exists_connectedComponent_of_isLocalRing_cartierDual_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/598a7aa1-0552-5543-a38d-268db1f467a2

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Theorems.Thm_Bialgebra_existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_ker_eq_span_one_sub_of_counit_eq_one_of_isLocalRing_quotient
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_connectedComponent_of_isLocalRing_cartierDual_zmodp
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

universe u v

open scoped TensorProduct
open Function Polynomial

namespace H4aBody

private theorem henselianLocalRing_of_isAdicComplete {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) [IsAdicComplete I R] (hI : IsLocalRing.maximalIdeal R = I) :
    HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ := by
    have hH : HenselianRing R I := inferInstance
    rw [hI] at h₁ ⊢
    exact hH.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk I))

private theorem includeRight_surjective {𝓞 : Type u} [CommRing 𝓞] {k : Type*} [CommRing k]
    [Algebra 𝓞 k] (hk : Surjective (algebraMap 𝓞 k)) (ℛ : Type v) [CommRing ℛ] [Algebra 𝓞 ℛ] :
    Surjective (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a r =>
    obtain ⟨o, rfl⟩ := hk a
    refine ⟨o • r, ?_⟩
    rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, map_add _ _ _⟩

end H4aBody

open H4aBody in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [HopfAlgebra 𝓞 H] [Coalgebra.IsCocomm 𝓞 H]
    [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) H))) :
    ∃ (R₀ : Type v) (_ : CommRing R₀) (_ : HopfAlgebra 𝓞 R₀) (_ : Module.Free 𝓞 R₀)
      (_ : Module.Finite 𝓞 R₀) (ρ : H →ₐc[𝓞] R₀) (e : H),
      IsIdempotentElem e ∧ Coalgebra.counit (R := 𝓞) e = 1 ∧
      Function.Surjective ρ ∧ RingHom.ker (ρ : H →ₐ[𝓞] R₀) = Ideal.span {1 - e} ∧
      IsLocalRing R₀ ∧ IsLocalRing (TensorProduct 𝓞 (ZMod p) R₀) ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R₀)) := by
  classical

  obtain ⟨hD, hDVR, -, hmax⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  haveI : HenselianLocalRing 𝓞 := henselianLocalRing_of_isAdicComplete (Ideal.span {(p : 𝓞)}) hmax
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _

  obtain ⟨hfin, e, hce, -, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := 𝓞) (S := H)

  let σ : Fin (Fintype.card (MaximalSpectrum H)) ≃ MaximalSpectrum H := (Fintype.equivFin _).symm
  have hce' : CompleteOrthogonalIdempotents (e ∘ σ) := (CompleteOrthogonalIdempotents.equiv σ).2 hce
  obtain ⟨i₀, hi₀, -⟩ :=
    Bialgebra.existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents (R := 𝓞) (e ∘ σ) hce'

  obtain ⟨R₀, _, _, ρ, hρs, hρk, hR₀loc, hR₀fin, hcocomm, hflat⟩ :=
    HopfAlgebra.exists_bialgHom_surjective_ker_eq_span_one_sub_of_counit_eq_one_of_isLocalRing_quotient
      (R := 𝓞) (e (σ i₀)) (hce.idem (σ i₀)) hi₀ (hloc (σ i₀))
  haveI : Module.Finite 𝓞 R₀ := hR₀fin
  haveI : Coalgebra.IsCocomm 𝓞 R₀ := hcocomm inferInstance
  haveI : Module.Flat 𝓞 R₀ := hflat inferInstance
  haveI : IsLocalRing R₀ := hR₀loc

  haveI : Module.Free 𝓞 R₀ := Module.free_of_flat_of_isLocalRing

  haveI : Module.FaithfullyFlat 𝓞 R₀ := inferInstance
  haveI : Nontrivial ((ZMod p) ⊗[𝓞] R₀) := inferInstance
  have hfib : IsLocalRing (TensorProduct 𝓞 (ZMod p) R₀) :=
    IsLocalRing.of_surjective'
      (Algebra.TensorProduct.includeRight : R₀ →ₐ[𝓞] (ZMod p) ⊗[𝓞] R₀).toRingHom
      (includeRight_surjective hk R₀)

  have hcd : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R₀)) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective (ZMod p) (TensorProduct 𝓞 (ZMod p) H)
      (TensorProduct 𝓞 (ZMod p) R₀)
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ρ)
      (by
        have h : Surjective (((ρ : H →ₐ[𝓞] R₀).toLinearMap).lTensor (ZMod p)) :=
          LinearMap.lTensor_surjective (ZMod p) (fun x => hρs x)
        have key : ∀ w, Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ρ w =
            ((ρ : H →ₐ[𝓞] R₀).toLinearMap).lTensor (ZMod p) w := by
          intro w
          induction w using TensorProduct.induction_on with
          | zero => simp only [map_zero]
          | tmul a b => rw [Bialgebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
          | add x y hx hy => simp only [map_add, hx, hy]
        intro z
        obtain ⟨w, hw⟩ := h z
        exact ⟨w, by rw [key, hw]⟩)
      hunip
  exact ⟨R₀, inferInstance, inferInstance, inferInstance, inferInstance, ρ, e (σ i₀), hce.idem (σ i₀), hi₀,
    hρs, hρk, hR₀loc, hfib, hcd⟩

end S_HopfAlgebra_exists_connectedComponent_of_isLocalRing_cartierDual_zmodp
end P2MW
export P2MW.S_HopfAlgebra_exists_connectedComponent_of_isLocalRing_cartierDual_zmodp (solution)
