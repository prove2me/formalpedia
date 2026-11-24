-- Prove2me | solution 1 for GlobalTheory.isRegularRing_tensor_of_fibre_localRings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:10:20.672853+00:00
-- url     : https://prove2.me/submissions/6d633a0f-240f-42fd-be15-92cc6517d7c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularRingTensorOfFibreLocalRings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K]
      [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q →
      (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) →
      (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q →
        IsRegularLocalRing (Localization.AtPrime n ⧸
          (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) →
      IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hQ hfrac hreg
  haveI : Q.IsPrime := hQ ▸ RingHom.ker_isPrime (algebraMap S K)
  let φ : Q.ResidueField →ₐ[S] K := Ideal.ResidueField.liftₐ Q (Algebra.ofId S K) hQ.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hQ ▸ h0))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, b, hb, hy⟩ := hfrac y
    have hb0 : algebraMap S K b ≠ 0 := fun h0 => hb (hQ ▸ h0)
    refine ⟨algebraMap S Q.ResidueField a * (algebraMap S Q.ResidueField b)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, AlgHom.commutes, AlgHom.commutes]
    rw [← hy, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  let e : Q.ResidueField ≃ₐ[S] K := AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, hsurj⟩
  let E : Q.Fiber T ≃ₐ[S] T ⊗[S] K :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans (Algebra.TensorProduct.comm S K T)
  haveI : IsNoetherianRing (Q.Fiber T) := by
    letI : Algebra T (Q.Fiber T) := Algebra.TensorProduct.rightAlgebra
    let Sp := Localization (Algebra.algebraMapSubmonoid T Q.primeCompl)
    haveI : IsNoetherianRing Sp :=
      IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid T Q.primeCompl) Sp inferInstance
    exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ Q (S := T)).toRingEquiv.symm
  haveI : IsRegularRing (Q.Fiber T) := by
    rw [isRegularRing_iff]
    intro q hq
    let n : Ideal T := q.comap (Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T)
    haveI : n.IsPrime := Ideal.comap_isPrime _ _
    have hn : n.comap (algebraMap S T) = Q := by
      change Ideal.comap (algebraMap S T) (Ideal.comap
        ((Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T) : T →+* Q.Fiber T) q) = Q
      rw [Ideal.comap_comap, AlgHom.comp_algebraMap]
      exact (Ideal.over_def q Q).symm
    haveI := hreg n hn
    exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ Q q).toRingEquiv.symm
  exact IsRegularRing.of_ringEquiv E.toRingEquiv
end GlobalTheory
