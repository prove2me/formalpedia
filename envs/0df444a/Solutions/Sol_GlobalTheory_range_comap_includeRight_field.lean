-- Prove2me | solution 1 for GlobalTheory.range_comap_includeRight_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:34.867268+00:00
-- url     : https://prove2.me/submissions/103cd1d8-463c-45bf-a088-fe3f7c9f7761

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k],
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  intro A B _ _ _ k _ _
  ext r
  constructor
  · rintro ⟨q, rfl⟩
    show Ideal.comap (algebraMap A B) (Ideal.comap _ q.asIdeal) = _
    rw [Ideal.comap_comap, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ q.asIdeal),
      ← RingHom.ker_eq_comap_bot]
  · intro hr
    change Ideal.comap (algebraMap A B) r.asIdeal = RingHom.ker (algebraMap A k) at hr
    set f := algebraMap A k with hf
    let I := RingHom.ker f
    let K := r.asIdeal.ResidueField
    let g : A →+* K := (algebraMap B K).comp (algebraMap A B)
    have hg : RingHom.ker g = I := by
      change RingHom.ker ((algebraMap B K).comp (algebraMap A B)) = RingHom.ker f
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hr]
    have hIg : ∀ a ∈ I, g a = 0 := fun a ha => by rw [← RingHom.mem_ker, hg]; exact ha
    let ι₁ : A ⧸ I →+* k := RingHom.kerLift f
    let ι₂ : A ⧸ I →+* K := Ideal.Quotient.lift I g hIg
    have inj₁ : Function.Injective ι₁ := RingHom.kerLift_injective f
    have inj₂ : Function.Injective ι₂ := RingHom.lift_injective_of_ker_le_ideal I hIg hg.le
    letI : Algebra (A ⧸ I) k := ι₁.toAlgebra
    letI : Algebra (A ⧸ I) K := ι₂.toAlgebra
    haveI : Nontrivial (k ⊗[A ⧸ I] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ I) k K inj₁ inj₂
    haveI : SMulCommClass (A ⧸ I) A k := ⟨fun x a y => by
      simp only [Algebra.smul_def]; ring⟩
    let α : k →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.includeLeft
    let β : B →ₐ[A] k ⊗[A ⧸ I] K :=
      { ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) with
        commutes' := fun a => by
          change (1 : k) ⊗ₜ[A ⧸ I] (algebraMap (A ⧸ I) K (Ideal.Quotient.mk I a)) = _
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := K),
            ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
          rfl }
    let φ : k ⊗[A] B →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[A ⧸ I] K)
    refine ⟨PrimeSpectrum.comap φ.toRingHom ⟨m, hm.isPrime⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.comap φ.toRingHom m) = r.asIdeal
    have hcomp : φ.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom =
        ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) := by
      ext b
      simp [φ, α, β, Algebra.TensorProduct.lift_tmul]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ m),
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
end GlobalTheory
