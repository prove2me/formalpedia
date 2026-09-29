-- Prove2me | solution 1 for IsArtinianRing.isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2b8b628c-df58-5ac3-9a53-990502d4580a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem K3apAux
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : Type) [CommRing C] [IsLocalRing C]
    (O : Type) [CommRing O]
    (κ k : Type) [Field κ] [Finite κ] [CharP κ ℓ] [Field k] [CharP k ℓ]
    (r : C →+* κ) (hr : Function.Surjective r) (hrk : ∀ a, r a = 0 ↔ a ∈ maximalIdeal C)
    (q : O →+* k) (hq : Function.Surjective q) (hqℓ : RingHom.ker q = Ideal.span {((ℓ : ℕ) : O)})
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ] (jk : k →+* Ω)
    (A : Type) [CommRing A] (mkA : C ⊗[ℤ] O →+* A) (hmk : Function.Surjective mkA)
    (hker : RingHom.ker mkA = (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C))) :
    IsReduced A ∧ IsArtinianRing A ∧ Nontrivial A := by
  classical
  have hmem : ∀ x, mkA x = 0 ↔ x ∈ (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) := fun x => by rw [← RingHom.mem_ker, hker]

  have hℓC : ((ℓ : ℕ) : C) ∈ maximalIdeal C := by
    rw [← hrk, map_natCast]; exact CharP.cast_eq_zero _ ℓ
  have hℓM : ((ℓ : ℕ) : C ⊗[ℤ] O) ∈ (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) := by
    rw [← map_natCast (algebraMap C (C ⊗[ℤ] O))]; exact Ideal.mem_map_of_mem _ hℓC

  let ιO : O →+* C ⊗[ℤ] O := (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C ⊗[ℤ] O).toRingHom
  have hιO : ∀ o, ιO o = (1 : C) ⊗ₜ[ℤ] o := fun o => rfl
  let eq : O ⧸ RingHom.ker q ≃+* k := RingHom.quotientKerEquivOfSurjective hq
  let ψk₀ : O ⧸ RingHom.ker q →+* A :=
    Ideal.Quotient.lift (RingHom.ker q) (mkA.comp ιO) (by
      intro a ha
      rw [hqℓ, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      show mkA (ιO (b * ℓ)) = 0
      rw [hmem, map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ hℓM)
  let ψk : k →+* A := ψk₀.comp eq.symm.toRingHom
  have hψk : ∀ o : O, ψk (q o) = mkA (ιO o) := by
    intro o
    have : eq.symm (q o) = Ideal.Quotient.mk _ o := by
      apply eq.injective; rw [RingEquiv.apply_symm_apply]; rfl
    show ψk₀ (eq.symm (q o)) = _
    rw [this]; rfl
  letI algkA : Algebra k A := ψk.toAlgebra
  let er : C ⧸ RingHom.ker r ≃+* κ := RingHom.quotientKerEquivOfSurjective hr
  let ψκ₀ : C ⧸ RingHom.ker r →+* A :=
    Ideal.Quotient.lift (RingHom.ker r) (mkA.comp (algebraMap C (C ⊗[ℤ] O))) (by
      intro a ha
      show mkA (algebraMap C (C ⊗[ℤ] O) a) = 0
      rw [hmem]
      exact Ideal.mem_map_of_mem _ ((hrk a).mp ha))
  let ψκ : κ →+* A := ψκ₀.comp er.symm.toRingHom
  have hψκ : ∀ c : C, ψκ (r c) = mkA (algebraMap C (C ⊗[ℤ] O) c) := by
    intro c
    have : er.symm (r c) = Ideal.Quotient.mk _ c := by
      apply er.injective; rw [RingEquiv.apply_symm_apply]; rfl
    show ψκ₀ (er.symm (r c)) = _
    rw [this]; rfl

  let Φ : k ⊗[ℤ] κ →ₐ[k] A :=
    Algebra.TensorProduct.lift (Algebra.ofId k A) ψκ.toIntAlgHom (fun x y => Commute.all _ _)
  have hΦ : Function.Surjective Φ := by
    intro a
    obtain ⟨t, rfl⟩ := hmk a
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul c o =>
      refine ⟨(q o) ⊗ₜ[ℤ] (r c), ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      show ψk (q o) * ψκ (r c) = mkA (c ⊗ₜ[ℤ] o)
      rw [hψk, hψκ, ← map_mul, hιO, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

  letI : Algebra (ZMod ℓ) κ := ZMod.algebra κ ℓ
  haveI : Algebra.FormallyUnramified (ZMod ℓ) κ := Algebra.FormallyUnramified.of_isSeparable _ _
  haveI : Algebra.FormallyUnramified ℤ (ZMod ℓ) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (ZMod ℓ)) (ZMod.intCast_surjective)
  haveI : Algebra.FormallyUnramified ℤ κ := Algebra.FormallyUnramified.comp ℤ (ZMod ℓ) κ
  haveI : Module.Finite ℤ κ := Module.Finite.of_finite
  haveI : Module.Finite k (k ⊗[ℤ] κ) := inferInstance
  haveI : Algebra.FormallyUnramified k (k ⊗[ℤ] κ) := inferInstance
  haveI : Algebra.FormallyUnramified k A := Algebra.FormallyUnramified.of_surjective Φ hΦ
  haveI : Module.Finite k A := Module.Finite.of_surjective Φ.toLinearMap hΦ
  refine ⟨Algebra.FormallyUnramified.isReduced_of_field k A, IsArtinianRing.of_finite k A, ?_⟩

  letI : Algebra (ZMod ℓ) Ω := ZMod.algebra Ω ℓ
  let jκ : κ →ₐ[ZMod ℓ] Ω := IsAlgClosed.lift
  let jC : C →+* Ω := jκ.toRingHom.comp r
  let jO : O →+* Ω := jk.comp q
  let Θ : C ⊗[ℤ] O →ₐ[ℤ] Ω := Algebra.TensorProduct.lift jC.toIntAlgHom jO.toIntAlgHom (fun x y => Commute.all _ _)
  have hΘ : ∀ a ∈ RingHom.ker mkA, Θ.toRingHom a = 0 := by
    intro a ha
    rw [hker] at ha
    have hle : (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) ≤ RingHom.ker Θ.toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      show Θ (algebraMap C (C ⊗[ℤ] O) m) = 0
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul]
      show jC _ * jO 1 = 0
      have : jC m = 0 := by
        show jκ (r m) = 0
        rw [(hrk m).mpr (by simpa using hm), map_zero]
      rw [Algebra.algebraMap_self, RingHom.id_apply, this, zero_mul]
    exact hle ha
  let eA : (C ⊗[ℤ] O) ⧸ RingHom.ker mkA ≃+* A := RingHom.quotientKerEquivOfSurjective hmk
  exact RingHom.domain_nontrivial ((Ideal.Quotient.lift (RingHom.ker mkA) Θ.toRingHom hΘ).comp eA.symm.toRingHom)

set_option maxHeartbeats 1600000 in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] [CharP (ResidueField C) ℓ]
    (O : Type) [CommRing O] (hℓ : (Ideal.span {((ℓ : ℕ) : O)}).IsMaximal) :
    IsReduced ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) ∧
      IsArtinianRing ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) ∧
      Nontrivial ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) := by
  haveI : (Ideal.span {((ℓ : ℕ) : O)}).IsMaximal := hℓ
  have hℓk : ((ℓ : ℕ) : (Ideal.span {((ℓ : ℕ) : O)}).ResidueField) = 0 := by
    rw [← map_natCast (algebraMap O (Ideal.span {((ℓ : ℕ) : O)}).ResidueField), ← RingHom.mem_ker,
      Ideal.ker_algebraMap_residueField]
    exact Ideal.mem_span_singleton_self _
  haveI : CharP (Ideal.span {((ℓ : ℕ) : O)}).ResidueField ℓ := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hℓk
  haveI : CharP (AlgebraicClosure (Ideal.span {((ℓ : ℕ) : O)}).ResidueField) ℓ :=
    charP_of_injective_algebraMap (algebraMap (Ideal.span {((ℓ : ℕ) : O)}).ResidueField _).injective ℓ
  exact K3apAux ℓ C O (ResidueField C) (Ideal.span {((ℓ : ℕ) : O)}).ResidueField (IsLocalRing.residue C)
    IsLocalRing.residue_surjective (fun a => IsLocalRing.residue_eq_zero_iff a)
    (algebraMap O _) (Ideal.algebraMap_residueField_surjective _) (Ideal.ker_algebraMap_residueField _)
    (AlgebraicClosure (Ideal.span {((ℓ : ℕ) : O)}).ResidueField) (algebraMap _ _)
    ((C ⊗[ℤ] O) ⧸ (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C))) (Ideal.Quotient.mk (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C))) Ideal.Quotient.mk_surjective Ideal.mk_ker

end S_IsArtinianRing_isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal
end P2MW
export P2MW.S_IsArtinianRing_isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal (solution)
