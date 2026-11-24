-- Prove2me | solution 1 for GlobalTheory.BaseChangeComponents.components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:48.884841+00:00
-- url     : https://prove2.me/submissions/30be45a2-68d1-4ecb-ad6d-a025bdf89318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
import Theorems.Thm_GlobalTheory_BaseChangeComponents_incl_tmul
import Theorems.Thm_GlobalTheory_BaseChangeComponents_minimalPrimes_eq
import Theorems.Thm_GlobalTheory_BaseChangeComponents_isNoetherianRing_tensor
import Theorems.Thm_GlobalTheory_BaseChangeComponents_range_comp_incl
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_quotient_minimalPrime_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BaseChangeComponents.incl_tmul
section
open scoped TensorProduct
namespace GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
set_option maxHeartbeats 400000 in
private theorem closure_range_tensor_quotient_fraction (P : Ideal (F ⊗[K] Ω)) [P.IsPrime] :
    Subfield.closure (Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) = ⊤ := by
  have key : ∀ s : (F ⊗[K] Ω), ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) s ∈
      Subfield.closure (Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subfield.zero_mem _
    | tmul a w =>
      have hsplit : ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ w) =
          ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ (1 : Ω)) * ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) ((1 : F) ⊗ₜ w) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
        (Subfield.subset_closure (Or.inl ⟨w, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subfield.add_mem _ hx hy
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := (F ⊗[K] Ω) ⧸ P) z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact Subfield.div_mem _ (key s) (key t)
set_option maxHeartbeats 400000 in
private theorem isIntegrallyClosed_closure_minimalPrime_quotient (R : Subalgebra K Ω) [Algebra.Smooth K R]
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (P : Ideal (F ⊗[K] Ω)) (hP : P ∈ minimalPrimes (F ⊗[K] Ω)) : IsIntegrallyClosed (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))))) := by
  have hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let e := (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans
    (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))
  have hmin : Ideal.comap (incl F R) P ∈ minimalPrimes (F ⊗[K] R) := by
    rw [minimalPrimes_eq F R hR]
    exact ⟨P, hP, rfl⟩
  haveI : IsIntegrallyClosed ((F ⊗[K] R) ⧸ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R))) :=
    GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth F (F ⊗[K] R) _ (hker.symm ▸ hmin)
  exact IsIntegrallyClosed.of_equiv e
set_option maxHeartbeats 400000 in
private theorem exists_minimalPrime_closure_lift (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (L : Type) [Field L] (χ : F →+* L) (ψ : R →+* L)
    (hχψ : ∀ a : K, ψ (algebraMap K R a) = χ (algebraMap K F a)) :
    ∃ (P : Ideal (F ⊗[K] Ω)) (_ : P ∈ minimalPrimes (F ⊗[K] Ω)) (φ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))))) →+* L),
      (∀ (r : R) (h : (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) r ∈ (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))), φ ⟨(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) r, h⟩ = ψ r) ∧
      ∀ (a : F) (h : (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))) a ∈ (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))), φ ⟨(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))) a, h⟩ = χ a := by
  letI : Algebra K L := (χ.comp (algebraMap K F)).toAlgebra
  let χ' : F →ₐ[K] L := { χ with commutes' := fun a => rfl }
  let ψ' : R →ₐ[K] L := { ψ with commutes' := fun a => hχψ a }
  let θ : F ⊗[K] R →ₐ[K] L := Algebra.TensorProduct.productMap χ' ψ'
  haveI : (RingHom.ker θ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal (F ⊗[K] R))) (J := RingHom.ker θ.toRingHom) bot_le
  have hq' : q ∈ minimalPrimes (F ⊗[K] R) := hq
  rw [minimalPrimes_eq F R hR] at hq'
  obtain ⟨P, hP, rfl⟩ := hq'
  have hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let e := (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans
    (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))
  have hlift : ∀ a ∈ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)), θ.toRingHom a = 0 := by
    intro a ha
    rw [hker] at ha
    exact RingHom.mem_ker.1 (hqle ha)
  let φ := (Ideal.Quotient.lift _ θ.toRingHom hlift).comp e.symm.toRingHom
  have hφ : ∀ x, φ (e (Ideal.Quotient.mk _ x)) = θ x := by
    intro x
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
    rfl
  refine ⟨P, hP, φ, fun r h => ?_, fun a h => ?_⟩
  · have hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ ((1 : F) ⊗ₜ[K] r)) :=
      Subtype.ext (by
        show _ = ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (incl F R ((1 : F) ⊗ₜ[K] r))
        rw [incl_tmul]; rfl)
    rw [hpt, hφ]
    show χ 1 * ψ r = ψ r
    rw [map_one, one_mul]
  · have hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ (a ⊗ₜ[K] (1 : R))) :=
      Subtype.ext (by
        show _ = ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (incl F R (a ⊗ₜ[K] (1 : R)))
        rw [incl_tmul]; rfl)
    rw [hpt, hφ]
    show χ a * ψ 1 = χ a
    rw [map_one, mul_one]
end GlobalTheory.BaseChangeComponents
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
namespace GlobalTheory.BaseChangeComponents
theorem _root_.solution : ∀ (K F Ω : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω] (R₀ : Subalgebra K Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∃ (J : Type) (_ : Finite J) (Ω' : J → Type) (_ : ∀ j, Field (Ω' j)) (α : ∀ j, Ω →+* Ω' j) (γ : ∀ j, F →+* Ω' j), (∀ j (a : K), α j (algebraMap K Ω a) = γ j (algebraMap K F a)) ∧ (∀ j, Subfield.closure (Set.range (α j) ∪ Set.range (γ j)) = ⊤) ∧ ∀ (R : Subalgebra K Ω), Algebra.Smooth K R → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) → (∀ j, IsIntegrallyClosed (Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)))) ∧ ∀ (L : Type) [Field L] (χ : F →+* L) (ψ : R →+* L), (∀ a : K, ψ (algebraMap K R a) = χ (algebraMap K F a)) → ∃ (j : J) (φ : Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)) →+* L), (∀ (r : R) (h : α j r ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨α j r, h⟩ = ψ r) ∧ ∀ (a : F) (h : γ j a ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨γ j a, h⟩ = χ a :=
  by
    intro K F Ω _ _ _ _ _ R₀ hfg hR₀
    haveI := isNoetherianRing_tensor F R₀ hfg hR₀
    haveI hJ : Finite ↥(minimalPrimes (F ⊗[K] Ω)) :=
      (minimalPrimes.finite_of_isNoetherianRing (F ⊗[K] Ω)).to_subtype
    haveI hprime : ∀ j : ↥(minimalPrimes (F ⊗[K] Ω)), (j.1).IsPrime :=
      fun j => Ideal.minimalPrimes_isPrime j.2
    refine ⟨↥(minimalPrimes (F ⊗[K] Ω)), hJ, fun j => FractionRing ((F ⊗[K] Ω) ⧸ j.1),
      fun j => inferInstance, fun j => (((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom), fun j => (((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))), ?_, ?_, ?_⟩
    · intro j a
      show ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) (Algebra.TensorProduct.includeRight (algebraMap K Ω a)) =
        ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) ((algebraMap K F a) ⊗ₜ (1 : Ω))
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    · intro j
      exact closure_range_tensor_quotient_fraction F j.1
    · intro R _ hR
      refine ⟨fun j => isIntegrallyClosed_closure_minimalPrime_quotient F R hR j.1 j.2, fun L _ χ ψ hχψ => ?_⟩
      obtain ⟨P, hP, φ, h₁, h₂⟩ := exists_minimalPrime_closure_lift F R hR L χ ψ hχψ
      exact ⟨⟨P, hP⟩, φ, h₁, h₂⟩
end GlobalTheory.BaseChangeComponents
