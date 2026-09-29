-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dee8e67e-33a9-5b5c-9d47-ede6115781af

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified
import Theorems.Thm_LanglandsTunnell_TateLocal_mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_tensor_adicCompletion_algEquiv_of_baseChange
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_valued_eq_exp_inertiaDeg_mul_of_valued_norm_eq_of_baseChange
import Theorems.Thm_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

namespace TensorFixedRight

variable (F : Type) [Field F] (E M : Type) [CommRing E] [Algebra F E] [CommRing M] [Algebra F M]
  (τ : M →ₐ[F] M)

theorem exact_linearMap_sub (hfix : ∀ m : M, τ m = m → m ∈ Set.range (algebraMap F M)) :
    Function.Exact (Algebra.linearMap F M) (τ.toLinearMap - LinearMap.id : M →ₗ[F] M) := by
  intro y
  simp only [LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply, sub_eq_zero,
    Set.mem_range, Algebra.linearMap_apply]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := hfix y h
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact τ.commutes k

theorem lTensor_sub_apply (z : E ⊗[F] M) :
    ((τ.toLinearMap - LinearMap.id : M →ₗ[F] M).lTensor E) z =
      Algebra.TensorProduct.map (AlgHom.id F E) τ z - z := by
  induction z with
  | zero => simp
  | tmul x b => simp [LinearMap.lTensor_tmul]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add]
    abel

theorem range_lTensor_linearMap :
    Set.range ((Algebra.linearMap F M).lTensor E) =
      Set.range (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] M) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    induction t with
    | zero => exact ⟨0, by simp⟩
    | tmul b k =>
      refine ⟨k • b, ?_⟩
      simp [LinearMap.lTensor_tmul, Algebra.TensorProduct.includeLeft_apply,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
    | add x y hx hy =>
      obtain ⟨b, hb⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨b + c, by rw [map_add, hb, hc, map_add]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b ⊗ₜ 1, by simp [LinearMap.lTensor_tmul, Algebra.TensorProduct.includeLeft_apply]⟩

theorem iff (hfix : ∀ m : M, τ m = m ↔ m ∈ Set.range (algebraMap F M)) (z : E ⊗[F] M) :
    Algebra.TensorProduct.map (AlgHom.id F E) τ z = z ↔
      z ∈ Set.range (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] M) := by
  have hex := Module.Flat.lTensor_exact E (exact_linearMap_sub F M τ fun m h => (hfix m).mp h)
  rw [← range_lTensor_linearMap F E M, ← hex z, lTensor_sub_apply, sub_eq_zero]

end TensorFixedRight

namespace Algebra p2m_export "Algebra" "algebraMap_eq_smul_one TensorProduct.map_id linearMap_apply commutes TensorProduct.includeRight TensorProduct.includeLeft_apply algebraMap norm_eq_prod_automorphisms TensorProduct.congr mem_top FormallyUnramified norm_eq_of_algEquiv Extension norm TensorProduct.map_tmul TensorProduct.algebraMap_apply FormallyUnramified.of_isSeparable IsIntegral.of_finite algebraMap_self_apply adjoin TensorProduct.includeLeft id TensorProduct.map_comp TensorProduct.congr_apply TensorProduct.map FormallyUnramified.isReduced_of_field TensorProduct.includeRight_injective" namespace TensorProduct p2m_export "Algebra.TensorProduct" "mul_apply map_id includeRight includeLeft_apply congr lTensor map_tmul algebraMap_apply includeLeft map_comp congr_apply map ext includeRight_injective" end Algebra.TensorProduct
p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.map_id_apply_eq_self_iff_mem_range_includeLeft
    (F : Type) [Field F] (E M : Type) [CommRing E] [Algebra F E] [CommRing M] [Algebra F M]
    (τ : M →ₐ[F] M) (hfix : ∀ m : M, τ m = m ↔ m ∈ Set.range (algebraMap F M))
    (z : E ⊗[F] M) :
    Algebra.TensorProduct.map (AlgHom.id F E) τ z = z ↔
      z ∈ Set.range (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] M) :=
  TensorFixedRight.iff F E M τ hfix z

namespace RankOneWitness

variable {R : Type} [CommRing R]

theorem one_add_mul_mul_one_add_mul (X : R) {r t : R} (h : r * t = 0) :
    (1 + r * X) * (1 + t * X) = 1 + (r + t) * X := by
  linear_combination (X ^ 2) * h

theorem one_add_mul_mul_eq_one (X Y : R) {e : R} (he : IsIdempotentElem e) (h : X + Y + X * Y = 0) :
    (1 + e * X) * (1 + e * Y) = 1 := by
  have he' : e * e = e := he.eq
  linear_combination (X * Y) * he' + e * h

theorem iterate_mul_iterate_eq_zero (s : R →+* R) (e : R) (n : ℕ)
    (horth : ∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) {i j : ℕ} (hij : i < j) (hj : j < n) :
    (⇑s)^[i] e * (⇑s)^[j] e = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  rw [Function.iterate_add_apply, ← RingHom.coe_pow, ← map_mul, horth k (by omega) (by omega),
    map_zero]

theorem sum_iterate_mul_iterate_eq_zero (s : R →+* R) (e : R) (n : ℕ)
    (horth : ∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) {m : ℕ} (hm : m < n) :
    (∑ i ∈ Finset.range m, (⇑s)^[i] e) * (⇑s)^[m] e = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun i hi =>
    iterate_mul_iterate_eq_zero s e n horth (Finset.mem_range.mp hi) hm

theorem iterate_one_add_mul (s : R →+* R) (e X : R) (hX : s X = X) (i : ℕ) :
    (⇑s)^[i] (1 + e * X) = 1 + (⇑s)^[i] e * X := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_add, map_one, map_mul, hX]

theorem prod_range (s : R →+* R) (e X : R) (hX : s X = X) (n : ℕ)
    (horth : ∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) (m : ℕ) (hm : m ≤ n) :
    ((List.range m).map fun i => (⇑s)^[i] (1 + e * X)).prod =
      1 + (∑ i ∈ Finset.range m, (⇑s)^[i] e) * X := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ih (by omega), iterate_one_add_mul s e X hX,
      one_add_mul_mul_one_add_mul X (sum_iterate_mul_iterate_eq_zero s e n horth (by omega)),
      Finset.sum_range_succ]

theorem exists_units (s : R →+* R) (n : ℕ) (e : R) (he : IsIdempotentElem e)
    (horth : ∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0)
    (hsum : (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1)
    (x : Rˣ) (hx : s x = x) :
    ∃ u : Rˣ, ((List.range n).map fun i => (⇑s)^[i] (u : R)).prod = x := by
  have hXY : ((x : R) - 1) + ((x⁻¹ : Rˣ) - 1 : R) + ((x : R) - 1) * ((x⁻¹ : Rˣ) - 1 : R) = 0 := by
    linear_combination x.mul_inv
  have hYX : ((x⁻¹ : Rˣ) - 1 : R) + ((x : R) - 1) + ((x⁻¹ : Rˣ) - 1 : R) * ((x : R) - 1) = 0 := by
    linear_combination x.mul_inv
  refine ⟨⟨1 + e * ((x : R) - 1), 1 + e * ((x⁻¹ : Rˣ) - 1 : R),
    one_add_mul_mul_eq_one _ _ he hXY, one_add_mul_mul_eq_one _ _ he hYX⟩, ?_⟩
  have hX : s ((x : R) - 1) = (x : R) - 1 := by rw [map_sub, map_one, hx]
  change ((List.range n).map fun i => (⇑s)^[i] (1 + e * ((x : R) - 1))).prod = x
  rw [prod_range s e _ hX n horth n le_rfl, hsum, one_mul, add_sub_cancel]

end RankOneWitness

theorem exists_units_prod_iterate_eq_of_isIdempotentElem_of_sum_iterate_eq_one
    (R : Type) [CommRing R] (s : R →+* R) (n : ℕ)
    (e : R) (he : IsIdempotentElem e)
    (horth : ∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0)
    (hsum : (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1)
    (x : Rˣ) (hx : s x = x) :
    ∃ u : Rˣ, ((List.range n).map fun i => (⇑s)^[i] (u : R)).prod = x :=
  RankOneWitness.exists_units s n e he horth hsum x hx

namespace Algebra
p2m_export "Algebra" "algebraMap_eq_smul_one TensorProduct.map_id linearMap_apply commutes TensorProduct.includeRight TensorProduct.includeLeft_apply algebraMap norm_eq_prod_automorphisms TensorProduct.congr mem_top FormallyUnramified norm_eq_of_algEquiv Extension norm TensorProduct.map_tmul TensorProduct.algebraMap_apply FormallyUnramified.of_isSeparable IsIntegral.of_finite algebraMap_self_apply adjoin TensorProduct.includeLeft id TensorProduct.map_comp TensorProduct.congr_apply TensorProduct.map FormallyUnramified.isReduced_of_field TensorProduct.includeRight_injective"
namespace TensorProduct
p2m_export "Algebra.TensorProduct" "mul_apply map_id includeRight includeLeft_apply congr lTensor map_tmul algebraMap_apply includeLeft map_comp congr_apply map ext includeRight_injective"
namespace NormBC
p2m_open "Algebra.TensorProduct Algebra"

theorem list_prod_range_map {α : Type*} [CommMonoid α] (g : ℕ → α) (k : ℕ) :
    ((List.range k).map g).prod = ∏ i ∈ Finset.range k, g i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ, ih]; simp

end Algebra.TensorProduct.NormBC

p2m_open_scoped "Algebra Algebra.TensorProduct" in
open Algebra.TensorProduct.NormBC in

theorem Algebra.TensorProduct.algebraMap_norm_eq_prod_iterate_map_of_isDomain
    (F E M : Type*) [Field F] [Field E] [Field M] [Algebra F E] [Algebra F M]
    [FiniteDimensional F M] [IsGalois F M]
    (τ : M ≃ₐ[F] M) (hτ : ∀ ρ : M ≃ₐ[F] M, ρ ∈ Subgroup.zpowers τ)
    [IsDomain (E ⊗[F] M)] (z : E ⊗[F] M) :
    algebraMap E (E ⊗[F] M) (Algebra.norm E z) =
      ((List.range (Module.finrank F M)).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id F E) (τ : M →ₐ[F] M)))^[i] z).prod := by
  classical
  set n := Module.finrank F M with hn

  have hcardM : Nat.card (M ≃ₐ[F] M) = n := IsGalois.card_aut_eq_finrank F M
  have htop : Subgroup.zpowers τ = ⊤ := (Subgroup.eq_top_iff' _).mpr hτ
  have horder : orderOf τ = n := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hcardM]

  let σ : ℕ → (E ⊗[F] M ≃ₐ[E] E ⊗[F] M) := fun i =>
    Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) (τ ^ i)
  have hσ_tmul : ∀ (i : ℕ) (e : E) (m : M), σ i (e ⊗ₜ[F] m) = e ⊗ₜ[F] (τ ^ i) m := by
    intro i e m
    simp [σ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hσ_iter : ∀ (i : ℕ) (x : E ⊗[F] M),
      σ i x = (⇑(Algebra.TensorProduct.map (AlgHom.id F E) (τ : M →ₐ[F] M)))^[i] x := by
    intro i
    induction i with
    | zero =>
      intro x
      simp only [Function.iterate_zero, id_eq]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul e m => rw [hσ_tmul, pow_zero, AlgEquiv.one_apply]
      | add x y hx hy => rw [map_add, hx, hy]
    | succ i ih =>
      intro x
      rw [Function.iterate_succ_apply', ← ih]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul e m =>
        rw [hσ_tmul, hσ_tmul, Algebra.TensorProduct.map_tmul, pow_succ', AlgEquiv.mul_apply]
        rfl
      | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

  have hincl : Function.Injective
      (Algebra.TensorProduct.includeRight : M →ₐ[F] E ⊗[F] M) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective F E)
  have hσ_inj : ∀ i j : ℕ, i < n → j < n → σ i = σ j → i = j := by
    intro i j hi hj hij
    have hpow : τ ^ i = τ ^ j := by
      ext m
      apply hincl
      change (1 : E) ⊗ₜ[F] (τ ^ i) m = (1 : E) ⊗ₜ[F] (τ ^ j) m
      rw [← hσ_tmul, ← hσ_tmul, hij]
    exact pow_injOn_Iio_orderOf (by rwa [Set.mem_Iio, horder]) (by rwa [Set.mem_Iio, horder]) hpow

  haveI : Algebra.IsIntegral E (E ⊗[F] M) := Algebra.IsIntegral.of_finite E (E ⊗[F] M)
  have hfield : IsField (E ⊗[F] M) := isField_of_isIntegral_of_isField' (Field.toIsField E)
  letI : Field (E ⊗[F] M) := hfield.toField
  have hfr : Module.finrank E (E ⊗[F] M) = n := Module.finrank_baseChange
  let f : Fin n → (E ⊗[F] M ≃ₐ[E] E ⊗[F] M) := fun i => σ i
  have hf_inj : Function.Injective f := fun i j hij =>
    Fin.ext (hσ_inj i j i.isLt j.isLt hij)
  have hcard_le : Fintype.card (E ⊗[F] M ≃ₐ[E] E ⊗[F] M) ≤ n := hfr ▸ AlgEquiv.card_le
  have hcard_ge : n ≤ Fintype.card (E ⊗[F] M ≃ₐ[E] E ⊗[F] M) := by
    simpa using Fintype.card_le_of_injective f hf_inj
  have hcard : Fintype.card (E ⊗[F] M ≃ₐ[E] E ⊗[F] M) = n := le_antisymm hcard_le hcard_ge
  haveI : IsGalois E (E ⊗[F] M) :=
    IsGalois.of_card_aut_eq_finrank E (E ⊗[F] M) (by rw [Nat.card_eq_fintype_card, hcard, hfr])
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by simp [hcard]⟩

  have hnorm := Algebra.norm_eq_prod_automorphisms E z
  rw [← (Equiv.ofBijective f hf_bij).prod_comp (fun ρ => ρ z)] at hnorm
  simp only [Equiv.ofBijective_apply] at hnorm
  rw [list_prod_range_map, ← Fin.prod_univ_eq_prod_range (fun i => (⇑(Algebra.TensorProduct.map
    (AlgHom.id F E) (τ : M →ₐ[F] M)))^[i] z) n]
  convert hnorm using 2 with i
  exact (hσ_iter i z).symm

namespace N2cgTrunk

theorem iterate_map_id_apply {R A C : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring C] [Algebra R C] (g : C ≃ₐ[R] C) (i : ℕ) (z : A ⊗[R] C) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id R A) (g : C →ₐ[R] C)))^[i] z =
      Algebra.TensorProduct.map (AlgHom.id R A) ((g ^ i : C ≃ₐ[R] C) : C →ₐ[R] C) z := by
  induction i generalizing z with
  | zero =>
    have h1 : ((g ^ 0 : C ≃ₐ[R] C) : C →ₐ[R] C) = AlgHom.id R C := by
      ext y; simp
    rw [Function.iterate_zero, id_eq, h1, Algebra.TensorProduct.map_id, AlgHom.id_apply]
  | succ i ih =>
    have hc : (g : C →ₐ[R] C).comp ((g ^ i : C ≃ₐ[R] C) : C →ₐ[R] C) =
        ((g ^ (i + 1) : C ≃ₐ[R] C) : C →ₐ[R] C) := by
      ext y; simp [pow_succ', AlgEquiv.mul_apply]
    rw [Function.iterate_succ_apply', ih, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, hc]

theorem isGalois_of_fixedPoints {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (θ : E ≃ₐ[F] E) (hθfix : ∀ y : E, θ y = y ↔ y ∈ Set.range (algebraMap F E)) : IsGalois F E := by
  apply IsGalois.of_fixedField_eq_bot
  rw [eq_bot_iff]
  intro y hy
  rw [IntermediateField.mem_fixedField_iff] at hy
  obtain ⟨c, rfl⟩ := (hθfix y).mp (hy θ (Subgroup.mem_top θ))
  exact IntermediateField.algebraMap_mem ⊥ c

theorem mem_zpowers_of_orderOf_eq_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (θ : E ≃ₐ[F] E) (hθ : orderOf θ = Module.finrank F E) (ρ : E ≃ₐ[F] E) :
    ρ ∈ Subgroup.zpowers θ := by
  have htop : Subgroup.zpowers θ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hθ, IsGalois.card_aut_eq_finrank]
  rw [htop]; exact Subgroup.mem_top ρ

theorem exists_units_of_not_isField {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E]
    [Algebra F C] [FiniteDimensional F C] [IsReduced (E ⊗[F] C)]
    (θ : C ≃ₐ[F] C) (n : ℕ) (hn : n.Prime) (hθ : orderOf θ = n)
    (hθfix : ∀ y : C, θ y = y ↔ y ∈ Set.range (algebraMap F C))
    (hB : ¬ IsField (E ⊗[F] C)) (x : E) (hx : x ≠ 0) :
    ∃ e : (E ⊗[F] C)ˣ,
      ((List.range n).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id F E) (θ : C →ₐ[F] C)))^[i] (e : E ⊗[F] C)).prod
        = x ⊗ₜ[F] (1 : C) := by
  classical
  set T := Algebra.TensorProduct.map (AlgHom.id F E) (θ : C →ₐ[F] C) with hT
  haveI : Module.Finite E (E ⊗[F] C) := inferInstance
  have hsn : (⇑T.toRingHom)^[n] = id := by
    funext z
    change (⇑T)^[n] z = z
    have h1 : ((θ ^ n : C ≃ₐ[F] C) : C →ₐ[F] C) = AlgHom.id _ _ := by
      rw [← hθ, pow_orderOf_eq_one]; ext y; simp
    rw [hT, N2cgTrunk.iterate_map_id_apply, h1, Algebra.TensorProduct.map_id, AlgHom.id_apply]
  have hθfix' : ∀ m : C, (θ : C →ₐ[F] C) m = m ↔ m ∈ Set.range (algebraMap F C) := fun m => by
    rw [AlgEquiv.coe_algHom]; exact hθfix m
  have hfix : ∀ a : E ⊗[F] C, T.toRingHom a = a → a ∈ Set.range (algebraMap E (E ⊗[F] C)) := by
    intro a ha
    obtain ⟨b, hb⟩ :=
      (Algebra.TensorProduct.map_id_apply_eq_self_iff_mem_range_includeLeft F E C _ hθfix' a).mp ha
    exact ⟨b, by rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]; exact hb⟩
  obtain ⟨ε, hε, horth, hsum⟩ :=
    exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
      E (E ⊗[F] C) T.toRingHom n hn hsn hfix hB
  have hxu : IsUnit (x ⊗ₜ[F] (1 : C)) := by
    have h := (Units.mk0 x hx).isUnit.map (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] C)
    rwa [Units.val_mk0, Algebra.TensorProduct.includeLeft_apply] at h
  have hsx : T.toRingHom (hxu.unit : E ⊗[F] C) = hxu.unit := by
    change T (hxu.unit : E ⊗[F] C) = hxu.unit
    rw [hxu.unit_spec, hT, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  obtain ⟨u, hu⟩ := exists_units_prod_iterate_eq_of_isIdempotentElem_of_sum_iterate_eq_one
    (E ⊗[F] C) T.toRingHom n ε hε horth hsum hxu.unit hsx
  refine ⟨u, ?_⟩
  rw [hxu.unit_spec] at hu
  exact hu

end N2cgTrunk

theorem solution
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (hdeg : (Module.finrank K L).Prime) (hK' : Module.finrank K K' = 2)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (w : v.Extension (𝓞 L)) (hw : ∀ w' : v.Extension (𝓞 L), w' = w)
    (𝔳 : v.Extension (𝓞 K')) (h𝔳 : ∀ 𝔳' : v.Extension (𝓞 K'), 𝔳' = 𝔳)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank K L)
    (hθfix : ∀ y : w.1.adicCompletion L, θ y = y ↔
      y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (hfin : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hθσ : ∀ y : L, θ (algebraMap L (w.1.adicCompletion L) y) =
      algebraMap L (w.1.adicCompletion L) (σ y))
    (x : 𝔳.1.adicCompletion K') (hx : x ≠ 0)
    (hdiv : ∃ k : ℤ, Valued.v (Algebra.norm (v.adicCompletion K) x) =
      ((Multiplicative.ofAdd ((Module.finrank K L : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ e : (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L)ˣ,
      ((List.range (Module.finrank K L)).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (𝔳.1.adicCompletion K'))
              (θ : w.1.adicCompletion L →ₐ[v.adicCompletion K] w.1.adicCompletion L)))^[i]
            (e : 𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L)).prod
        = x ⊗ₜ[v.adicCompletion K] (1 : w.1.adicCompletion L) := by
  classical

  haveI : IsGalois (v.adicCompletion K) (w.1.adicCompletion L) := N2cgTrunk.isGalois_of_fixedPoints θ hθfix
  have hτ : ∀ ρ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L,
      ρ ∈ Subgroup.zpowers θ :=
    N2cgTrunk.mem_zpowers_of_orderOf_eq_finrank θ (hθ.trans hfin.symm)

  have hv' : ∀ w' : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w'.1.asIdeal = 1 := by
    intro w'
    have h := hv w'.1 w'.2
    rwa [w'.2] at h

  obtain ⟨e₁, -⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_tensor_adicCompletion_algEquiv_of_baseChange
      K L K' M hdisj hcomp v w 𝔳 hfin
  by_cases hB : IsField (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L)
  ·

    haveI : IsDomain (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L) := hB.isDomain
    open scoped TensorProduct.RightActions in
    have hA : IsField (M ⊗[K'] 𝔳.1.adicCompletion K') := MulEquiv.isField hB e₁.toMulEquiv
    open scoped TensorProduct.RightActions in
    obtain ⟨𝔴, e₂, -, -, -⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
        K' M 𝔳.1 hA

    open scoped TensorProduct.RightActions in
    have hΦ : ∃ Φ : (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L) ≃ₐ[𝔳.1.adicCompletion K']
        𝔴.1.adicCompletion M, True := ⟨e₁.symm.trans e₂, trivial⟩
    obtain ⟨Φ, -⟩ := hΦ

    obtain ⟨k, hk⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_valued_eq_exp_inertiaDeg_mul_of_valued_norm_eq_of_baseChange
        K L K' M hdisj hcomp hdeg hK' v hv' 𝔳 𝔴 x hx hdiv
    have he𝔴 := (IsDedekindDomain.HeightOneSpectrum.ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified
      K L K' M hdisj hcomp v hv' 𝔳 𝔴).1
    obtain ⟨y, hy⟩ :=
      (LanglandsTunnell.TateLocal.mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one
        K' M 𝔳.1 𝔴 he𝔴 (Units.mk0 x hx)).mpr ⟨k, hk⟩
    have hy' : Algebra.norm (𝔳.1.adicCompletion K') (y : 𝔴.1.adicCompletion M) = x := by
      have h := congrArg Units.val hy
      simpa only [Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] using h

    have hunit : IsUnit (Φ.symm (y : 𝔴.1.adicCompletion M)) := (Units.isUnit y).map Φ.symm
    refine ⟨hunit.unit, ?_⟩
    rw [hunit.unit_spec, ← hfin,
      ← Algebra.TensorProduct.algebraMap_norm_eq_prod_iterate_map_of_isDomain (v.adicCompletion K)
        (𝔳.1.adicCompletion K') (w.1.adicCompletion L) θ hτ,
      Algebra.norm_eq_of_algEquiv, hy', Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  ·

    haveI : Module.Finite (𝔳.1.adicCompletion K')
        (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L) := inferInstance
    haveI : Algebra.FormallyUnramified (v.adicCompletion K) (w.1.adicCompletion L) :=
      Algebra.FormallyUnramified.of_isSeparable _ _
    haveI : Algebra.FormallyUnramified (𝔳.1.adicCompletion K')
        (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L) := inferInstance
    haveI : IsReduced (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L) :=
      Algebra.FormallyUnramified.isReduced_of_field (𝔳.1.adicCompletion K') _
    exact N2cgTrunk.exists_units_of_not_isField θ (Module.finrank K L) hdeg hθ hθfix hB x hx

end S_IsDedekindDomain_HeightOneSpectrum_exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm (solution)
