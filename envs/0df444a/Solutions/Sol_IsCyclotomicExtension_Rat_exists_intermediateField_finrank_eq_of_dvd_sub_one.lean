-- Prove2me | solution 1 for IsCyclotomicExtension.Rat.exists_intermediateField_finrank_eq_of_dvd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-06T20:54:19.709767+00:00
-- url     : https://prove2.me/submissions/2214afd6-0e9b-42db-a4be-6c7af27318d5

import Mathlib
open NumberField

namespace KWB

theorem isAbelianGalois_congr_rat {L : Type*} [Field L] {a b : Algebra ℚ L}
    (h : @IsAbelianGalois ℚ L _ _ a) : @IsAbelianGalois ℚ L _ _ b := by
  obtain rfl := Subsingleton.elim a b
  exact h

theorem isCyclotomicExtension_congr_rat {S : Set ℕ} {L : Type*} [Field L] {a b : Algebra ℚ L}
    (h : @IsCyclotomicExtension S ℚ L _ _ a) : @IsCyclotomicExtension S ℚ L _ _ b := by
  obtain rfl := Subsingleton.elim a b
  exact h

/-- A finite-dimensional intermediate field of `Ω / ℚ` is a number field. -/
theorem numberField_of_finiteDimensional {Ω : Type*} [Field Ω]
    [Algebra ℚ Ω] (E : IntermediateField ℚ Ω) [h : FiniteDimensional ℚ E] : NumberField E :=
  { to_finiteDimensional := by
      convert h
      exact Subsingleton.elim _ _ }

theorem span_isPrime (q : ℕ) (hq : q.Prime) : (Ideal.span {(q : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)

/-- Unramified primes stay unramified in subfields (discriminant argument). -/
theorem isUnramifiedIn_of_algHom (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] (f : K →ₐ[ℚ] L) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h : Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(ℓ : ℤ)})) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)}) := by
  let := f.toRingHom.toAlgebra
  have hℓ' := Nat.prime_iff_prime_int.mp hℓ
  rw [← not_dvd_discr_iff_isUnramifiedIn L (𝓞 L) hℓ'] at h
  rw [← not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) hℓ']
  exact fun hd => h (hd.trans (discr_dvd_discr K L))

/-- In a Galois number field, the ramification index of `q` divides the degree. -/
theorem ramificationIdxIn_dvd_finrank (K : Type*) [Field K]
    [NumberField K] [IsGalois ℚ K] (q : ℕ) (hq : q.Prime) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) ∣ Module.finrank ℚ K := by
  have := span_isPrime q hq
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)))
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := (K ≃ₐ[ℚ] K)) (Ideal.span {(q : ℤ)}) Q,
    ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_subgroup_dvd_card _

/-- If `q` is totally ramified in a Galois number field `K`, then it is totally ramified in
every Galois subfield `F`. -/
theorem ramificationIdxIn_eq_finrank_of_algebra (F K : Type*) [Field F] [Field K]
    [NumberField F] [NumberField K] [Algebra F K] [IsGalois ℚ F] [IsGalois ℚ K]
    (q : ℕ) (hq : q.Prime)
    (hK : (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) = Module.finrank ℚ K) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 F) = Module.finrank ℚ F := by
  have := span_isPrime q hq
  obtain ⟨⟨P, hP1, hP2⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)))
  let 𝔭 : Ideal (𝓞 F) := P.under (𝓞 F)
  have : 𝔭.IsPrime := Ideal.IsPrime.under (𝓞 F) P
  have : P.LiesOver 𝔭 := ⟨rfl⟩
  have : 𝔭.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.tower_bot P 𝔭 _
  have h1 : 𝔭.ramificationIdx ℤ ≤ Module.finrank ℚ F := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 (F ≃ₐ[ℚ] F)]
    exact Nat.le_of_dvd Module.finrank_pos (ramificationIdxIn_dvd_finrank F q hq)
  have h2 : P.ramificationIdx (𝓞 F) ≤ Module.finrank F K := by
    rw [IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K]
    let : Fintype (𝔭.primesOver (𝓞 K)) := (Algebra.QuasiFinite.finite_primesOver 𝔭).fintype
    rw [← Ideal.sum_ramification_inertia_eq_finrank 𝔭 (𝓞 K)]
    have hmem : (⟨P, inferInstance, inferInstance⟩ : 𝔭.primesOver (𝓞 K)) ∈ Finset.univ :=
      Finset.mem_univ _
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
    exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos P (𝓞 F))
  have h3 : P.ramificationIdx ℤ = Module.finrank ℚ F * Module.finrank F K := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(q : ℤ)}) P (K ≃ₐ[ℚ] K), hK,
      Module.finrank_mul_finrank]
  have ht := Ideal.ramificationIdx_tower (R := ℤ) 𝔭 P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 (F ≃ₐ[ℚ] F)]
  have h5 : 0 < Module.finrank F K := Module.finrank_pos
  have h6 : 0 < Module.finrank ℚ F := Module.finrank_pos
  nlinarith

/-- A prime `ℓ` that does not divide `q` is unramified in the `q`-th cyclotomic field. -/
theorem isUnramifiedIn_of_not_dvd (q : ℕ) [NeZero q] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {q} ℚ K] (ℓ : ℕ) (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ q) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)}) := by
  have := Fact.mk hℓ
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P _ hP
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ℓ K P h

theorem numberField_of_ringEquiv {A B : Type*} [Field A] [Field B] [NumberField A]
    (f : A ≃+* B) : NumberField B :=
  have : CharZero B := charZero_of_injective_ringHom f.toRingHom.injective
  { to_finiteDimensional := f.toRatAlgEquiv.toLinearEquiv.finiteDimensional }

theorem finrank_eq_of_ringEquiv {A B : Type*} [Field A] [Field B] [CharZero A] [CharZero B]
    (f : A ≃+* B) : Module.finrank ℚ A = Module.finrank ℚ B :=
  f.toRatAlgEquiv.toLinearEquiv.finrank_eq

theorem core {Ω : Type*} [Field Ω] [Algebra ℚ Ω] (q e : ℕ) (hq : q.Prime) (he : e ∣ q - 1)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {q} ℚ K] (φ : K →ₐ[ℚ] Ω) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧ IsAbelianGalois ℚ F ∧
      Module.finrank ℚ F = e ∧ Nonempty (F →ₐ[ℚ] K) ∧
      (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 F) = e ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ℓ : ℤ)}) := by
  have := Fact.mk hq
  have : NeZero q := ⟨hq.ne_zero⟩
  have hKg : IsGalois ℚ K := IsCyclotomicExtension.isGalois {q} ℚ K
  have hKa : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  have hKdeg : Module.finrank ℚ K = q - 1 := by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos q)),
      Nat.totient_prime hq]
  -- The subgroup of index `e` of `Gal(K/ℚ) ≃* (ZMod q)ˣ`.
  let H0 : Subgroup (ZMod q)ˣ := (powMonoidHom e : (ZMod q)ˣ →* (ZMod q)ˣ).range
  have hH0 : H0.index = e := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units, Nat.card_zmod, Nat.gcd_eq_right he]
  let H : Subgroup Gal(K/ℚ) :=
    H0.comap (IsCyclotomicExtension.Rat.galEquivZMod q K).toMonoidHom
  have hH : H.index = e := by
    exact (Subgroup.index_comap_of_surjective H0
      (IsCyclotomicExtension.Rat.galEquivZMod q K).surjective).trans hH0
  -- Its fixed field `E` has degree `e`.
  let E : IntermediateField ℚ K := IntermediateField.fixedField H
  have hEdeg : Module.finrank ℚ E = e := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField, hH]
  -- Its image `F` in `Ω`.
  let F : IntermediateField ℚ Ω := E.map φ
  let ρ : E ≃+* F := (E.equivMap φ : E ≃+* E.map φ)
  have : FiniteDimensional ℚ E := inferInstance
  have : NumberField E := numberField_of_finiteDimensional E
  have : NumberField F := numberField_of_ringEquiv ρ
  have hFfin : FiniteDimensional ℚ F := by
    convert (inferInstance : NumberField F).to_finiteDimensional
    exact Subsingleton.elim _ _
  have hFdeg : Module.finrank ℚ F = e := by
    rw [← hEdeg]
    convert (finrank_eq_of_ringEquiv ρ).symm using 2; exact Subsingleton.elim _ _
  let f : F →ₐ[ℚ] K := ((E.val : E →+* K).comp (ρ.symm : F →+* E)).toRatAlgHom
  have hEab : IsAbelianGalois ℚ E :=
    isAbelianGalois_congr_rat (inferInstance : @IsAbelianGalois ℚ E _ _ E.algebra')
  have hFab : IsAbelianGalois ℚ F :=
    IsAbelianGalois.of_algHom ((ρ.symm : F →+* E).toRatAlgHom)
  refine ⟨F, hFfin, hFab, hFdeg, ⟨f⟩, ?_, ?_⟩
  · let : Algebra F K := f.toRingHom.toAlgebra
    have : IsGalois ℚ F := hFab.toIsGalois
    have hK : (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) = Module.finrank ℚ K := by
      rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime q K, hKdeg]
    rw [ramificationIdxIn_eq_finrank_of_algebra F K q hq hK, ← hFdeg]
    congr 1
    exact Subsingleton.elim _ _
  · intro ℓ hℓ hne
    exact isUnramifiedIn_of_algHom F K f ℓ hℓ
      (isUnramifiedIn_of_not_dvd q K ℓ hℓ (fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hq).1 h)))

end KWB

theorem solution
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (q e : ℕ) (hq : q.Prime)
    (he : e ∣ q - 1) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧ IsAbelianGalois ℚ F ∧
      Module.finrank ℚ F = e ∧
      Nonempty (F →ₐ[ℚ] CyclotomicField q ℚ) ∧
      (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 F) = e ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ℓ : ℤ)}) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) :=
    KWB.isCyclotomicExtension_congr_rat (inferInstance :
      @IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) _ _ (CyclotomicField.algebra q ℚ))
  let φ : CyclotomicField q ℚ →ₐ[ℚ] Ω := IsAlgClosed.lift
  exact KWB.core q e hq he (CyclotomicField q ℚ) φ
