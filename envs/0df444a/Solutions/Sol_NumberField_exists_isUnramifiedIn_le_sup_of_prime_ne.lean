-- Prove2me | solution 1 for NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T10:13:12.694067+00:00
-- url     : https://prove2.me/submissions/22b851c4-0ee5-47e8-b756-eecdda4c7337
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NumberField_exists_injective_inertia_monoidHom_zmod_units
import Theorems.Thm_IsCyclotomicExtension_Rat_exists_intermediateField_finrank_eq_of_dvd_sub_one
import Theorems.Thm_NumberField_isUnramifiedIn_sup

open NumberField

/-! ## Second-layer lemmas -/


/-- Consequence of (A). Proved. -/
theorem NumberField.card_inertia_dvd_sub_one (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] (q : ℕ) (hq : q.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] (h : ¬ q ∣ Nat.card (Q.inertia (K ≃ₐ[ℚ] K))) :
    Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) ∣ q - 1 := by
  have := Fact.mk hq
  obtain ⟨f, hf⟩ := NumberField.exists_injective_inertia_monoidHom_zmod_units K q hq Q h
  have := Subgroup.card_dvd_of_injective f hf
  rwa [Nat.card_units, Nat.card_zmod] at this

/-- Mathlib bridge. Proved. -/
theorem NumberField.card_inertia_eq_ramificationIdxIn' (K : Type*) [Field K]
    [NumberField K] [IsGalois ℚ K] (q : ℕ) (hq : q.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] :
    Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) = (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) := by
  have : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  exact Ideal.card_inertia_eq_ramificationIdxIn (G := (K ≃ₐ[ℚ] K)) (Ideal.span {(q : ℤ)}) Q

/-- `ramificationIdxIn` form of (A). Proved from (A). -/
theorem NumberField.ramificationIdxIn_dvd_sub_one (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] (q : ℕ) (hq : q.Prime)
    (h : ¬ q ∣ (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K)) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) ∣ q - 1 := by
  have : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)))
  rw [← NumberField.card_inertia_eq_ramificationIdxIn' K q hq Q] at h ⊢
  exact NumberField.card_inertia_dvd_sub_one K q hq Q h

/-- The ramification index divides the degree. Proved. -/
theorem NumberField.ramificationIdxIn_dvd_finrank (K : Type*) [Field K]
    [NumberField K] [IsGalois ℚ K] (q : ℕ) (hq : q.Prime) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) ∣ Module.finrank ℚ K := by
  have : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)))
  rw [← NumberField.card_inertia_eq_ramificationIdxIn' K q hq Q, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_subgroup_dvd_card _

/-! ### Transport between the two `ℚ`-structures on an intermediate field

For `E : IntermediateField ℚ Ω`, elaboration picks `DivisionRing.toRatAlgebra` for
`IsGalois ℚ E` and `IsAbelianGalois ℚ E`, but `IntermediateField.module'` for
`FiniteDimensional ℚ E` and `Module.finrank ℚ E`. The two structures are equal because
`Algebra ℚ _` and `Module ℚ _` are subsingletons. -/

theorem isGalois_congr_rat {L : Type*} [Field L] {a b : Algebra ℚ L}
    (h : @IsGalois ℚ _ L _ a) : @IsGalois ℚ _ L _ b := by
  obtain rfl := Subsingleton.elim a b
  exact h

theorem isAbelianGalois_congr_rat {L : Type*} [Field L] {a b : Algebra ℚ L}
    (h : @IsAbelianGalois ℚ L _ _ a) : @IsAbelianGalois ℚ L _ _ b := by
  obtain rfl := Subsingleton.elim a b
  exact h

/-- A finite-dimensional intermediate field of `Ω / ℚ` is a number field. Proved. -/
theorem IntermediateField.numberField_of_finiteDimensional {Ω : Type*} [Field Ω]
    [Algebra ℚ Ω] (E : IntermediateField ℚ Ω) [h : FiniteDimensional ℚ E] : NumberField E :=
  { to_finiteDimensional := by
      convert h
      exact Subsingleton.elim _ _ }

/-- `ramificationIdxIn_dvd_sub_one` for an intermediate field. Proved. -/
theorem NumberField.ramificationIdxIn_dvd_sub_one_of_intermediateField {Ω : Type*} [Field Ω]
    [Algebra ℚ Ω] (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsAbelianGalois ℚ M]
    (q : ℕ) (hq : q.Prime) (h : ¬ q ∣ (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 M)) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 M) ∣ q - 1 := by
  have := M.numberField_of_finiteDimensional
  exact NumberField.ramificationIdxIn_dvd_sub_one M q hq h

/-- `ramificationIdxIn_dvd_finrank` for an intermediate field. Proved. -/
theorem NumberField.ramificationIdxIn_dvd_finrank_of_intermediateField {Ω : Type*} [Field Ω]
    [Algebra ℚ Ω] (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M]
    (q : ℕ) (hq : q.Prime) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 M) ∣ Module.finrank ℚ M := by
  have := M.numberField_of_finiteDimensional
  convert NumberField.ramificationIdxIn_dvd_finrank M q hq using 2
  exact Subsingleton.elim _ _



/-- Unramified passes to subfields. Proved. -/
theorem NumberField.isUnramifiedIn_of_algHom (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] (f : K →ₐ[ℚ] L) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h : Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(ℓ : ℤ)})) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)}) := by
  let := f.toRingHom.toAlgebra
  have hℓ' := Nat.prime_iff_prime_int.mp hℓ
  rw [← not_dvd_discr_iff_isUnramifiedIn L (𝓞 L) hℓ'] at h
  rw [← not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) hℓ']
  exact fun hd => h (hd.trans (discr_dvd_discr K L))

/-- Unramified passes to smaller intermediate fields. Proved. -/
theorem NumberField.isUnramifiedIn_of_le {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (K L : IntermediateField ℚ Ω) [FiniteDimensional ℚ K] [FiniteDimensional ℚ L] (h : K ≤ L)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hL : Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(ℓ : ℤ)})) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)}) := by
  have := K.numberField_of_finiteDimensional
  have := L.numberField_of_finiteDimensional
  exact NumberField.isUnramifiedIn_of_algHom K L
    (↑(IntermediateField.inclusion h) : K →+* L).toRatAlgHom ℓ hℓ hL

namespace KWTameD

theorem isGalois_congr_rat {L : Type*} [Field L] {a b : Algebra ℚ L}
    (h : @IsGalois ℚ _ L _ a) : @IsGalois ℚ _ L _ b := by
  obtain rfl := Subsingleton.elim a b
  exact h

theorem isAbelianGalois_congr_rat {L : Type*} [Field L] {a b : Algebra ℚ L}
    (h : @IsAbelianGalois ℚ L _ _ a) : @IsAbelianGalois ℚ L _ _ b := by
  obtain rfl := Subsingleton.elim a b
  exact h

theorem numberField_of_finiteDimensional {Ω : Type*} [Field Ω]
    [Algebra ℚ Ω] (E : IntermediateField ℚ Ω) [h : FiniteDimensional ℚ E] : NumberField E :=
  { to_finiteDimensional := by
      convert h
      exact Subsingleton.elim _ _ }

theorem isUnramifiedIn_of_ramificationIdx_eq_one (F : Type*) [Field F] [NumberField F]
    [IsGalois ℚ F] (q : ℕ) (𝔮 : Ideal (𝓞 F)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(q : ℤ)})]
    (h : 𝔮.ramificationIdx ℤ = 1) :
    Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)}) := by
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro 𝔓 _ h𝔓
  rw [Ideal.ramificationIdx_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) 𝔓 𝔮 (F ≃ₐ[ℚ] F)]
  exact h

theorem exists_inertiaField (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K]
    (q : ℕ) (hq : q.Prime) :
    ∃ E : IntermediateField ℚ K,
      Module.finrank ℚ E * (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) =
        Module.finrank ℚ K ∧
      Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(q : ℤ)}) := by
  have hpr : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  have hp0 : Ideal.span {(q : ℤ)} ≠ ⊥ := by simp [hq.ne_zero]
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)))
  have hQm : Q.IsMaximal := hQ1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q)
  let I := Q.inertia (K ≃ₐ[ℚ] K)
  let E : IntermediateField ℚ K := FixedPoints.intermediateField I
  refine ⟨E, ?_, ?_⟩
  · have h1 := IsInertiaField.rank_left ℤ ℚ K Q E hp0
    rw [← h1, Module.finrank_mul_finrank]
  · have : NumberField E := numberField_of_finiteDimensional E
    have hEgal := isGalois_congr_rat (b := DivisionRing.toRatAlgebra)
      (IsAbelianGalois.tower_bot ℚ E K).toIsGalois
    let 𝔮 : Ideal (𝓞 E) := Q.under (𝓞 E)
    refine isUnramifiedIn_of_ramificationIdx_eq_one E q 𝔮 ?_
    have ht := Ideal.ramificationIdx_tower (R := ℤ) 𝔮 Q
    have hK : Q.ramificationIdx ℤ = Nat.card I := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[ℚ] K) (Ideal.span {(q:ℤ)}) Q,
        Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(q:ℤ)}) Q (K ≃ₐ[ℚ] K)]
    have hE : Q.ramificationIdx (𝓞 E) = Nat.card I := by
      have : IsGaloisGroup I E K := IsGaloisGroup.subgroup (K ≃ₐ[ℚ] K) ℚ K I
      have : IsGaloisGroup I (𝓞 E) (𝓞 K) := IsGaloisGroup.of_isFractionRing I (𝓞 E) (𝓞 K) E K
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮 Q I,
        ← Ideal.card_inertia_eq_ramificationIdxIn (G := I) 𝔮 Q]
      have htop : Q.inertia I = ⊤ := by
        ext σ
        simp only [Subgroup.mem_top, iff_true]
        exact fun x => σ.2 x
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hK, hE] at ht
    have hpos : Nat.card I ≠ 0 := Nat.card_pos.ne'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) (by rw [one_mul]; exact ht.symm)

theorem exists_inertiaField' (K : Type*) [Field K] [inst : Algebra ℚ K] [FiniteDimensional ℚ K]
    [IsAbelianGalois ℚ K] (q : ℕ) (hq : q.Prime) :
    ∃ E : IntermediateField ℚ K, NumberField E ∧
      Module.finrank ℚ E * (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) =
        Module.finrank ℚ K ∧
      Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(q : ℤ)}) := by
  have : CharZero K := algebraRat.charZero K
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have : NumberField K := ⟨⟩
  obtain ⟨E, h1, h2⟩ := exists_inertiaField K q hq
  exact ⟨E, numberField_of_finiteDimensional E, h1, h2⟩

theorem isUnramifiedIn_of_algHom (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] (f : K →ₐ[ℚ] L) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h : Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(ℓ : ℤ)})) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)}) := by
  let := f.toRingHom.toAlgebra
  have hℓ' := Nat.prime_iff_prime_int.mp hℓ
  rw [← not_dvd_discr_iff_isUnramifiedIn L (𝓞 L) hℓ'] at h
  rw [← not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) hℓ']
  exact fun hd => h (hd.trans (discr_dvd_discr K L))

theorem numberField_of_ringEquiv {A B : Type*} [Field A] [Field B] [NumberField A]
    (f : A ≃+* B) : NumberField B :=
  have : CharZero B := charZero_of_injective_ringHom f.toRingHom.injective
  { to_finiteDimensional := f.toRatAlgEquiv.toLinearEquiv.finiteDimensional }

theorem finrank_eq_of_ringEquiv {A B : Type*} [Field A] [Field B] [CharZero A] [CharZero B]
    (f : A ≃+* B) : Module.finrank ℚ A = Module.finrank ℚ B :=
  f.toRatAlgEquiv.toLinearEquiv.finrank_eq

end KWTameD

theorem NumberField.exists_le_isUnramifiedIn_finrank_mul_ramificationIdxIn
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω] (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M]
    [IsAbelianGalois ℚ M] (q : ℕ) (hq : q.Prime) :
    ∃ E' : IntermediateField ℚ Ω, E' ≤ M ∧ FiniteDimensional ℚ E' ∧ IsAbelianGalois ℚ E' ∧
      Module.finrank ℚ E' * (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 M) =
        Module.finrank ℚ M ∧
      Algebra.IsUnramifiedIn (𝓞 E') (Ideal.span {(q : ℤ)}) := by
  have hMab : @IsAbelianGalois ℚ M _ _ (IntermediateField.algebra' M) :=
    KWTameD.isAbelianGalois_congr_rat ‹_›
  obtain ⟨E, hEnf, hdeg, hunr⟩ := @KWTameD.exists_inertiaField' M _
    (IntermediateField.algebra' M) _ hMab q hq
  have hE'M : IntermediateField.lift E ≤ M := IntermediateField.lift_le E
  let φ : E ≃+* IntermediateField.lift E := (IntermediateField.liftAlgEquiv E : _)
  let ψ := φ.toRatAlgEquiv
  have hnf : NumberField (IntermediateField.lift E) := KWTameD.numberField_of_ringEquiv φ
  have hfin : FiniteDimensional ℚ (IntermediateField.lift E) := by
    convert hnf.to_finiteDimensional
    exact Subsingleton.elim _ _
  have hfr : Module.finrank ℚ (IntermediateField.lift E) = Module.finrank ℚ E := by
    convert (KWTameD.finrank_eq_of_ringEquiv φ).symm using 2 <;>
      exact Subsingleton.elim _ _
  refine ⟨IntermediateField.lift E, hE'M, hfin, ?_, ?_, ?_⟩
  · exact IsAbelianGalois.of_algHom
      (IntermediateField.inclusion hE'M : IntermediateField.lift E →+* M).toRatAlgHom
  · rw [hfr]
    exact hdeg
  · exact KWTameD.isUnramifiedIn_of_algHom _ E ψ.symm.toAlgHom q hq hunr

namespace KWTameE1

theorem span_isPrime (q : ℕ) (hq : q.Prime) : (Ideal.span {(q : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)

/-- A finite-dimensional intermediate field of `Ω / ℚ` is a number field. -/
theorem numberField_of_finiteDimensional {Ω : Type*} [Field Ω]
    [Algebra ℚ Ω] (E : IntermediateField ℚ Ω) [h : FiniteDimensional ℚ E] : NumberField E :=
  { to_finiteDimensional := by
      convert h
      exact Subsingleton.elim _ _ }

/-- E1 for number fields given as types, with an algebra `K → L`. -/
theorem dvd_types (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois ℚ K] [IsGalois ℚ L] (q : ℕ) (hq : q.Prime) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) ∣
      (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 L) := by
  have := span_isPrime q hq
  obtain ⟨⟨P, hP1, hP2⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 L)))
  let 𝔭 : Ideal (𝓞 K) := P.under (𝓞 K)
  have : 𝔭.IsPrime := Ideal.IsPrime.under (𝓞 K) P
  have : P.LiesOver 𝔭 := ⟨rfl⟩
  have : 𝔭.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.tower_bot P 𝔭 _
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ 𝔭 (K ≃ₐ[ℚ] K),
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[ℚ] L),
    Ideal.ramificationIdx_tower 𝔭 P]
  exact Dvd.intro _ rfl

end KWTameE1

theorem NumberField.ramificationIdxIn_dvd_of_le {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (K L : IntermediateField ℚ Ω) [FiniteDimensional ℚ K] [FiniteDimensional ℚ L]
    [IsGalois ℚ K] [IsGalois ℚ L] (h : K ≤ L) (q : ℕ) (hq : q.Prime) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) ∣
      (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 L) := by
  have := KWTameE1.numberField_of_finiteDimensional K
  have := KWTameE1.numberField_of_finiteDimensional L
  let : Algebra K L := (IntermediateField.inclusion h : K →+* L).toAlgebra
  exact KWTameE1.dvd_types K L q hq

namespace KWTameE2

theorem span_isPrime (q : ℕ) (hq : q.Prime) : (Ideal.span {(q : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)

/-- A finite-dimensional intermediate field of `Ω / ℚ` is a number field. -/
theorem numberField_of_finiteDimensional {Ω : Type*} [Field Ω]
    [Algebra ℚ Ω] (E : IntermediateField ℚ Ω) [h : FiniteDimensional ℚ E] : NumberField E :=
  { to_finiteDimensional := by
      convert h
      exact Subsingleton.elim _ _ }

/-- E2 for number fields given as types, with an algebra `K → L`. -/
theorem finrank_eq_one_types (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois ℚ L] (q : ℕ) (hq : q.Prime)
    (hL : (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 L) = Module.finrank ℚ L)
    (hK : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})) :
    Module.finrank ℚ K = 1 := by
  have := span_isPrime q hq
  obtain ⟨⟨P, hP1, hP2⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(q : ℤ)}).primesOver (𝓞 L)))
  let 𝔭 : Ideal (𝓞 K) := P.under (𝓞 K)
  have : 𝔭.IsPrime := Ideal.IsPrime.under (𝓞 K) P
  have : P.LiesOver 𝔭 := ⟨rfl⟩
  have : 𝔭.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.tower_bot P 𝔭 _
  have h1 : 𝔭.ramificationIdx ℤ = 1 := by
    have := hK 𝔭 inferInstance inferInstance
    exact Ideal.ramificationIdx_eq_one 𝔭 ℤ
  have h2 : P.ramificationIdx (𝓞 K) ≤ Module.finrank K L := by
    rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
    let : Fintype (𝔭.primesOver (𝓞 L)) := (Algebra.QuasiFinite.finite_primesOver 𝔭).fintype
    rw [← Ideal.sum_ramification_inertia_eq_finrank 𝔭 (𝓞 L)]
    have hmem : (⟨P, inferInstance, inferInstance⟩ : 𝔭.primesOver (𝓞 L)) ∈ Finset.univ :=
      Finset.mem_univ _
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
    exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos P (𝓞 K))
  have h3 : Module.finrank ℚ L ≤ Module.finrank K L := by
    rw [← hL, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[ℚ] L),
      Ideal.ramificationIdx_tower 𝔭 P, h1, one_mul]
    exact h2
  have h4 := Module.finrank_mul_finrank ℚ K L
  have h5 : 0 < Module.finrank K L := Module.finrank_pos
  have h6 : 0 < Module.finrank ℚ K := Module.finrank_pos
  nlinarith

end KWTameE2

theorem NumberField.eq_bot_of_le_of_isUnramifiedIn {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (K L : IntermediateField ℚ Ω) [FiniteDimensional ℚ L] [IsGalois ℚ L] (h : K ≤ L)
    (q : ℕ) (hq : q.Prime)
    (hL : (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 L) = Module.finrank ℚ L)
    (hK : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})) :
    K = ⊥ := by
  have := KWTameE2.numberField_of_finiteDimensional L
  have : NumberField K := by
    let f : K →ₐ[ℚ] L := (↑(IntermediateField.inclusion h) : K →+* L).toRatAlgHom
    let : Module ℚ K := Algebra.toModule
    let : Module ℚ L := Algebra.toModule
    exact { to_finiteDimensional := FiniteDimensional.of_injective f.toLinearMap f.injective }
  let : Algebra K L := (IntermediateField.inclusion h : K →+* L).toAlgebra
  have hL' : (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 L) =
      @Module.finrank ℚ L _ _ Algebra.toModule := by
    convert hL using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have key := KWTameE2.finrank_eq_one_types K L q hq hL' hK
  rw [← IntermediateField.finrank_eq_one_iff]
  convert key using 2 <;> first | rfl | exact Subsingleton.elim _ _

namespace KWTameF

open IntermediateField

/-- A `K`-automorphism of `E₁ ⊔ E₂` that fixes the points of `E₁` and of `E₂` is the identity. -/
theorem algEquiv_eq_one_of_fix {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (E₁ E₂ : IntermediateField K Ω) (σ : ↥(E₁ ⊔ E₂) ≃ₐ[K] ↥(E₁ ⊔ E₂))
    (h₁ : ∀ (x : Ω) (hx : x ∈ E₁), σ ⟨x, le_sup_left (b := E₂) hx⟩ = ⟨x, le_sup_left (b := E₂) hx⟩)
    (h₂ : ∀ (x : Ω) (hx : x ∈ E₂), σ ⟨x, le_sup_right (a := E₁) hx⟩ =
      ⟨x, le_sup_right (a := E₁) hx⟩) :
    σ = 1 := by
  have key : σ.toAlgHom = (AlgHom.id K ↥(E₁ ⊔ E₂)) := by
    refine algHom_ext_of_eq_adjoin K (sup_def E₁ E₂) ?_
    intro x hx
    rcases hx with hx | hx
    · exact h₁ x hx
    · exact h₂ x hx
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun key x)

end KWTameF

theorem IntermediateField.exists_injective_algEquiv_sup_prod {K Ω : Type*} [Field K] [Field Ω]
    [Algebra K Ω] (E₁ E₂ : IntermediateField K Ω) [IsGalois K E₁] [IsGalois K E₂] :
    ∃ f : (↥(E₁ ⊔ E₂) ≃ₐ[K] ↥(E₁ ⊔ E₂)) →* (E₁ ≃ₐ[K] E₁) × (E₂ ≃ₐ[K] E₂),
      Function.Injective f := by
  let a₁ : Algebra E₁ ↥(E₁ ⊔ E₂) :=
    (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).toRingHom.toAlgebra
  let a₂ : Algebra E₂ ↥(E₁ ⊔ E₂) :=
    (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)).toRingHom.toAlgebra
  have : IsScalarTower K E₁ ↥(E₁ ⊔ E₂) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K E₂ ↥(E₁ ⊔ E₂) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨(AlgEquiv.restrictNormalHom E₁).prod (AlgEquiv.restrictNormalHom E₂), ?_⟩
  rw [injective_iff_map_eq_one]
  intro σ hσ
  rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
  obtain ⟨hσ₁, hσ₂⟩ := hσ
  apply KWTameF.algEquiv_eq_one_of_fix E₁ E₂ σ
  · intro x hx
    have := AlgEquiv.restrictNormal_commutes σ E₁ ⟨x, hx⟩
    change algebraMap E₁ _ (AlgEquiv.restrictNormalHom E₁ σ ⟨x, hx⟩) = _ at this
    rw [hσ₁] at this
    exact this.symm
  · intro x hx
    have := AlgEquiv.restrictNormal_commutes σ E₂ ⟨x, hx⟩
    change algebraMap E₂ _ (AlgEquiv.restrictNormalHom E₂ σ ⟨x, hx⟩) = _ at this
    rw [hσ₂] at this
    exact this.symm

/-- The compositum of two abelian subextensions is abelian. Proved from (F). -/
theorem IntermediateField.isAbelianGalois_sup {K Ω : Type*} [Field K] [Field Ω]
    [Algebra K Ω] (E₁ E₂ : IntermediateField K Ω) [IsAbelianGalois K E₁]
    [IsAbelianGalois K E₂] : IsAbelianGalois K ↥(E₁ ⊔ E₂) := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_injective_algEquiv_sup_prod E₁ E₂
  exact
    { toIsMulCommutative := ⟨⟨fun x y => hφ (by
        rw [map_mul, map_mul]
        exact Prod.ext (IsMulCommutative.is_comm.comm _ _)
          (IsMulCommutative.is_comm.comm _ _))⟩⟩ }

/-- The degree of a compositum of two Galois subextensions divides the product of the
degrees. Proved from (F). -/
theorem IntermediateField.finrank_sup_dvd_mul {K Ω : Type*} [Field K] [Field Ω]
    [Algebra K Ω] (E₁ E₂ : IntermediateField K Ω) [FiniteDimensional K E₁]
    [FiniteDimensional K E₂] [IsGalois K E₁] [IsGalois K E₂] :
    Module.finrank K ↥(E₁ ⊔ E₂) ∣ Module.finrank K E₁ * Module.finrank K E₂ := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_injective_algEquiv_sup_prod E₁ E₂
  have := Subgroup.card_dvd_of_injective φ hφ
  rwa [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank] at this

/-- `isAbelianGalois_sup` over `ℚ`, with the elaborated `ℚ`-structures. Proved. -/
theorem IntermediateField.isAbelianGalois_sup_rat {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (E₁ E₂ : IntermediateField ℚ Ω) [IsAbelianGalois ℚ E₁] [IsAbelianGalois ℚ E₂] :
    IsAbelianGalois ℚ ↥(E₁ ⊔ E₂) :=
  isAbelianGalois_congr_rat (@IntermediateField.isAbelianGalois_sup ℚ Ω _ _ _ E₁ E₂
    (isAbelianGalois_congr_rat ‹_›) (isAbelianGalois_congr_rat ‹_›))

/-- `finrank_sup_dvd_mul` over `ℚ`, with the elaborated `ℚ`-structures. Proved. -/
theorem IntermediateField.finrank_sup_dvd_mul_rat {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (E₁ E₂ : IntermediateField ℚ Ω) [FiniteDimensional ℚ E₁] [FiniteDimensional ℚ E₂]
    [IsGalois ℚ E₁] [IsGalois ℚ E₂] :
    Module.finrank ℚ ↥(E₁ ⊔ E₂) ∣ Module.finrank ℚ E₁ * Module.finrank ℚ E₂ :=
  @IntermediateField.finrank_sup_dvd_mul ℚ Ω _ _ _ E₁ E₂ _ _
    (isGalois_congr_rat ‹_›) (isGalois_congr_rat ‹_›)

/-! ## Assembly -/

theorem solution {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] [IsAbelianGalois ℚ E]
    (k : ℕ) (hE : Module.finrank ℚ E = p ^ k) :
    ∃ E' F : IntermediateField ℚ Ω, FiniteDimensional ℚ E' ∧ IsAbelianGalois ℚ E' ∧
      (∃ m : ℕ, Module.finrank ℚ E' = p ^ m) ∧
      Algebra.IsUnramifiedIn (𝓞 E') (Ideal.span {(q : ℤ)}) ∧
      (∀ ℓ : ℕ, ℓ.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(ℓ : ℤ)}) →
        Algebra.IsUnramifiedIn (𝓞 E') (Ideal.span {(ℓ : ℤ)})) ∧
      Nonempty (F →ₐ[ℚ] CyclotomicField q ℚ) ∧ E ≤ E' ⊔ F := by
  have hq1 : q - 1 ≠ 0 := by have := hq.two_le; omega
  -- `p ^ a` is the exact power of `p` that divides `q - 1`.
  obtain ⟨a, ha⟩ : ∃ a, a = (q - 1).factorization p := ⟨_, rfl⟩
  have hpa : p ^ a ∣ q - 1 := ha ▸ Nat.ordProj_dvd (q - 1) p
  -- The field `F` of degree `p ^ a` inside `ℚ(ζ_q)`.
  obtain ⟨F, hFfin, hFab, hFdeg, hFhom, hFram, hFunr⟩ :=
    IsCyclotomicExtension.Rat.exists_intermediateField_finrank_eq_of_dvd_sub_one
      (Ω := Ω) q (p ^ a) hq hpa
  have := hFfin
  have := hFab
  -- The compositum `E ⊔ F` is abelian of `p`-power degree.
  have : IsAbelianGalois ℚ ↥(E ⊔ F) := IntermediateField.isAbelianGalois_sup_rat E F
  have hMdvd : Module.finrank ℚ ↥(E ⊔ F) ∣ p ^ (k + a) := by
    have := IntermediateField.finrank_sup_dvd_mul_rat E F
    rwa [hE, hFdeg, ← pow_add] at this
  -- The ramification index `e` of `q` in `E ⊔ F` is `p ^ a`.
  have h1 := NumberField.ramificationIdxIn_dvd_finrank_of_intermediateField (E ⊔ F) q hq
  obtain ⟨j, -, hej⟩ := (Nat.dvd_prime_pow hp).1 (h1.trans hMdvd)
  have hnq : ¬ q ∣ (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 ↥(E ⊔ F)) := by
    rw [hej]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))
  have h2 := NumberField.ramificationIdxIn_dvd_sub_one_of_intermediateField (E ⊔ F) q hq hnq
  have hja : j ≤ a := by
    rw [hej] at h2
    rw [ha]
    exact (hp.pow_dvd_iff_le_factorization hq1).1 h2
  have h3 : p ^ a ∣ (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 ↥(E ⊔ F)) := by
    have := NumberField.ramificationIdxIn_dvd_of_le F (E ⊔ F) le_sup_right q hq
    rwa [hFram] at this
  have heM : (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 ↥(E ⊔ F)) = p ^ a :=
    Nat.dvd_antisymm (hej ▸ Nat.pow_dvd_pow p hja) h3
  -- The inertia field `E'`.
  obtain ⟨E', hE'M, hE'fin, hE'ab, hE'deg, hE'q⟩ :=
    NumberField.exists_le_isUnramifiedIn_finrank_mul_ramificationIdxIn (E ⊔ F) q hq
  have := hE'fin
  have := hE'ab
  rw [heM] at hE'deg
  have hdegE' : ∃ m : ℕ, Module.finrank ℚ E' = p ^ m := by
    have : Module.finrank ℚ E' ∣ p ^ (k + a) := (Dvd.intro _ hE'deg).trans hMdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 this
    exact ⟨m, hm⟩
  -- `E'` and `F` meet in `ℚ`.
  have hinf : F ⊓ E' = ⊥ := by
    apply NumberField.eq_bot_of_le_of_isUnramifiedIn (F ⊓ E') F inf_le_left q hq
    · rw [hFram, hFdeg]
    · exact NumberField.isUnramifiedIn_of_le (F ⊓ E') E' inf_le_right q hq hE'q
  have hlin : F.LinearDisjoint E' :=
    @IntermediateField.LinearDisjoint.of_inf_eq_bot _ _ _ _ _ F E'
      (isGalois_congr_rat hFab.toIsGalois) _ _ hinf
  -- Hence `E' ⊔ F = E ⊔ F`.
  have hsup : E' ⊔ F = E ⊔ F := by
    apply IntermediateField.eq_of_le_of_finrank_eq (sup_le hE'M le_sup_right)
    rw [sup_comm E' F, hlin.finrank_sup, hFdeg, ← hE'deg, mul_comm]
  refine ⟨E', F, inferInstance, inferInstance, hdegE', hE'q, ?_, hFhom, ?_⟩
  · intro ℓ hℓ hEℓ
    by_cases hℓq : ℓ = q
    · subst hℓq
      exact hE'q
    · exact NumberField.isUnramifiedIn_of_le E' (E ⊔ F) hE'M ℓ hℓ
        (NumberField.isUnramifiedIn_sup E F ℓ hℓ hEℓ (hFunr ℓ hℓ hℓq))
  · rw [hsup]
    exact le_sup_left
