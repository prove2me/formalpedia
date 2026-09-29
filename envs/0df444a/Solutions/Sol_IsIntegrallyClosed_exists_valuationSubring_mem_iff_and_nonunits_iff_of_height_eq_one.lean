-- Prove2me | solution 1 for IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8dd86e19-4b61-5cf8-ae05-b92fc7e76d53

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing

theorem solution
    {C K : Type*} [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Field K] [Algebra C K] [IsFractionRing C K]
    (P : Ideal C) [P.IsPrime] (hP : P.height = 1) :
    ∃ V : ValuationSubring K,
      (∀ x : K, x ∈ V ↔ ∃ c s : C, s ∉ P ∧ x * algebraMap C K s = algebraMap C K c) ∧
      (∀ c : C, algebraMap C K c ∈ V) ∧
      (∀ c : C, algebraMap C K c ∈ V.nonunits ↔ c ∈ P) ∧
      (∀ ϖ : C, ϖ ∈ P →
        ((∀ f : K, f ∈ V.nonunits → ∃ g : K, g ∈ V ∧ f = algebraMap C K ϖ * g) ↔
          IsLocalRing.maximalIdeal (Localization.AtPrime P) =
            Ideal.span {algebraMap C (Localization.AtPrime P) ϖ})) ∧
      ∃ ι : IsLocalRing.ResidueField ↥V ≃+* P.ResidueField,
        ∀ (c : C) (hc : algebraMap C K c ∈ V),
          ι (IsLocalRing.residue ↥V ⟨algebraMap C K c, hc⟩) = algebraMap C P.ResidueField c := by
  classical
  have hinjK : Function.Injective (algebraMap C K) := IsFractionRing.injective C K
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hP
    exact zero_ne_one hP

  let D : Subalgebra C K := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hmemD : ∀ x : K, x ∈ D ↔ ∃ (a s : C) (_ : s ∈ P.primeCompl), x = algebraMap C K a * (algebraMap C K s)⁻¹ :=
    fun _ => Iff.rfl
  haveI : IsLocalization.AtPrime ↥D P := Localization.subalgebra.isLocalization_ofField K _ _
  haveI hloc : IsLocalRing ↥D := IsLocalization.AtPrime.isLocalRing ↥D P
  haveI : IsNoetherianRing ↥D := IsLocalization.isNoetherianRing P.primeCompl ↥D inferInstance
  haveI : IsIntegrallyClosed ↥D := isIntegrallyClosed_of_isLocalization ↥D P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hinjD : Function.Injective (algebraMap C ↥D) := IsLocalization.injective ↥D P.primeCompl_le_nonZeroDivisors

  have hmaxD : Ideal.map (algebraMap C ↥D) P = maximalIdeal ↥D := IsLocalization.AtPrime.map_eq_maximalIdeal P ↥D
  have hprimes : ∀ Q : Ideal ↥D, Q.IsPrime → Q ≠ ⊥ → Q = maximalIdeal ↥D := by
    intro Q hQ hQ0
    let q : Ideal C := Q.comap (algebraMap C ↥D)
    haveI : q.IsPrime := Ideal.comap_isPrime _ Q
    have hqP : q ≤ P := by
      intro c hc
      have : algebraMap C ↥D c ∈ maximalIdeal ↥D := IsLocalRing.le_maximalIdeal hQ.ne_top hc
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff ↥D P c).mp this
    have hQq : Ideal.map (algebraMap C ↥D) q = Q := IsLocalization.map_comap P.primeCompl ↥D Q
    by_cases hqeq : q = P
    · rw [← hQq, hqeq, hmaxD]
    · exfalso
      have hqlt : q < P := lt_of_le_of_ne hqP hqeq
      have hqbot : q = ⊥ := by
        by_contra hq0
        have hbotlt : (⊥ : Ideal C) < q := lt_of_le_of_ne bot_le (Ne.symm hq0)
        have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
        have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hqlt
        rw [hP] at h2
        rw [Ideal.height_bot, zero_add] at h1
        have h3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h1 1).trans (by simpa [add_comm] using h2)
        exact absurd h3 (by decide)
      apply hQ0
      rw [← hQq, hqbot, Ideal.map_bot]

  obtain ⟨p0, hp0P, hp00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hnotfield : ¬ IsField ↥D := by
    intro hF
    have hm : maximalIdeal ↥D = ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    have : algebraMap C ↥D p0 ∈ maximalIdeal ↥D := (IsLocalization.AtPrime.to_map_mem_maximal_iff ↥D P p0).mpr hp0P
    rw [hm, Ideal.mem_bot] at this
    exact hp00 (hinjD (this.trans (map_zero _).symm))
  have h4 : IsIntegrallyClosed ↥D ∧ ∃! Q : Ideal ↥D, Q ≠ ⊥ ∧ Q.IsPrime := by
    refine ⟨inferInstance, maximalIdeal ↥D, ⟨?_, inferInstance⟩, ?_⟩
    · exact IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnotfield
    · rintro Q ⟨hQ0, hQ⟩
      exact hprimes Q hQ hQ0
  have hVR : ValuationRing ↥D := ((IsDiscreteValuationRing.TFAE ↥D hnotfield).out 1 3).mpr h4

  let V : ValuationSubring K :=
    { D.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger ↥D x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact Or.inl (hy ▸ y.2)
        · exact Or.inr (hy ▸ y.2) }
  have hVD : ∀ x : K, x ∈ V ↔ x ∈ D := fun _ => Iff.rfl
  have hCV : ∀ c : C, algebraMap C K c ∈ V := fun c => (hVD _).mpr (D.algebraMap_mem c)

  have hnu : ∀ (x : K) (hx : x ∈ V), x ∈ V.nonunits ↔ (⟨x, hx⟩ : ↥D) ∈ maximalIdeal ↥D := by
    intro x hx
    rw [ValuationSubring.mem_nonunits_iff]
    exact (ValuationSubring.valuation_lt_one_iff V ⟨x, hx⟩).symm
  have hcen : ∀ c : C, algebraMap C K c ∈ V.nonunits ↔ c ∈ P := by
    intro c
    rw [hnu _ (hCV c)]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff ↥D P c
  refine ⟨V, ?_, hCV, hcen, ?_, ?_⟩
  ·
    intro x
    rw [hVD, hmemD]
    constructor
    · rintro ⟨a, s, hs, rfl⟩
      have hs0 : algebraMap C K s ≠ 0 := fun h0 => hs (by rw [hinjK (h0.trans (map_zero _).symm)]; exact P.zero_mem)
      exact ⟨a, s, hs, by rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]⟩
    · rintro ⟨c, s, hs, hcs⟩
      have hs0 : algebraMap C K s ≠ 0 := fun h0 => hs (by rw [hinjK (h0.trans (map_zero _).symm)]; exact P.zero_mem)
      exact ⟨c, s, hs, (eq_mul_inv_iff_mul_eq₀ hs0).mpr hcs⟩
  ·
    intro ϖ hϖP
    let e : ↥D ≃ₐ[C] Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl ↥D (Localization.AtPrime P)
    have heϖ : e (algebraMap C ↥D ϖ) = algebraMap C (Localization.AtPrime P) ϖ := e.commutes ϖ
    have hmaxL : Ideal.map (algebraMap C (Localization.AtPrime P)) P = maximalIdeal (Localization.AtPrime P) :=
      IsLocalization.AtPrime.map_eq_maximalIdeal P _

    have hemax : Ideal.map (e : ↥D →+* Localization.AtPrime P) (maximalIdeal ↥D) = maximalIdeal (Localization.AtPrime P) := by
      rw [← hmaxD, ← hmaxL, Ideal.map_map]
      congr 1
      exact RingHom.ext fun c => e.commutes c
    have hespan : Ideal.map (e : ↥D →+* Localization.AtPrime P) (Ideal.span {algebraMap C ↥D ϖ}) =
        Ideal.span {algebraMap C (Localization.AtPrime P) ϖ} := by
      rw [Ideal.map_span, Set.image_singleton]
      exact congrArg (fun z => Ideal.span {z}) heϖ
    constructor
    · intro hgen

      have hD : maximalIdeal ↥D = Ideal.span {algebraMap C ↥D ϖ} := by
        apply le_antisymm
        · intro y hy
          have hyV : (y : K) ∈ V.nonunits := (hnu y y.2).mpr hy
          obtain ⟨g, hg, hfg⟩ := hgen y hyV
          refine Ideal.mem_span_singleton'.mpr ⟨⟨g, hg⟩, Subtype.ext ?_⟩
          show g * ((algebraMap C ↥D ϖ : ↥D) : K) = (y : K)
          rw [mul_comm, hfg]; rfl
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact (IsLocalization.AtPrime.to_map_mem_maximal_iff ↥D P ϖ).mpr hϖP
      rw [← hemax, hD, hespan]
    · intro hL f hf
      have hD : maximalIdeal ↥D = Ideal.span {algebraMap C ↥D ϖ} := by
        have h := congrArg (Ideal.comap (e : ↥D →+* Localization.AtPrime P)) (hemax.trans (hL.trans hespan.symm))
        rwa [Ideal.comap_map_of_bijective (e : ↥D →+* Localization.AtPrime P) e.bijective,
          Ideal.comap_map_of_bijective (e : ↥D →+* Localization.AtPrime P) e.bijective] at h
      have hfV : f ∈ V := V.nonunits_subset hf
      have hfm : (⟨f, hfV⟩ : ↥D) ∈ maximalIdeal ↥D := (hnu f hfV).mp hf
      rw [hD] at hfm
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hfm
      refine ⟨(g : K), g.2, ?_⟩
      have := congrArg (fun z : ↥D => (z : K)) hg
      simp only [MulMemClass.coe_mul] at this
      rw [← this, mul_comm]
      rfl
  ·
    let e : ↥D ≃ₐ[C] Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl ↥D (Localization.AtPrime P)
    let eVD : ↥V ≃+* ↥D :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl }
    refine ⟨(IsLocalRing.ResidueField.mapEquiv eVD).trans (IsLocalRing.ResidueField.mapEquiv e.toRingEquiv), ?_⟩
    intro c hc
    rw [RingEquiv.trans_apply, IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
    show IsLocalRing.residue (Localization.AtPrime P) (e (algebraMap C ↥D c)) = algebraMap C P.ResidueField c
    rw [AlgEquiv.commutes]
    rfl

end S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
end P2MW
export P2MW.S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (solution)
