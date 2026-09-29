-- Prove2me | solution 1 for Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/fb0d0add-1707-549d-bae9-43fc73bcf273

import Mathlib
import Theorems.Thm_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one

set_option autoImplicit false

universe u v

namespace P2mBertiniHyp

open Ideal Polynomial

private lemma exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem height_eq_of_isMaximal_mvPolynomial (k : Type u) [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have hle : (M.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) k) :=
      Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [ringKrullDim_mvPolynomial_fin] at hle
    have : M.height ≤ 0 := by exact_mod_cast hle
    simpa using this
  | succ n ih =>
    intro M hM
    haveI := hM
    let e : MvPolynomial (Fin (n + 1)) k ≃+* (MvPolynomial (Fin n) k)[X] :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (MvPolynomial (Fin n) k)[X] := M.map e
    haveI hM' : M'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p : Ideal (MvPolynomial (Fin n) k) := M'.under (MvPolynomial (Fin n) k)
    haveI : M'.LiesOver p := ⟨rfl⟩
    have hp : p.IsMaximal := by
      have : p = M'.comap (C : MvPolynomial (Fin n) k →+* (MvPolynomial (Fin n) k)[X]) := by
        simp only [p, Ideal.under_def, Polynomial.algebraMap_eq]
      rw [this]
      exact Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have h1 : M'.height = p.height + 1 := Polynomial.height_eq_height_add_one p M'
    have h2 : p.height = n := ih p hp
    have h3 : M'.height = M.height := RingEquiv.height_map e M
    rw [← h3, h1, h2]
    norm_cast

theorem height_eq_ringKrullDim_of_isMaximal (k : Type u) {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have hint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hdim : ringKrullDim A = s := by
    rw [← ringKrullDim_mvPolynomial_fin k s]
    exact (ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) hinj).symm
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) ?_
  let m' : Ideal (MvPolynomial (Fin s) k) := m.under (MvPolynomial (Fin s) k)
  have h1 : m'.height = s := height_eq_of_isMaximal_mvPolynomial k s m' inferInstance
  have h2 : m.height = m'.height + _ := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m' m
  have h3 : (s : ℕ∞) ≤ m.height := by
    rw [h2, h1]; exact le_self_add
  rw [hdim]
  exact_mod_cast h3

theorem ringKrullDim_quotient_radical {A : Type v} [CommRing A] (I : Ideal A) :
    ringKrullDim (A ⧸ I.radical) = ringKrullDim (A ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

theorem ringKrullDim_quotient_radical_span_add_one (k : Type u) {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal]
    {f : A} (hf : f ≠ 0) (hfm : f ∈ m) :
    ringKrullDim (A ⧸ (Ideal.span {f}).radical) + 1 = ringKrullDim A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [ringKrullDim_quotient_radical]
  exact Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf) (height_eq_ringKrullDim_of_isMaximal k m) hfm

theorem exists_ringKrullDim_eq_natCast (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] : ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  refine ⟨s, ?_⟩
  rw [← ringKrullDim_mvPolynomial_fin k s]
  exact (ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) hinj).symm

theorem exists_isMaximal_ne (k : Type u) {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A) (m : Ideal A) [hm : m.IsMaximal] :
    ∃ m' : Ideal A, m'.IsMaximal ∧ m' ≠ m := by
  by_contra! h
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› Ideal.isRadical_bot_of_noZeroDivisors
  have hle : m ≤ (⊥ : Ideal A).jacobson :=
    le_sInf fun J hJ => le_of_eq (h J hJ.2).symm
  rw [hjac, le_bot_iff] at hle
  subst hle
  have hF : IsField A := (Ring.isField_iff_maximal_bot).mpr hm
  have h0 := ringKrullDim_eq_zero_of_isField hF
  rw [h0] at hA
  exact absurd hA (by decide)

section Main

variable (k : Type u) [Field k] [IsAlgClosed k]

theorem step {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : 2 ≤ ringKrullDim A) (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] (hne : m₀ ≠ m₁) :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  obtain ⟨f, hf₀, hf₁, hf, hprime⟩ :=
    Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime k hA m₀ m₁ hne
  refine ⟨(Ideal.span {f}).radical, hprime, ?_, ?_,
    ringKrullDim_quotient_radical_span_add_one k m₀ hf hf₀⟩
  · exact (Ideal.IsPrime.radical_le_iff inferInstance).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hf₀)
  · exact (Ideal.IsPrime.radical_le_iff inferInstance).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hf₁)

theorem comap_mk_le {A : Type v} [CommRing A] {P' n : Ideal A} (h : P' ≤ n)
    {Q : Ideal (A ⧸ P')} (hQ : Q ≤ n.map (Ideal.Quotient.mk P')) :
    Q.comap (Ideal.Quotient.mk P') ≤ n := by
  calc Q.comap (Ideal.Quotient.mk P')
      ≤ (n.map (Ideal.Quotient.mk P')).comap (Ideal.Quotient.mk P') := Ideal.comap_mono hQ
    _ = n ⊔ Ideal.comap (Ideal.Quotient.mk P') ⊥ :=
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _
    _ = n := by
        refine sup_eq_left.mpr ?_
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        exact h

theorem ringKrullDim_quotient_comap_mk {A : Type v} [CommRing A] (P' : Ideal A)
    (Q : Ideal (A ⧸ P')) :
    ringKrullDim (A ⧸ Q.comap (Ideal.Quotient.mk P')) = ringKrullDim ((A ⧸ P') ⧸ Q) := by
  let g : A →+* (A ⧸ P') ⧸ Q := (Ideal.Quotient.mk Q).comp (Ideal.Quotient.mk P')
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = Q.comap (Ideal.Quotient.mk P') := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hg)

theorem main : ∀ (n : ℕ) {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A],
    ringKrullDim A = n → 1 ≤ n → ∀ (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal],
      ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ hdim hn m₀ m₁ _ _
  by_cases h1 : n = 1
  · subst h1
    refine ⟨⊥, Ideal.isPrime_bot, bot_le, bot_le, ?_⟩
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    exact hdim
  have hn2 : 2 ≤ n := by omega
  have hA2 : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by rw [hdim]; exact_mod_cast hn2
  have hA1 : (1 : WithBot ℕ∞) ≤ ringKrullDim A := le_trans (by decide) hA2

  have key : ∀ (n₀ n₁ : Ideal A) [n₀.IsMaximal] [n₁.IsMaximal], n₀ ≠ n₁ →
      ∃ P : Ideal A, P.IsPrime ∧ P ≤ n₀ ∧ P ≤ n₁ ∧ ringKrullDim (A ⧸ P) = 1 := by
    intro n₀ n₁ _ _ hne
    obtain ⟨P', hP', h0, h1', hdimP'⟩ := step k hA2 n₀ n₁ hne
    haveI := hP'

    have hq : ringKrullDim (A ⧸ P') = (n - 1 : ℕ) := by
      obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast k (A ⧸ P')
      rw [hdim, hd] at hdimP'
      have hdn : d + 1 = n := by exact_mod_cast hdimP'
      rw [hd]
      have : d = n - 1 := by omega
      rw [this]
    haveI hM0 : (n₀.map (Ideal.Quotient.mk P')).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact h0)
    haveI hM1 : (n₁.map (Ideal.Quotient.mk P')).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact h1')
    obtain ⟨Q, hQ, hQ0, hQ1, hQdim⟩ := ih (n - 1) (by omega) hq (by omega)
      (n₀.map (Ideal.Quotient.mk P')) (n₁.map (Ideal.Quotient.mk P'))
    haveI := hQ
    refine ⟨Q.comap (Ideal.Quotient.mk P'), Ideal.comap_isPrime _ Q, comap_mk_le h0 hQ0,
      comap_mk_le h1' hQ1, ?_⟩
    rw [ringKrullDim_quotient_comap_mk, hQdim]
  by_cases heq : m₀ = m₁
  · subst heq
    obtain ⟨m₂, hm₂, hne⟩ := exists_isMaximal_ne k hA1 m₀
    haveI := hm₂
    obtain ⟨P, hP, hP0, -, hd⟩ := key m₀ m₂ hne.symm
    exact ⟨P, hP, hP0, hP0, hd⟩
  · exact key m₀ m₁ heq

end Main

end P2mBertiniHyp

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 := by
  obtain ⟨n, hn⟩ := P2mBertiniHyp.exists_ringKrullDim_eq_natCast k A
  have h1 : 1 ≤ n := by
    rw [hn] at hA
    exact_mod_cast hA
  exact P2mBertiniHyp.main k n hn h1 m₀ m₁

end S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
end P2MW
export P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one (solution)
