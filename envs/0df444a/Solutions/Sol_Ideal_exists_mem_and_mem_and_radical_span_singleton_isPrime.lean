-- Prove2me | solution 1 for Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ec76eebd-adf7-56ae-bc5b-a17907e135da

import Mathlib
import Theorems.Thm_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
import Theorems.Thm_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime

set_option autoImplicit false

universe u v

open MvPolynomial

namespace P2mIrredHyp

theorem sub_mem_span_of_algHom {R : Type*} [CommRing R] {σ : Type*}
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (p : MvPolynomial σ R) :
    p - φ p ∈ Ideal.span (Set.range fun i : σ => (X i - φ (X i) : MvPolynomial σ R)) := by
  set I := Ideal.span (Set.range fun i : σ => (X i - φ (X i) : MvPolynomial σ R))
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : φ (C a) = C a := by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rw [this, sub_self]; exact I.zero_mem
  | add p q hp hq =>
    have : p + q - φ (p + q) = (p - φ p) + (q - φ q) := by rw [map_add]; ring
    rw [this]; exact I.add_mem hp hq
  | mul_X p i hp =>
    have : p * X i - φ (p * X i) = (p - φ p) * X i + φ p * (X i - φ (X i)) := by
      rw [map_mul]; ring
    rw [this]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩))

theorem mem_span_X_sub_C_of_aeval_eq_zero {R : Type*} [CommRing R] {σ : Type*} (a : σ → R)
    {p : MvPolynomial σ R} (hp : MvPolynomial.aeval a p = 0) :
    p ∈ Ideal.span (Set.range fun i : σ => (X i - C (a i) : MvPolynomial σ R)) := by
  let φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := MvPolynomial.aeval fun i => C (a i)
  have hφX : ∀ i, φ (X i) = C (a i) := fun i => by simp [φ]
  have hφ : ∀ q : MvPolynomial σ R, φ q = C (MvPolynomial.aeval a q) := by
    intro q
    have h1 : φ = (IsScalarTower.toAlgHom R R (MvPolynomial σ R)).comp (MvPolynomial.aeval a) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [φ]
    rw [h1]; rfl
  have hmem := sub_mem_span_of_algHom φ p
  simp only [hφX] at hmem
  rwa [hφ p, hp, map_zero, sub_zero] at hmem

theorem exists_sub_algebraMap_mem (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] (t : A) :
    ∃ c : k, t - algebraMap k A c ∈ m := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (A ⧸ m) := inferInstance
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k (A ⧸ m)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ m)).2
    (Ideal.Quotient.mk m t)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, ← Ideal.Quotient.mkₐ_eq_mk k, AlgHom.commutes]

theorem mem_bot_of_isSeparable (k : Type u) [Field k] [IsAlgClosed k] {K : Type*} [Field K]
    [Algebra k K] (θ : K) (hθ : IsSeparable k θ) : θ ∈ (⊥ : IntermediateField k K) := by
  have hint : IsIntegral k θ := hθ.isIntegral
  have h1 : (minpoly k θ).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
  have h2 : θ ∈ (algebraMap k K).range := minpoly.mem_range_of_degree_eq_one k θ h1
  exact IntermediateField.mem_bot.mpr h2

theorem isSeparable_transport {R₁ R₂ L L' : Type*} [Field R₁] [Field R₂] [Field L] [Field L']
    [Algebra R₁ L] [Algebra R₂ L'] (e : R₁ ≃+* R₂) (σ : L →+* L')
    (he : ∀ r, algebraMap R₂ L' (e r) = σ (algebraMap R₁ L r)) {y : L}
    (h : IsSeparable R₁ y) : IsSeparable R₂ (σ y) := by
  have hp : (minpoly R₁ y).Separable := h
  have hmap : ((minpoly R₁ y).map e.toRingHom).Separable := hp.map
  have hroot : Polynomial.aeval (σ y) ((minpoly R₁ y).map e.toRingHom) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap R₂ L').comp e.toRingHom = σ.comp (algebraMap R₁ L) := by
      ext r; simp [he]
    rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  exact hmap.of_dvd (minpoly.dvd R₂ (σ y) hroot)

theorem fg_top_fractionRing (k : Type u) [Field k] (B : Type*) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    (⊤ : IntermediateField k (FractionRing B)).FG := by
  classical
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := k) (A := B)
  let ι : B →ₐ[k] FractionRing B := IsScalarTower.toAlgHom k B (FractionRing B)
  refine ⟨S.image ι, ?_⟩
  rw [eq_top_iff]
  intro z _
  have hB : ∀ b : B, ι b ∈ IntermediateField.adjoin k (↑(S.image ι) : Set (FractionRing B)) := by
    intro b
    have hb : b ∈ Algebra.adjoin k (S : Set B) := hS ▸ Algebra.mem_top
    have h1 : ι b ∈ (Algebra.adjoin k (S : Set B)).map ι := ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    have h2 : (ι '' (S : Set B)) = ↑(S.image ι) := by simp
    rw [h2] at h1
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  exact div_mem (hB p) (hB q)

theorem adjoin_algebra_adjoin (k : Type u) [Field k] {L : Type*} [Field L] [Algebra k L]
    (S : Set L) :
    IntermediateField.adjoin k (↑(Algebra.adjoin k S) : Set L) = IntermediateField.adjoin k S := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    exact IntermediateField.algebra_adjoin_le_adjoin k S
  · exact IntermediateField.adjoin.mono k _ _ Algebra.subset_adjoin

theorem transcendental_add_mul {S L : Type*} [CommRing S] [IsDomain S] [Field L] [Algebra S L]
    {v : L} (hv : Transcendental S v) (c d : S) (hd : algebraMap S L d ≠ 0) :
    Transcendental S (algebraMap S L c + v * algebraMap S L d) := by
  intro halg
  apply hv
  have h1 : IsAlgebraic S (v * algebraMap S L d) := by
    have := halg.sub (isAlgebraic_algebraMap c)
    simpa using this
  have h2 : IsAlgebraic S (algebraMap S L d * v) := by rwa [mul_comm] at h1
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hd) (isAlgebraic_algebraMap d) h2

theorem two_le_height_of_mem_of_mem (k : Type u) [Field k] {σ : Type*} [DecidableEq σ]
    {i j : σ} (hij : i ≠ j) (a b : k) (q : Ideal (MvPolynomial σ k)) [q.IsPrime]
    (hi : (X i - C a : MvPolynomial σ k) ∈ q) (hj : (X j - C b : MvPolynomial σ k) ∈ q) :
    (2 : ℕ∞) ≤ q.height := by

  let v₁ : σ → MvPolynomial σ k := fun l => if l = i then C a else X l
  let v₂ : σ → MvPolynomial σ k := fun l => if l = i then C a else if l = j then C b else X l
  let φ₁ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k := MvPolynomial.aeval v₁
  let φ₂ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k := MvPolynomial.aeval v₂
  have hφ₁X : ∀ l, φ₁ (X l) = v₁ l := fun l => by simp [φ₁]
  have hφ₂X : ∀ l, φ₂ (X l) = v₂ l := fun l => by simp [φ₂]
  let P₁ : Ideal (MvPolynomial σ k) := RingHom.ker φ₁.toRingHom
  let P₂ : Ideal (MvPolynomial σ k) := RingHom.ker φ₂.toRingHom
  haveI hP₁ : P₁.IsPrime := RingHom.ker_isPrime _
  haveI hP₂ : P₂.IsPrime := RingHom.ker_isPrime _

  have hcomp : φ₂.comp φ₁ = φ₂ := by
    apply MvPolynomial.algHom_ext
    intro l
    simp only [AlgHom.comp_apply, hφ₁X, v₁]
    split_ifs with h
    · subst h
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq, hφ₂X]
      simp [v₂]
    · rfl
  have h12 : P₁ ≤ P₂ := by
    intro p hp
    change φ₂ p = 0
    have hp' : φ₁ p = 0 := hp
    rw [← hcomp, AlgHom.comp_apply, hp', map_zero]

  have hne1 : (X i - C a : MvPolynomial σ k) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval fun _ => a + 1) h
    simp at this
  have hmem1 : (X i - C a : MvPolynomial σ k) ∈ P₁ := by
    change φ₁ (X i - C a) = 0
    rw [map_sub, hφ₁X]
    simp [v₁, φ₁]
  have hbot : (⊥ : Ideal (MvPolynomial σ k)) < P₁ :=
    bot_lt_iff_ne_bot.mpr fun h => hne1 (by simpa [h] using hmem1)

  have hmem2 : (X j - C b : MvPolynomial σ k) ∈ P₂ := by
    change φ₂ (X j - C b) = 0
    rw [map_sub, hφ₂X]
    simp [v₂, φ₂, hij.symm]
  have hnmem2 : (X j - C b : MvPolynomial σ k) ∉ P₁ := by
    intro h
    change φ₁ (X j - C b) = 0 at h
    rw [map_sub, hφ₁X] at h
    simp only [v₁, if_neg hij.symm] at h
    have hne : (X j - C b : MvPolynomial σ k) ≠ 0 := by
      intro h'
      have := congrArg (MvPolynomial.eval fun _ => b + 1) h'
      simp at this
    apply hne
    simpa [φ₁] using h
  have hlt : P₁ < P₂ := lt_of_le_of_ne h12 fun h => hnmem2 (h ▸ hmem2)

  have hP₂q : P₂ ≤ q := by
    intro p hp
    have hp' : φ₂ p = 0 := hp
    have hmem := sub_mem_span_of_algHom φ₂ p
    rw [hp', sub_zero] at hmem
    refine (Ideal.span_le.mpr ?_) hmem
    rintro _ ⟨l, rfl⟩
    simp only [hφ₂X, v₂]
    split_ifs with h1 h2
    · subst h1; exact hi
    · subst h2; exact hj
    · simp

  haveI : (⊥ : Ideal (MvPolynomial σ k)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (MvPolynomial σ k)).height + 1 ≤ P₁.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 : P₁.height + 1 ≤ P₂.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : P₂.height ≤ q.height := Ideal.height_mono hP₂q
  rw [Ideal.height_bot, zero_add] at h1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ P₁.height + 1 := by gcongr
    _ ≤ P₂.height := h2
    _ ≤ q.height := h3

theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
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

theorem exists_noether_two_le (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (hA : 2 ≤ ringKrullDim A) :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] A, Function.Injective g ∧ g.Finite ∧ 2 ≤ s := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  refine ⟨s, g, hinj, hfin, ?_⟩
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  have h1 : ringKrullDim A ≤ s := by
    rw [← ringKrullDim_mvPolynomial_fin k s]
    exact ringKrullDim_le_of_isIntegral (R := MvPolynomial (Fin s) k) (S := A)
  have h2 : (2 : WithBot ℕ∞) ≤ s := hA.trans h1
  exact_mod_cast h2

section AvoidMinimalPrimes

variable (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem not_mem_of_mem_minimalPrimes {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hg : Function.Injective g) (hfin : g.Finite) {i j : Fin s} (hij : i ≠ j) (a a' b b' : k)
    (Q : Ideal A)
    (hQ : Q ∈ (Ideal.span {(g (X i) - algebraMap k A a) * (g (X i) - algebraMap k A a')}).minimalPrimes) :
    (g (X j) - algebraMap k A b) * (g (X j) - algebraMap k A b') ∉ Q := by
  classical
  haveI hQp : Q.IsPrime := hQ.1.1
  intro hmem

  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hQh : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ

  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let q : Ideal (MvPolynomial (Fin s) k) := Q.under (MvPolynomial (Fin s) k)
  have hqh : q.height ≤ 1 := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q
    calc q.height ≤ q.height + _ := le_self_add
      _ = Q.height := h.symm
      _ ≤ 1 := hQh

  have hmemq : ∀ (l : Fin s) (c : k), g (X l) - algebraMap k A c ∈ Q →
      (X l - C c : MvPolynomial (Fin s) k) ∈ q := by
    intro l c h
    change g.toRingHom (X l - C c) ∈ Q
    simpa [map_sub, ← MvPolynomial.algebraMap_eq, AlgHom.commutes] using h

  have hf₀ : (g (X i) - algebraMap k A a) * (g (X i) - algebraMap k A a') ∈ Q :=
    hQ.1.2 (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ : k, g (X i) - algebraMap k A γ ∈ Q := by
    rcases hQp.mem_or_mem hf₀ with h | h
    exacts [⟨a, h⟩, ⟨a', h⟩]
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ : k, g (X j) - algebraMap k A γ ∈ Q := by
    rcases hQp.mem_or_mem hmem with h | h
    exacts [⟨b, h⟩, ⟨b', h⟩]
  have h2 : (2 : ℕ∞) ≤ q.height :=
    two_le_height_of_mem_of_mem k hij γ₁ γ₂ q (hmemq i γ₁ hγ₁) (hmemq j γ₂ hγ₂)
  have : (2 : ℕ∞) ≤ 1 := h2.trans hqh
  exact absurd this (by decide)

end AvoidMinimalPrimes

section Fields

variable (k : Type u) [Field k] [IsAlgClosed k] (A' : Type v) [CommRing A'] [IsDomain A']
  [Algebra k A'] [Algebra.FiniteType k A'] (u w : A')

local notation "Kf" => FractionRing A'
local notation "C2" => MvPolynomial (Fin 2) A'
local notation "KX" => MvPolynomial (Fin 2) (FractionRing A')
local notation "Ω" => FractionRing (MvPolynomial (Fin 2) (FractionRing A'))
local notation "R3" => MvPolynomial (Fin 3) k

noncomputable def rhoVec : Fin 3 → C2 := ![C u * X 0 + C w * X 1, X 0, X 1]

noncomputable def rho : R3 →ₐ[k] C2 := MvPolynomial.aeval (rhoVec A' u w)

theorem exists_ne_zero_forall_fibre
    (huw : AlgebraicIndependent k ![algebraMap A' Kf u, algebraMap A' Kf w]) :
    ∃ r : R3, r ≠ 0 ∧ ∀ n : Ideal R3, n.IsMaximal → r ∉ n →
      n.map (rho k A' u w).toRingHom = ⊤ ∨ (n.map (rho k A' u w).toRingHom).radical.IsPrime := by
  classical

  set U : Kf := algebraMap A' Kf u with hU
  set W : Kf := algebraMap A' Kf w with hW
  let uvK : Fin 2 → Kf := ![U, W]
  have huvK : AlgebraicIndependent k uvK := huw
  let xΩ : Fin 2 → Ω := fun i => algebraMap KX Ω (X i)
  have hxdef : ∀ i, xΩ i = algebraMap KX Ω (X i) := fun _ => rfl
  set UΩ : Ω := algebraMap Kf Ω U with hUΩ
  set WΩ : Ω := algebraMap Kf Ω W with hWΩ

  have hxΩ : AlgebraicIndependent (FractionRing A') xΩ :=
    (MvPolynomial.algebraicIndependent_X (Fin 2) (FractionRing A')).map'
      (f := IsScalarTower.toAlgHom (FractionRing A') KX Ω) (IsFractionRing.injective KX Ω)

  have hbase : AlgebraicIndependent k (Sum.elim xΩ (algebraMap Kf Ω ∘ uvK)) :=
    huvK.sumElim_comp hxΩ

  let b₃ : Fin 3 → Ω := Fin.snoc xΩ UΩ
  let ι₃ : Fin 3 → Fin 2 ⊕ Fin 2 := ![Sum.inl 0, Sum.inl 1, Sum.inr 0]
  have hι₃ : Function.Injective ι₃ := by decide
  have hb₃eq : Sum.elim xΩ (algebraMap Kf Ω ∘ uvK) ∘ ι₃ = b₃ := by
    funext i
    fin_cases i <;> simp [ι₃, b₃, uvK, Fin.snoc, hUΩ]
  have hb₃ : AlgebraicIndependent k b₃ := hb₃eq ▸ hbase.comp ι₃ hι₃

  have hrange : Sum.elim xΩ (algebraMap Kf Ω ∘ uvK) '' Set.range ι₃ = Set.range b₃ := by
    rw [← Set.range_comp, hb₃eq]
  have hW_tr : Transcendental (Algebra.adjoin k (Set.range b₃)) WΩ := by
    have h := hbase.transcendental_adjoin (s := Set.range ι₃) (i := Sum.inr 1)
      (by rintro ⟨j, hj⟩; fin_cases j <;> simp [ι₃] at hj)
    rw [hrange] at h
    simpa [uvK, hWΩ] using h

  set S := Algebra.adjoin k (Set.range b₃) with hS
  have hx0S : xΩ 0 ∈ S := Algebra.subset_adjoin ⟨0, by simp [b₃]⟩
  have hx1S : xΩ 1 ∈ S := Algebra.subset_adjoin ⟨1, by simp [b₃, Fin.snoc]⟩
  have h2last : (2 : Fin 3) = Fin.last 2 := rfl
  have hb₃2 : b₃ 2 = UΩ := by simp only [b₃, h2last, Fin.snoc_last]
  have hb₃0 : b₃ 0 = xΩ 0 := by simp [b₃]
  have hb₃1 : b₃ 1 = xΩ 1 := by simp [b₃, Fin.snoc]
  have hUS : UΩ ∈ S := Algebra.subset_adjoin ⟨2, hb₃2⟩
  have hx1ne : xΩ 1 ≠ 0 := hxΩ.ne_zero 1
  have hξ_tr : Transcendental S (UΩ * xΩ 0 + WΩ * xΩ 1) := by
    have h := transcendental_add_mul hW_tr ⟨UΩ * xΩ 0, S.mul_mem hUS hx0S⟩ ⟨xΩ 1, hx1S⟩
      (by simpa using hx1ne)
    simpa using h

  have hopt : AlgebraicIndependent k (fun o : Option (Fin 3) => o.elim (UΩ * xΩ 0 + WΩ * xΩ 1) b₃) :=
    AlgebraicIndependent.option_iff.mpr ⟨hb₃, hξ_tr⟩

  let cK : Fin 2 → k := ![1, 0]
  have hξ_eq : (∑ i, algebraMap Kf Ω (uvK i) * xΩ i) = UΩ * xΩ 0 + WΩ * xΩ 1 := by
    simp [Fin.sum_univ_two, uvK, hUΩ, hWΩ]
  have hδ_eq : algebraMap Kf Ω (∑ i, cK i • uvK i) = UΩ := by
    simp [Fin.sum_univ_two, uvK, cK, hUΩ]

  have hind : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc xΩ (∑ i, algebraMap Kf Ω (uvK i) * xΩ i))
        (algebraMap Kf Ω (∑ i, cK i • uvK i))) := by
    rw [hξ_eq, hδ_eq]
    refine (algebraicIndependent_equiv' (R := k) (finSuccEquiv' (2 : Fin 4))
      (f := fun o : Option (Fin 3) => o.elim (UΩ * xΩ 0 + WΩ * xΩ 1) b₃)
      (g := Fin.snoc (Fin.snoc xΩ (UΩ * xΩ 0 + WΩ * xΩ 1)) UΩ) ?_).mpr hopt
    funext i
    fin_cases i
    · have : finSuccEquiv' (2 : Fin 4) 0 = some 0 := by decide
      simp [this, b₃, Fin.snoc]
    · have : finSuccEquiv' (2 : Fin 4) 1 = some 1 := by decide
      simp [this, b₃, Fin.snoc]
    · have : finSuccEquiv' (2 : Fin 4) 2 = none := by decide
      simp [this, Fin.snoc]
    · show ((finSuccEquiv' (2 : Fin 4)) (Fin.last 3)).elim (UΩ * xΩ 0 + WΩ * xΩ 1) b₃ =
        (Fin.snoc (α := fun _ => Ω) (Fin.snoc (α := fun _ => Ω) xΩ (UΩ * xΩ 0 + WΩ * xΩ 1)) UΩ
          (Fin.last 3) : Ω)
      have : finSuccEquiv' (2 : Fin 4) (Fin.last 3) = some 2 := by decide
      rw [this, Fin.snoc_last]
      exact hb₃2

  set ξ' : Ω := UΩ * xΩ 0 + WΩ * xΩ 1 with hξ'
  let g_C : C2 →ₐ[k] Ω := (MvPolynomial.aeval (R := A') xΩ).restrictScalars k
  have hgCX : ∀ i, g_C (X i) = xΩ i := fun i => by simp [g_C]
  have hgCC : ∀ a : A', g_C (C a) = algebraMap Kf Ω (algebraMap A' Kf a) := by
    intro a
    simp only [g_C, AlgHom.coe_restrictScalars', MvPolynomial.algHom_C]
    exact IsScalarTower.algebraMap_apply A' Kf Ω a
  have hgC_eq : g_C.toRingHom = (algebraMap KX Ω).comp (MvPolynomial.map (algebraMap A' Kf)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
        MvPolynomial.map_C]
      rw [hgCC, IsScalarTower.algebraMap_apply Kf KX Ω, MvPolynomial.algebraMap_eq]
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
        MvPolynomial.map_X]
      exact hgCX i
  have hgC_inj : Function.Injective g_C := by
    have : (g_C : C2 → Ω) = (algebraMap KX Ω) ∘ (MvPolynomial.map (algebraMap A' Kf)) := by
      have h := congrArg (fun f : C2 →+* Ω => (f : C2 → Ω)) hgC_eq
      simpa using h
    rw [this]
    exact (IsFractionRing.injective KX Ω).comp
      (MvPolynomial.map_injective _ (IsFractionRing.injective A' Kf))
  have hgCρ : ∀ i, g_C (rhoVec A' u w i) = (![ξ', xΩ 0, xΩ 1] : Fin 3 → Ω) i := by
    intro i
    match i with
    | 0 =>
      simp only [rhoVec, Matrix.cons_val_zero, map_add, map_mul]
      rw [hgCC, hgCC, hgCX, hgCX]
    | 1 => simp [rhoVec, hgCX]
    | 2 => simp [rhoVec, hgCX]

  have hρv : AlgebraicIndependent k (rhoVec A' u w) := by
    refine AlgebraicIndependent.of_comp g_C ?_
    let ι' : Fin 3 → Option (Fin 3) := ![none, some 0, some 1]
    have hι' : Function.Injective ι' := by decide
    have h := hopt.comp ι' hι'
    convert h using 1
    funext i
    simp only [Function.comp_apply, hgCρ]
    fin_cases i <;> simp [ι', hb₃0, hb₃1, hξ']
  have hρ_inj : Function.Injective (rho k A' u w) := hρv

  letI : Algebra R3 C2 := (rho k A' u w).toRingHom.toAlgebra
  haveI : IsScalarTower k R3 C2 :=
    IsScalarTower.of_algebraMap_eq fun c => ((rho k A' u w).commutes c).symm
  haveI : FaithfulSMul R3 C2 := (faithfulSMul_iff_algebraMap_injective R3 C2).mpr hρ_inj
  haveI : Algebra.FiniteType R3 C2 := Algebra.FiniteType.of_restrictScalars_finiteType k R3 C2

  have hfg : (⊤ : IntermediateField k Kf).FG := fg_top_fractionRing k A'
  have hsc : ∀ θ : Kf, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k Kf) :=
    fun θ hθ => mem_bot_of_isSeparable k θ hθ
  have hgi : ∀ θ : FractionRing C2,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R3 (FractionRing C2)))) θ →
        θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R3 (FractionRing C2))) := by
    intro θ hθ
    set F₁ := IntermediateField.adjoin k (Set.range (algebraMap R3 (FractionRing C2))) with hF₁
    let j : FractionRing C2 →ₐ[k] Ω := IsFractionRing.liftAlgHom hgC_inj
    have hj_alg : ∀ c : C2, j (algebraMap C2 (FractionRing C2) c) = g_C c := fun c =>
      IsFractionRing.lift_algebraMap hgC_inj c
    have hF₂ : F₁.map j = IntermediateField.adjoin k (Set.range xΩ ∪ {ξ'}) := by
      rw [hF₁, IntermediateField.adjoin_map, ← Set.range_comp]
      have hcomp : (j : FractionRing C2 → Ω) ∘ (algebraMap R3 (FractionRing C2)) =
          (g_C : C2 → Ω) ∘ (rho k A' u w) := by
        funext r
        simp only [Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply R3 C2 (FractionRing C2) r, hj_alg]
        rfl
      rw [hcomp]
      refine le_antisymm ?_ ?_
      · rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨r, rfl⟩
        simp only [Function.comp_apply]
        have hr : g_C (rho k A' u w r) ∈ (g_C.comp (rho k A' u w)).range := ⟨r, rfl⟩
        rw [rho, MvPolynomial.comp_aeval, MvPolynomial.aeval_range] at hr
        refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
        refine (Algebra.adjoin_mono ?_) hr
        rintro _ ⟨i, rfl⟩
        show g_C (rhoVec A' u w i) ∈ _
        rw [hgCρ]
        fin_cases i
        · exact Or.inr rfl
        · exact Or.inl ⟨0, rfl⟩
        · exact Or.inl ⟨1, rfl⟩
      · rw [IntermediateField.adjoin_le_iff]
        rintro y (⟨i, rfl⟩ | rfl)
        · refine IntermediateField.subset_adjoin k _ ⟨X i.succ, ?_⟩
          fin_cases i
          · show g_C (rho k A' u w (X 1)) = xΩ 0
            rw [rho, MvPolynomial.aeval_X, hgCρ]; rfl
          · show g_C (rho k A' u w (X 2)) = xΩ 1
            rw [rho, MvPolynomial.aeval_X, hgCρ]; rfl
        · refine IntermediateField.subset_adjoin k _ ⟨X 0, ?_⟩
          show g_C (rho k A' u w (X 0)) = ξ'
          rw [rho, MvPolynomial.aeval_X, hgCρ]; rfl
    have hθ' : IsSeparable (F₁.map j) (j θ) :=
      isSeparable_transport (IntermediateField.equivMap F₁ j).toRingEquiv j.toRingHom
        (fun r => rfl) hθ
    rw [hF₂] at hθ'
    have hθ'' : IsSeparable
        (IntermediateField.adjoin k (Set.range xΩ ∪ {∑ i, algebraMap Kf Ω (uvK i) * xΩ i})) (j θ) := by
      rw [hξ_eq]; exact hθ'
    have hmem := IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
      (k := k) (K := Kf) hfg hsc (n := 1) uvK cK xΩ hxdef hind (j θ) hθ''
    have hmem' : j θ ∈ F₁.map j := by
      rw [hF₂]; rw [hξ_eq] at hmem; exact hmem
    rw [IntermediateField.mem_map] at hmem'
    obtain ⟨θ₀, hθ₀, hθ₀eq⟩ := hmem'
    have : θ₀ = θ := j.toRingHom.injective hθ₀eq
    exact this ▸ hθ₀

  obtain ⟨r, hr0, hr⟩ :=
    Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime k (R := R3) (C := C2) hgi
  exact ⟨r, hr0, fun n hn hrn => hr n hn hrn⟩

end Fields

theorem algebraicIndependent_ratio (k : Type u) [Field k] {L : Type*} [Field L] [Algebra k L]
    (τ : Fin 2 → L) (hτ : AlgebraicIndependent k τ) (a₁ b₁ a₂ b₂ : k) (v : L)
    (hv : v * ((τ 0 - algebraMap k L a₁) * (τ 0 - algebraMap k L b₁)) =
      (τ 1 - algebraMap k L a₂) * (τ 1 - algebraMap k L b₂)) :
    AlgebraicIndependent k ![τ 1, v] := by
  classical
  set D : L := (τ 0 - algebraMap k L a₁) * (τ 0 - algebraMap k L b₁) with hD
  set N : L := (τ 1 - algebraMap k L a₂) * (τ 1 - algebraMap k L b₂) with hN
  have hne : ∀ (i : Fin 2) (c : k), τ i - algebraMap k L c ≠ 0 := by
    intro i c h
    have halg : IsAlgebraic k (τ i) := by
      rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap c
    exact hτ.transcendental i halg
  have hD0 : D ≠ 0 := mul_ne_zero (hne 0 a₁) (hne 0 b₁)
  have hN0 : N ≠ 0 := mul_ne_zero (hne 1 a₂) (hne 1 b₂)
  have hv0 : v ≠ 0 := by
    intro h; rw [h, zero_mul] at hv; exact hN0 hv.symm

  set S₁ := Algebra.adjoin k ({τ 1} : Set L) with hS₁
  have hτ0 : Transcendental S₁ (τ 0) := by
    have h := hτ.transcendental_adjoin (s := {1}) (i := 0) (by simp)
    rwa [Set.image_singleton] at h

  have hvS : Transcendental S₁ v := by
    intro halg
    apply hτ0
    have hNS : N ∈ S₁ := by
      refine S₁.mul_mem (S₁.sub_mem (Algebra.subset_adjoin rfl) (algebraMap_mem S₁ a₂))
        (S₁.sub_mem (Algebra.subset_adjoin rfl) (algebraMap_mem S₁ b₂))
    have hDalg : IsAlgebraic S₁ D := by
      have hDeq : D = N * v⁻¹ := by
        field_simp
        rw [mul_comm] at hv
        exact hv
      rw [hDeq]
      exact (isAlgebraic_algebraMap (⟨N, hNS⟩ : S₁)).mul (IsAlgebraic.inv_iff.mpr halg)

    let P : Polynomial S₁ :=
      (Polynomial.X - Polynomial.C (algebraMap k S₁ a₁)) *
        (Polynomial.X - Polynomial.C (algebraMap k S₁ b₁))
    have hPmonic : P.Monic := (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _)
    have hPdeg : P.natDegree = 2 := by
      rw [(Polynomial.monic_X_sub_C _).natDegree_mul (Polynomial.monic_X_sub_C _),
        Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
    have hPeval : Polynomial.aeval (τ 0) P = D := by
      simp only [P, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hD]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [← hPeval] at hDalg
    exact hDalg.of_aeval P (by rw [hPdeg]; norm_num)
      (by rw [hPmonic.leadingCoeff]; exact Submonoid.one_mem _)

  have h1 : AlgebraicIndependent k (fun _ : Fin 1 => τ 1) :=
    algebraicIndependent_unique_type_iff.mpr (hτ.transcendental 1)
  have h2 : AlgebraicIndependent k (fun o : Option (Fin 1) => o.elim v fun _ : Fin 1 => τ 1) := by
    refine AlgebraicIndependent.option_iff.mpr ⟨h1, ?_⟩
    have : Set.range (fun _ : Fin 1 => τ 1) = {τ 1} := Set.range_const
    rw [this]
    exact hvS
  refine (algebraicIndependent_equiv' (R := k) (finSuccEquiv' (1 : Fin 2))
    (f := fun o : Option (Fin 1) => o.elim v fun _ : Fin 1 => τ 1) (g := ![τ 1, v]) ?_).mpr h2
  funext i
  fin_cases i
  · have : finSuccEquiv' (1 : Fin 2) 0 = some 0 := by decide
    simp [this]
  · have : finSuccEquiv' (1 : Fin 2) 1 = none := by decide
    simp [this]

theorem radical_span_isPrime_of_away {A : Type v} [CommRing A] (f₀ F : A)
    (A' : Type*) [CommRing A'] [Algebra A A'] [IsLocalization.Away f₀ A']
    (hex : ((Ideal.span {F}).minimalPrimes).Nonempty)
    (havoid : ∀ P ∈ (Ideal.span {F}).minimalPrimes, f₀ ∉ P)
    (h : (Ideal.span {F}).map (algebraMap A A') = ⊤ ∨
      (((Ideal.span {F}).map (algebraMap A A')).radical).IsPrime) :
    (Ideal.span {F}).radical.IsPrime := by
  set I := Ideal.span {F} with hI
  set φ := algebraMap A A' with hφ
  rcases h with htop | hprime
  · exfalso
    have hnd : ¬ Disjoint ((Submonoid.powers f₀ : Submonoid A) : Set A) (I : Set A) := by
      intro hd
      exact ((IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers f₀) A' I).mpr
        hd) htop
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨x, ⟨n, rfl⟩, hxI⟩ := hnd
    obtain ⟨P, hP⟩ := hex
    haveI := hP.1.1
    exact havoid P hP (hP.1.1.mem_of_pow_mem n (hP.1.2 hxI))
  · set 𝔓 := (I.map φ).radical with h𝔓
    have heq : I.radical = 𝔓.comap φ := by
      refine le_antisymm ?_ ?_
      · rw [h𝔓, Ideal.comap_radical]
        exact Ideal.radical_mono Ideal.le_comap_map
      · rw [← Ideal.sInf_minimalPrimes]
        refine le_sInf fun P hP => ?_
        haveI hPp : P.IsPrime := hP.1.1
        have hdisj : Disjoint ((Submonoid.powers f₀ : Submonoid A) : Set A) (P : Set A) := by
          rw [Set.disjoint_left]
          rintro _ ⟨n, rfl⟩ hn
          exact havoid P hP (hPp.mem_of_pow_mem n hn)
        haveI : (P.map φ).IsPrime :=
          IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) A' P hPp hdisj
        have hunder : (P.map φ).comap φ = P := by
          have := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f₀) A' hPp hdisj
          rwa [Ideal.under_def] at this
        calc 𝔓.comap φ ≤ ((P.map φ).radical).comap φ :=
              Ideal.comap_mono (Ideal.radical_mono (Ideal.map_mono hP.1.2))
          _ = (P.map φ).comap φ := by rw [Ideal.IsPrime.radical ‹_›]
          _ = P := hunder
    rw [heq]
    exact Ideal.comap_isPrime φ 𝔓

theorem irredHyp
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 2 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] (_hne : m₀ ≠ m₁) :
    ∃ f : A, f ∈ m₀ ∧ f ∈ m₁ ∧ f ≠ 0 ∧ (Ideal.span {f}).radical.IsPrime := by
  classical
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A

  obtain ⟨s, g, hg, hfin, hs⟩ := exists_noether_two_le k hA
  let i₀ : Fin s := ⟨0, by omega⟩
  let i₁ : Fin s := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let ι : Fin 2 → Fin s := ![i₀, i₁]
  have hι : Function.Injective ι := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [ι]
  let T : Fin 2 → A := fun j => g (X (ι j))
  have hT : AlgebraicIndependent k T :=
    ((MvPolynomial.algebraicIndependent_X (Fin s) k).comp ι hι).map' (f := g) hg
  set t₁ : A := g (X i₀) with ht₁
  set t₂ : A := g (X i₁) with ht₂
  have hT0 : T 0 = t₁ := by simp [T, ι, ht₁]
  have hT1 : T 1 = t₂ := by simp [T, ι, ht₂]

  obtain ⟨α₁, hα₁⟩ := exists_sub_algebraMap_mem k m₀ t₁
  obtain ⟨β₁, hβ₁⟩ := exists_sub_algebraMap_mem k m₁ t₁
  obtain ⟨α₂, hα₂⟩ := exists_sub_algebraMap_mem k m₀ t₂
  obtain ⟨β₂, hβ₂⟩ := exists_sub_algebraMap_mem k m₁ t₂

  set f₀ : A := (t₁ - algebraMap k A α₁) * (t₁ - algebraMap k A β₁) with hf₀
  set f₂ : A := (t₂ - algebraMap k A α₂) * (t₂ - algebraMap k A β₂) with hf₂
  have hf₀m₀ : f₀ ∈ m₀ := m₀.mul_mem_right _ hα₁
  have hf₀m₁ : f₀ ∈ m₁ := m₁.mul_mem_left _ hβ₁
  have hf₂m₀ : f₂ ∈ m₀ := m₀.mul_mem_right _ hα₂
  have hf₂m₁ : f₂ ∈ m₁ := m₁.mul_mem_left _ hβ₂
  have hsubne : ∀ (j : Fin 2) (c : k), T j - algebraMap k A c ≠ 0 := by
    intro j c h
    have halg : IsAlgebraic k (T j) := by
      rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap c
    exact hT.transcendental j halg
  have hf₀ne : f₀ ≠ 0 := by
    rw [hf₀, ← hT0]; exact mul_ne_zero (hsubne 0 α₁) (hsubne 0 β₁)

  have havoid₂ : ∀ Q ∈ (Ideal.span {f₀}).minimalPrimes, f₂ ∉ Q := fun Q hQ =>
    not_mem_of_mem_minimalPrimes k g hg hfin hi α₁ β₁ α₂ β₂ Q hQ

  let A' : Type v := Localization.Away f₀
  haveI : IsDomain A' :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf₀ne)
  have hinjA' : Function.Injective (algebraMap A A') :=
    IsLocalization.injective A' (powers_le_nonZeroDivisors_of_noZeroDivisors hf₀ne)
  set t₂' : A' := algebraMap A A' t₂ with ht₂'
  set g₂ : A' := algebraMap A A' f₂ * IsLocalization.Away.invSelf (S := A') f₀ with hg₂
  have hg₂f₀ : g₂ * algebraMap A A' f₀ = algebraMap A A' f₂ := by
    rw [hg₂, mul_assoc, mul_comm (IsLocalization.Away.invSelf (S := A') f₀),
      IsLocalization.Away.mul_invSelf, mul_one]

  have huw : AlgebraicIndependent k
      ![algebraMap A' (FractionRing A') t₂', algebraMap A' (FractionRing A') g₂] := by
    let τ : Fin 2 → FractionRing A' := fun j => algebraMap A (FractionRing A') (T j)
    have hτ : AlgebraicIndependent k τ :=
      hT.map' (f := IsScalarTower.toAlgHom k A (FractionRing A'))
        ((IsFractionRing.injective A' (FractionRing A')).comp hinjA')
    have hτ1 : τ 1 = algebraMap A' (FractionRing A') t₂' := by
      simp only [τ, hT1, ht₂']
      exact IsScalarTower.algebraMap_apply A A' (FractionRing A') t₂
    rw [← hτ1]
    refine algebraicIndependent_ratio k τ hτ α₁ β₁ α₂ β₂ _ ?_
    have h := congrArg (algebraMap A' (FractionRing A')) hg₂f₀
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    simp only [τ, hT0, hT1]
    simpa [hf₀, hf₂, ← IsScalarTower.algebraMap_apply] using h

  obtain ⟨r, hr0, hr⟩ := exists_ne_zero_forall_fibre k A' t₂' g₂ huw

  obtain ⟨a, ha⟩ : ∃ a : Fin 3 → k, MvPolynomial.eval a (X 2 * r) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : (X 2 * r : MvPolynomial (Fin 3) k) = 0 :=
      MvPolynomial.funext fun x => by rw [hcon x, map_zero]
    exact (mul_ne_zero (MvPolynomial.X_ne_zero 2) hr0) this
  rw [map_mul, MvPolynomial.eval_X] at ha
  have ha2 : a 2 ≠ 0 := left_ne_zero_of_mul ha
  have har : MvPolynomial.eval a r ≠ 0 := right_ne_zero_of_mul ha

  let n : Ideal (MvPolynomial (Fin 3) k) := RingHom.ker (MvPolynomial.eval a)
  haveI hn : n.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, MvPolynomial.eval_C c⟩
  have hrn : r ∉ n := har
  have hfib := hr n hn hrn

  set F : A := -(algebraMap k A (a 0)) * f₀ + algebraMap k A (a 1) * (t₂ * f₀) +
    algebraMap k A (a 2) * f₂ with hF
  have hFm₀ : F ∈ m₀ :=
    m₀.add_mem (m₀.add_mem (m₀.mul_mem_left _ hf₀m₀) (m₀.mul_mem_left _ (m₀.mul_mem_left _ hf₀m₀)))
      (m₀.mul_mem_left _ hf₂m₀)
  have hFm₁ : F ∈ m₁ :=
    m₁.add_mem (m₁.add_mem (m₁.mul_mem_left _ hf₀m₁) (m₁.mul_mem_left _ (m₁.mul_mem_left _ hf₀m₁)))
      (m₁.mul_mem_left _ hf₂m₁)

  have havoidF : ∀ Q ∈ (Ideal.span {f₀}).minimalPrimes, F ∉ Q := by
    intro Q hQ hFQ
    haveI hQp : Q.IsPrime := hQ.1.1
    have hf₀Q : f₀ ∈ Q := hQ.1.2 (Ideal.subset_span (Set.mem_singleton _))
    have h1 : algebraMap k A (a 2) * f₂ ∈ Q := by
      have : algebraMap k A (a 2) * f₂ =
          F - (-(algebraMap k A (a 0)) * f₀ + algebraMap k A (a 1) * (t₂ * f₀)) := by
        rw [hF]; ring
      rw [this]
      exact Q.sub_mem hFQ (Q.add_mem (Q.mul_mem_left _ hf₀Q)
        (Q.mul_mem_left _ (Q.mul_mem_left _ hf₀Q)))
    have hunit : IsUnit (algebraMap k A (a 2)) := (IsUnit.mk0 _ ha2).map _
    rcases hQp.mem_or_mem h1 with h | h
    · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem Q h hunit)
    · exact havoid₂ Q hQ h
  obtain ⟨Q₀, hQ₀, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f₀}) (J := m₀)
    ((Ideal.span_singleton_le_iff_mem _).mpr hf₀m₀)
  have hFne : F ≠ 0 := fun h => havoidF Q₀ hQ₀ (h ▸ Q₀.zero_mem)

  have havoid : ∀ P ∈ (Ideal.span {F}).minimalPrimes, f₀ ∉ P := by
    intro P hP hf₀P
    haveI hPp : P.IsPrime := hP.1.1
    have hPh : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f₀}) (J := P)
      ((Ideal.span_singleton_le_iff_mem _).mpr hf₀P)
    haveI hQp : Q.IsPrime := hQ.1.1
    have hFP : F ∈ P := hP.1.2 (Ideal.subset_span (Set.mem_singleton _))
    have hQne : Q ≠ P := fun h => havoidF Q hQ (h ▸ hFP)
    have hlt : Q < P := lt_of_le_of_ne hQP hQne
    have hbot : (⊥ : Ideal A) < Q := by
      refine bot_lt_iff_ne_bot.mpr fun h => hf₀ne ?_
      have := hQ.1.2 (Ideal.subset_span (Set.mem_singleton f₀))
      simpa [h] using this
    haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [Ideal.height_bot, zero_add] at h1
    have h3 : (2 : ℕ∞) ≤ P.height :=
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ Q.height + 1 := by gcongr
        _ ≤ P.height := h2
    exact absurd (h3.trans hPh) (by decide)
  obtain ⟨P₀, hP₀, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {F}) (J := m₀)
    ((Ideal.span_singleton_le_iff_mem _).mpr hFm₀)

  set h : A' := algebraMap k A' (a 1) * t₂' + algebraMap k A' (a 2) * g₂ - algebraMap k A' (a 0)
    with hh
  have hFh : algebraMap A A' F = h * algebraMap A A' f₀ := by
    rw [hF, hh]
    simp only [map_add, map_mul, map_neg, ← IsScalarTower.algebraMap_apply k A A']
    rw [← hg₂f₀, ← ht₂']
    ring
  have hspan : (Ideal.span {F}).map (algebraMap A A') = Ideal.span {h} := by
    rw [Ideal.map_span, Set.image_singleton, hFh]
    exact Ideal.span_singleton_mul_right_unit (IsLocalization.Away.algebraMap_isUnit f₀) h

  let ρ := rho k A' t₂' g₂
  let av : Fin 2 → A' := ![algebraMap k A' (a 1), algebraMap k A' (a 2)]
  let ψ : MvPolynomial (Fin 2) A' →ₐ[A'] A' := MvPolynomial.aeval av
  have hψ : Function.Surjective ψ := fun b => ⟨C b, by simp [ψ]⟩
  have hρC : ∀ c : k, ρ (C c) = C (algebraMap k A' c) := by
    intro c
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply]
  have hρX0 : ρ (X 0) = C t₂' * X 0 + C g₂ * X 1 := by
    simp [ρ, rho, rhoVec]
  have hρX1 : ρ (X 1) = X 0 := by simp [ρ, rho, rhoVec]
  have hρX2 : ρ (X 2) = X 1 := by simp [ρ, rho, rhoVec]
  have hψX0 : ψ (X 0) = algebraMap k A' (a 1) := by simp [ψ, av]
  have hψX1 : ψ (X 1) = algebraMap k A' (a 2) := by simp [ψ, av]
  set J : Ideal (MvPolynomial (Fin 2) A') := n.map ρ.toRingHom with hJ

  have hnle : n ≤ Ideal.span (Set.range fun i : Fin 3 => (X i - C (a i) : MvPolynomial (Fin 3) k)) :=
    fun p hp => mem_span_X_sub_C_of_aeval_eq_zero a (by simp [MvPolynomial.aeval_eq_eval] at hp ⊢; exact hp)
  have hJle : J ≤ (Ideal.span {h}).comap ψ.toRingHom := by
    rw [hJ]
    refine (Ideal.map_mono hnle).trans ?_
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub,
      hρC, MvPolynomial.algHom_C, Algebra.algebraMap_self, RingHom.id_apply]
    fin_cases i
    · simp only [Fin.zero_eta, hρX0, map_add, map_mul, MvPolynomial.algHom_C,
        Algebra.algebraMap_self, RingHom.id_apply, hψX0, hψX1]
      refine Ideal.mem_span_singleton.mpr ⟨1, ?_⟩
      rw [hh]; ring
    · simp only [Fin.mk_one, hρX1, hψX0, sub_self]
      exact Ideal.zero_mem _
    · show ψ (ρ (X 2)) - algebraMap k A' (a 2) ∈ Ideal.span {h}
      rw [hρX2, hψX1, sub_self]
      exact Ideal.zero_mem _

  have hX0J : (X 0 - C (algebraMap k A' (a 1)) : MvPolynomial (Fin 2) A') ∈ J := by
    have : (X 0 - C (algebraMap k A' (a 1)) : MvPolynomial (Fin 2) A') = ρ (X 1 - C (a 1)) := by
      rw [map_sub, hρX1, hρC]
    rw [this]
    exact Ideal.mem_map_of_mem _ (by simp [n, RingHom.mem_ker])
  have hX1J : (X 1 - C (algebraMap k A' (a 2)) : MvPolynomial (Fin 2) A') ∈ J := by
    have : (X 1 - C (algebraMap k A' (a 2)) : MvPolynomial (Fin 2) A') = ρ (X 2 - C (a 2)) := by
      rw [map_sub, hρX2, hρC]
    rw [this]
    exact Ideal.mem_map_of_mem _ (by simp [n, RingHom.mem_ker])
  have hkerJ : RingHom.ker ψ.toRingHom ≤ J := by
    intro p hp
    have hp' : MvPolynomial.aeval av p = 0 := hp
    have hmem := mem_span_X_sub_C_of_aeval_eq_zero av hp'
    refine (Ideal.span_le.mpr ?_) hmem
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa [av] using hX0J
    · simpa [av] using hX1J
  have hChJ : (C h : MvPolynomial (Fin 2) A') ∈ J := by
    have : (C h : MvPolynomial (Fin 2) A') = ρ (X 0 - C (a 0)) -
        C t₂' * (X 0 - C (algebraMap k A' (a 1))) - C g₂ * (X 1 - C (algebraMap k A' (a 2))) := by
      rw [map_sub ρ (X 0) (C (a 0)), hρX0, hρC, hh]
      simp only [map_sub, map_add, map_mul]
      ring
    rw [this]
    refine J.sub_mem (J.sub_mem ?_ (J.mul_mem_left _ hX0J)) (J.mul_mem_left _ hX1J)
    exact Ideal.mem_map_of_mem _ (by simp [n, RingHom.mem_ker])
  have hmapJ : J.map ψ.toRingHom = Ideal.span {h} := by
    refine le_antisymm ?_ ?_
    · exact (Ideal.map_mono hJle).trans Ideal.map_comap_le
    · rw [Ideal.span_singleton_le_iff_mem]
      have : ψ.toRingHom (C h) = h := by simp [ψ]
      rw [← this]
      exact Ideal.mem_map_of_mem _ hChJ

  have hA' : (Ideal.span {F}).map (algebraMap A A') = ⊤ ∨
      (((Ideal.span {F}).map (algebraMap A A')).radical).IsPrime := by
    rw [hspan, ← hmapJ]
    rcases hfib with htop | hprime
    · left
      rw [show J = ⊤ from htop, Ideal.map_top]
    · right
      haveI : J.radical.IsPrime := hprime
      rw [← Ideal.map_radical_of_surjective hψ hkerJ]
      exact Ideal.map_isPrime_of_surjective hψ (I := J.radical) (hkerJ.trans Ideal.le_radical)
  exact ⟨F, hFm₀, hFm₁, hFne, radical_span_isPrime_of_away f₀ F A' ⟨P₀, hP₀⟩ havoid hA'⟩

end P2mIrredHyp

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 2 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] (hne : m₀ ≠ m₁) :
    ∃ f : A, f ∈ m₀ ∧ f ∈ m₁ ∧ f ≠ 0 ∧ (Ideal.span {f}).radical.IsPrime :=
  P2mIrredHyp.irredHyp k hA m₀ m₁ hne

end S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime
end P2MW
export P2MW.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime (solution)
