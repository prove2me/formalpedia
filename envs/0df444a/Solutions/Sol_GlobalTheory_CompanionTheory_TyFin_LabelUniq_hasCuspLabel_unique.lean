-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:13.527828+00:00
-- url     : https://prove2.me/submissions/39a8ef05-5c1a-42e5-b3ff-6858fb98a901

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_minpoly_pow_card_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_two_le_card
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_gen_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_exists_root
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_exists_elliptic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
section Field
variable {K : Type} [Field K] [Fintype K]
end Field
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
section Label
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
private theorem two_mul_le_two_pow_lemma_2 : ∀ m : ℕ, 1 ≤ m → 2 * m ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      norm_num
    · have h1 := ih h
      have h2 : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ]
      omega
private theorem small_lt_lemma_3 {q d e : ℕ} (hq : 2 ≤ q) (he : 1 ≤ e) (hed : 2 * e ≤ d) :
    d * (q ^ e - 1) < q ^ d - 1 := by
  have hB : d ≤ q ^ (d - e) := by
    have h1 : d ≤ 2 * (d - e) := by omega
    have h2 := two_mul_le_two_pow_lemma_2 (d - e) (by omega)
    have h3 : 2 ^ (d - e) ≤ q ^ (d - e) := Nat.pow_le_pow_left hq _
    omega
  have hsplit : q ^ d = q ^ e * q ^ (d - e) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  have hA : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
  obtain ⟨A', hA'⟩ : ∃ A', q ^ e = A' + 1 := ⟨q ^ e - 1, by omega⟩
  rw [hsplit, hA', Nat.add_sub_cancel]
  have key : d * A' ≤ A' * q ^ (d - e) := by
    rw [mul_comm A']
    exact Nat.mul_le_mul_right A' hB
  have h5 : (A' + 1) * q ^ (d - e) = A' * q ^ (d - e) + q ^ (d - e) := by ring
  rw [h5]
  omega
private theorem reg_small_lemma_4 {q d : ℕ} (hq : 2 ≤ q) {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (e : ℕ) (he : 0 < e) (hed : e < d) : ¬ j * q ^ e ≡ j [MOD q ^ d - 1] := by
  have hqd : q ^ d ≡ 1 [MOD q ^ d - 1] := by
    have h1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
    have e1 : q ^ d = (q ^ d - 1) + 1 := by omega
    rw [e1, Nat.add_sub_cancel]
    exact Nat.add_modEq_left
  have hsmall : ∀ e', 0 < e' → 2 * e' ≤ d → ¬ j * q ^ e' ≡ j [MOD q ^ d - 1] := by
    intro e' he' h2e hmod
    have hle : j ≤ j * q ^ e' := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    have hdvd : q ^ d - 1 ∣ j * q ^ e' - j := (Nat.modEq_iff_dvd' hle).1 hmod.symm
    have hpos : 0 < j * q ^ e' - j := by
      have h1 : q ≤ q ^ e' := Nat.le_self_pow he'.ne' q
      have h2 : j * q ≤ j * q ^ e' := Nat.mul_le_mul_left _ h1
      have h3 : j * 2 ≤ j * q := Nat.mul_le_mul_left _ hq
      omega
    have hlt : j * q ^ e' - j < q ^ d - 1 := by
      have h1 := small_lt_lemma_3 hq he' h2e
      have h2 : j * (q ^ e' - 1) ≤ d * (q ^ e' - 1) := Nat.mul_le_mul_right _ hjd
      have h3 : j * q ^ e' - j = j * (q ^ e' - 1) := by rw [Nat.mul_sub_one]
      omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hlt)
  by_cases h2e : 2 * e ≤ d
  · exact hsmall e he h2e
  · intro hmod
    apply hsmall (d - e) (by omega) (by omega)
    have h1 : j * q ^ e * q ^ (d - e) ≡ j * q ^ (d - e) [MOD q ^ d - 1] := hmod.mul_right _
    have e2 : j * q ^ e * q ^ (d - e) = j * q ^ d := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hed.le]
    rw [e2] at h1
    have h3 : j * q ^ d ≡ j [MOD q ^ d - 1] := by simpa using hqd.mul_left j
    exact h1.symm.trans h3
private theorem multiset_eq_of_psum_lemma_5 {d : ℕ} (u v : Fin d → ℂ)
    (h : ∀ j, 1 ≤ j → j ≤ d → ∑ a, u a ^ j = ∑ a, v a ^ j) :
    Multiset.map u Finset.univ.val = Multiset.map v Finset.univ.val := by
  have hps : ∀ j, 1 ≤ j → j ≤ d → MvPolynomial.aeval u (MvPolynomial.psum (Fin d) ℂ j) =
      MvPolynomial.aeval v (MvPolynomial.psum (Fin d) ℂ j) := by
    intro j h1 h2
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
    exact h j h1 h2
  have hes : ∀ k, k ≤ d → MvPolynomial.aeval u (MvPolynomial.esymm (Fin d) ℂ k) =
      MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        simp [MvPolynomial.esymm_zero]
      · have hu := congrArg (MvPolynomial.aeval u) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k)
        have hv := congrArg (MvPolynomial.aeval v) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k)
        simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at hu hv
        have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
        apply mul_left_cancel₀ hk0
        rw [hu, hv]
        congr 1
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_filter] at ha
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 ha.1
        rw [ih a.1 ha.2 (by omega), hps a.2 (by omega) (by omega)]
  have hUc : (Multiset.map u Finset.univ.val).card = d := by simp
  have hVc : (Multiset.map v Finset.univ.val).card = d := by simp
  have hE : ∀ k, k ≤ d → (Multiset.map u Finset.univ.val).esymm k =
      (Multiset.map v Finset.univ.val).esymm k := by
    intro k hk
    have h1 := hes k hk
    rwa [MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm] at h1
  have hprod : ((Multiset.map u Finset.univ.val).map fun t => X - C t).prod =
      ((Multiset.map v Finset.univ.val).map fun t => X - C t).prod := by
    ext n
    by_cases hn : n ≤ d
    · rw [Multiset.prod_X_sub_C_coeff _ (by omega), Multiset.prod_X_sub_C_coeff _ (by omega), hUc, hVc,
        hE _ (by omega)]
    · push Not at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
      all_goals first
        | (rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hUc]; exact hn)
        | (rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hVc]; exact hn)
  have h2 := congrArg Polynomial.roots hprod
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h2
end Label
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
end

set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.LabelUniq
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (ι : Type)
    [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) (P P' : K[X]),
    HasCuspLabel C τ P → HasCuspLabel C τ P' → P = P' := by
  intro K _ _ _ C ι _ _ τ P P' hP hP'
  obtain ⟨hm, hi, hX, hdeg, htr⟩ := hP
  obtain ⟨hm', hi', hX', hdeg', htr'⟩ := hP'
  have hd : 0 < Fintype.card ι := by
    rw [← hdeg]
    exact Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hi)
  obtain ⟨x, s, hx, hmin, hs, -⟩ := exists_root C hd hm hi hX hdeg
  obtain ⟨x', s', hx', hmin', hs', -⟩ := exists_root C hd hm' hi' hX' hdeg'
  have hx0 : x ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero _ (gen_ne_zero C hd)
  have hx0' : x' ≠ 0 := by
    rw [← hs']
    exact pow_ne_zero _ (gen_ne_zero C hd)
  have hq : 2 ≤ Fintype.card K := two_le_card
  have epow : ∀ (y : ℂ) (a j : ℕ), (y ^ Fintype.card K ^ a) ^ j = y ^ (j * Fintype.card K ^ a) := by
    intro y a j
    rw [← pow_mul, mul_comm]
  have hpow : ∀ j, 1 ≤ j → j ≤ Fintype.card ι →
      ∑ a : Fin (Fintype.card ι), (C.ι x ^ Fintype.card K ^ (a : ℕ)) ^ j =
      ∑ a : Fin (Fintype.card ι), (C.ι x' ^ Fintype.card K ^ (a : ℕ)) ^ j := by
    intro j hj1 hjd
    obtain ⟨γ, hγ, hγr⟩ :=
      exists_elliptic C hd j (fun e he hed => reg_small_lemma_4 hq hj1 hjd e he hed)
    have h1 := htr x hx γ hγ _ hγr j rfl
    have h2 := htr' x' hx' γ hγ _ hγr j rfl
    rw [h1] at h2
    have h3 := mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h2
    rw [Finset.sum_range, Finset.sum_range] at h3
    simp only [epow]
    exact h3
  have hmult := multiset_eq_of_psum_lemma_5 _ _ hpow
  have hmem : C.ι x ∈ Multiset.map (fun a : Fin (Fintype.card ι) => C.ι x' ^ Fintype.card K ^ (a : ℕ))
      Finset.univ.val := by
    rw [← hmult]
    refine Multiset.mem_map.2 ⟨⟨0, hd⟩, Finset.mem_univ_val _, ?_⟩
    simp
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 hmem
  have hxa : x = x' ^ Fintype.card K ^ (a : ℕ) := by
    apply C.ι_inj _ _ hx0 (pow_ne_zero _ hx0')
    rw [map_pow]
    exact ha.symm
  rw [← hmin, ← hmin', hxa, minpoly_pow_card_pow]
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
