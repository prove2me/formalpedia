-- Prove2me | solution 1 for MvFormalGroup.BigWittLaw.exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/64d39642-1cb8-5025-9d77-a1a68ff2bc1e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse
import Theorems.Thm_MvFormalGroup_ArtinHasse_subst_addFam_map_coord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

universe u

open PowerSeries MvFormalGroup MvFormalGroup.ArtinHasse

namespace SplitSol

variable (p : ℕ) [hp : Fact p.Prime]

section Trunc

variable {A : Type*} [CommRing A]

theorem trunc_eq_of_coeff_eq {K : ℕ} {f g : A⟦X⟧} (h : ∀ k, k < K → coeff k f = coeff k g) :
    trunc K f = trunc K g := by
  ext k
  rw [coeff_trunc, coeff_trunc]
  split_ifs with hk
  · exact h k hk
  · rfl

theorem coeff_eq_of_trunc_eq {K : ℕ} {f g : A⟦X⟧} (h : trunc K f = trunc K g) {k : ℕ} (hk : k < K) :
    coeff k f = coeff k g := by
  have := congrArg (fun q : Polynomial A => q.coeff k) h
  simpa only [coeff_trunc, if_pos hk] using this

theorem trunc_mul_congr {n : ℕ} {f f' g g' : A⟦X⟧}
    (hf : trunc n f = trunc n f') (hg : trunc n g = trunc n g') : trunc n (f * g) = trunc n (f' * g') := by
  rw [← trunc_trunc_mul_trunc, hf, hg, trunc_trunc_mul_trunc]

theorem trunc_prod_congr {ι : Type*} {n : ℕ} (s : Finset ι) {f g : ι → A⟦X⟧}
    (h : ∀ i ∈ s, trunc n (f i) = trunc n (g i)) : trunc n (∏ i ∈ s, f i) = trunc n (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact trunc_mul_congr (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem trunc_prod_eq_one {ι : Type*} (s : Finset ι) (f : ι → A⟦X⟧)
    (k : ℕ) (hf : ∀ i ∈ s, trunc (k + 1) (f i) = 1) :
    trunc (k + 1) (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← trunc_trunc_mul, hf a (Finset.mem_insert_self _ _),
      Polynomial.coe_one, one_mul, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem trunc_prod_filter {ι : Type*} {k : ℕ} (s : Finset ι) (P : ι → Prop) [DecidablePred P]
    (f : ι → A⟦X⟧) (h : ∀ i ∈ s, ¬ P i → trunc (k + 1) (f i) = 1) :
    trunc (k + 1) (∏ i ∈ s, f i) = trunc (k + 1) (∏ i ∈ s.filter P, f i) := by
  have h1 : trunc (k + 1) (∏ i ∈ s.filter (fun i => ¬ P i), f i) = trunc (k + 1) 1 :=
    (trunc_prod_eq_one _ _ k fun i hi => h i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2).trans
      (trunc_one k).symm
  rw [← Finset.prod_filter_mul_prod_filter_not s P f, trunc_mul_congr rfl h1, mul_one]

theorem trunc_map_congr {B : Type*} [CommRing B] (φ : A →+* B) {K : ℕ} {f g : A⟦X⟧}
    (h : trunc K f = trunc K g) : trunc K (PowerSeries.map φ f) = trunc K (PowerSeries.map φ g) :=
  trunc_eq_of_coeff_eq fun k hk => by rw [coeff_map, coeff_map, coeff_eq_of_trunc_eq h hk]

theorem trunc_subst_X_pow_congr {n : ℕ} (hn : 0 < n) {K : ℕ} {f g : A⟦X⟧} (h : trunc K f = trunc K g) :
    trunc K (f.subst (X ^ n : A⟦X⟧)) = trunc K (g.subst (X ^ n : A⟦X⟧)) :=
  trunc_eq_of_coeff_eq fun k hk => by
    rw [coeff_subst_X_pow hn.ne', coeff_subst_X_pow hn.ne']
    split_ifs with hd
    · rw [coeff_eq_of_trunc_eq h (lt_of_le_of_lt (Nat.div_le_self k n) hk)]
    · rfl

end Trunc

section Scaled

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

theorem scaled_zero (z : A) : scaled p 0 z = 1 := by
  ext k
  rw [coeff_scaled, coeff_one]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_pos (dvd_refl 0), if_pos rfl, Nat.zero_div, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_series, map_one, pow_zero, mul_one]
  · rw [if_neg, if_neg hk.ne']
    rintro ⟨c, hc⟩
    omega

theorem coeff_scaled_self {M : ℕ} (hM : 0 < M) (z : A) : coeff M (scaled p M z) = z := by
  rw [coeff_scaled, if_pos (dvd_refl M), Nat.div_self hM, coeff_one_series, map_one, one_mul, pow_one]

theorem trunc_scaled_eq_one (z : A) {k M : ℕ} (hk : k < M) : trunc (k + 1) (scaled p M z) = 1 := by
  ext j
  rw [coeff_trunc, Polynomial.coeff_one]
  by_cases hj : j < k + 1
  · rw [if_pos hj, coeff_scaled]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [if_pos (dvd_zero _), Nat.zero_div, coeff_zero_eq_constantCoeff_apply, constantCoeff_series,
        map_one, pow_zero, mul_one, if_pos rfl]
    · rw [if_neg, if_neg hj0.ne']
      intro hdvd
      have := Nat.le_of_dvd hj0 hdvd
      omega
  · rw [if_neg hj, if_neg (by omega)]

theorem coeff_mul_scaled_self {P : A⟦X⟧} (hP : constantCoeff P = 1) {M : ℕ} (hM : 0 < M) (z : A) :
    coeff M (P * scaled p M z) = coeff M P + z := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.sub_self, Nat.sub_zero, coeff_zero_eq_constantCoeff_apply, constantCoeff_scaled, hP,
    mul_one, one_mul, coeff_scaled_self p hM]
  have hz : ∑ i ∈ Finset.range M', coeff (i + 1) P * coeff (M' + 1 - (i + 1)) (scaled p (M' + 1) z) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [coeff_scaled, if_neg, mul_zero]
    intro hd
    have h1 : 0 < M' + 1 - (i + 1) := by omega
    have := Nat.le_of_dvd h1 hd
    omega
  rw [hz, zero_add, add_comm]

theorem scaled_mul_left {n : ℕ} (hn : 0 < n) (M : ℕ) (z : A) :
    scaled p (n * M) z = (scaled p M z).subst (X ^ n : A⟦X⟧) := by
  ext k
  rw [coeff_subst_X_pow hn.ne', coeff_scaled, show ∀ x : A, algebraMap A A x = x from fun _ => rfl, coeff_scaled]
  by_cases hnk : n ∣ k
  · obtain ⟨k', rfl⟩ := hnk
    rw [if_pos (dvd_mul_right n k'), Nat.mul_div_cancel_left k' hn]
    by_cases hM : M ∣ k'
    · rw [if_pos (mul_dvd_mul_left n hM), if_pos hM, Nat.mul_div_mul_left _ _ hn]
    · rw [if_neg, if_neg hM]
      intro h
      exact hM ((Nat.mul_dvd_mul_iff_left hn).mp h)
  · rw [if_neg hnk, if_neg]
    intro h
    exact hnk (dvd_trans (dvd_mul_right n M) h)

theorem map_scaled' {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ r, φ (algebraMap ℤ_[p] A r) = algebraMap ℤ_[p] B r) (q : ℕ) (z : A) :
    PowerSeries.map φ (scaled p q z) = scaled p q (φ z) := by
  ext k
  rw [coeff_map, coeff_scaled, coeff_scaled]
  split_ifs
  · rw [map_mul, map_pow, hφ]
  · exact map_zero _

theorem map_prodSeries' {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ r, φ (algebraMap ℤ_[p] A r) = algebraMap ℤ_[p] B r) (z : ℕ → A) (N : ℕ) :
    PowerSeries.map φ (prodSeries p z N) = prodSeries p (fun m => φ (z m)) N := by
  rw [prodSeries, prodSeries, map_prod]
  exact Finset.prod_congr rfl fun m _ => map_scaled' p φ hφ _ _

theorem prodSeries_subst_X_pow (z : ℕ → A) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    (prodSeries p z N).subst (X ^ n : A⟦X⟧) = ∏ m ∈ Finset.range N, scaled p (n * p ^ m) (z m) := by
  rw [prodSeries, ← coe_substAlgHom (HasSubst.X_pow hn.ne'), map_prod]
  exact Finset.prod_congr rfl fun m _ => by rw [coe_substAlgHom, scaled_mul_left p hn]

theorem coeff_prodSeries_of_le (z : ℕ → A) {N N' k : ℕ} (hN : N ≤ N') (hk : k < p ^ N) :
    coeff k (prodSeries p z N') = coeff k (prodSeries p z N) := by
  classical
  rw [prodSeries, prodSeries, ← Finset.prod_range_mul_prod_Ico _ hN]
  have htr : trunc (k + 1) (∏ m ∈ Finset.Ico N N', scaled p (p ^ m) (z m)) = 1 :=
    trunc_prod_eq_one _ _ k fun m hm => trunc_scaled_eq_one p (z m)
      (lt_of_lt_of_le hk (Nat.pow_le_pow_right hp.out.pos (Finset.mem_Ico.mp hm).1))
  rw [← coeff_coe_trunc_of_lt (Nat.lt_succ_self k), ← trunc_mul_trunc, htr, Polynomial.coe_one,
    mul_one, coeff_coe_trunc_of_lt (Nat.lt_succ_self k)]

theorem trunc_prodSeries_of_le (z : ℕ → A) {N N' : ℕ} (hN : N ≤ N') :
    trunc N (prodSeries p z N') = trunc N (prodSeries p z N) :=
  trunc_eq_of_coeff_eq fun k hk => coeff_prodSeries_of_le p z hN (lt_trans hk (Nat.lt_pow_self hp.out.one_lt))

def eprod (z : ℕ → A) (K : ℕ) : A⟦X⟧ := ∏ M ∈ Finset.Ico 1 K, scaled p M (z M)

theorem eprod_def (z : ℕ → A) (K : ℕ) : eprod p z K = ∏ M ∈ Finset.Ico 1 K, scaled p M (z M) := rfl

theorem constantCoeff_eprod (z : ℕ → A) (K : ℕ) : constantCoeff (eprod p z K) = 1 := by
  rw [eprod, map_prod]
  exact Finset.prod_eq_one fun M _ => constantCoeff_scaled p _ _

theorem eprod_succ (z : ℕ → A) {K : ℕ} (hK : 1 ≤ K) :
    eprod p z (K + 1) = eprod p z K * scaled p K (z K) := by
  rw [eprod, eprod, Finset.prod_Ico_succ_top hK]

theorem eprod_one (z : ℕ → A) : eprod p z 1 = 1 := by
  simp [eprod]

theorem coeff_eprod_of_le (z : ℕ → A) {K K' k : ℕ} (hK : K ≤ K') (hk : k < K) :
    coeff k (eprod p z K') = coeff k (eprod p z K) := by
  have h1 : 1 ≤ K := by omega
  rw [eprod, eprod, ← Finset.prod_Ico_consecutive _ h1 hK]
  have htr : trunc (k + 1) (∏ M ∈ Finset.Ico K K', scaled p M (z M)) = 1 :=
    trunc_prod_eq_one _ _ k fun M hM => trunc_scaled_eq_one p (z M) (lt_of_lt_of_le hk (Finset.mem_Ico.mp hM).1)
  rw [← coeff_coe_trunc_of_lt (Nat.lt_succ_self k), ← trunc_mul_trunc, htr, Polynomial.coe_one, mul_one,
    coeff_coe_trunc_of_lt (Nat.lt_succ_self k)]

theorem trunc_eprod_of_le (z : ℕ → A) {K K' : ℕ} (hK : K ≤ K') :
    trunc K (eprod p z K') = trunc K (eprod p z K) :=
  trunc_eq_of_coeff_eq fun k hk => coeff_eprod_of_le p z hK hk

theorem map_eprod {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ r, φ (algebraMap ℤ_[p] A r) = algebraMap ℤ_[p] B r) (z : ℕ → A) (K : ℕ) :
    PowerSeries.map φ (eprod p z K) = eprod p (fun M => φ (z M)) K := by
  rw [eprod, eprod, map_prod]
  exact Finset.prod_congr rfl fun M _ => map_scaled' p φ hφ _ _

theorem eq_of_forall_trunc_eprod_eq (c d : ℕ → A)
    (h : ∀ K, trunc K (eprod p c K) = trunc K (eprod p d K)) : ∀ M, 0 < M → c M = d M := by
  suffices H : ∀ N, ∀ M, M < N → 0 < M → c M = d M from fun M hM => H (M + 1) M (Nat.lt_succ_self M) hM
  intro N
  induction N with
  | zero => intro M hM; omega
  | succ N ih =>
    intro M hMN hM
    rcases Nat.lt_succ_iff_lt_or_eq.mp hMN with hlt | rfl
    · exact ih M hlt hM
    · have hcd : eprod p c M = eprod p d M :=
        Finset.prod_congr rfl fun L hL => by
          rw [ih L (Finset.mem_Ico.mp hL).2 (Finset.mem_Ico.mp hL).1]
      have hK := coeff_eq_of_trunc_eq (h (M + 1)) (Nat.lt_succ_self M)
      rw [eprod_succ p c hM, eprod_succ p d hM, coeff_mul_scaled_self p (constantCoeff_eprod p c M) hM,
        coeff_mul_scaled_self p (constantCoeff_eprod p d M) hM, hcd] at hK
      exact add_left_cancel hK

end Scaled

section Regroup

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

theorem factorization_pow_mul {n m : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) : (p ^ m * n).factorization p = m := by
  rw [Nat.factorization_mul (pow_ne_zero m hp.out.ne_zero) hn.ne', Finsupp.add_apply,
    hp.out.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpn, add_zero]

theorem ordCompl_pow_mul {n : ℕ} (m : ℕ) (hpn : ¬ p ∣ n) : ordCompl[p] (p ^ m * n) = n :=
  Nat.ordCompl_pow_mul_of_not_dvd m hp.out hpn

theorem trunc_prod_subst_prodSeries (y : ℕ → ℕ → A) (N : ℕ) :
    trunc N (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n),
        (prodSeries p (y n) N).subst (X ^ n : A⟦X⟧)) =
      trunc N (eprod p (fun M => y (ordCompl[p] M) (M.factorization p)) N) := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  set S := (Finset.range (k + 1)).filter (fun n => 0 < n ∧ ¬ p ∣ n) with hS
  have h1 : ∀ n ∈ S, (prodSeries p (y n) (k + 1)).subst (X ^ n : A⟦X⟧) =
      ∏ m ∈ Finset.range (k + 1), scaled p (n * p ^ m) (y n m) := fun n hn =>
    prodSeries_subst_X_pow p (y n) (k + 1) (Finset.mem_filter.mp hn).2.1
  rw [Finset.prod_congr rfl h1, ← Finset.prod_product'
    (f := fun n m => scaled p (n * p ^ m) (y n m)),
    trunc_prod_filter (S ×ˢ Finset.range (k + 1)) (fun x => p ^ x.2 * x.1 < k + 1) _ fun x hx hlt =>
      trunc_scaled_eq_one p _ (by rw [mul_comm]; exact Nat.lt_of_succ_le (not_lt.mp hlt)), eprod]
  congr 1
  refine Finset.prod_nbij' (fun x => p ^ x.2 * x.1) (fun M => (ordCompl[p] M, M.factorization p))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxS, -⟩ := Finset.mem_product.mp hx1
    obtain ⟨-, hpos, -⟩ := Finset.mem_filter.mp hxS
    exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt (mul_pos (pow_pos hp.out.pos _) hpos), hx2⟩
  · intro M hM
    obtain ⟨hM1, hM2⟩ := Finset.mem_Ico.mp hM
    have hM0 : M ≠ 0 := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.ordCompl_le M p) hM2)
    · exact Nat.ordCompl_pos p hM0
    · exact Nat.not_dvd_ordCompl hp.out hM0
    · exact Finset.mem_range.mpr (lt_trans (Nat.factorization_lt p hM0) hM2)
    · show p ^ M.factorization p * ordCompl[p] M < k + 1
      rw [Nat.ordProj_mul_ordCompl_eq_self]
      exact hM2
  · intro x hx
    obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxS, -⟩ := Finset.mem_product.mp hx1
    obtain ⟨-, hpos, hpn⟩ := Finset.mem_filter.mp hxS
    show (ordCompl[p] (p ^ x.2 * x.1), (p ^ x.2 * x.1).factorization p) = x
    rw [ordCompl_pow_mul p x.2 hpn, factorization_pow_mul p hpos hpn]
  · intro M hM
    exact Nat.ordProj_mul_ordCompl_eq_self M p
  · intro x hx
    obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxS, -⟩ := Finset.mem_product.mp hx1
    obtain ⟨-, hpos, hpn⟩ := Finset.mem_filter.mp hxS
    show scaled p (x.1 * p ^ x.2) (y x.1 x.2) =
      scaled p (p ^ x.2 * x.1) (y (ordCompl[p] (p ^ x.2 * x.1)) ((p ^ x.2 * x.1).factorization p))
    rw [ordCompl_pow_mul p x.2 hpn, factorization_pow_mul p hpos hpn, mul_comm]

end Regroup

section Tri

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A] (F : A⟦X⟧)

def triQ : ℕ → A⟦X⟧
  | 0 => 1
  | K + 1 => triQ K * scaled p K (coeff K F - coeff K (triQ K))

def tri (K : ℕ) : A := coeff K F - coeff K (triQ p F K)

theorem triQ_zero : triQ p F 0 = 1 := rfl

theorem triQ_succ (K : ℕ) : triQ p F (K + 1) = triQ p F K * scaled p K (tri p F K) := rfl

theorem triQ_eq_prod_range (K : ℕ) : triQ p F K = ∏ M ∈ Finset.range K, scaled p M (tri p F M) := by
  induction K with
  | zero => rw [triQ_zero, Finset.prod_range_zero]
  | succ K ih => rw [triQ_succ, ih, Finset.prod_range_succ]

theorem triQ_eq_eprod (K : ℕ) : triQ p F K = eprod p (tri p F) K := by
  rw [triQ_eq_prod_range, eprod]
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hK, scaled_zero, one_mul]

theorem coeff_eprod_tri (hF : constantCoeff F = 1) : ∀ K k, k < K → coeff k (eprod p (tri p F) K) = coeff k F := by
  intro K
  induction K with
  | zero => intro k hk; omega
  | succ K ih =>
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · rw [coeff_eprod_of_le p _ (Nat.le_succ K) hlt]
      exact ih k hlt
    · rw [heq]
      rcases Nat.eq_zero_or_pos K with hK0 | hK
      · subst hK0
        rw [coeff_zero_eq_constantCoeff, constantCoeff_eprod, hF]
      · rw [eprod_succ p _ hK, coeff_mul_scaled_self p (constantCoeff_eprod p _ K) hK, tri, triQ_eq_eprod]
        ring

theorem trunc_eprod_tri (hF : constantCoeff F = 1) (K : ℕ) : trunc K (eprod p (tri p F) K) = trunc K F :=
  trunc_eq_of_coeff_eq (coeff_eprod_tri p F hF K)

end Tri

section Universal

def wt : ℕ → ℕ := fun j => j + 1

def F₀ : (MvPolynomial ℕ ℤ_[p])⟦X⟧ :=
  PowerSeries.mk fun k => if k = 0 then 1 else MvPolynomial.X (k - 1)

theorem constantCoeff_F₀ : constantCoeff (F₀ p) = 1 := by
  rw [F₀, PowerSeries.constantCoeff_mk, if_pos rfl]

def Graded (G : (MvPolynomial ℕ ℤ_[p])⟦X⟧) : Prop :=
  ∀ k, MvPolynomial.IsWeightedHomogeneous wt (coeff k G) k

theorem graded_one : Graded p 1 := fun k => by
  rw [coeff_one]
  split_ifs with h
  · subst h; exact MvPolynomial.isWeightedHomogeneous_one _ _
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

theorem Graded.mul {G H : (MvPolynomial ℕ ℤ_[p])⟦X⟧} (hG : Graded p G) (hH : Graded p H) :
    Graded p (G * H) := fun k => by
  classical
  rw [coeff_mul]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun ij hij => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← h]
  exact (hG ij.1).mul (hH ij.2)

theorem graded_scaled {M : ℕ} {z : MvPolynomial ℕ ℤ_[p]} (hz : MvPolynomial.IsWeightedHomogeneous wt z M) :
    Graded p (scaled p M z) := fun k => by
  rw [coeff_scaled]
  split_ifs with hd
  · rw [MvPolynomial.algebraMap_eq]
    have h := (hz.pow (k / M)).C_mul (coeff (k / M) (series p))
    have hw : (k / M) • M = k := Nat.div_mul_cancel hd
    rwa [hw] at h
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

theorem graded_F₀ : Graded p (F₀ p) := fun k => by
  rw [F₀, coeff_mk]
  split_ifs with h
  · subst h; exact MvPolynomial.isWeightedHomogeneous_one _ _
  · have h1 := MvPolynomial.isWeightedHomogeneous_X ℤ_[p] wt (k - 1)
    have hk : wt (k - 1) = k := by unfold wt; omega
    rwa [hk] at h1

theorem isWeightedHomogeneous_sub {φ ψ : MvPolynomial ℕ ℤ_[p]} {n : ℕ}
    (h1 : MvPolynomial.IsWeightedHomogeneous wt φ n) (h2 : MvPolynomial.IsWeightedHomogeneous wt ψ n) :
    MvPolynomial.IsWeightedHomogeneous wt (φ - ψ) n := by
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule] at h1 h2 ⊢
  exact Submodule.sub_mem _ h1 h2

theorem graded_triQ : ∀ K, Graded p (triQ p (F₀ p) K)
  | 0 => graded_one p
  | K + 1 => (graded_triQ K).mul p (graded_scaled p (isWeightedHomogeneous_sub p (graded_F₀ p K) (graded_triQ K K)))

theorem isWeightedHomogeneous_tri (K : ℕ) : MvPolynomial.IsWeightedHomogeneous wt (tri p (F₀ p) K) K :=
  isWeightedHomogeneous_sub p (graded_F₀ p K) (graded_triQ p K K)

end Universal

section OverR

variable (R : Type u) [CommRing R] [Algebra ℤ_[p] R]

def cR (M : ℕ) : MvPowerSeries ℕ R :=
  ((MvPolynomial.map (algebraMap ℤ_[p] R) (tri p (F₀ p) M) : MvPolynomial ℕ R) : MvPowerSeries ℕ R)

def piR (n m : ℕ) : MvPowerSeries ℕ R := cR p R (n * p ^ m)

theorem piR_def (n m : ℕ) : piR p R n m = cR p R (n * p ^ m) := rfl

theorem coeff_cR (M : ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (cR p R M) = algebraMap ℤ_[p] R (MvPolynomial.coeff e (tri p (F₀ p) M)) := by
  rw [cR, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

theorem weight_eq_of_coeff_cR_ne_zero {M : ℕ} {e : ℕ →₀ ℕ} (h : MvPowerSeries.coeff e (cR p R M) ≠ 0) :
    Finsupp.weight wt e = M := by
  rw [coeff_cR] at h
  have h' : MvPolynomial.coeff e (tri p (F₀ p) M) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_tri p M h'

theorem constantCoeff_cR {M : ℕ} (hM : 0 < M) : MvPowerSeries.constantCoeff (cR p R M) = 0 := by
  by_contra h
  have h' : MvPowerSeries.coeff (0 : ℕ →₀ ℕ) (cR p R M) ≠ 0 := by
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff]
  have hw := weight_eq_of_coeff_cR_ne_zero p R h'
  simp at hw
  omega

theorem constantCoeff_piR {n : ℕ} (hn : 0 < n) (m : ℕ) : MvPowerSeries.constantCoeff (piR p R n m) = 0 :=
  constantCoeff_cR p R (mul_pos hn (pow_pos hp.out.pos m))

theorem hasSubst_piR {n : ℕ} (hn : 0 < n) : MvPowerSeries.HasSubst (piR p R n) := by
  refine ⟨fun m => by rw [constantCoeff_piR p R hn]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight wt e)).subset ?_
  intro m hm
  have hw := weight_eq_of_coeff_cR_ne_zero p R hm
  show m < Finsupp.weight wt e
  rw [hw]
  calc m < p ^ m := Nat.lt_pow_self hp.out.one_lt
    _ ≤ n * p ^ m := Nat.le_mul_of_pos_left _ hn

def genL : (MvPowerSeries ℕ R)⟦X⟧ :=
  PowerSeries.mk fun k => if k = 0 then (1 : MvPowerSeries ℕ R) else MvPowerSeries.X (k - 1)

theorem constantCoeff_genL : constantCoeff (genL R) = 1 := by
  rw [genL, PowerSeries.constantCoeff_mk, if_pos rfl]

theorem coeff_succ_genL (j : ℕ) : coeff (j + 1) (genL R) = MvPowerSeries.X j := by
  rw [genL, coeff_mk, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]

def ψ : MvPolynomial ℕ ℤ_[p] →+* MvPowerSeries ℕ R :=
  (MvPolynomial.coeToMvPowerSeries.ringHom (σ := ℕ) (R := R)).comp (MvPolynomial.map (algebraMap ℤ_[p] R))

theorem ψ_apply (P : MvPolynomial ℕ ℤ_[p]) :
    ψ p R P = ((MvPolynomial.map (algebraMap ℤ_[p] R) P : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := rfl

theorem algebraMap_mvPowerSeries {τ : Type*} (r : ℤ_[p]) :
    algebraMap ℤ_[p] (MvPowerSeries τ R) r = MvPowerSeries.C (algebraMap ℤ_[p] R r) := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] R (MvPowerSeries τ R), MvPowerSeries.algebraMap_apply]
  simp

theorem ψ_algebraMap (r : ℤ_[p]) : ψ p R (algebraMap ℤ_[p] (MvPolynomial ℕ ℤ_[p]) r) = algebraMap ℤ_[p] (MvPowerSeries ℕ R) r := by
  rw [ψ_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C, MvPolynomial.coe_C, algebraMap_mvPowerSeries]

theorem map_ψ_F₀ : PowerSeries.map (ψ p R) (F₀ p) = genL R := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_map, F₀, genL, coeff_mk, coeff_mk]
  split_ifs
  · exact (ψ p R).map_one
  · rw [ψ_apply, MvPolynomial.map_X, MvPolynomial.coe_X]

theorem trunc_eprod_cR (K : ℕ) : trunc K (eprod p (cR p R) K) = trunc K (genL R) := by
  have h := trunc_map_congr (ψ p R) (trunc_eprod_tri p (F₀ p) (constantCoeff_F₀ p) K)
  rwa [map_eprod p (ψ p R) (ψ_algebraMap p R), map_ψ_F₀] at h

theorem subst_coordR {τ : Type*} (u : ℕ → MvPowerSeries τ R) (j : ℕ) :
    MvPowerSeries.subst u (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p j)) : MvPowerSeries ℕ R) =
      coeff (j + 1) (prodSeries p u (j + 1)) := by
  rw [MvPowerSeries.subst_coe, MvPolynomial.aeval_map_algebraMap, aeval_coord]

theorem trunc_mkFactor (u : ℕ → MvPowerSeries ℕ R) {n : ℕ} (hn : 0 < n) (N : ℕ) :
    trunc N (PowerSeries.mk fun k =>
        if k = 0 then (1 : MvPowerSeries ℕ R)
        else if n ∣ k then
          MvPowerSeries.subst u
            (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p (k / n - 1))) : MvPowerSeries ℕ R)
        else 0) =
      trunc N ((prodSeries p u N).subst (X ^ n : (MvPowerSeries ℕ R)⟦X⟧)) := by
  refine trunc_eq_of_coeff_eq fun k hk => ?_
  rw [coeff_mk, coeff_subst_X_pow hn.ne', show ∀ x : MvPowerSeries ℕ R,
    algebraMap (MvPowerSeries ℕ R) (MvPowerSeries ℕ R) x = x from fun _ => rfl]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [if_pos rfl, if_pos (dvd_zero n), Nat.zero_div, coeff_zero_eq_constantCoeff_apply, constantCoeff_prodSeries]
  · rw [if_neg hk0.ne']
    by_cases hnk : n ∣ k
    · have hq : 1 ≤ k / n := (Nat.one_le_div_iff hn).mpr (Nat.le_of_dvd hk0 hnk)
      rw [if_pos hnk, if_pos hnk, subst_coordR, Nat.sub_add_cancel hq]
      exact (coeff_prodSeries_of_le p u (le_trans (Nat.div_le_self k n) hk.le)
        (Nat.lt_pow_self hp.out.one_lt)).symm
    · rw [if_neg hnk, if_neg hnk]

end OverR

section Assembly

variable (R : Type u) [CommRing R] [Algebra ℤ_[p] R]

theorem ordCompl_mul_pow {n : ℕ} (m : ℕ) (hpn : ¬ p ∣ n) : ordCompl[p] (n * p ^ m) = n := by
  rw [mul_comm]; exact ordCompl_pow_mul p m hpn

theorem factorization_mul_pow {n m : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) : (n * p ^ m).factorization p = m := by
  rw [mul_comm]; exact factorization_pow_mul p hn hpn

theorem piR_ordCompl (M : ℕ) : piR p R (ordCompl[p] M) (M.factorization p) = cR p R M := by
  rw [piR_def, mul_comm, Nat.ordProj_mul_ordCompl_eq_self]

theorem trunc_genL_eq_trunc_prod (N : ℕ) :
    trunc N (PowerSeries.mk fun k => if k = 0 then (1 : MvPowerSeries ℕ R) else MvPowerSeries.X (k - 1)) =
      trunc N (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n),
        PowerSeries.mk fun k =>
          if k = 0 then (1 : MvPowerSeries ℕ R)
          else if n ∣ k then
            MvPowerSeries.subst (piR p R n)
              (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p (k / n - 1))) : MvPowerSeries ℕ R)
          else 0) := by
  symm
  refine (trunc_prod_congr _ fun n hn => trunc_mkFactor p R (piR p R n) (Finset.mem_filter.mp hn).2.1 N).trans ?_
  rw [trunc_prod_subst_prodSeries p (piR p R) N]
  have hfun : (fun M => piR p R (ordCompl[p] M) (M.factorization p)) = cR p R := funext fun M => piR_ordCompl p R M
  rw [hfun]
  exact trunc_eprod_cR p R N

def cordR (m : ℕ) : MvPowerSeries ℕ R :=
  ((MvPolynomial.map (algebraMap ℤ_[p] R) (coord p m) : MvPolynomial ℕ R) : MvPowerSeries ℕ R)

theorem coeff_cordR (n : ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (cordR p R n) = algebraMap ℤ_[p] R (MvPolynomial.coeff e (coord p n)) := by
  rw [cordR, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

theorem weight_eq_of_coeff_cordR_ne_zero {n : ℕ} {e : ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff e (cordR p R n) ≠ 0) :
    Finsupp.weight (fun i : ℕ => p ^ i) e = n + 1 := by
  rw [coeff_cordR] at h
  have h' : MvPolynomial.coeff e (coord p n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_coord p n h'

theorem constantCoeff_cordR (n : ℕ) : MvPowerSeries.constantCoeff (cordR p R n) = 0 := by
  by_contra h
  have h' : MvPowerSeries.coeff (0 : ℕ →₀ ℕ) (cordR p R n) ≠ 0 := by
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff]
  have hw := weight_eq_of_coeff_cordR_ne_zero p R h'
  simp at hw

theorem hasSubst_cordR : MvPowerSeries.HasSubst (cordR p R) := by
  refine ⟨fun n => by rw [constantCoeff_cordR]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun i : ℕ => p ^ i) e)).subset ?_
  intro n hn
  have hw := weight_eq_of_coeff_cordR_ne_zero p R hn
  show n < Finsupp.weight (fun i : ℕ => p ^ i) e
  omega

theorem algHom_algebraMap {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    [Algebra ℤ_[p] B] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] R B] [IsScalarTower ℤ_[p] R C]
    (f : B →ₐ[R] C) (r : ℤ_[p]) : f (algebraMap ℤ_[p] B r) = algebraMap ℤ_[p] C r := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] R B, IsScalarTower.algebraMap_apply ℤ_[p] R C, AlgHom.commutes]

def blkHom (i : Fin 2) : MvPowerSeries ℕ R →+* MvPowerSeries (Fin 2 × ℕ) R :=
  (MvPowerSeries.substAlgHom (WittLaw.hasSubst_blk (R := R) i)).toRingHom

theorem blkHom_apply (i : Fin 2) (f : MvPowerSeries ℕ R) :
    blkHom R i f = MvPowerSeries.subst (WittLaw.blk i) f := by
  unfold blkHom
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPowerSeries.coe_substAlgHom]

theorem blkHom_algebraMap (i : Fin 2) (r : ℤ_[p]) :
    blkHom R i (algebraMap ℤ_[p] (MvPowerSeries ℕ R) r) = algebraMap ℤ_[p] (MvPowerSeries (Fin 2 × ℕ) R) r := by
  unfold blkHom
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  exact algHom_algebraMap p R _ r

def addHom : MvPowerSeries ℕ R →+* MvPowerSeries (Fin 2 × ℕ) R :=
  (MvPowerSeries.substAlgHom (BigWittLaw.hasSubst_addFam R)).toRingHom

theorem addHom_apply (f : MvPowerSeries ℕ R) :
    addHom R f = MvPowerSeries.subst (BigWittLaw.addFam R) f := by
  unfold addHom
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPowerSeries.coe_substAlgHom]

theorem addHom_algebraMap (r : ℤ_[p]) :
    addHom R (algebraMap ℤ_[p] (MvPowerSeries ℕ R) r) = algebraMap ℤ_[p] (MvPowerSeries (Fin 2 × ℕ) R) r := by
  unfold addHom
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  exact algHom_algebraMap p R _ r

def pairHom {n : ℕ} (hn : 0 < n) : MvPowerSeries (Fin 2 × ℕ) R →+* MvPowerSeries (Fin 2 × ℕ) R :=
  (MvPowerSeries.substAlgHom (WittLaw.hasSubst_pairFam (hasSubst_piR p R hn) (constantCoeff_piR p R hn))).toRingHom

theorem pairHom_apply {n : ℕ} (hn : 0 < n) (f : MvPowerSeries (Fin 2 × ℕ) R) :
    pairHom p R hn f = MvPowerSeries.subst (WittLaw.pairFam (piR p R n)) f := by
  unfold pairHom
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPowerSeries.coe_substAlgHom]

theorem pairHom_algebraMap {n : ℕ} (hn : 0 < n) (r : ℤ_[p]) :
    pairHom p R hn (algebraMap ℤ_[p] (MvPowerSeries (Fin 2 × ℕ) R) r) =
      algebraMap ℤ_[p] (MvPowerSeries (Fin 2 × ℕ) R) r := by
  unfold pairHom
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  exact algHom_algebraMap p R _ r

theorem pairHom_X {n : ℕ} (hn : 0 < n) (b : Fin 2) (m : ℕ) :
    pairHom p R hn (MvPowerSeries.X (b, m)) = blkHom R b (piR p R n m) := by
  rw [pairHom_apply, MvPowerSeries.subst_X (WittLaw.hasSubst_pairFam (hasSubst_piR p R hn) (constantCoeff_piR p R hn)),
    WittLaw.pairFam_apply, blkHom_apply]

theorem constantCoeff_map_genL {B : Type*} [CommRing B] (φ : MvPowerSeries ℕ R →+* B) :
    constantCoeff (PowerSeries.map φ (genL R)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, constantCoeff_genL,
    map_one]

theorem coeff_succ_map_blkHom_genL (i : Fin 2) (j : ℕ) :
    coeff (j + 1) (PowerSeries.map (blkHom R i) (genL R)) = MvPowerSeries.X (i, j) := by
  rw [coeff_map, coeff_succ_genL, blkHom_apply, MvPowerSeries.subst_X (WittLaw.hasSubst_blk i), WittLaw.blk_apply]

theorem map_addHom_genL :
    PowerSeries.map (addHom R) (genL R) =
      PowerSeries.map (blkHom R 0) (genL R) * PowerSeries.map (blkHom R 1) (genL R) := by
  have h0 := constantCoeff_map_genL R (blkHom R 0)
  have h1 := constantCoeff_map_genL R (blkHom R 1)
  refine PowerSeries.ext fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, h0, h1, mul_one,
      constantCoeff_map_genL]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [BigWittLaw.coeff_succ_mul h0 h1, coeff_map, coeff_succ_genL, addHom_apply,
      MvPowerSeries.subst_X (BigWittLaw.hasSubst_addFam R), BigWittLaw.addFam_eq]
    simp only [coeff_succ_map_blkHom_genL]

theorem trunc_prodSeries_addFam (K : ℕ) :
    trunc K (prodSeries p (WittLaw.addFam p R) K) =
      trunc K (prodSeries p (WittLaw.blk (R := R) 0) K * prodSeries p (WittLaw.blk (R := R) 1) K) := by
  have h0 := constantCoeff_prodSeries p (WittLaw.blk (R := R) 0) K
  have h1 := constantCoeff_prodSeries p (WittLaw.blk (R := R) 1) K
  have hPc := WittLaw.hasSubst_pairFam (hasSubst_cordR p R) (constantCoeff_cordR p R)
  refine trunc_eq_of_coeff_eq fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, constantCoeff_prodSeries,
      map_mul, h0, h1, mul_one]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hAH := MvFormalGroup.ArtinHasse.subst_addFam_map_coord p R j
    have hL : MvPowerSeries.subst (WittLaw.addFam p R)
        (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p j)) : MvPowerSeries ℕ R) =
        coeff (j + 1) (prodSeries p (WittLaw.addFam p R) (j + 1)) := subst_coordR p R _ j
    have hRHS : MvPowerSeries.subst (WittLaw.pairFam fun m =>
          (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p m)) : MvPowerSeries ℕ R))
        (BigWittLaw.addFam R j) =
        coeff (j + 1) (prodSeries p (WittLaw.blk (R := R) 0) (j + 1)) +
          coeff (j + 1) (prodSeries p (WittLaw.blk (R := R) 1) (j + 1)) +
          ∑ i ∈ Finset.range j, coeff (i + 1) (prodSeries p (WittLaw.blk (R := R) 0) (i + 1)) *
            coeff (j - 1 - i + 1) (prodSeries p (WittLaw.blk (R := R) 1) (j - 1 - i + 1)) := by
      rw [show (fun m => (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p m)) : MvPowerSeries ℕ R)) = cordR p R
        from rfl, BigWittLaw.subst_addFam hPc j]
      simp only [WittLaw.pairFam_apply, cordR, subst_coordR]
    rw [hL, hRHS] at hAH
    rw [coeff_prodSeries_of_le p (WittLaw.addFam p R) hk.le (Nat.lt_pow_self hp.out.one_lt), hAH,
      BigWittLaw.coeff_succ_mul h0 h1,
      coeff_prodSeries_of_le p (WittLaw.blk (R := R) 0) (N := j + 1) hk.le (Nat.lt_pow_self hp.out.one_lt),
      coeff_prodSeries_of_le p (WittLaw.blk (R := R) 1) (N := j + 1) hk.le (Nat.lt_pow_self hp.out.one_lt)]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [coeff_prodSeries_of_le p (WittLaw.blk (R := R) 0) (N := i + 1) (N' := K) (by omega)
        (Nat.lt_pow_self hp.out.one_lt),
      coeff_prodSeries_of_le p (WittLaw.blk (R := R) 1) (N := j - 1 - i + 1) (N' := K) (by omega)
        (Nat.lt_pow_self hp.out.one_lt)]

theorem trunc_prodSeries_pair {n : ℕ} (hn : 0 < n) (K : ℕ) :
    trunc K (prodSeries p (fun m => MvPowerSeries.subst (WittLaw.pairFam (piR p R n)) (WittLaw.addFam p R m)) K) =
      trunc K (prodSeries p (fun m => blkHom R 0 (piR p R n m)) K *
        prodSeries p (fun m => blkHom R 1 (piR p R n m)) K) := by
  have h := trunc_map_congr (pairHom p R hn) (trunc_prodSeries_addFam p R K)
  rw [map_prodSeries' p _ (pairHom_algebraMap p R hn), map_mul, map_prodSeries' p _ (pairHom_algebraMap p R hn),
    map_prodSeries' p _ (pairHom_algebraMap p R hn)] at h
  simp only [WittLaw.blk_apply, pairHom_X] at h
  simp only [pairHom_apply] at h
  exact h

def dFam (n m : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  MvPowerSeries.subst (WittLaw.pairFam (piR p R n)) (WittLaw.addFam p R m)

theorem trunc_eprod_addHom_cR (K : ℕ) :
    trunc K (eprod p (fun M => addHom R (cR p R M)) K) =
      trunc K (PowerSeries.map (blkHom R 0) (genL R) * PowerSeries.map (blkHom R 1) (genL R)) := by
  rw [← map_eprod p (addHom R) (addHom_algebraMap p R), ← map_addHom_genL]
  exact trunc_map_congr _ (trunc_eprod_cR p R K)

theorem trunc_eprod_blkHom_cR (i : Fin 2) (K : ℕ) :
    trunc K (eprod p (fun M => blkHom R i (cR p R M)) K) = trunc K (PowerSeries.map (blkHom R i) (genL R)) := by
  rw [← map_eprod p (blkHom R i) (blkHom_algebraMap p R i)]
  exact trunc_map_congr _ (trunc_eprod_cR p R K)

theorem trunc_eprod_dFam (K : ℕ) :
    trunc K (eprod p (fun M => dFam p R (ordCompl[p] M) (M.factorization p)) K) =
      trunc K (PowerSeries.map (blkHom R 0) (genL R) * PowerSeries.map (blkHom R 1) (genL R)) := by
  classical
  rw [← trunc_prod_subst_prodSeries p (dFam p R) K]
  have hstep : ∀ n ∈ (Finset.range K).filter (fun n => 0 < n ∧ ¬ p ∣ n),
      trunc K ((prodSeries p (dFam p R n) K).subst (X ^ n : (MvPowerSeries (Fin 2 × ℕ) R)⟦X⟧)) =
        trunc K ((prodSeries p (fun m => blkHom R 0 (piR p R n m)) K).subst (X ^ n : (MvPowerSeries (Fin 2 × ℕ) R)⟦X⟧) *
          (prodSeries p (fun m => blkHom R 1 (piR p R n m)) K).subst (X ^ n : (MvPowerSeries (Fin 2 × ℕ) R)⟦X⟧)) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_filter.mp hn).2.1
    rw [← subst_mul (HasSubst.X_pow hn0.ne')]
    exact trunc_subst_X_pow_congr hn0 (trunc_prodSeries_pair p R hn0 K)
  rw [trunc_prod_congr _ hstep, Finset.prod_mul_distrib]
  refine trunc_mul_congr ?_ ?_
  · rw [trunc_prod_subst_prodSeries p (fun n m => blkHom R 0 (piR p R n m)) K]
    have hfun : (fun M => blkHom R 0 (piR p R (ordCompl[p] M) (M.factorization p))) =
        fun M => blkHom R 0 (cR p R M) := funext fun M => by rw [piR_ordCompl]
    rw [hfun]
    exact trunc_eprod_blkHom_cR p R 0 K
  · rw [trunc_prod_subst_prodSeries p (fun n m => blkHom R 1 (piR p R n m)) K]
    have hfun : (fun M => blkHom R 1 (piR p R (ordCompl[p] M) (M.factorization p))) =
        fun M => blkHom R 1 (cR p R M) := funext fun M => by rw [piR_ordCompl]
    rw [hfun]
    exact trunc_eprod_blkHom_cR p R 1 K

theorem addHom_cR_eq_dFam (M : ℕ) (hM : 0 < M) :
    addHom R (cR p R M) = dFam p R (ordCompl[p] M) (M.factorization p) :=
  eq_of_forall_trunc_eprod_eq p (fun M => addHom R (cR p R M))
    (fun M => dFam p R (ordCompl[p] M) (M.factorization p))
    (fun K => (trunc_eprod_addHom_cR p R K).trans (trunc_eprod_dFam p R K).symm) M hM

theorem subst_addFam_piR {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) (k : ℕ) :
    MvPowerSeries.subst (BigWittLaw.addFam R) (piR p R n k) =
      MvPowerSeries.subst (WittLaw.pairFam (piR p R n)) (WittLaw.addFam p R k) := by
  have h := addHom_cR_eq_dFam p R (n * p ^ k) (mul_pos hn (pow_pos hp.out.pos k))
  rw [addHom_apply, ordCompl_mul_pow p k hpn, factorization_mul_pow p hn hpn] at h
  exact h

end Assembly

end SplitSol

theorem solution
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] :
    ∃ π : ℕ → ℕ → MvPowerSeries ℕ R,
      (∀ n, 0 < n → ¬ p ∣ n →
        MvPowerSeries.HasSubst (π n) ∧ (∀ k, MvPowerSeries.constantCoeff (π n k) = 0) ∧
        ∀ k, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (π n k) =
          MvPowerSeries.subst (MvFormalGroup.WittLaw.pairFam (π n)) (MvFormalGroup.WittLaw.addFam p R k)) ∧
      ∀ N : ℕ,
        PowerSeries.trunc N
            (PowerSeries.mk fun k => if k = 0 then (1 : MvPowerSeries ℕ R) else MvPowerSeries.X (k - 1)) =
          PowerSeries.trunc N
            (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n),
              PowerSeries.mk fun k =>
                if k = 0 then (1 : MvPowerSeries ℕ R)
                else if n ∣ k then
                  MvPowerSeries.subst (π n)
                    (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p (k / n - 1))) :
                      MvPowerSeries ℕ R)
                else 0) :=
  ⟨SplitSol.piR p R,
    fun n hn hpn => ⟨SplitSol.hasSubst_piR p R hn, fun k => SplitSol.constantCoeff_piR p R hn k,
      fun k => SplitSol.subst_addFam_piR p R hn hpn k⟩,
    fun N => SplitSol.trunc_genL_eq_trunc_prod p R N⟩

end

end S_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt (solution)
