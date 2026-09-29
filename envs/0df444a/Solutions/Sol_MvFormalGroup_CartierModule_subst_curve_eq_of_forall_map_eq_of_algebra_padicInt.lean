-- Prove2me | solution 1 for MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/13d58cbd-55bc-56d5-969d-eecd46687f39

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse
import Theorems.Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq
import Theorems.Thm_MvFormalGroup_ArtinHasse_subst_addFam_map_coord
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_addFam_verschiebungFam
import Theorems.Thm_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

universe u

open PowerSeries MvFormalGroup MvFormalGroup.ArtinHasse

namespace PTypSol

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

section TOrder

variable {A : Type*} [CommRing A]

def OrdGe (n : ℕ) (f : A⟦X⟧) : Prop := ∀ d, d < n → coeff d f = 0

theorem OrdGe.of_zero (f : A⟦X⟧) : OrdGe 0 f := fun d hd => absurd hd (Nat.not_lt_zero d)

theorem OrdGe.zero (n : ℕ) : OrdGe n (0 : A⟦X⟧) := fun d _ => map_zero _

theorem OrdGe.mono {m n : ℕ} (h : m ≤ n) {f : A⟦X⟧} (hf : OrdGe n f) : OrdGe m f :=
  fun d hd => hf d (lt_of_lt_of_le hd h)

theorem OrdGe.add {n : ℕ} {f g : A⟦X⟧} (hf : OrdGe n f) (hg : OrdGe n g) : OrdGe n (f + g) :=
  fun d hd => by rw [map_add, hf d hd, hg d hd, add_zero]

theorem OrdGe.sub {n : ℕ} {f g : A⟦X⟧} (hf : OrdGe n f) (hg : OrdGe n g) : OrdGe n (f - g) :=
  fun d hd => by rw [map_sub, hf d hd, hg d hd, sub_zero]

theorem OrdGe.mul {m n : ℕ} {f g : A⟦X⟧} (hf : OrdGe m f) (hg : OrdGe n g) : OrdGe (m + n) (f * g) :=
  fun d hd => by
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases h1 : ij.1 < m
    · rw [hf _ h1, zero_mul]
    · have h2 : ij.2 < n := by omega
      rw [hg _ h2, mul_zero]

theorem OrdGe.pow {n : ℕ} {f : A⟦X⟧} (hf : OrdGe n f) (k : ℕ) : OrdGe (k * n) (f ^ k) := by
  induction k with
  | zero => rw [zero_mul, pow_zero]; exact OrdGe.of_zero _
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact ih.mul hf

theorem OrdGe.sum {ι : Type*} (s : Finset ι) {n : ℕ} {f : ι → A⟦X⟧} (h : ∀ i ∈ s, OrdGe n (f i)) :
    OrdGe n (∑ i ∈ s, f i) :=
  fun d hd => by rw [map_sum]; exact Finset.sum_eq_zero fun i hi => h i hi d hd

theorem ordGe_X : OrdGe 1 (X : A⟦X⟧) := fun d hd => by
  interval_cases d; exact coeff_zero_X

theorem OrdGe.constantCoeff {n : ℕ} {f : A⟦X⟧} (hf : OrdGe (n + 1) f) : constantCoeff f = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; exact hf 0 (Nat.succ_pos n)

theorem OrdGe.trunc_eq_zero {n : ℕ} {f : A⟦X⟧} (hf : OrdGe n f) : trunc n f = 0 := by
  ext d
  rw [coeff_trunc, Polynomial.coeff_zero]
  split_ifs with hd
  · exact hf d hd
  · rfl

def SGraded (c : ℕ) (F : (A⟦X⟧)⟦X⟧) : Prop := ∀ i, OrdGe (c * i) (coeff i F)

theorem SGraded.one (c : ℕ) : SGraded c (1 : (A⟦X⟧)⟦X⟧) := fun i => by
  rw [coeff_one]
  split_ifs with h
  · subst h; rw [mul_zero]; exact OrdGe.of_zero _
  · exact OrdGe.zero _

theorem SGraded.mul {c : ℕ} {F G : (A⟦X⟧)⟦X⟧} (hF : SGraded c F) (hG : SGraded c G) : SGraded c (F * G) :=
  fun i => by
    rw [coeff_mul]
    refine OrdGe.sum _ fun ab hab => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have h2 := (hF ab.1).mul (hG ab.2)
    rwa [← mul_add, h] at h2

theorem SGraded.prod {ι : Type*} {c : ℕ} (s : Finset ι) {F : ι → (A⟦X⟧)⟦X⟧} (h : ∀ i ∈ s, SGraded c (F i)) :
    SGraded c (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact SGraded.one c
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end TOrder

section TOrderScaled

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

theorem sGraded_scaled {c q : ℕ} {z : A⟦X⟧} (hz : OrdGe (c * q) z) : SGraded c (scaled p q z) := fun i => by
  rw [coeff_scaled]
  split_ifs with hd
  · have h := hz.pow (i / q)
    have heq : i / q * (c * q) = c * i := by
      rw [mul_comm c q, ← mul_assoc, Nat.div_mul_cancel hd, mul_comm]
    rw [heq] at h
    rw [← zero_add (c * i)]
    exact (OrdGe.of_zero _).mul h
  · exact OrdGe.zero _

theorem sGraded_prodSeries {c : ℕ} {z : ℕ → A⟦X⟧} (hz : ∀ m, OrdGe (c * p ^ m) (z m)) (N : ℕ) :
    SGraded c (prodSeries p z N) :=
  SGraded.prod _ fun m _ => sGraded_scaled p (hz m)

theorem ordGe_of_trunc_eprod_eq {z : ℕ → A⟦X⟧} {F : (A⟦X⟧)⟦X⟧} (hF : SGraded 1 F)
    (h : ∀ K, trunc K (eprod p z K) = trunc K F) : ∀ M, 0 < M → OrdGe M (z M) := by
  suffices H : ∀ N, ∀ M, M < N → 0 < M → OrdGe M (z M) from fun M hM => H (M + 1) M (Nat.lt_succ_self M) hM
  intro N
  induction N with
  | zero => intro M hM; omega
  | succ N ih =>
    intro M hMN hM
    rcases Nat.lt_succ_iff_lt_or_eq.mp hMN with hlt | rfl
    · exact ih M hlt hM
    · have hgr : SGraded 1 (eprod p z M) :=
        SGraded.prod _ fun L hL => sGraded_scaled p (by
          rw [one_mul]; exact ih L (Finset.mem_Ico.mp hL).2 (Finset.mem_Ico.mp hL).1)
      have hK := coeff_eq_of_trunc_eq (h (M + 1)) (Nat.lt_succ_self M)
      rw [eprod_succ p z hM, coeff_mul_scaled_self p (constantCoeff_eprod p z M) hM] at hK
      have hz : z M = coeff M F - coeff M (eprod p z M) := by rw [← hK]; ring
      rw [hz]
      have h1 := hF M
      have h2 := hgr M
      rw [one_mul] at h1 h2
      exact h1.sub h2

end TOrderScaled

section Families

variable {A : Type*} [CommRing A]

def OrdFam (x : ℕ → A⟦X⟧) : Prop := ∀ k, OrdGe (k + 1) (x k)

theorem mvcoeff_eq (d : Unit →₀ ℕ) (f : A⟦X⟧) : MvPowerSeries.coeff d f = coeff (d ()) f := by
  rw [PowerSeries.coeff_def (s := d) rfl]

theorem OrdFam.constantCoeff {x : ℕ → A⟦X⟧} (hx : OrdFam x) (k : ℕ) : MvPowerSeries.constantCoeff (x k) = 0 :=
  (hx k).constantCoeff

theorem hasSubst_of_ordGe {x : ℕ → A⟦X⟧} {o : ℕ → ℕ} (ho : ∀ k, k < o k) (hx : ∀ k, OrdGe (o k) (x k)) :
    MvPowerSeries.HasSubst x := by
  refine ⟨fun k => ?_, fun d => ?_⟩
  · have : MvPowerSeries.constantCoeff (x k) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mvcoeff_eq]
      exact hx k 0 (lt_of_le_of_lt (Nat.zero_le k) (ho k))
    rw [this]; exact IsNilpotent.zero
  · refine (Set.finite_lt_nat (d ())).subset ?_
    intro k hk
    show k < d ()
    by_contra hkd
    exact hk (by rw [mvcoeff_eq]; exact hx k _ (lt_of_le_of_lt (not_lt.mp hkd) (ho k)))

theorem OrdFam.hasSubst {x : ℕ → A⟦X⟧} (hx : OrdFam x) : MvPowerSeries.HasSubst x :=
  hasSubst_of_ordGe (o := fun k => k + 1) (fun k => Nat.lt_succ_self k) hx

def ser (x : ℕ → A⟦X⟧) : (A⟦X⟧)⟦X⟧ := PowerSeries.mk fun k => if k = 0 then 1 else x (k - 1)

theorem constantCoeff_ser (x : ℕ → A⟦X⟧) : constantCoeff (ser x) = 1 := by
  rw [ser, PowerSeries.constantCoeff_mk, if_pos rfl]

theorem coeff_succ_ser (x : ℕ → A⟦X⟧) (k : ℕ) : coeff (k + 1) (ser x) = x k := by
  rw [ser, coeff_mk, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]

theorem OrdFam.sGraded_ser {x : ℕ → A⟦X⟧} (hx : OrdFam x) : SGraded 1 (ser x) := fun i => by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [mul_zero]; exact OrdGe.of_zero _
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [coeff_succ_ser, one_mul]; exact hx k

theorem ordFam_of_sGraded_ser {x : ℕ → A⟦X⟧} (hx : SGraded 1 (ser x)) : OrdFam x := fun k => by
  have := hx (k + 1); rwa [coeff_succ_ser, one_mul] at this

theorem eq_of_ser_eq {x y : ℕ → A⟦X⟧} (h : ser x = ser y) : x = y := funext fun k => by
  rw [← coeff_succ_ser x k, ← coeff_succ_ser y k, h]

def pairG {τ : Type*} (x y : ℕ → MvPowerSeries τ A) : Fin 2 × ℕ → MvPowerSeries τ A :=
  fun im => (![x, y] : Fin 2 → ℕ → MvPowerSeries τ A) im.1 im.2

@[scoped simp] theorem pairG_zero {τ : Type*} (x y : ℕ → MvPowerSeries τ A) (m : ℕ) : pairG x y (0, m) = x m := rfl
@[scoped simp] theorem pairG_one {τ : Type*} (x y : ℕ → MvPowerSeries τ A) (m : ℕ) : pairG x y (1, m) = y m := rfl

theorem hasSubst_pairG {x y : ℕ → A⟦X⟧} (hx : OrdFam x) (hy : OrdFam y) :
    MvPowerSeries.HasSubst (pairG (τ := Unit) x y) := by
  refine ⟨fun im => ?_, fun d => ?_⟩
  · obtain ⟨i, m⟩ := im
    have : MvPowerSeries.constantCoeff (pairG (τ := Unit) x y (i, m)) = 0 := by
      fin_cases i
      · exact hx.constantCoeff m
      · exact hy.constantCoeff m
    rw [this]; exact IsNilpotent.zero
  · refine ((Set.finite_univ (α := Fin 2)).prod (Set.finite_lt_nat (d ()))).subset ?_
    rintro ⟨i, m⟩ him
    refine ⟨Set.mem_univ _, ?_⟩
    show m < d ()
    by_contra hmd
    apply him
    rw [mvcoeff_eq]
    fin_cases i
    · exact hx m _ (lt_of_le_of_lt (not_lt.mp hmd) (Nat.lt_succ_self m))
    · exact hy m _ (lt_of_le_of_lt (not_lt.mp hmd) (Nat.lt_succ_self m))

private def _root_.PTypSol.lsum (x y : ℕ → A⟦X⟧) (k : ℕ) : A⟦X⟧ := MvPowerSeries.subst (pairG (τ := Unit) x y) (BigWittLaw.addFam A k)

p2m_export "PTypSol" "lsum"

theorem ser_lsum {x y : ℕ → A⟦X⟧} (hx : OrdFam x) (hy : OrdFam y) : ser (lsum x y) = ser x * ser y := by
  refine PowerSeries.ext fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_ser,
      constantCoeff_ser, constantCoeff_ser, mul_one]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [coeff_succ_ser, BigWittLaw.coeff_succ_mul (constantCoeff_ser x) (constantCoeff_ser y), lsum,
      BigWittLaw.subst_addFam (hasSubst_pairG hx hy)]
    simp only [pairG_zero, pairG_one, coeff_succ_ser]

theorem OrdFam.lsum {x y : ℕ → A⟦X⟧} (hx : OrdFam x) (hy : OrdFam y) : OrdFam (lsum x y) :=
  ordFam_of_sGraded_ser (by rw [ser_lsum hx hy]; exact hx.sGraded_ser.mul hy.sGraded_ser)

private def _root_.PTypSol.lprod {ι : Type*} (ε : ι → ℕ → A⟦X⟧) (s : Finset ι) (k : ℕ) : A⟦X⟧ := coeff (k + 1) (∏ n ∈ s, ser (ε n))

p2m_export "PTypSol" "lprod"
theorem ser_lprod {ι : Type*} (ε : ι → ℕ → A⟦X⟧) (s : Finset ι) : ser (lprod ε s) = ∏ n ∈ s, ser (ε n) := by
  refine PowerSeries.ext fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, constantCoeff_ser, map_prod]
    exact (Finset.prod_eq_one fun n _ => constantCoeff_ser (ε n)).symm
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [coeff_succ_ser, lprod]

theorem OrdFam.lprod {ι : Type*} {ε : ι → ℕ → A⟦X⟧} (s : Finset ι) (h : ∀ n ∈ s, OrdFam (ε n)) :
    OrdFam (lprod ε s) :=
  ordFam_of_sGraded_ser (by rw [ser_lprod]; exact SGraded.prod _ fun n hn => (h n hn).sGraded_ser)

theorem lprod_empty {ι : Type*} (ε : ι → ℕ → A⟦X⟧) : lprod ε ∅ = fun _ => 0 := funext fun k => by
  rw [lprod, Finset.prod_empty, coeff_one, if_neg (Nat.succ_ne_zero k)]

theorem lprod_insert {ι : Type*} [DecidableEq ι] {ε : ι → ℕ → A⟦X⟧} {s : Finset ι} {n : ι} (hn : n ∉ s)
    (h : ∀ m ∈ insert n s, OrdFam (ε m)) : lprod ε (insert n s) = lsum (ε n) (lprod ε s) := by
  apply eq_of_ser_eq
  rw [ser_lprod, Finset.prod_insert hn, ser_lsum (h n (Finset.mem_insert_self n s))
    (OrdFam.lprod s fun m hm => h m (Finset.mem_insert_of_mem hm)), ser_lprod]

theorem trunc_subst_congr {x y : ℕ → A⟦X⟧} (hx : MvPowerSeries.HasSubst x) (hy : MvPowerSeries.HasSubst y)
    {N : ℕ} (h : ∀ k, trunc N (x k) = trunc N (y k)) (f : MvPowerSeries ℕ A) :
    trunc N (MvPowerSeries.subst x f) = trunc N (MvPowerSeries.subst y f) := by
  classical
  refine trunc_eq_of_coeff_eq fun i hi => ?_
  rw [PowerSeries.coeff_def (s := Finsupp.single () i) (Finsupp.single_eq_same),
    MvPowerSeries.coeff_subst hx, MvPowerSeries.coeff_subst hy]
  refine finsum_congr fun d => ?_
  congr 1
  rw [← PowerSeries.coeff_def (s := Finsupp.single () i) (Finsupp.single_eq_same), Finsupp.prod, Finsupp.prod]
  apply coeff_eq_of_trunc_eq _ hi
  refine trunc_prod_congr _ fun s _ => ?_
  rw [← trunc_trunc_pow, h s, trunc_trunc_pow]

theorem subst_zero_family {f : MvPowerSeries ℕ A} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : ℕ => (0 : A⟦X⟧)) f = 0 := by
  classical
  have h0 : MvPowerSeries.HasSubst (fun _ : ℕ => (0 : A⟦X⟧)) :=
    ⟨fun _ => by rw [map_zero]; exact IsNilpotent.zero, fun d => by simp⟩
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_subst h0, map_zero, finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra! hc
      exact hd (Finsupp.ext hc)
    have : (d.prod fun _ e => (0 : A⟦X⟧) ^ e) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi) (zero_pow hi)
    rw [this, map_zero, smul_zero]

theorem eq_of_forall_trunc_eq {f g : A⟦X⟧} (h : ∀ N, trunc N f = trunc N g) : f = g :=
  PowerSeries.ext fun i => coeff_eq_of_trunc_eq (h (i + 1)) (Nat.lt_succ_self i)

end Families

section OverR

variable (R : Type u) [CommRing R] [Algebra ℤ_[p] R]

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

theorem subst_cordR {τ : Type*} (u : ℕ → MvPowerSeries τ R) (j : ℕ) :
    MvPowerSeries.subst u (cordR p R j) = coeff (j + 1) (prodSeries p u (j + 1)) := by
  rw [cordR, MvPowerSeries.subst_coe, MvPolynomial.aeval_map_algebraMap, aeval_coord]

theorem trunc_mk_eq_trunc_subst_prodSeries {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (v : ℕ → B) (c : ℕ → B)
    (hc : ∀ j, c j = coeff (j + 1) (prodSeries p v (j + 1))) {n : ℕ} (hn : 0 < n) (N : ℕ) :
    trunc N (PowerSeries.mk fun k => if k = 0 then (1 : B) else if n ∣ k then c (k / n - 1) else 0) =
      trunc N ((prodSeries p v N).subst (X ^ n : B⟦X⟧)) := by
  refine trunc_eq_of_coeff_eq fun k hk => ?_
  rw [coeff_mk, coeff_subst_X_pow hn.ne', show ∀ x : B, algebraMap B B x = x from fun _ => rfl]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [if_pos rfl, if_pos (dvd_zero n), Nat.zero_div, coeff_zero_eq_constantCoeff_apply, constantCoeff_prodSeries]
  · rw [if_neg hk0.ne']
    by_cases hnk : n ∣ k
    · have hq : 1 ≤ k / n := (Nat.one_le_div_iff hn).mpr (Nat.le_of_dvd hk0 hnk)
      rw [if_pos hnk, if_pos hnk, hc, Nat.sub_add_cancel hq]
      exact (coeff_prodSeries_of_le p v (le_trans (Nat.div_le_self k n) hk.le)
        (Nat.lt_pow_self hp.out.one_lt)).symm
    · rw [if_neg hnk, if_neg hnk]

def wFam (n k : ℕ) : MvPowerSeries ℕ R := if n ∣ k + 1 then cordR p R ((k + 1) / n - 1) else 0

def vFam (n k : ℕ) : MvPowerSeries ℕ R := if n ∣ k + 1 then MvPowerSeries.X ((k + 1) / n - 1) else 0

theorem constantCoeff_wFam (n k : ℕ) : MvPowerSeries.constantCoeff (wFam p R n k) = 0 := by
  unfold wFam
  split_ifs
  · exact constantCoeff_cordR p R _
  · exact map_zero _

theorem hasSubst_wFam {n : ℕ} (hn : 0 < n) : MvPowerSeries.HasSubst (wFam p R n) := by
  refine ⟨fun k => by rw [constantCoeff_wFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (n * Finsupp.weight (fun i : ℕ => p ^ i) e)).subset ?_
  intro k hk
  show k ≤ n * Finsupp.weight (fun i : ℕ => p ^ i) e
  have hk' : MvPowerSeries.coeff e (wFam p R n k) ≠ 0 := hk
  unfold wFam at hk'
  split_ifs at hk' with hd
  · have hw := weight_eq_of_coeff_cordR_ne_zero p R hk'
    obtain ⟨q, hq⟩ := hd
    have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
    rw [hw, hq, Nat.mul_div_cancel_left q hn, Nat.sub_add_cancel hq1, ← hq]
    omega
  · exact absurd (map_zero _) hk'

theorem constantCoeff_vFam (n k : ℕ) : MvPowerSeries.constantCoeff (vFam R n k) = 0 := by
  unfold vFam
  split_ifs
  · exact MvPowerSeries.constantCoeff_X _
  · exact map_zero _

theorem hasSubst_vFam {n : ℕ} (hn : 0 < n) : MvPowerSeries.HasSubst (vFam R n) := by
  classical
  refine ⟨fun j => by rw [constantCoeff_vFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (n * Finsupp.weight (fun i : ℕ => i + 1) e)).subset ?_
  intro j hj
  have hj' : MvPowerSeries.coeff e (vFam R n j) ≠ 0 := hj
  unfold vFam at hj'
  split_ifs at hj' with hd
  · rw [MvPowerSeries.coeff_X] at hj'
    by_cases he : e = Finsupp.single ((j + 1) / n - 1) 1
    · show j ≤ n * Finsupp.weight (fun i : ℕ => i + 1) e
      obtain ⟨q, hq⟩ := hd
      have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
      rw [he, Finsupp.weight_single, hq, Nat.mul_div_cancel_left q hn, smul_eq_mul, one_mul,
        Nat.sub_add_cancel hq1, ← hq]
      omega
    · rw [if_neg he] at hj'
      exact absurd rfl hj'
  · exact absurd (map_zero _) hj'

theorem wFam_eq_subst_vFam (n k : ℕ) : wFam p R n k = MvPowerSeries.subst (cordR p R) (vFam R n k) := by
  unfold wFam vFam
  split_ifs with hd
  · rw [MvPowerSeries.subst_X (hasSubst_cordR p R)]
  · rw [← MvPowerSeries.coe_substAlgHom (hasSubst_cordR p R), map_zero]

theorem subst_addFam_wFam {n : ℕ} (hn : 0 < n) (k : ℕ) :
    MvPowerSeries.subst (WittLaw.addFam p R) (wFam p R n k) =
      MvPowerSeries.subst (WittLaw.pairFam (wFam p R n)) (BigWittLaw.addFam R k) := by
  have hC := hasSubst_cordR p R
  have hC0 := constantCoeff_cordR p R
  have hPc := WittLaw.hasSubst_pairFam hC hC0
  have hV := hasSubst_vFam R hn
  have hV0 := constantCoeff_vFam R n
  have hPv := WittLaw.hasSubst_pairFam hV hV0
  have hAH : ∀ m, MvPowerSeries.subst (WittLaw.addFam p R) (cordR p R m) =
      MvPowerSeries.subst (WittLaw.pairFam (cordR p R)) (BigWittLaw.addFam R m) :=
    fun m => MvFormalGroup.ArtinHasse.subst_addFam_map_coord p R m
  have hVER : ∀ j, MvPowerSeries.subst (BigWittLaw.addFam R) (vFam R n j) =
      MvPowerSeries.subst (WittLaw.pairFam (vFam R n)) (BigWittLaw.addFam R j) :=
    fun j => MvFormalGroup.BigWittLaw.subst_addFam_verschiebungFam R n hn j
  calc MvPowerSeries.subst (WittLaw.addFam p R) (wFam p R n k)
      = MvPowerSeries.subst (WittLaw.addFam p R) (MvPowerSeries.subst (cordR p R) (vFam R n k)) := by
        rw [wFam_eq_subst_vFam]
    _ = MvPowerSeries.subst (fun m => MvPowerSeries.subst (WittLaw.addFam p R) (cordR p R m)) (vFam R n k) :=
        MvPowerSeries.subst_comp_subst_apply hC (WittLaw.hasSubst_addFam p R) _
    _ = MvPowerSeries.subst (fun m => MvPowerSeries.subst (WittLaw.pairFam (cordR p R)) (BigWittLaw.addFam R m))
          (vFam R n k) := by rw [funext hAH]
    _ = MvPowerSeries.subst (WittLaw.pairFam (cordR p R)) (MvPowerSeries.subst (BigWittLaw.addFam R) (vFam R n k)) :=
        (MvPowerSeries.subst_comp_subst_apply (BigWittLaw.hasSubst_addFam R) hPc _).symm
    _ = MvPowerSeries.subst (WittLaw.pairFam (cordR p R))
          (MvPowerSeries.subst (WittLaw.pairFam (vFam R n)) (BigWittLaw.addFam R k)) := by rw [hVER]
    _ = MvPowerSeries.subst (fun im => MvPowerSeries.subst (WittLaw.pairFam (cordR p R)) (WittLaw.pairFam (vFam R n) im))
          (BigWittLaw.addFam R k) := MvPowerSeries.subst_comp_subst_apply hPv hPc _
    _ = MvPowerSeries.subst (WittLaw.pairFam (wFam p R n)) (BigWittLaw.addFam R k) := by
        congr 1
        funext im
        obtain ⟨i, m⟩ := im
        rw [WittLaw.pairFam_apply, WittLaw.subst_pairFam_subst_blk hC hC0 i, ← wFam_eq_subst_vFam,
          WittLaw.pairFam_apply]

variable {d : ℕ} (Φ : MvFormalGroup d R)

def GinBlk (i : Fin 2) (G : Fin d → MvPowerSeries ℕ R) : Fin d → MvPowerSeries (Fin 2 × ℕ) R :=
  fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l)

theorem constantCoeff_GinBlk (i : Fin 2) {G : Fin d → MvPowerSeries ℕ R}
    (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0) (l : Fin d) :
    MvPowerSeries.constantCoeff (GinBlk R i G l) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (WittLaw.hasSubst_blk i) (fun m => MvPowerSeries.constantCoeff_X _) (hG0 l)

def cmOfHom (G : Fin d → MvPowerSeries ℕ R) (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hGhom : ∀ j, MvPowerSeries.subst (BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst (Sum.elim (GinBlk R 0 G) (GinBlk R 1 G)) (Φ.toPowerSeries j))
    {n : ℕ} (hn : 0 < n) : CartierModule p Φ where
  toPowerSeries := fun j => MvPowerSeries.subst (wFam p R n) (G j)
  constantCoeff_eq_zero := fun j =>
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_wFam p R hn) (constantCoeff_wFam p R n) (hG0 j)
  subst_eq := by
    intro j
    have hw := hasSubst_wFam p R hn
    have hw0 := constantCoeff_wFam p R n
    have hPw := WittLaw.hasSubst_pairFam hw hw0
    show MvPowerSeries.subst (WittLaw.addFam p R) (MvPowerSeries.subst (wFam p R n) (G j)) =
      MvPowerSeries.subst (Sum.elim (GinBlk R 0 fun l => MvPowerSeries.subst (wFam p R n) (G l))
        (GinBlk R 1 fun l => MvPowerSeries.subst (wFam p R n) (G l))) (Φ.toPowerSeries j)
    rw [MvPowerSeries.subst_comp_subst_apply hw (WittLaw.hasSubst_addFam p R)]
    have hfam : (fun k => MvPowerSeries.subst (WittLaw.addFam p R) (wFam p R n k)) =
        fun k => MvPowerSeries.subst (WittLaw.pairFam (wFam p R n)) (BigWittLaw.addFam R k) :=
      funext (subst_addFam_wFam p R hn)
    rw [hfam, ← MvPowerSeries.subst_comp_subst_apply (BigWittLaw.hasSubst_addFam R) hPw, hGhom j,
      MvFormalGroup.subst_subst_elim Φ (constantCoeff_GinBlk R 0 hG0) (constantCoeff_GinBlk R 1 hG0) hPw j]
    congr 1
    funext s
    rcases s with l | l
    · exact WittLaw.subst_pairFam_subst_blk hw hw0 0 (G l)
    · exact WittLaw.subst_pairFam_subst_blk hw hw0 1 (G l)

@[scoped simp] theorem cmOfHom_toPowerSeries (G : Fin d → MvPowerSeries ℕ R) (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hGhom : ∀ j, MvPowerSeries.subst (BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst (Sum.elim (GinBlk R 0 G) (GinBlk R 1 G)) (Φ.toPowerSeries j))
    {n : ℕ} (hn : 0 < n) (j : Fin d) :
    (cmOfHom p R Φ G hG0 hGhom hn).toPowerSeries j = MvPowerSeries.subst (wFam p R n) (G j) := rfl

theorem subst_lsum_hom {τ : Type*} {x y : ℕ → MvPowerSeries τ R}
    (hx : MvPowerSeries.HasSubst x) (hy : MvPowerSeries.HasSubst y) (hP : MvPowerSeries.HasSubst (pairG x y))
    (G : Fin d → MvPowerSeries ℕ R) (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hGhom : ∀ j, MvPowerSeries.subst (BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst (Sum.elim (GinBlk R 0 G) (GinBlk R 1 G)) (Φ.toPowerSeries j))
    {d' : ℕ} {Φ' : MvFormalGroup d' R} (φ : Φ.Hom Φ') (i : Fin d') :
    MvPowerSeries.subst (fun k => MvPowerSeries.subst (pairG x y) (BigWittLaw.addFam R k))
        (MvPowerSeries.subst G (φ.toPowerSeries i)) =
      MvPowerSeries.subst
        (Sum.elim (fun j => MvPowerSeries.subst x (MvPowerSeries.subst G (φ.toPowerSeries j)))
          fun j => MvPowerSeries.subst y (MvPowerSeries.subst G (φ.toPowerSeries j)))
        (Φ'.toPowerSeries i) := by
  have hsG : MvPowerSeries.HasSubst G := MvPowerSeries.hasSubst_of_constantCoeff_zero hG0
  have ha := constantCoeff_GinBlk R 0 hG0
  have hb := constantCoeff_GinBlk R 1 hG0
  rw [← MvPowerSeries.subst_comp_subst_apply (BigWittLaw.hasSubst_addFam R) hP,
    MvPowerSeries.subst_comp_subst_apply hsG (BigWittLaw.hasSubst_addFam R),
    show (fun j => MvPowerSeries.subst (BigWittLaw.addFam R) (G j)) =
      fun j => MvPowerSeries.subst (Sum.elim (GinBlk R 0 G) (GinBlk R 1 G)) (Φ.toPowerSeries j) from funext hGhom,
    φ.subst_subst_elim ha hb i,
    MvFormalGroup.subst_subst_elim Φ'
      (fun j => MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha
        (φ.constantCoeff_eq_zero j))
      (fun j => MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hb) hb
        (φ.constantCoeff_eq_zero j)) hP i]
  congr 1
  funext s
  rcases s with j | j
  · show MvPowerSeries.subst (pairG x y) (MvPowerSeries.subst (GinBlk R 0 G) (φ.toPowerSeries j)) =
      MvPowerSeries.subst x (MvPowerSeries.subst G (φ.toPowerSeries j))
    rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) hP,
      MvPowerSeries.subst_comp_subst_apply hsG hx]
    congr 1
    funext l
    show MvPowerSeries.subst (pairG x y) (MvPowerSeries.subst
      (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l)) = MvPowerSeries.subst x (G l)
    have hB0 : MvPowerSeries.HasSubst (fun m => (MvPowerSeries.X ((0 : Fin 2), m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
      WittLaw.hasSubst_blk 0
    rw [MvPowerSeries.subst_comp_subst_apply hB0 hP]
    congr 1
    funext m
    rw [MvPowerSeries.subst_X hP]
    rfl
  · show MvPowerSeries.subst (pairG x y) (MvPowerSeries.subst (GinBlk R 1 G) (φ.toPowerSeries j)) =
      MvPowerSeries.subst y (MvPowerSeries.subst G (φ.toPowerSeries j))
    rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hb) hP,
      MvPowerSeries.subst_comp_subst_apply hsG hy]
    congr 1
    funext l
    show MvPowerSeries.subst (pairG x y) (MvPowerSeries.subst
      (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l)) = MvPowerSeries.subst y (G l)
    have hB1 : MvPowerSeries.HasSubst (fun m => (MvPowerSeries.X ((1 : Fin 2), m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
      WittLaw.hasSubst_blk 1
    rw [MvPowerSeries.subst_comp_subst_apply hB1 hP]
    congr 1
    funext m
    rw [MvPowerSeries.subst_X hP]
    rfl

end OverR

section Main

variable (R : Type u) [CommRing R] [Algebra ℤ_[p] R]

theorem ordCompl_mul_pow {n : ℕ} (m : ℕ) (hpn : ¬ p ∣ n) : ordCompl[p] (n * p ^ m) = n := by
  rw [mul_comm]; exact ordCompl_pow_mul p m hpn

theorem factorization_mul_pow {n m : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) : (n * p ^ m).factorization p = m := by
  rw [mul_comm]; exact factorization_pow_mul p hn hpn

def curveHom : MvPowerSeries ℕ R →+* R⟦X⟧ :=
  (MvPowerSeries.substAlgHom (CartierModule.hasSubst_curveFam (R := R))).toRingHom

theorem curveHom_apply (f : MvPowerSeries ℕ R) :
    curveHom R f = MvPowerSeries.subst (CartierModule.curveFam R) f := by
  unfold curveHom
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPowerSeries.coe_substAlgHom]

theorem ordFam_curveFam : OrdFam (CartierModule.curveFam R) := fun k => by
  cases k with
  | zero => exact (ordGe_X : OrdGe 1 (X : R⟦X⟧))
  | succ k => exact OrdGe.zero _

def genL : (MvPowerSeries ℕ R)⟦X⟧ :=
  PowerSeries.mk fun k => if k = 0 then (1 : MvPowerSeries ℕ R) else MvPowerSeries.X (k - 1)

def factor (πn : ℕ → MvPowerSeries ℕ R) (n : ℕ) : (MvPowerSeries ℕ R)⟦X⟧ :=
  PowerSeries.mk fun k =>
    if k = 0 then (1 : MvPowerSeries ℕ R)
    else if n ∣ k then
      MvPowerSeries.subst πn (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p (k / n - 1))) : MvPowerSeries ℕ R)
    else 0

variable (π : ℕ → ℕ → MvPowerSeries ℕ R)

def piU (n m : ℕ) : R⟦X⟧ := MvPowerSeries.subst (CartierModule.curveFam R) (π n m)

def eU (n k : ℕ) : R⟦X⟧ :=
  if n ∣ k + 1 then MvPowerSeries.subst (piU R π n) (cordR p R ((k + 1) / n - 1)) else 0

theorem subst_piU_wFam {n : ℕ} (h : MvPowerSeries.HasSubst (piU R π n)) (k : ℕ) :
    MvPowerSeries.subst (piU R π n) (wFam p R n k) = eU p R π n k := by
  unfold wFam eU
  split_ifs
  · rfl
  · rw [← MvPowerSeries.coe_substAlgHom h, map_zero]

theorem map_curveHom_genL : PowerSeries.map (curveHom R) (genL R) = ser (CartierModule.curveFam R) := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_map, genL, ser, coeff_mk, coeff_mk]
  split_ifs with hk
  · exact (curveHom R).map_one
  · rw [curveHom_apply, MvPowerSeries.subst_X CartierModule.hasSubst_curveFam]

theorem map_curveHom_factor {n : ℕ} (hπn : MvPowerSeries.HasSubst (π n)) :
    PowerSeries.map (curveHom R) (factor p R (π n) n) = ser (eU p R π n) := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_map, factor, ser, coeff_mk, coeff_mk]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_pos rfl, if_pos rfl, map_one]
  · rw [if_neg hk.ne', if_neg hk.ne', eU, Nat.sub_add_cancel hk]
    split_ifs with hd
    · rw [curveHom_apply, MvPowerSeries.subst_comp_subst_apply hπn CartierModule.hasSubst_curveFam]
      rfl
    · exact map_zero _

variable (hS : ∀ n, 0 < n → ¬ p ∣ n → MvPowerSeries.HasSubst (π n))
  (hprod : ∀ N : ℕ, trunc N (genL R) =
    trunc N (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n), factor p R (π n) n))
include hS hprod

theorem trunc_ser_curveFam (N : ℕ) :
    trunc N (ser (CartierModule.curveFam R)) =
      trunc N (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n), ser (eU p R π n)) := by
  have h := trunc_map_congr (curveHom R) (hprod N)
  rw [map_curveHom_genL, map_prod] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun n hn => ?_
  obtain ⟨-, hn0, hpn⟩ := Finset.mem_filter.mp hn
  exact map_curveHom_factor p R π (hS n hn0 hpn)

theorem ordGe_piU {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) (m : ℕ) : OrdGe (n * p ^ m) (piU R π n m) := by
  have key : ∀ K, trunc K (eprod p (fun M => piU R π (ordCompl[p] M) (M.factorization p)) K) =
      trunc K (ser (CartierModule.curveFam R)) := by
    intro K
    rw [← trunc_prod_subst_prodSeries p (piU R π) K, trunc_ser_curveFam p R π hS hprod K]
    refine trunc_prod_congr _ fun n hn => ?_
    obtain ⟨-, hn0, -⟩ := Finset.mem_filter.mp hn
    have hser : ser (eU p R π n) = PowerSeries.mk fun k =>
        if k = 0 then (1 : R⟦X⟧)
        else if n ∣ k then MvPowerSeries.subst (piU R π n) (cordR p R (k / n - 1)) else 0 := by
      refine PowerSeries.ext fun k => ?_
      rw [ser, coeff_mk, coeff_mk]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hk.ne', if_neg hk.ne', eU, Nat.sub_add_cancel hk]
    rw [hser]
    exact (trunc_mk_eq_trunc_subst_prodSeries p (piU R π n) _ (fun j => subst_cordR p R (piU R π n) j) hn0 K).symm
  have hord := ordGe_of_trunc_eprod_eq p (ordFam_curveFam R).sGraded_ser key (n * p ^ m)
    (mul_pos hn (pow_pos hp.out.pos m))
  beta_reduce at hord
  rwa [ordCompl_mul_pow p m hpn, factorization_mul_pow p hn hpn] at hord

theorem hasSubst_piU {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) : MvPowerSeries.HasSubst (piU R π n) :=
  hasSubst_of_ordGe (o := fun m => n * p ^ m)
    (fun m => lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) (Nat.le_mul_of_pos_left _ hn))
    (ordGe_piU p R π hS hprod hn hpn)

theorem ordFam_eU {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) : OrdFam (eU p R π n) := fun k => by
  unfold eU
  split_ifs with hd
  · rw [subst_cordR]
    have hq : 1 ≤ (k + 1) / n := (Nat.one_le_div_iff hn).mpr (Nat.le_of_dvd (Nat.succ_pos k) hd)
    have hgr := sGraded_prodSeries p (c := n) (z := piU R π n)
      (fun m => ordGe_piU p R π hS hprod hn hpn m) ((k + 1) / n - 1 + 1)
    have h2 := hgr ((k + 1) / n - 1 + 1)
    rw [Nat.sub_add_cancel hq, Nat.mul_div_cancel' hd] at h2
    rw [Nat.sub_add_cancel hq]
    exact h2
  · exact OrdGe.zero _

end Main

end PTypSol
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt.PTypSol"

open PTypSol in

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f)
    (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (k : Fin d') :
    MvPowerSeries.subst γ (φ.toPowerSeries k) = MvPowerSeries.subst γ (ψ.toPowerSeries k) := by
  obtain ⟨G, hG0, hGhom, hGγ⟩ := MvFormalGroup.BigWittLaw.exists_hom_subst_curveFam_eq Φ γ hγ
  obtain ⟨π, hπ, hprod⟩ :=
    MvFormalGroup.BigWittLaw.exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt p R
  have hS : ∀ n, 0 < n → ¬ p ∣ n → MvPowerSeries.HasSubst (π n) := fun n hn hpn => (hπ n hn hpn).1
  have hprod' : ∀ N : ℕ, PowerSeries.trunc N (genL R) =
      PowerSeries.trunc N (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n), factor p R (π n) n) :=
    hprod
  have hsG : MvPowerSeries.HasSubst G := MvPowerSeries.hasSubst_of_constantCoeff_zero hG0
  have hu : MvPowerSeries.HasSubst (MvFormalGroup.CartierModule.curveFam R) :=
    MvFormalGroup.CartierModule.hasSubst_curveFam
  have hγG : γ = fun j => MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) (G j) :=
    funext fun j => (hGγ j).symm
  rw [hγG, ← MvPowerSeries.subst_comp_subst_apply hsG hu, ← MvPowerSeries.subst_comp_subst_apply hsG hu]
  have hH0 : ∀ (χ : Φ.Hom Φ') (i : Fin d'),
      MvPowerSeries.constantCoeff (MvPowerSeries.subst G (χ.toPowerSeries i)) = 0 := fun χ i =>
    MvPowerSeries.constantCoeff_subst_eq_zero hsG hG0 (χ.constantCoeff_eq_zero i)

  have hE : ∀ n, 0 < n → ¬ p ∣ n → ∀ i,
      MvPowerSeries.subst (eU p R π n) (MvPowerSeries.subst G (φ.toPowerSeries i)) =
        MvPowerSeries.subst (eU p R π n) (MvPowerSeries.subst G (ψ.toPowerSeries i)) := by
    intro n hn hpn i
    have hw := hasSubst_wFam p R hn
    have hpu : MvPowerSeries.HasSubst (piU R π n) := hasSubst_piU p R π hS hprod' hn hpn
    have hf := congrArg (fun f : MvFormalGroup.CartierModule p Φ' => f.toPowerSeries i)
      (h (cmOfHom p R Φ G hG0 hGhom hn))
    change MvPowerSeries.subst (fun j => MvPowerSeries.subst (wFam p R n) (G j)) (φ.toPowerSeries i) =
      MvPowerSeries.subst (fun j => MvPowerSeries.subst (wFam p R n) (G j)) (ψ.toPowerSeries i) at hf
    rw [← MvPowerSeries.subst_comp_subst_apply hsG hw (φ.toPowerSeries i),
      ← MvPowerSeries.subst_comp_subst_apply hsG hw (ψ.toPowerSeries i)] at hf
    have hf2 := congrArg (MvPowerSeries.subst (piU R π n)) hf
    rw [MvPowerSeries.subst_comp_subst_apply hw hpu (MvPowerSeries.subst G (φ.toPowerSeries i)),
      MvPowerSeries.subst_comp_subst_apply hw hpu (MvPowerSeries.subst G (ψ.toPowerSeries i))] at hf2
    rwa [show (fun k => MvPowerSeries.subst (piU R π n) (wFam p R n k)) = eU p R π n from
      funext (subst_piU_wFam p R π hpu)] at hf2

  have IND : ∀ s : Finset ℕ, (∀ n ∈ s, 0 < n ∧ ¬ p ∣ n) → ∀ i,
      MvPowerSeries.subst (lprod (eU p R π) s) (MvPowerSeries.subst G (φ.toPowerSeries i)) =
        MvPowerSeries.subst (lprod (eU p R π) s) (MvPowerSeries.subst G (ψ.toPowerSeries i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ i
      rw [lprod_empty, subst_zero_family (hH0 φ i), subst_zero_family (hH0 ψ i)]
    | insert n s hns ih =>
      intro hs i
      have hord : ∀ m ∈ insert n s, OrdFam (eU p R π m) := fun m hm =>
        ordFam_eU p R π hS hprod' (hs m hm).1 (hs m hm).2
      have hx : OrdFam (eU p R π n) := hord n (Finset.mem_insert_self n s)
      have hy : OrdFam (lprod (eU p R π) s) := OrdFam.lprod s fun m hm => hord m (Finset.mem_insert_of_mem hm)
      have ih' := ih fun m hm => hs m (Finset.mem_insert_of_mem hm)
      rw [lprod_insert hns hord]
      show MvPowerSeries.subst (fun k => MvPowerSeries.subst (pairG (eU p R π n) (lprod (eU p R π) s))
          (MvFormalGroup.BigWittLaw.addFam R k)) (MvPowerSeries.subst G (φ.toPowerSeries i)) =
        MvPowerSeries.subst (fun k => MvPowerSeries.subst (pairG (eU p R π n) (lprod (eU p R π) s))
          (MvFormalGroup.BigWittLaw.addFam R k)) (MvPowerSeries.subst G (ψ.toPowerSeries i))
      rw [subst_lsum_hom R Φ hx.hasSubst hy.hasSubst (hasSubst_pairG hx hy) G hG0 hGhom φ i,
        subst_lsum_hom R Φ hx.hasSubst hy.hasSubst (hasSubst_pairG hx hy) G hG0 hGhom ψ i]
      congr 1
      funext s'
      rcases s' with j | j
      · exact hE n (hs n (Finset.mem_insert_self n s)).1 (hs n (Finset.mem_insert_self n s)).2 j
      · exact ih' j

  apply eq_of_forall_trunc_eq
  intro N
  have hSmem : ∀ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n), 0 < n ∧ ¬ p ∣ n := fun n hn =>
    (Finset.mem_filter.mp hn).2
  have hP : OrdFam (lprod (eU p R π) ((Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n))) :=
    OrdFam.lprod _ fun n hn => ordFam_eU p R π hS hprod' (hSmem n hn).1 (hSmem n hn).2
  have hcong : ∀ k', PowerSeries.trunc N (MvFormalGroup.CartierModule.curveFam R k') =
      PowerSeries.trunc N (lprod (eU p R π) ((Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n)) k') := by
    intro k'
    by_cases hk : k' + 1 < N
    · have h1 := coeff_eq_of_trunc_eq (trunc_ser_curveFam p R π hS hprod' N) hk
      rw [coeff_succ_ser, ← ser_lprod, coeff_succ_ser] at h1
      rw [h1]
    · have hN : N ≤ k' + 1 := not_lt.mp hk
      rw [(((ordFam_curveFam R) k').mono hN).trunc_eq_zero, ((hP k').mono hN).trunc_eq_zero]
  rw [trunc_subst_congr hu hP.hasSubst hcong, trunc_subst_congr hu hP.hasSubst hcong,
    IND _ hSmem k]

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt.PTypSol"

end S_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt (solution)
