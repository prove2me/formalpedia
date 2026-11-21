-- Prove2me | solution 1 for MomentSearch.Supplement.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:13:56.281388+00:00
-- url     : https://prove2.me/submissions/6416c7d0-6e5e-4bda-8faf-aa99e93bd0b0

import Mathlib
import Definitions.Def_MomentSearch_Supplement_quantileDist
import Theorems.Thm_MomentSearch_Supplement_theorem_5
import Theorems.Thm_MomentSearch_Supplement_sparse_sketch_hard_fibre
import Theorems.Thm_MomentSearch_Supplement_sparse_support_opt_upper_bound

open scoped ENNReal
open MomentSearch MomentSearch.Supplement

private lemma cdf_mono {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ stdSimplex ℝ (Fin n)) : Monotone (cdf p) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro t _
  split_ifs <;> first | rfl | positivity | exact hp.1 t | omega

private lemma cdf_bounds {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ stdSimplex ℝ (Fin n)) (t : ℕ) : 0 ≤ cdf p t ∧ cdf p t ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> [exact hp.1 i; rfl])
  · calc
      cdf p t ≤ ∑ i, p i := Finset.sum_le_sum (fun i _ => by split_ifs <;> [rfl; exact hp.1 i])
      _ = 1 := hp.2

private lemma quantile_spec {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) (l : Fin q) :
    quantileSketch n q p l < n ∧
      ((l.val + 1 : ℕ) : ℝ) / q ≤ cdf p (quantileSketch n q p l) := by
  change sInf {t : ℕ | t < n ∧ ((l.val + 1 : ℕ) : ℝ) / q ≤ cdf p t} ∈
    {t : ℕ | t < n ∧ ((l.val + 1 : ℕ) : ℝ) / q ≤ cdf p t}
  apply Nat.sInf_mem
  refine ⟨n-1, by omega, ?_⟩
  have hc : cdf p (n-1) = 1 := by
    simpa [cdf, show ∀ i : Fin n, i.val ≤ n-1 from fun i => by omega] using hp.2
  rw [hc]
  apply (div_le_one (by exact_mod_cast hq)).2
  exact_mod_cast l.isLt

private lemma quantile_le_iff {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) (l : Fin q)
    (t : ℕ) (ht : t < n) :
    quantileSketch n q p l ≤ t ↔ ((l.val + 1 : ℕ) : ℝ) / q ≤ cdf p t := by
  constructor
  · intro h
    exact (quantile_spec hn hq hp l).2.trans (cdf_mono hp h)
  · intro h
    exact Nat.sInf_le ⟨ht, h⟩

private lemma quantile_dist_cdf {n q : ℕ} (x : Fin q → ℕ)
    (hx : ∀ l, x l < n) (t : ℕ) :
    cdf (quantileDist n q x) t =
      ((Finset.univ.filter (fun l => x l ≤ t)).card : ℝ) / q := by
  classical
  have hmass (i : Fin n) : quantileDist n q x i =
      ∑ l : Fin q, if x l = i.val then (1 : ℝ) / q else 0 := by
    simp [quantileDist, Finset.sum_ite, div_eq_mul_inv]
  have hswap (i : Fin n) :
      (if i.val ≤ t then ∑ l : Fin q, if x l = i.val then (1 : ℝ) / q else 0 else 0) =
      ∑ l : Fin q, if i.val ≤ t then if x l = i.val then (1 : ℝ) / q else 0 else 0 := by
    by_cases hi : i.val ≤ t <;> simp [hi]
  simp only [cdf, hmass, hswap]
  rw [Finset.sum_comm]
  have ht (l : Fin q) :
      (∑ i : Fin n, if i.val ≤ t then if x l = i.val then (1 : ℝ) / q else 0 else 0) =
        if x l ≤ t then (1 : ℝ) / q else 0 := by
    rw [Finset.sum_eq_single (⟨x l, hx l⟩ : Fin n)]
    · simp
    · intro i _ hi
      have hne : x l ≠ i.val := by intro h; apply hi; exact Fin.ext h.symm
      simp [hne]
    · simp
  simp_rw [ht]
  simp [Finset.sum_ite, div_eq_mul_inv]

private lemma quantile_dist_simplex {n q : ℕ} (hq : 0 < q) (x : Fin q → ℕ)
    (hx : ∀ l, x l < n) : quantileDist n q x ∈ stdSimplex ℝ (Fin n) := by
  constructor
  · intro i; unfold quantileDist; positivity
  · have hc := quantile_dist_cdf x hx n
    have he : cdf (quantileDist n q x) n = ∑ i, quantileDist n q x i := by
      apply Finset.sum_congr rfl; intro i _; simp [show i.val ≤ n by omega]
    rw [he] at hc
    simpa [show ∀ l, x l ≤ n from fun l => (hx l).le, ne_of_gt hq] using hc

private lemma quantile_approx {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    quantileDist n q (quantileSketch n q p) ∈ stdSimplex ℝ (Fin n) ∧
      kolDist p (quantileDist n q (quantileSketch n q p)) ≤ 1 / q := by
  classical
  have hx := fun l => (quantile_spec hn hq hp l).1
  refine ⟨quantile_dist_simplex hq _ hx, ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply ciSup_le
  intro t
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb := cdf_bounds hp t.val
  have hf : ⌊cdf p t.val * q⌋₊ ≤ q := by
    apply Nat.floor_le_of_le
    nlinarith
  have he : (Finset.univ.filter (fun l : Fin q => quantileSketch n q p l ≤ t.val)) =
      Finset.univ.filter (fun l : Fin q => l.val < ⌊cdf p t.val * q⌋₊) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [quantile_le_iff hn hq hp l _ t.isLt, div_le_iff₀ hqR]
    rw [← Nat.le_floor_iff (mul_nonneg hb.1 hqR.le)]
    omega
  rw [quantile_dist_cdf _ hx, he, Fin.card_filter_val_lt, min_eq_right hf]
  have hlo := Nat.floor_le (mul_nonneg hb.1 hqR.le)
  have hhi := Nat.lt_floor_add_one (cdf p t.val * q)
  rw [abs_of_nonneg (by apply sub_nonneg.mpr; exact (div_le_iff₀ hqR).2 hlo)]
  apply (le_div_iff₀ hqR).2
  have heq : (cdf p t.val - (⌊cdf p t.val * q⌋₊ : ℝ) / q) * q =
      cdf p t.val * q - ⌊cdf p t.val * q⌋₊ := by field_simp
  rw [heq]
  linarith

private lemma quantile_image_bound (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    (quantileSketch n q '' stdSimplex ℝ (Fin n)).Finite ∧
      (quantileSketch n q '' stdSimplex ℝ (Fin n)).ncard ≤ n ^ q := by
  classical
  let f : (Fin q → Fin n) → (Fin q → ℕ) := fun x l => (x l).val
  have hs : quantileSketch n q '' stdSimplex ℝ (Fin n) ⊆ Set.range f := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨fun l => ⟨quantileSketch n q p l, (quantile_spec hn hq hp l).1⟩, rfl⟩
  refine ⟨(Set.finite_range f).subset hs, (Set.ncard_le_ncard hs (Set.finite_range f)).trans ?_⟩
  have hc := Set.ncard_image_le (s := Set.univ) (f := f)
  simpa [Set.image_univ, Set.ncard_univ, Nat.card_fun] using hc

private lemma quantile_bits (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    (quantileSketch n ⌈(n : ℝ) ^ ε⌉₊ '' stdSimplex ℝ (Fin n)).Finite ∧
    ∃ b : ℕ, (b : ℝ) ≤ 4 * (n : ℝ) ^ ε * Real.logb 2 n ∧
      (quantileSketch n ⌈(n : ℝ) ^ ε⌉₊ '' stdSimplex ℝ (Fin n)).ncard ≤ 2 ^ b := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hq : 0 < ⌈(n : ℝ) ^ ε⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  obtain ⟨hfin, hcard⟩ := quantile_image_bound n ⌈(n : ℝ) ^ ε⌉₊ (by omega) hq
  have hlog : 1 ≤ Real.logb 2 n := by
    simpa using (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 2) hnR)
  have hqc : (⌈(n : ℝ) ^ ε⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ ε := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ (n : ℝ) ^ ε)
    linarith
  have hlc : (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n := by
    have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.logb 2 n)
    rw [show ⌈Real.logb 2 (n : ℝ)⌉₊ = Nat.clog 2 n from Real.natCeil_logb_natCast 2 n] at hc
    linarith
  refine ⟨hfin, ⌈(n : ℝ) ^ ε⌉₊ * Nat.clog 2 n, ?_, ?_⟩
  · push_cast
    nlinarith [mul_le_mul hqc hlc (Nat.cast_nonneg (Nat.clog 2 n)) (by linarith)]
  · calc
      _ ≤ n ^ ⌈(n : ℝ) ^ ε⌉₊ := hcard
      _ ≤ (2 ^ Nat.clog 2 n) ^ ⌈(n : ℝ) ^ ε⌉₊ := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) n) _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]

private lemma lower_ball (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (he : 0 < ε)
    (scale : 1 ≤ ε * Real.logb 2 n) (δ : ℝ) (hδ : (n:ℝ)^(-ε) ≤ δ) :
    ENNReal.ofReal ((1/24) / ε) ≤ approxFactor (kolCollection n δ) := by
  classical
  let m := ⌈(n:ℝ)^ε⌉₊
  let q := 8*m
  have np : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have a : 1 ≤ (n:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) he.le
  have mle : (n:ℝ)^ε ≤ m := Nat.le_ceil _
  have mp : 0 < m := by exact_mod_cast (zero_lt_one.trans_le (a.trans mle))
  have qp : 0 < q := by dsimp [q]; omega
  have lp : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ n))
  obtain ⟨hfin,k,hk,hcount⟩ := quantile_bits n hn ε he
  have budget : (k:ℝ) ≤ (q:ℝ)/2 * Real.logb 2 n := by
    apply hk.trans
    dsimp [q]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right mle lp]
  obtain ⟨x,⟨p₀,hp₀,ex⟩,hard⟩ := sparse_sketch_hard_fibre hn qp _ (quantileSketch n m) budget hfin hcount
  let π := quantileDist n m x
  have hπ : π ∈ stdSimplex ℝ (Fin n) := by
    dsimp [π]; rw [← ex]; exact (quantile_approx (by omega) mp hp₀).1
  have qm : (q:ℝ) ≤ 16*(n:ℝ)^ε := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans a)
    change (m:ℝ) < _ at h
    dsimp [q]; push_cast; linarith
  have lq := Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num) (by exact_mod_cast qp : 0 < (q:ℝ)) qm
  rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos np ε).ne',
    Real.logb_rpow_eq_mul_logb_of_pos np] at lq
  have l16 : Real.logb 2 16 = 4 := by
    rw [show (16:ℝ) = 2^(4:ℕ) by norm_num,Real.logb_pow]; norm_num
  rw [l16] at lq
  unfold approxFactor
  apply le_iSup_of_le (kolBall π δ)
  apply le_iSup_of_le (show kolBall π δ ∈ kolCollection n δ from ⟨π,hπ,rfl⟩)
  apply le_iInf
  intro T
  obtain ⟨p,hp,eq,hs,hcost⟩ := hard T
  have dist := (quantile_approx (by omega) mp hp).2
  rw [eq] at dist
  have inv : 1/(m:ℝ) ≤ (n:ℝ)^(-ε) := by
    rw [Real.rpow_neg np.le,← one_div]; exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos np _) mle
  apply le_iSup_of_le p
  apply le_iSup_of_le (show p ∈ kolBall π δ from ⟨hp,dist.trans (inv.trans hδ)⟩)
  obtain ⟨op,ub⟩ := sparse_support_opt_upper_bound hn qp p hp hs
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ op).mpr
  rw [div_mul_eq_mul_div,div_le_iff₀ he]
  nlinarith [mul_le_mul_of_nonneg_right hcost he.le]

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ δ : ℝ, 1 / (n : ℝ) ≤ δ → δ ≤ 1 / 2 →
        ENNReal.ofReal (c * Real.logb 2 n / Real.logb 2 (1 / δ)) ≤ approxFactor (kolCollection n δ) ∧
        approxFactor (kolCollection n δ) ≤ ENNReal.ofReal (C * Real.logb 2 n / Real.logb 2 (1 / δ))) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (n : ℕ), 2 ≤ n → (2 : ℝ) ^ (1 / ε) ≤ n →
        ENNReal.ofReal (c / ε) ≤ approxFactor (kolCollection n ((n : ℝ) ^ (-ε))) ∧
        approxFactor (kolCollection n ((n : ℝ) ^ (-ε))) ≤ ENNReal.ofReal (C / ε)) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (n : ℕ), 2 ≤ n → (2 : ℝ) ^ (1 / ε) ≤ n →
        ∀ δ : ℝ, (n : ℝ) ^ (-ε) ≤ δ →
          ENNReal.ofReal (c / ε) ≤ approxFactor (kolCollection n δ)) := by
  obtain ⟨C,hC,_,_,upper⟩ := MomentSearch.Supplement.theorem_5
  refine ⟨1/24,C,by norm_num,hC,?_,?_⟩
  · intro n hn δ hmin hmax
    have np : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have dp : 0 < δ := (one_div_pos.mpr np).trans_le hmin
    have two : (2:ℝ) ≤ 1/δ := (le_div_iff₀ dp).mpr (by linarith)
    have hi : 1/δ ≤ (n:ℝ) := (div_le_iff₀ dp).mpr (by linarith [(div_le_iff₀ np).mp hmin])
    let L := Real.logb 2 n
    let A := Real.logb 2 (1/δ)
    have Lp : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < n))
    have Aone : 1 ≤ A := by
      simpa [A] using Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ)<2) two
    have Ap : 0 < A := zero_lt_one.trans_le Aone
    let ε := A/L
    have ep : 0 < ε := div_pos Ap Lp
    have es : ε*L = A := div_mul_cancel₀ _ Lp.ne'
    have ele : ε ≤ 1 := (div_le_iff₀ Lp).mpr (by
      simpa [A,L] using Real.logb_le_logb_of_le (b := 2) (by norm_num) (one_div_pos.mpr dp) hi)
    have poweq : (n:ℝ)^ε = 1/δ := by
      calc
        _ = (2:ℝ)^(Real.logb 2 ((n:ℝ)^ε)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (Real.rpow_pos_of_pos np _)).symm
        _ = (2:ℝ)^A := by rw [Real.logb_rpow_eq_mul_logb_of_pos np,es]
        _ = _ := Real.rpow_logb (by norm_num) (by norm_num) (one_div_pos.mpr dp)
    have de : (n:ℝ)^(-ε) = δ := by rw [Real.rpow_neg np.le,poweq]; simp
    have ratio (z : ℝ) : z*L/A = z/ε := by dsimp [ε]; field_simp
    change ENNReal.ofReal (_*L/A) ≤ _ ∧ _ ≤ ENNReal.ofReal (_*L/A)
    rw [ratio,ratio]
    refine ⟨lower_ball n hn ε ep (es.symm ▸ Aone) δ de.le, ?_⟩
    rw [← de]; exact upper n hn ε ep ele
  · have scale (n : ℕ) (ε : ℝ) (he : 0 < ε) (h : (2:ℝ)^(1/ε) ≤ n) :
        1 ≤ ε * Real.logb 2 n := by
      have l := Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num)
        (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _) h
      rw [Real.logb_rpow (by norm_num) (by norm_num)] at l
      linarith [(div_le_iff₀ he).mp l]
    exact ⟨fun ε he he' n hn h =>
      ⟨lower_ball n hn ε he (scale n ε he h) _ le_rfl, upper n hn ε he he'⟩,
      fun ε he _ n hn h δ hδ => lower_ball n hn ε he (scale n ε he h) δ hδ⟩
