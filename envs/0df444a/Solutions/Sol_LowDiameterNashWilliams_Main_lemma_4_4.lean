-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T18:53:33.294803+00:00
-- url     : https://prove2.me/submissions/135e2672-e369-40ce-905d-cd91db1c18a5

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling

section
set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal

namespace LowDiameterNashWilliams.Main.Dev.L44
open LowDiameterNashWilliams.Main

/-- Integer core of the edge-count bound. -/
lemma arith (e u w m A B : ℤ) (hu : 0 ≤ u) (hw : 0 ≤ w) (hm : 0 ≤ m) (hsum : u + w = m + 1)
    (h1 : u * A ≤ e + u * (u - 1)) (h2 : w * B ≤ e + w * (w - 1))
    (h5 : 5 * m ≤ 4 * (A + B)) : m * min u w ≤ 8 * e := by
  have k1 : w * (u * A) ≤ w * (e + u * (u - 1)) := mul_le_mul_of_nonneg_left h1 hw
  have k2 : u * (w * B) ≤ u * (e + w * (w - 1)) := mul_le_mul_of_nonneg_left h2 hu
  have huw : 0 ≤ u * w := mul_nonneg hu hw
  -- u w (A + B - m + 1) ≤ e (u + w)
  have k3 : u * w * (A + B - m + 1) ≤ e * (u + w) := by nlinarith
  have k4 : u * w * m ≤ 4 * e * (u + w) := by nlinarith
  have hpos : 0 < u + w := by omega
  rcases le_total u w with h | h
  · rw [min_eq_left h]
    have : m * u * (u + w) ≤ 8 * e * (u + w) := by nlinarith [mul_nonneg hm hu]
    exact le_of_mul_le_mul_right (by linarith) hpos
  · rw [min_eq_right h]
    have : m * w * (u + w) ≤ 8 * e * (u + w) := by nlinarith [mul_nonneg hm hw]
    exact le_of_mul_le_mul_right (by linarith) hpos

lemma leftMin_le {m : ℕ} (N : Fin m → Finset (Fin m)) (i : Fin m) :
    leftMin N ≤ (Finset.univ.filter fun j => i ∈ N j).card := by
  unfold leftMin
  rw [dif_pos ⟨i, Finset.mem_univ i⟩]
  exact Finset.inf'_le _ (Finset.mem_univ i)

lemma rightMin_le {m : ℕ} (N : Fin m → Finset (Fin m)) (j : Fin m) :
    rightMin N ≤ (N j).card := by
  unfold rightMin
  rw [dif_pos ⟨j, Finset.mem_univ j⟩]
  exact Finset.inf'_le (fun j => (N j).card) (Finset.mem_univ j)

/-- Double counting of the edges between `W` (right) and `U` (left). -/
lemma double_count {m : ℕ} (N : Fin m → Finset (Fin m)) (U W : Finset (Fin m)) :
    ∑ j ∈ W, (U ∩ N j).card = ∑ i ∈ U, (W.filter fun j => i ∈ N j).card := by
  have : ∀ j, (U ∩ N j).card = ∑ i ∈ U, if i ∈ N j then 1 else 0 := by
    intro j
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  simp_rw [this, Finset.card_filter]
  exact Finset.sum_comm

/-- The edge-count bound `m · min(|U|,|W|) ≤ 8 e(U,W)` when `|U| + |W| = m + 1`. -/
lemma edge_bound {m : ℕ} (N : Fin m → Finset (Fin m))
    (hδ : 5 * m ≤ 4 * (leftMin N + rightMin N)) (U W : Finset (Fin m))
    (huw : U.card + W.card = m + 1) :
    m * min U.card W.card ≤ 8 * ∑ j ∈ W, (U ∩ N j).card := by
  have hUm : U.card ≤ m := by simpa using Finset.card_le_univ U
  have hWm : W.card ≤ m := by simpa using Finset.card_le_univ W
  -- left side
  have hL : ∀ i ∈ U, leftMin N ≤ (W.filter fun j => i ∈ N j).card + (m - W.card) := by
    intro i _
    refine (leftMin_le N i).trans ?_
    have hsub : (Finset.univ.filter fun j => i ∈ N j) ⊆
        (W.filter fun j => i ∈ N j) ∪ (Finset.univ \ W) := by
      intro j hj
      by_cases hjW : j ∈ W
      · exact Finset.mem_union_left _ (by simp_all)
      · exact Finset.mem_union_right _ (by simp [hjW])
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hR : ∀ j ∈ W, rightMin N ≤ (U ∩ N j).card + (m - U.card) := by
    intro j _
    refine (rightMin_le N j).trans ?_
    have hsub : N j ⊆ (U ∩ N j) ∪ (Finset.univ \ U) := by
      intro i hi
      by_cases hiU : i ∈ U
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hiU, hi⟩)
      · exact Finset.mem_union_right _ (by simp [hiU])
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have sL := Finset.sum_le_sum hL
  have sR := Finset.sum_le_sum hR
  rw [Finset.sum_add_distrib, ← double_count] at sL
  rw [Finset.sum_add_distrib] at sR
  simp only [Finset.sum_const, smul_eq_mul] at sL sR
  set e := ∑ j ∈ W, (U ∩ N j).card
  have hmw : m - W.card = U.card - 1 := by omega
  have hmu : m - U.card = W.card - 1 := by omega
  rw [hmw] at sL
  rw [hmu] at sR
  have hU1 : 1 ≤ U.card := by omega
  have hW1 : 1 ≤ W.card := by omega
  have := arith e U.card W.card m (leftMin N) (rightMin N) (by positivity) (by positivity)
    (by positivity) (by exact_mod_cast huw)
    (by have := sL; zify [hU1] at this; linarith)
    (by have := sR; zify [hW1] at this; linarith) (by exact_mod_cast hδ)
  have h' : ((m * min U.card W.card : ℕ) : ℤ) ≤ ((8 * e : ℕ) : ℤ) := by
    push_cast; exact this
  exact_mod_cast h'

/-- Hall's theorem, contrapositive form: a deficient set gives a pair `(U, W)`. -/
lemma hall_pair {m : ℕ} (s : Fin m → Finset (Fin m)) (h : ¬ PerfectMatching s) :
    ∃ U W : Finset (Fin m), U.card + W.card = m + 1 ∧ ∀ j ∈ W, Disjoint (s j) U := by
  have hHall : ¬ ∀ W : Finset (Fin m), W.card ≤ (W.biUnion s).card := by
    intro hH
    obtain ⟨f, hf, hfs⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective s).1 hH
    exact h ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), hfs⟩
  push Not at hHall
  obtain ⟨W, hW⟩ := hHall
  set T := W.biUnion s
  have hWm : W.card ≤ m := by simpa using Finset.card_le_univ W
  have hc : m + 1 - W.card ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have : T.card ≤ m := by simpa using Finset.card_le_univ T
    omega
  obtain ⟨U, hUsub, hUc⟩ := Finset.exists_subset_card_eq hc
  refine ⟨U, W, by omega, fun j hj => ?_⟩
  rw [Finset.disjoint_left]
  intro i hi hiU
  have := hUsub hiU
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
  exact this (Finset.mem_biUnion.2 ⟨j, hj, hi⟩)

lemma part_one {m : ℕ} (hm : 2 ≤ m) (N : Fin m → Finset (Fin m))
    (hδ : 5 * m ≤ 4 * (leftMin N + rightMin N)) : PerfectMatching N := by
  by_contra h
  obtain ⟨U, W, huw, hdisj⟩ := hall_pair N h
  have hb := edge_bound N hδ U W huw
  have h0 : ∑ j ∈ W, (U ∩ N j).card = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.card_eq_zero, Finset.inter_comm]
    exact Finset.disjoint_iff_inter_eq_empty.1 (hdisj j hj)
  rw [h0] at hb
  have hUm : U.card ≤ m := by simpa using Finset.card_le_univ U
  have hWm : W.card ≤ m := by simpa using Finset.card_le_univ W
  have : 1 ≤ min U.card W.card := le_min (by omega) (by omega)
  have : 2 ≤ m * min U.card W.card := le_trans (by omega) (Nat.mul_le_mul hm this)
  omega

/-! ## The probability bound -/

lemma pmf_sum_one {m : ℕ} (ν : PMF (Finset (Fin m))) : ∑ S, ν S = 1 := by
  simpa [tsum_fintype] using PMF.tsum_coe ν

lemma sum_prod_one {m : ℕ} (μ : Fin m → PMF (Finset (Fin m))) :
    ∑ s : Fin m → Finset (Fin m), ∏ j, μ j (s j) = 1 := by
  rw [← Fintype.prod_sum]
  simp [pmf_sum_one]

/-- Independence: the probability that every `j ∈ W` avoids `U` factorizes. -/
lemma factor {m : ℕ} (μ : Fin m → PMF (Finset (Fin m))) (U W : Finset (Fin m)) :
    ∑ s : Fin m → Finset (Fin m),
      (if ∀ j ∈ W, Disjoint (s j) U then ∏ j, μ j (s j) else 0)
      = ∏ j ∈ W, avoidance (μ j) U := by
  set g : Fin m → Finset (Fin m) → ℝ≥0∞ := fun j S =>
    if j ∈ W then (if Disjoint S U then μ j S else 0) else μ j S with hg
  have h1 : ∀ s : Fin m → Finset (Fin m),
      (if ∀ j ∈ W, Disjoint (s j) U then ∏ j, μ j (s j) else 0) = ∏ j, g j (s j) := by
    intro s
    split_ifs with h
    · refine Finset.prod_congr rfl fun j _ => ?_
      simp only [hg]
      split_ifs with h1 h2 <;> first | rfl | exact absurd (h j h1) h2
    · push Not at h
      obtain ⟨j, hj, hd⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hg, hj, hd])
  simp_rw [h1]
  rw [← Fintype.prod_sum]
  have h2 : ∀ j, ∑ S, g j S = if j ∈ W then avoidance (μ j) U else 1 := by
    intro j
    by_cases hj : j ∈ W
    · simp [hg, hj, avoidance]
    · simp [hg, hj, pmf_sum_one]
  simp_rw [h2]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- Union bound over Hall violators. -/
lemma union_bound {m : ℕ} (μ : Fin m → PMF (Finset (Fin m))) :
    ∑ s : Fin m → Finset (Fin m), (if PerfectMatching s then 0 else ∏ j, μ j (s j))
      ≤ ∑ U : Finset (Fin m), ∑ W : Finset (Fin m),
          (if U.card + W.card = m + 1 then ∏ j ∈ W, avoidance (μ j) U else 0) := by
  have key : ∀ s : Fin m → Finset (Fin m),
      (if PerfectMatching s then 0 else ∏ j, μ j (s j)) ≤
        ∑ U : Finset (Fin m), ∑ W : Finset (Fin m),
          (if U.card + W.card = m + 1 ∧ ∀ j ∈ W, Disjoint (s j) U
            then ∏ j, μ j (s j) else 0) := by
    intro s
    split_ifs with h
    · exact zero_le
    · obtain ⟨U, W, huw, hd⟩ := hall_pair s h
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ U))
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ W))
      rw [if_pos ⟨huw, hd⟩]
  refine (Finset.sum_le_sum fun s _ => key s).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  split_ifs with h
  · rw [← factor]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [h]
  · simp [h]

lemma exp_bound {m : ℕ} (hm : 2 ≤ m) {p : ℝ} (hp : 0 < p)
    (hpm : 96 * Real.log m ≤ p * m) (e k : ℕ) (h : m * k ≤ 8 * e) :
    Real.exp (-p * e) ≤ ((m : ℝ)⁻¹) ^ (12 * k) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [show (m : ℝ)⁻¹ = Real.exp (-Real.log m) by rw [Real.exp_neg, Real.exp_log hmpos],
    ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have hc : (m : ℝ) * k ≤ 8 * e := by exact_mod_cast h
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hk : (0 : ℝ) ≤ k := by positivity
  have a1 := mul_le_mul_of_nonneg_left hc hp.le
  have a2 := mul_le_mul_of_nonneg_right hpm hk
  push_cast
  nlinarith

lemma avoid_mono {m : ℕ} (ν : PMF (Finset (Fin m))) (U X : Finset (Fin m)) (h : X ⊆ U) :
    avoidance ν U ≤ avoidance ν X := by
  unfold avoidance
  refine Finset.sum_le_sum fun S _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.mono_right h) h2
  · exact zero_le
  · exact le_rfl

lemma term_bound {m : ℕ} (hm : 2 ≤ m) (N : Fin m → Finset (Fin m))
    (hδ : 5 * m ≤ 4 * (leftMin N + rightMin N))
    (μ : Fin m → PMF (Finset (Fin m))) (p : ℝ) (hp : 0 < p)
    (havoid : ∀ j X, X ⊆ N j → avoidance (μ j) X ≤ ENNReal.ofReal (Real.exp (-p * X.card)))
    (hpm : 96 * Real.log m ≤ p * m) (U W : Finset (Fin m)) (huw : U.card + W.card = m + 1) :
    ∏ j ∈ W, avoidance (μ j) U ≤
      ENNReal.ofReal (((m : ℝ)⁻¹) ^ (12 * U.card) + ((m : ℝ)⁻¹) ^ (12 * W.card)) := by
  have h1 : ∏ j ∈ W, avoidance (μ j) U ≤
      ∏ j ∈ W, ENNReal.ofReal (Real.exp (-p * (U ∩ N j).card)) := by
    refine Finset.prod_le_prod' fun j _ => ?_
    exact (avoid_mono _ _ _ Finset.inter_subset_left).trans
      (havoid j _ Finset.inter_subset_right)
  refine h1.trans ?_
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
  apply ENNReal.ofReal_le_ofReal
  have hs : ∑ j ∈ W, -p * ((U ∩ N j).card : ℝ) = -p * ((∑ j ∈ W, (U ∩ N j).card : ℕ) : ℝ) := by
    rw [← Finset.mul_sum]; push_cast; rfl
  rw [hs]
  refine (exp_bound hm hp hpm _ _ (edge_bound N hδ U W huw)).trans ?_
  have hx : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  rcases le_total U.card W.card with h | h
  · rw [min_eq_left h]; linarith [pow_nonneg hx (12 * W.card)]
  · rw [min_eq_right h]; linarith [pow_nonneg hx (12 * U.card)]

/-- Counting: `∑_{|U|+|W|=m+1} x^{12|U|} ≤ 2 x^{11}` with `x = 1/m`. -/
lemma count_half {m : ℕ} (hm : 2 ≤ m) :
    ∑ U : Finset (Fin m), ∑ W : Finset (Fin m),
      (if U.card + W.card = m + 1 then ((m : ℝ)⁻¹) ^ (12 * U.card) else 0)
      ≤ 2 * ((m : ℝ)⁻¹) ^ 11 := by
  set x : ℝ := (m : ℝ)⁻¹ with hxdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hx0 : 0 ≤ x := by positivity
  have hmx : (m : ℝ) * x = 1 := by rw [hxdef]; field_simp
  have hx2 : x ≤ 1 / 2 := by
    rw [hxdef, one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hm)
  have inner : ∀ U : Finset (Fin m), ∑ W : Finset (Fin m),
      (if U.card + W.card = m + 1 then x ^ (12 * U.card) else 0)
      = x ^ (12 * U.card) * (m.choose (m + 1 - U.card) : ℝ) := by
    intro U
    have hU : U.card ≤ m := by simpa using Finset.card_le_univ U
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    have : (Finset.univ.filter fun W : Finset (Fin m) => U.card + W.card = m + 1)
        = Finset.powersetCard (m + 1 - U.card) (Finset.univ : Finset (Fin m)) := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      omega
    rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  simp_rw [inner]
  rw [← Finset.powerset_univ]
  rw [Finset.sum_powerset_apply_card (fun u => x ^ (12 * u) * (m.choose (m + 1 - u) : ℝ)),
    Finset.card_univ, Fintype.card_fin, Finset.sum_range_succ']
  simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, smul_zero, add_zero,
    show m + 1 - 0 = m + 1 from rfl]
  have hterm : ∀ i ∈ Finset.range m,
      m.choose (i + 1) • (x ^ (12 * (i + 1)) * (m.choose (m + 1 - (i + 1)) : ℝ))
        ≤ x ^ 11 * (x ^ 10) ^ i := by
    intro i hi
    have hi' : i ≤ m := (Finset.mem_range.1 hi).le
    rw [nsmul_eq_mul, show m + 1 - (i + 1) = m - i by omega, Nat.choose_symm hi']
    have c1 : (m.choose (i + 1) : ℝ) ≤ (m : ℝ) ^ (i + 1) := by
      exact_mod_cast Nat.choose_le_pow m (i + 1)
    have c2 : (m.choose i : ℝ) ≤ (m : ℝ) ^ i := by exact_mod_cast Nat.choose_le_pow m i
    have hxp : 0 ≤ x ^ (12 * (i + 1)) := pow_nonneg hx0 _
    have key : (m : ℝ) ^ (i + 1) * (x ^ (12 * (i + 1)) * (m : ℝ) ^ i) = x ^ 11 * (x ^ 10) ^ i := by
      have : x ^ (12 * (i + 1)) = x ^ 11 * (x ^ 10) ^ i * (x ^ (i + 1) * x ^ i) := by
        rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      rw [this]
      calc (m : ℝ) ^ (i + 1) * (x ^ 11 * (x ^ 10) ^ i * (x ^ (i + 1) * x ^ i) * (m : ℝ) ^ i)
          = x ^ 11 * (x ^ 10) ^ i * (((m : ℝ) * x) ^ (i + 1) * ((m : ℝ) * x) ^ i) := by
            rw [mul_pow, mul_pow]; ring
        _ = x ^ 11 * (x ^ 10) ^ i := by rw [hmx]; simp
    rw [← key]
    calc (m.choose (i + 1) : ℝ) * (x ^ (12 * (i + 1)) * (m.choose i : ℝ))
        ≤ (m : ℝ) ^ (i + 1) * (x ^ (12 * (i + 1)) * (m.choose i : ℝ)) :=
          mul_le_mul_of_nonneg_right c1 (by positivity)
      _ ≤ (m : ℝ) ^ (i + 1) * (x ^ (12 * (i + 1)) * (m : ℝ) ^ i) := by
          gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.range_eq_Ico]
  have hy0 : 0 ≤ x ^ 10 := pow_nonneg hx0 _
  have hy : x ^ 10 ≤ 1 / 2 := by
    have : x ^ 10 ≤ x := pow_le_of_le_one hx0 (by linarith) (by norm_num)
    linarith
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hy0 (by linarith)
  rw [pow_zero] at hg
  have h2 : 1 / (1 - x ^ 10) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h11 : 0 ≤ x ^ 11 := pow_nonneg hx0 _
  nlinarith [mul_le_mul_of_nonneg_left (hg.trans h2) h11]

lemma count_full {m : ℕ} (hm : 2 ≤ m) :
    ∑ U : Finset (Fin m), ∑ W : Finset (Fin m),
      (if U.card + W.card = m + 1 then
        ((m : ℝ)⁻¹) ^ (12 * U.card) + ((m : ℝ)⁻¹) ^ (12 * W.card) else 0)
      ≤ 4 * ((m : ℝ)⁻¹) ^ 11 := by
  have hsplit : ∀ U W : Finset (Fin m),
      (if U.card + W.card = m + 1 then
        ((m : ℝ)⁻¹) ^ (12 * U.card) + ((m : ℝ)⁻¹) ^ (12 * W.card) else 0)
      = (if U.card + W.card = m + 1 then ((m : ℝ)⁻¹) ^ (12 * U.card) else 0)
        + (if W.card + U.card = m + 1 then ((m : ℝ)⁻¹) ^ (12 * W.card) else 0) := by
    intro U W
    rw [add_comm W.card U.card]
    split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib]
  have e : (∑ U : Finset (Fin m), ∑ W : Finset (Fin m),
      if W.card + U.card = m + 1 then ((m : ℝ)⁻¹) ^ (12 * W.card) else 0)
      = ∑ U : Finset (Fin m), ∑ W : Finset (Fin m),
      if U.card + W.card = m + 1 then ((m : ℝ)⁻¹) ^ (12 * U.card) else 0 := Finset.sum_comm
  rw [e]
  linarith [count_half hm]

end LowDiameterNashWilliams.Main.Dev.L44

namespace LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Main.Dev.L44 in
theorem chk_lemma_4_4 :
  ∀ m : ℕ, 2 ≤ m → ∀ N : Fin m → Finset (Fin m),
  (5 : ℝ) * m / 4 ≤ (leftMin N : ℝ) + rightMin N →
  PerfectMatching N ∧
  ∀ (μ : Fin m → PMF (Finset (Fin m))) (p : ℝ), 0 < p → p ≤ 1 →
    (∀ j S, μ j S ≠ 0 → S ⊆ N j) →
    (∀ j X, X ⊆ N j → avoidance (μ j) X ≤ ENNReal.ofReal (Real.exp (-p * X.card))) →
    96 * Real.log m ≤ p * m →
    ENNReal.ofReal (1 - 4 * (m : ℝ) ^ (-(11 : ℤ))) ≤ matchingProbability μ := by
  intro m hm N hδr
  have hδ : 5 * m ≤ 4 * (leftMin N + rightMin N) := by
    have : (5 : ℝ) * m ≤ 4 * ((leftMin N : ℝ) + rightMin N) := by linarith
    exact_mod_cast this
  refine ⟨part_one hm N hδ, ?_⟩
  intro μ p hp _ _ havoid hpm
  set Q : ℝ≥0∞ := ∑ s : Fin m → Finset (Fin m),
    (if PerfectMatching s then 0 else ∏ j, μ j (s j)) with hQ
  have hsum : matchingProbability μ + Q = 1 := by
    rw [← sum_prod_one μ, matchingProbability, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  have hQle : Q ≤ ENNReal.ofReal (4 * ((m : ℝ)⁻¹) ^ 11) := by
    refine (union_bound μ).trans ?_
    have hx : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
    have hnn : ∀ U W : Finset (Fin m), 0 ≤ (if U.card + W.card = m + 1 then
        ((m : ℝ)⁻¹) ^ (12 * U.card) + ((m : ℝ)⁻¹) ^ (12 * W.card) else 0) := by
      intro U W; split_ifs <;> positivity
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (count_full hm))
    rw [ENNReal.ofReal_sum_of_nonneg (fun U _ => Finset.sum_nonneg fun W _ => hnn U W)]
    refine Finset.sum_le_sum fun U _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun W _ => hnn U W)]
    refine Finset.sum_le_sum fun W _ => ?_
    split_ifs with h
    · exact term_bound hm N hδ μ p hp havoid hpm U W h
    · exact zero_le
  have hQtop : Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQle
  have hmp : matchingProbability μ = 1 - Q := ENNReal.eq_sub_of_add_eq hQtop hsum
  have hz : (m : ℝ) ^ (-(11 : ℤ)) = ((m : ℝ)⁻¹) ^ 11 := by
    rw [zpow_neg, inv_pow, zpow_ofNat]
  rw [hmp, hz, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left hQle 1

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_lemma_4_4 := @LowDiameterNashWilliams.Main.chk_lemma_4_4
