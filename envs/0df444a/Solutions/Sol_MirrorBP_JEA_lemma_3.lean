-- Prove2me | solution 1 for MirrorBP.JEA.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:29:38.617191+00:00
-- url     : https://prove2.me/submissions/d6cb96fd-bbbf-4e9c-8baf-03631f4a0141

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP
import Theorems.Thm_MirrorBP_JEA_lemma_2

set_option linter.unusedSectionVars false

namespace MirrorBP.JEA.Lemma3Aux

open Finset MirrorBP.JEA

theorem f_eq (m : ℕ) (x : ℝ) (hx : 0 < x) : fMBP m x = -Real.sqrt m / Real.sqrt x := by
  unfold fMBP
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

theorem deriv_f (m : ℕ) (x : ℝ) (hx : 0 < x) :
    deriv (fMBP m) x = Real.sqrt m / (2 * (x * Real.sqrt x)) := by
  have h := (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hx.ne')).const_mul
    (-Real.sqrt m)
  have hfun : fMBP m = fun x => -Real.sqrt m * x ^ (-(1 / 2 : ℝ)) := by
    funext y; rfl
  rw [hfun, h.deriv]
  have e : x ^ (-(1 / 2 : ℝ) - 1) = (Real.sqrt x)⁻¹ / x := by
    rw [Real.rpow_sub hx, Real.rpow_one, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  rw [e]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  field_simp


theorem le_ymax' {V : Type} [Fintype V] [Nonempty V] (y : V → ℝ) (i : V) : y i ≤ ymax y := by
  unfold ymax
  rw [dif_pos Finset.univ_nonempty]
  exact Finset.le_sup' _ (Finset.mem_univ i)

theorem ymin_le' {V : Type} [Fintype V] [Nonempty V] (y : V → ℝ) (i : V) : ymin y ≤ y i := by
  unfold ymin
  rw [dif_pos Finset.univ_nonempty]
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem L1 (s Kt x0 : ℝ) (hs : 2 ≤ s) (hKt : 0 < Kt) (hx0 : s / Kt ≤ x0) :
    x0 / 2 ≤ x0 - 1 / Kt := by
  have : 1 / Kt ≤ s / Kt / 2 := by
    rw [div_div, div_le_div_iff₀ hKt (by positivity)]; nlinarith
  linarith

theorem L2 (m p r : ℝ) (hp : 0 < p) (hr : 0 < r) (hp2 : p ^ 2 = m) (hm : 0 < m)
    (h : p / r ≤ 5 * m) : 1 / (25 * m) ≤ r ^ 2 := by
  rw [div_le_iff₀ hr] at h
  have h2 : p ^ 2 ≤ (5 * m * r) ^ 2 := pow_le_pow_left₀ hp.le h 2
  rw [hp2] at h2
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem L3 (m s Kt x0 : ℝ) (hm : 0 < m) (hs : 0 < s) (hKt : Kt = s ^ 2 + m * s)
    (hx0 : x0 = s / Kt) (h : 1 / (25 * m) ≤ x0) (h24 : 24 * m < s) : False := by
  have hKtpos : 0 < Kt := by rw [hKt]; positivity
  rw [hx0, div_le_div_iff₀ (by positivity) hKtpos, hKt] at h
  nlinarith

theorem L4 (m s Kt x0 : ℝ) (hm : 2 ≤ m) (hs : 2 ≤ s) (hKt : Kt = s ^ 2 + m * s)
    (h24 : 24 * m < s) (h : 1 / (25 * m) ≤ x0) : 1 / (64 * m) ≤ x0 - 1 / Kt := by
  have hKt50 : 50 * m ≤ Kt := by rw [hKt]; nlinarith
  have h1 : 1 / Kt ≤ 1 / (50 * m) := one_div_le_one_div_of_le (by positivity) hKt50
  have hm0 : 0 < m := by linarith
  have h2 : 1 / (25 * m) - 1 / (50 * m) = 1 / (50 * m) := by field_simp; ring
  have h3 : 1 / (64 * m) ≤ 1 / (50 * m) := one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem L5 (m p l : ℝ) (hp : 0 < p) (hp2 : p ^ 2 = m) (hm : 2 ≤ m) (hl : 1 / (64 * m) ≤ l) :
    p / (2 * (l * Real.sqrt l)) ≤ 256 * m ^ 2 := by
  have hm0 : 0 < m := by linarith
  have hlpos : 0 < l := lt_of_lt_of_le (by positivity) hl
  have hsql : 1 / (8 * p) ≤ Real.sqrt l := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, mul_pow, hp2]
    have : (1 : ℝ) ^ 2 / (8 ^ 2 * m) = 1 / (64 * m) := by norm_num
    rw [this]; exact hl
  have hprod : 1 / (64 * m) * (1 / (8 * p)) ≤ l * Real.sqrt l :=
    mul_le_mul hl hsql (by positivity) hlpos.le
  rw [div_le_iff₀ (by positivity)]
  have e1 : 1 / (64 * m) * (1 / (8 * p)) * (2 * (256 * m ^ 2)) = p := by
    rw [← hp2]; field_simp; ring
  have : 0 ≤ 2 * (256 * m ^ 2) := by positivity
  nlinarith

theorem L6 (p r x0 l : ℝ) (hp : 0 < p) (hr : 0 < r) (hr2 : r ^ 2 = x0) (hl : x0 / 2 ≤ l) :
    p / (2 * (l * Real.sqrt l)) ≤ 2 * (p / r) / x0 := by
  have hx0 : 0 < x0 := by rw [← hr2]; positivity
  have hlpos : 0 < l := by linarith
  have hsqlr : r / 2 ≤ Real.sqrt l := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, hr2]; nlinarith
  have hprod : x0 / 2 * (r / 2) ≤ l * Real.sqrt l :=
    mul_le_mul hl hsqlr (by positivity) hlpos.le
  have e : 2 * (p / r) / x0 = p / (2 * (x0 / 2 * (r / 2))) := by field_simp <;> ring_nf
  rw [e]
  apply div_le_div_of_nonneg_left hp.le (by positivity)
  linarith

theorem L7 (B a s x0 Kt : ℝ) (hB : B ≤ 2 * a / x0) (hsx : s ≤ x0 * Kt) (hx0 : 0 < x0)
    (hKt : 0 < Kt) (hs : 0 < s) (ha : 0 < a) : B / Kt ≤ 2 * a / s := by
  have h1 : B / Kt ≤ 2 * a / x0 / Kt := div_le_div_of_nonneg_right hB hKt.le
  have h2 : 2 * a / x0 / Kt = 2 * a / (x0 * Kt) := by rw [div_div]
  have h3 : 2 * a / (x0 * Kt) ≤ 2 * a / s :=
    div_le_div_of_nonneg_left (by positivity) hs hsx
  linarith

theorem L8 (α β s a : ℝ) (hs : 10 * β ≤ s) (hαβ : α * β = 1) (hα : 0 < α) (ha : 0 < a)
    (hspos : 0 < s) : 2 * a / s ≤ (1 / 5) * α * a := by
  rw [div_le_iff₀ hspos]
  have h1 : 10 ≤ α * s := by
    have := mul_le_mul_of_nonneg_left hs hα.le
    have e : α * (10 * β) = 10 := by rw [mul_left_comm, hαβ, mul_one]
    linarith
  have := mul_le_mul_of_nonneg_left h1 ha.le
  nlinarith

theorem L9 (m s Kt x0 r p a α β : ℝ) (hm : 2 ≤ m) (hs : 0 < s) (hKt : Kt = s ^ 2 + m * s)
    (hx0 : x0 = s / Kt) (hr : 0 < r) (hr2 : r ^ 2 = x0) (hp2 : p ^ 2 = m) (hp : 0 < p)
    (ha : a = p / r) (hsβ : 25 * β ^ 2 ≤ s) (hαβ : α * β = 1) (hα : 0 < α) (hβ : 0 < β) :
    1 ≤ (1 / 5) * α * a := by
  have hKtpos : 0 < Kt := by rw [hKt]; positivity
  have ha2 : a ^ 2 * s = m * Kt := by
    rw [ha, div_pow, hr2, hp2, hx0]; field_simp
  have has : s ≤ a ^ 2 := by
    have h1 : s * s ≤ a ^ 2 * s := by rw [ha2, hKt]; nlinarith
    nlinarith
  have hapos : 0 < a := by rw [ha]; positivity
  have hab : 5 * β ≤ a := by
    have h : (5 * β) ^ 2 ≤ a ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hapos.le (by norm_num)).mp h
  have := mul_le_mul_of_nonneg_left hab hα.le
  have e : α * (5 * β) = 5 := by rw [mul_left_comm, hαβ, mul_one]
  linarith

/-- the combination of the cases -/
theorem core3 (m s Kt x0 r p a α β V3 V4 : ℝ) (hm : 2 ≤ m)
    (hs2 : 2 ≤ s) (hs24 : 24 * m < s) (hsβ2 : 25 * β ^ 2 ≤ s) (hsβ : 10 * β ≤ s)
    (hKt : Kt = s ^ 2 + m * s) (hx0s : s / Kt ≤ x0) (hr : 0 < r) (hr2 : r ^ 2 = x0)
    (hp : 0 < p) (hp2 : p ^ 2 = m) (ha : a = p / r)
    (hαβ : α * β = 1) (hα : 0 < α) (hβ : 0 < β)
    (hV3 : V3 ≤ -α * max 0 (a - 3 * m))
    (hV4 : V4 = 0 ∨ (V4 = 1 ∧ x0 = s / Kt)) :
    p / (2 * ((x0 - 1 / Kt) * Real.sqrt (x0 - 1 / Kt))) / Kt + V3 + V4 ≤ 256 * m ^ 2 / Kt := by
  have hspos : 0 < s := by linarith
  have hKtpos : 0 < Kt := by rw [hKt]; positivity
  have hm0 : 0 < m := by linarith
  have hapos : 0 < a := by rw [ha]; positivity
  have hx0pos : 0 < x0 := by rw [← hr2]; positivity
  have hl := L1 s Kt x0 hs2 hKtpos hx0s
  have hV3le0 : V3 ≤ 0 := by
    have : 0 ≤ α * max 0 (a - 3 * m) := mul_nonneg hα.le (le_max_left _ _)
    linarith
  have hfin : 0 ≤ 256 * m ^ 2 / Kt := by positivity
  by_cases hcase : a ≤ 5 * m
  · have hx0big : 1 / (25 * m) ≤ x0 := by
      rw [← hr2]; exact L2 m p r hp hr hp2 hm0 (by rw [← ha]; exact hcase)
    have hV40 : V4 = 0 := by
      rcases hV4 with h | ⟨_, h⟩
      · exact h
      · exact (L3 m s Kt x0 hm0 hspos hKt h hx0big hs24).elim
    have hl64 := L4 m s Kt x0 hm hs2 hKt hs24 hx0big
    have hB := L5 m p (x0 - 1 / Kt) hp hp2 hm hl64
    have := div_le_div_of_nonneg_right hB hKtpos.le
    linarith
  · push_neg at hcase
    have hV3B : V3 ≤ -(2 / 5) * α * a := by
      rw [max_eq_right (by linarith)] at hV3
      have : (2 / 5) * a ≤ a - 3 * m := by linarith
      have := mul_le_mul_of_nonneg_left this hα.le
      linarith
    have hB := L6 p r x0 (x0 - 1 / Kt) hp hr hr2 hl
    rw [← ha] at hB
    have hsx : s ≤ x0 * Kt := by rw [div_le_iff₀ hKtpos] at hx0s; linarith
    have hBK := L7 _ a s x0 Kt hB hsx hx0pos hKtpos hspos hapos
    have hBK' := L8 α β s a hsβ hαβ hα hapos hspos
    have hV4' : V4 ≤ (1 / 5) * α * a := by
      rcases hV4 with h | ⟨h, h'⟩
      · rw [h]; positivity
      · rw [h]; exact L9 m s Kt x0 r p a α β hm hspos hKt h' hr hr2 hp2 hp ha hsβ2 hαβ hα hβ
    linarith

theorem sbounds (m β s : ℝ) (hm : 2 ≤ m) (hβ : 0 < β) (hs : 0 ≤ s)
    (hK : 1000 * (m + β) ^ 4 ≤ s ^ 2) :
    2 ≤ s ∧ 24 * m < s ∧ 25 * β ^ 2 ≤ s ∧ 10 * β ≤ s := by
  set t := m + β with ht
  have ht2 : 2 ≤ t := by linarith
  have htβ : β ≤ t := by linarith
  have htm : m ≤ t := by linarith
  have hs31 : 31 * t ^ 2 ≤ s := by
    have h : (31 * t ^ 2) ^ 2 ≤ s ^ 2 := by
      have : 0 ≤ t ^ 4 := by positivity
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hs (by norm_num)).mp h
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end MirrorBP.JEA.Lemma3Aux

open MirrorBP.JEA MirrorBP.JEA.Lemma3Aux Finset

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (K : ℕ) (q : V → ℕ),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        IsRate φ → 0 < alphaConn P D φ →
        c * ((Fintype.card V : ℝ) + 1 / alphaConn P D φ) ^ N ≤ (K : ℝ) →
        q ∈ StateSpace V K →
        ∃ B : ℝ,
          (∀ j, ∀ x ∈ Set.Icc (qbar K q j - 1 / Kt (Fintype.card V) K)
              (qbar K q j + 1 / Kt (Fintype.card V) K),
              0 < x → |deriv (fMBP (Fintype.card V)) x| ≤ B) ∧
          B / Kt (Fintype.card V) K
              + (Wspp P D w φ - gDual P D w φ (fun j => fMBP (Fintype.card V) (qbar K q j)))
              + (if ∃ j, q j = 0 then (1 : ℝ) else 0)
            ≤ C * (Fintype.card V : ℝ) ^ 2 / Kt (Fintype.card V) K := by
  refine ⟨256, by norm_num, 1000, 4, ?_⟩
  intro V Ty _ _ _ _ P D w φ K q hm hP hD hw hφ hα hK hq
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hm2 : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hm
  obtain ⟨β, hβdef⟩ : ∃ β, β = 1 / alphaConn P D φ := ⟨_, rfl⟩
  have hβpos : 0 < β := by rw [hβdef]; positivity
  have hαβ : alphaConn P D φ * β = 1 := by rw [hβdef]; field_simp
  rw [← hβdef] at hK
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt K := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hsK : s ^ 2 = K := by rw [hsdef]; exact Real.sq_sqrt (Nat.cast_nonneg K)
  rw [← hsK] at hK
  obtain ⟨hs2, hs24, hsβ2, hsβ⟩ := sbounds _ β s hm2 hβpos hs0 hK
  have hspos : 0 < s := by linarith
  have hKt : Kt (Fintype.card V) K = s ^ 2 + (Fintype.card V : ℝ) * s := by
    rw [Kt, ← hsdef, hsK]
  have hKtpos : 0 < Kt (Fintype.card V) K := by rw [hKt]; positivity
  have hqbar : ∀ j, qbar K q j = ((q j : ℝ) + s) / Kt (Fintype.card V) K := by
    intro j; rw [qbar, ← hsdef]
  -- the minimal queue
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image univ q Finset.univ_nonempty
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = qbar K q j0 := ⟨_, rfl⟩
  have hx0s : s / Kt (Fintype.card V) K ≤ x0 := by
    rw [hx0, hqbar]
    apply div_le_div_of_nonneg_right _ hKtpos.le
    have : (0 : ℝ) ≤ q j0 := Nat.cast_nonneg _
    linarith
  have hx0pos : 0 < x0 := lt_of_lt_of_le (div_pos hspos hKtpos) hx0s
  have hx0le : ∀ j, x0 ≤ qbar K q j := by
    intro j
    rw [hx0, hqbar, hqbar]
    apply div_le_div_of_nonneg_right _ hKtpos.le
    have : (q j0 : ℝ) ≤ q j := by exact_mod_cast hj0 j (Finset.mem_univ j)
    linarith
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.sqrt x0 := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hx0pos
  have hr2 : r ^ 2 = x0 := by rw [hrdef]; exact Real.sq_sqrt hx0pos.le
  obtain ⟨p, hpdef⟩ : ∃ p, p = Real.sqrt (Fintype.card V : ℝ) := ⟨_, rfl⟩
  have hppos : 0 < p := by rw [hpdef]; exact Real.sqrt_pos.mpr (by linarith)
  have hp2 : p ^ 2 = (Fintype.card V : ℝ) := by rw [hpdef]; exact Real.sq_sqrt (by linarith)
  obtain ⟨a, hadef⟩ : ∃ a, a = p / r := ⟨_, rfl⟩
  -- a large queue
  have hsumq : ∑ j, (q j : ℝ) = K := by
    have := hq
    simp only [StateSpace, Set.mem_setOf_eq] at this
    exact_mod_cast this
  obtain ⟨js, hjs⟩ : ∃ j, (K : ℝ) / (Fintype.card V : ℝ) ≤ q j := by
    by_contra hcon
    push_neg at hcon
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hcon j)
    rw [hsumq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    have hm0 : (0 : ℝ) < Fintype.card V := by linarith
    field_simp at this
    linarith
  have hjs_bar : 1 / (Fintype.card V : ℝ) ≤ qbar K q js := by
    rw [hqbar, le_div_iff₀ hKtpos, hKt]
    have hm0 : (0 : ℝ) < Fintype.card V := by linarith
    rw [← hsK] at hjs
    have h1 : 1 / (Fintype.card V : ℝ) * (s ^ 2 + (Fintype.card V : ℝ) * s)
        = s ^ 2 / (Fintype.card V : ℝ) + s := by field_simp
    rw [h1]
    linarith
  have hyjs : -(Fintype.card V : ℝ) ≤ fMBP (Fintype.card V) (qbar K q js) := by
    have hpos : 0 < qbar K q js := lt_of_lt_of_le hx0pos (hx0le js)
    rw [f_eq _ _ hpos, ← hpdef]
    have hsq : 1 / p ≤ Real.sqrt (qbar K q js) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, hp2]; simpa using hjs_bar
    have hsqpos : 0 < Real.sqrt (qbar K q js) := Real.sqrt_pos.mpr hpos
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hsqpos]
    have e : (Fintype.card V : ℝ) * (1 / p) = p := by rw [← hp2]; field_simp
    have := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ Fintype.card V)
    linarith
  have hyj0 : fMBP (Fintype.card V) (qbar K q j0) = -a := by
    rw [← hx0, f_eq _ _ hx0pos, ← hpdef, ← hrdef, hadef, neg_div]
  have hspread : a - 3 * (Fintype.card V : ℝ) ≤
      ymax (fun j => fMBP (Fintype.card V) (qbar K q j))
        - ymin (fun j => fMBP (Fintype.card V) (qbar K q j)) - 2 * (Fintype.card V : ℝ) := by
    have h1 := le_ymax' (fun j => fMBP (Fintype.card V) (qbar K q j)) js
    have h2 := ymin_le' (fun j => fMBP (Fintype.card V) (qbar K q j)) j0
    try simp only at h1 h2
    rw [hyj0] at h2
    linarith
  have hV3 := lemma_2 P D w hm hP hD hw φ hφ (fun j => fMBP (Fintype.card V) (qbar K q j))
  have hV3' : Wspp P D w φ - gDual P D w φ (fun j => fMBP (Fintype.card V) (qbar K q j))
      ≤ -alphaConn P D φ * max 0 (a - 3 * (Fintype.card V : ℝ)) := by
    have := mul_le_mul_of_nonneg_left (max_le_max (le_refl (0 : ℝ)) hspread) hα.le
    linarith
  have hV4 : (if ∃ j, q j = 0 then (1 : ℝ) else 0) = 0 ∨
      ((if ∃ j, q j = 0 then (1 : ℝ) else 0) = 1 ∧ x0 = s / Kt (Fintype.card V) K) := by
    by_cases hex : ∃ j, q j = 0
    · right
      refine ⟨if_pos hex, ?_⟩
      obtain ⟨j, hj⟩ := hex
      have hq0 : q j0 = 0 := by
        have := hj0 j (Finset.mem_univ j); omega
      rw [hx0, hqbar, hq0]; simp
    · left; exact if_neg hex
  have hl := L1 s _ x0 hs2 hKtpos hx0s
  have hlpos : 0 < x0 - 1 / Kt (Fintype.card V) K := by linarith
  refine ⟨p / (2 * ((x0 - 1 / Kt (Fintype.card V) K) * Real.sqrt (x0 - 1 / Kt (Fintype.card V) K))),
    ?_, ?_⟩
  · intro j x hx hxpos
    rw [deriv_f _ x hxpos, abs_of_nonneg (by positivity), ← hpdef]
    have hxl : x0 - 1 / Kt (Fintype.card V) K ≤ x := by
      have := hx.1
      have := hx0le j
      linarith
    apply div_le_div_of_nonneg_left hppos.le (by positivity)
    have h1 := Real.sqrt_le_sqrt hxl
    have : (x0 - 1 / Kt (Fintype.card V) K) * Real.sqrt (x0 - 1 / Kt (Fintype.card V) K)
        ≤ x * Real.sqrt x :=
      mul_le_mul hxl h1 (Real.sqrt_nonneg _) hxpos.le
    linarith
  · exact core3 _ s _ x0 r p a _ β _ _ hm2 hs2 hs24 hsβ2 hsβ hKt hx0s hrpos hr2 hppos hp2 hadef
      hαβ hα hβpos hV3' hV4
