-- Prove2me | solution 1 for KendallQueues.GIMs.theorem4_conditional_laws
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T00:29:28.73982+00:00
-- url     : https://prove2.me/submissions/e9a1045c-be78-4312-af05-fd2c9aefa8e5

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal Nat
open QueueingFundamentals.Foundations QueueingFundamentals.GM1 KendallQueues.GIMs

namespace KQ4

open QueueingFundamentals.Foundations

variable (P : TransitionMatrix)

noncomputable def q (i j : ℕ) : ℝ≥0∞ := ENNReal.ofReal (P.p i j)

lemma q_rowsum (i : ℕ) : ∑' j, q P i j = 1 := by
  unfold q
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => P.nonneg i j) (P.row_sum i).summable,
    (P.row_sum i).tsum_eq]
  simp

noncomputable def Pn : ℕ → ℕ → ℕ → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑' k, q P i k * Pn n k j

lemma Pn_le_one : ∀ n i j, Pn P n i j ≤ 1
  | 0, i, j => by simp only [Pn]; split_ifs <;> simp
  | n + 1, i, j => by
      simp only [Pn]
      calc ∑' k, q P i k * Pn P n k j ≤ ∑' k, q P i k := ENNReal.tsum_le_tsum (fun k =>
              mul_le_of_le_one_right' (Pn_le_one n k j))
        _ = 1 := q_rowsum P i

lemma Pn_ne_top (n i j : ℕ) : Pn P n i j ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (Pn_le_one P n i j)

lemma stepProb_eq : ∀ n i j, P.stepProb n i j = (Pn P n i j).toReal
  | 0, i, j => by simp only [TransitionMatrix.stepProb, Pn]; split_ifs <;> simp
  | n + 1, i, j => by
      simp only [TransitionMatrix.stepProb, Pn]
      have hnn : ∀ k, 0 ≤ P.p i k * P.stepProb n k j := fun k =>
        mul_nonneg (P.nonneg i k) (by rw [stepProb_eq n k j]; exact ENNReal.toReal_nonneg)
      have hsum : Summable (fun k => P.p i k * P.stepProb n k j) := by
        refine Summable.of_nonneg_of_le hnn (fun k => ?_) (P.row_sum i).summable
        rw [stepProb_eq n k j]
        have : (Pn P n k j).toReal ≤ 1 :=
          ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using Pn_le_one P n k j)
        exact mul_le_of_le_one_right (P.nonneg i k) this
      rw [← ENNReal.toReal_ofReal (tsum_nonneg hnn), ENNReal.ofReal_tsum_of_nonneg hnn hsum]
      congr 1
      refine tsum_congr (fun k => ?_)
      rw [ENNReal.ofReal_mul (P.nonneg i k), stepProb_eq n k j,
        ENNReal.ofReal_toReal (Pn_ne_top P n k j)]
      rfl

lemma stat_iter (πe : ℕ → ℝ≥0∞) (hst : ∀ j, ∑' i, πe i * q P i j = πe j) :
    ∀ n j, ∑' i, πe i * Pn P n i j = πe j
  | 0, j => by
      simp only [Pn]
      rw [tsum_eq_single j (fun i hi => by simp [hi])]; simp
  | n + 1, j => by
      simp only [Pn]
      calc ∑' i, πe i * ∑' k, q P i k * Pn P n k j
          = ∑' i, ∑' k, πe i * q P i k * Pn P n k j := by
              congr 1; ext i; rw [← ENNReal.tsum_mul_left]; congr 1; ext k; ring
        _ = ∑' k, ∑' i, πe i * q P i k * Pn P n k j := ENNReal.tsum_comm
        _ = ∑' k, πe k * Pn P n k j := by
              congr 1; ext k; rw [ENNReal.tsum_mul_right, hst k]
        _ = πe j := stat_iter πe hst n j

/-! Product chain. -/

noncomputable def Q (x y : ℕ × ℕ) : ℝ≥0∞ := q P x.1 y.1 * q P x.2 y.2

lemma Q_rowsum (x : ℕ × ℕ) : ∑' y, Q P x y = 1 := by
  unfold Q
  rw [ENNReal.tsum_prod (f := fun a b => q P x.1 a * q P x.2 b)]
  simp_rw [ENNReal.tsum_mul_left, q_rowsum, mul_one]
  exact q_rowsum P x.1

lemma Q_fst (n : ℕ) (x : ℕ × ℕ) (k : ℕ) :
    ∑' y, Q P x y * Pn P n y.1 k = Pn P (n + 1) x.1 k := by
  unfold Q
  rw [ENNReal.tsum_prod (f := fun a b => q P x.1 a * q P x.2 b * Pn P n a k)]
  simp only [Pn]
  congr 1; ext a
  have e : ∀ b, q P x.1 a * q P x.2 b * Pn P n a k = q P x.2 b * (q P x.1 a * Pn P n a k) :=
    fun b => by ring
  simp_rw [e]
  rw [ENNReal.tsum_mul_right, q_rowsum, one_mul]

lemma Q_snd (n : ℕ) (x : ℕ × ℕ) (k : ℕ) :
    ∑' y, Q P x y * Pn P n y.2 k = Pn P (n + 1) x.2 k := by
  unfold Q
  rw [ENNReal.tsum_prod (f := fun a b => q P x.1 a * q P x.2 b * Pn P n b k), ENNReal.tsum_comm]
  simp only [Pn]
  congr 1; ext b
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_right, q_rowsum, one_mul]

variable (z : ℕ)

noncomputable def g : ℕ → ℕ × ℕ → ℝ≥0∞
  | 0, _ => 1
  | n + 1, x => ∑' y, if y = (z, z) then 0 else Q P x y * g n y

lemma g_succ_le : ∀ n x, g P z (n + 1) x ≤ g P z n x
  | 0, x => by
      simp only [g]
      calc ∑' y, (if y = (z, z) then 0 else Q P x y * 1) ≤ ∑' y, Q P x y :=
            ENNReal.tsum_le_tsum (fun y => by split_ifs <;> simp)
        _ = 1 := Q_rowsum P x
  | n + 1, x => by
      simp only [g]
      refine ENNReal.tsum_le_tsum (fun y => ?_)
      split_ifs
      · exact le_rfl
      · gcongr; exact g_succ_le n y

lemma g_anti (x : ℕ × ℕ) : Antitone (fun n => g P z n x) :=
  antitone_nat_of_succ_le (fun n => g_succ_le P z n x)

noncomputable def G (x : ℕ × ℕ) : ℝ≥0∞ := ⨅ n, g P z n x

lemma G_super (x : ℕ × ℕ) :
    ∑' y, (if y = (z, z) then 0 else Q P x y * G P z y) ≤ G P z x := by
  refine le_iInf (fun n => ?_)
  calc ∑' y, (if y = (z, z) then 0 else Q P x y * G P z y)
      ≤ ∑' y, (if y = (z, z) then 0 else Q P x y * g P z n y) := by
        refine ENNReal.tsum_le_tsum (fun y => ?_)
        split_ifs
        · exact le_rfl
        · gcongr; exact iInf_le _ n
    _ = g P z (n + 1) x := rfl
    _ ≤ g P z n x := g_succ_le P z n x

lemma G_prop (hzz : G P z (z, z) = 0) : ∀ m (x1 x2 : ℕ), G P z (x1, x2) = 0 → ∀ i j, Pn P m x1 i ≠ 0 →
    Pn P m x2 j ≠ 0 → G P z (i, j) = 0
  | 0, x1, x2, h, i, j, hi, hj => by
      simp only [Pn] at hi hj
      split_ifs at hi hj with h1 h2
      · subst h1; subst h2; exact h
      all_goals simp_all
  | m + 1, x1, x2, h, i, j, hi, hj => by
      simp only [Pn] at hi hj
      obtain ⟨k, hk⟩ : ∃ k, q P x1 k * Pn P m k i ≠ 0 := by
        by_contra hc; push Not at hc; exact hi (ENNReal.tsum_eq_zero.mpr hc)
      obtain ⟨l, hl⟩ : ∃ l, q P x2 l * Pn P m l j ≠ 0 := by
        by_contra hc; push Not at hc; exact hj (ENNReal.tsum_eq_zero.mpr hc)
      have hk1 : q P x1 k ≠ 0 := left_ne_zero_of_mul hk
      have hk2 : Pn P m k i ≠ 0 := right_ne_zero_of_mul hk
      have hl1 : q P x2 l ≠ 0 := left_ne_zero_of_mul hl
      have hl2 : Pn P m l j ≠ 0 := right_ne_zero_of_mul hl
      have hG : G P z (k, l) = 0 := by
        by_cases hkl : (k, l) = (z, z)
        · rw [hkl]; exact hzz
        · have h1 := ENNReal.le_tsum (f := fun y => if y = (z, z) then 0 else
              Q P (x1, x2) y * G P z y) (k, l)
          simp only [hkl, if_false] at h1
          have h2 := le_trans h1 (G_super P z (x1, x2))
          rw [h, nonpos_iff_eq_zero] at h2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · exact absurd h3 (mul_ne_zero hk1 hl1)
          · exact h3
      exact G_prop hzz m k l hG i j hk2 hl2

/-! Kac identity for the product chain. -/

lemma my_split (f : ℕ × ℕ → ℝ≥0∞) (b : ℕ × ℕ) :
    ∑' y, f y = f b + ∑' y, (if y = b then 0 else f y) := by
  convert ENNReal.tsum_eq_add_tsum_ite (f := f) b

noncomputable def Pi2 (πe : ℕ → ℝ≥0∞) (x : ℕ × ℕ) : ℝ≥0∞ := πe x.1 * πe x.2

lemma Pi2_stat (πe : ℕ → ℝ≥0∞) (hst : ∀ j, ∑' i, πe i * q P i j = πe j) (y : ℕ × ℕ) :
    ∑' x, Pi2 πe x * Q P x y = Pi2 πe y := by
  unfold Pi2 Q
  rw [ENNReal.tsum_prod (f := fun a b => πe a * πe b * (q P a y.1 * q P b y.2))]
  have e : ∀ a b, πe a * πe b * (q P a y.1 * q P b y.2) =
      (πe a * q P a y.1) * (πe b * q P b y.2) := fun a b => by ring
  simp_rw [e, ENNReal.tsum_mul_left, hst, ENNReal.tsum_mul_right, hst]

lemma A_succ (πe : ℕ → ℝ≥0∞) (hst : ∀ j, ∑' i, πe i * q P i j = πe j) (n : ℕ) :
    ∑' x, Pi2 πe x * g P z (n + 1) x =
      ∑' y, (if y = (z, z) then 0 else Pi2 πe y * g P z n y) := by
  simp only [g]
  calc ∑' x, Pi2 πe x * ∑' y, (if y = (z, z) then 0 else Q P x y * g P z n y)
      = ∑' x, ∑' y, (if y = (z, z) then 0 else Pi2 πe x * Q P x y * g P z n y) := by
        congr 1; ext x; rw [← ENNReal.tsum_mul_left]; congr 1; ext y
        split_ifs <;> simp [mul_assoc]
    _ = ∑' y, ∑' x, (if y = (z, z) then 0 else Pi2 πe x * Q P x y * g P z n y) :=
        ENNReal.tsum_comm
    _ = _ := by
        congr 1; ext y; split_ifs
        · simp
        · rw [ENNReal.tsum_mul_right, Pi2_stat P πe hst y]

lemma A_sum (πe : ℕ → ℝ≥0∞) (hst : ∀ j, ∑' i, πe i * q P i j = πe j)
    (hone : ∑' i, πe i = 1) : ∀ N, ∑ n ∈ Finset.range N, Pi2 πe (z, z) * g P z n (z, z) +
      ∑' x, Pi2 πe x * g P z N x = 1
  | 0 => by
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, g, mul_one]
      unfold Pi2
      rw [ENNReal.tsum_prod (f := fun a b => πe a * πe b)]
      simp_rw [ENNReal.tsum_mul_left, hone, mul_one]
      exact hone
  | N + 1 => by
      have h := my_split (fun x => Pi2 πe x * g P z N x) (z, z)
      rw [Finset.sum_range_succ, add_assoc, A_succ P z πe hst N, ← h]
      exact A_sum πe hst hone N

lemma G_zz (πe : ℕ → ℝ≥0∞) (hst : ∀ j, ∑' i, πe i * q P i j = πe j)
    (hone : ∑' i, πe i = 1) (hpos : πe z ≠ 0) (hfin : πe z ≠ ⊤) : G P z (z, z) = 0 := by
  have h1 : ∑' n, Pi2 πe (z, z) * g P z n (z, z) ≤ 1 :=
    ENNReal.tsum_le_of_sum_range_le (fun N => by
      rw [← A_sum P z πe hst hone N]; exact le_self_add)
  have hc0 : Pi2 πe (z, z) ≠ 0 := mul_ne_zero hpos hpos
  have hct : Pi2 πe (z, z) ≠ ⊤ := ENNReal.mul_ne_top hfin hfin
  have h2 : ∑' n, g P z n (z, z) ≠ ⊤ := by
    intro htop
    rw [ENNReal.tsum_mul_left, htop, ENNReal.mul_top hc0] at h1
    exact absurd h1 (by simp)
  have h3 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h2
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' h3 (fun n => iInf_le (fun n => g P z n (z, z)) n))

lemma g_tendsto (hzz : G P z (z, z) = 0)
    (hreach : ∀ i j, ∃ m, Pn P m z i ≠ 0 ∧ Pn P m z j ≠ 0) (i j : ℕ) :
    Tendsto (fun n => g P z n (i, j)) atTop (𝓝 0) := by
  obtain ⟨m, h1, h2⟩ := hreach i j
  have hG := G_prop P z hzz m z z hzz i j h1 h2
  have := tendsto_atTop_iInf (g_anti P z (i, j))
  unfold G at hG
  rwa [hG] at this

/-! First-entrance decomposition. -/

noncomputable def tt (c : ℕ × ℕ → ℕ) : ℕ → ℕ × ℕ → ℕ → ℝ≥0∞
  | 0, x, k => if c x = k then 1 else 0
  | n + 1, x, k => ∑' y, if y = (z, z) then 0 else Q P x y * tt c n y k

noncomputable def hh : ℕ → ℕ × ℕ → ℝ≥0∞
  | 0, x => Q P x (z, z)
  | n + 1, x => ∑' y, if y = (z, z) then 0 else Q P x y * hh n y

lemma tt_le_g (c : ℕ × ℕ → ℕ) : ∀ n x k, tt P z c n x k ≤ g P z n x
  | 0, x, k => by simp only [tt, g]; split_ifs <;> simp
  | n + 1, x, k => by
      simp only [tt, g]
      refine ENNReal.tsum_le_tsum (fun y => ?_)
      split_ifs
      · exact le_rfl
      · gcongr; exact tt_le_g c n y k

lemma g_le_one (n : ℕ) (x : ℕ × ℕ) : g P z n x ≤ 1 :=
  le_trans (g_anti P z x (Nat.zero_le n)) (by simp [g])

lemma decomp (c : ℕ × ℕ → ℕ)
    (hc : ∀ n x k, ∑' y, Q P x y * Pn P n (c y) k = Pn P (n + 1) (c x) k)
    (hcz : c (z, z) = z) : ∀ n x k, Pn P n (c x) k =
      tt P z c n x k + ∑ m ∈ Finset.range n, hh P z m x * Pn P (n - (m + 1)) z k
  | 0, x, k => by simp [tt, Pn]
  | n + 1, x, k => by
      have h0 := my_split (fun y => Q P x y * Pn P n (c y) k) (z, z)
      simp only [hcz] at h0
      have hIH : ∀ y, (if y = (z, z) then 0 else Q P x y * Pn P n (c y) k) =
          (if y = (z, z) then 0 else Q P x y * tt P z c n y k) +
          ∑ m ∈ Finset.range n,
            (if y = (z, z) then 0 else Q P x y * hh P z m y) * Pn P (n - (m + 1)) z k := by
        intro y
        split_ifs
        · simp
        · rw [decomp c hc hcz n y k, mul_add, Finset.mul_sum]
          congr 1; exact Finset.sum_congr rfl (fun m _ => by ring)
      rw [← hc n x k, h0, tsum_congr hIH]
      rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      simp_rw [ENNReal.tsum_mul_right]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, zero_add, Nat.add_sub_cancel, tt, hh]
      ring

lemma diff_bound (n i j k : ℕ) :
    |P.stepProb n i k - P.stepProb n j k| ≤ (g P z n (i, j)).toReal := by
  have h1 := decomp P z Prod.fst (Q_fst P) rfl n (i, j) k
  have h2 := decomp P z Prod.snd (Q_snd P) rfl n (i, j) k
  simp only at h1 h2
  rw [stepProb_eq, stepProb_eq, h1, h2]
  have hg : g P z n (i, j) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (g_le_one P z n _)
  have ht1 := tt_le_g P z Prod.fst n (i, j) k
  have ht2 := tt_le_g P z Prod.snd n (i, j) k
  have hS : ∑ m ∈ Finset.range n, hh P z m (i, j) * Pn P (n - (m + 1)) z k ≠ ⊤ :=
    ne_top_of_le_ne_top (Pn_ne_top P n i k) (h1 ▸ le_add_self)
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top hg ht1) hS,
    ENNReal.toReal_add (ne_top_of_le_ne_top hg ht2) hS, add_sub_add_right_eq_sub,
    abs_sub_le_iff]
  have e1 := ENNReal.toReal_mono hg ht1
  have e2 := ENNReal.toReal_mono hg ht2
  constructor <;> linarith [(tt P z Prod.fst n (i, j) k).toReal_nonneg,
    (tt P z Prod.snd n (i, j) k).toReal_nonneg]

theorem converge (π : ℕ → ℝ) (hπ0 : ∀ j, 0 ≤ π j) (hπ1 : HasSum π 1)
    (hst : ∀ j, HasSum (fun i => π i * P.p i j) (π j)) (hz : 0 < π z)
    (hreach : ∀ i j, ∃ m, 0 < P.stepProb m z i ∧ 0 < P.stepProb m z j) :
    ∀ i j, Tendsto (fun n => P.stepProb n i j) atTop (𝓝 (π j)) := by
  set πe : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (π i) with hπe
  have hste : ∀ j, ∑' i, πe i * q P i j = πe j := by
    intro j
    have e : πe j = ENNReal.ofReal (∑' i, π i * P.p i j) := by rw [(hst j).tsum_eq]
    rw [e, ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hπ0 i) (P.nonneg i j))
      (hst j).summable]
    congr 1; ext i; rw [ENNReal.ofReal_mul (hπ0 i)]; rfl
  have hone : ∑' i, πe i = 1 := by
    rw [hπe, ← ENNReal.ofReal_tsum_of_nonneg hπ0 hπ1.summable, hπ1.tsum_eq, ENNReal.ofReal_one]
  have hzz := G_zz P z πe hste hone (by simp [hπe, hz]) ENNReal.ofReal_ne_top
  have hreach' : ∀ i j, ∃ m, Pn P m z i ≠ 0 ∧ Pn P m z j ≠ 0 := by
    intro i j
    obtain ⟨m, h1, h2⟩ := hreach i j
    refine ⟨m, fun h => ?_, fun h => ?_⟩
    · rw [stepProb_eq, h] at h1; simp at h1
    · rw [stepProb_eq, h] at h2; simp at h2
  intro i j
  have hsP : ∀ n k, 0 ≤ P.stepProb n k j ∧ P.stepProb n k j ≤ 1 := fun n k => by
    rw [stepProb_eq]
    exact ⟨ENNReal.toReal_nonneg,
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using Pn_le_one P n k j)⟩
  have key : ∀ n, P.stepProb n i j - π j =
      ∑' k, π k * (P.stepProb n i j - P.stepProb n k j) := by
    intro n
    have e1 : HasSum (fun k => π k * P.stepProb n k j) (π j) := by
      have hs : Summable (fun k => π k * P.stepProb n k j) :=
        Summable.of_nonneg_of_le (fun k => mul_nonneg (hπ0 k) (hsP n k).1)
          (fun k => mul_le_of_le_one_right (hπ0 k) (hsP n k).2) hπ1.summable
      have h := congrArg ENNReal.toReal (stat_iter P πe hste n j)
      rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (Pn_ne_top P n k j))] at h
      simp only [hπe, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hπ0 _), ← stepProb_eq] at h
      rw [← h]; exact hs.hasSum
    have e2 := (hπ1.mul_right (P.stepProb n i j)).sub e1
    simp only [one_mul] at e2
    rw [← e2.tsum_eq]
    congr 1; ext k; ring
  have hlim : Tendsto (fun n => ∑' k, π k * (P.stepProb n i j - P.stepProb n k j))
      atTop (𝓝 (∑' k : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := π) hπ1.summable (fun k => ?_)
      (Eventually.of_forall (fun n k => ?_))
    · have hgk := g_tendsto P z hzz hreach' i k
      have hgr : Tendsto (fun n => (g P z n (i, k)).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgk
        simpa [Function.comp_def] using this
      have hb : Tendsto (fun n => π k * (g P z n (i, k)).toReal) atTop (𝓝 0) := by
        simpa using hgr.const_mul (π k)
      refine squeeze_zero_norm (fun n => ?_) hb
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hπ0 k)]
      exact mul_le_mul_of_nonneg_left (diff_bound P z n i k j) (hπ0 k)
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hπ0 k)]
      refine mul_le_of_le_one_right (hπ0 k) ?_
      rw [abs_sub_le_iff]
      constructor <;> linarith [hsP n i, hsP n k]
  simp only [tsum_zero] at hlim
  have := hlim.add_const (π j)
  simp only [zero_add] at this
  refine this.congr (fun n => ?_)
  rw [← key n]; ring

end KQ4

namespace KQ4

open QueueingFundamentals.Foundations

variable (P : TransitionMatrix)

/-! ## Part B: stationary vector via cut equations -/

lemma esplit (f : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' i, f i = ∑ i ∈ Finset.range k, f i + ∑' i, f (i + k) :=
  (ENNReal.summable.sum_add_tsum_nat_add').symm

lemma esplit0 (f : ℕ → ℝ≥0∞) : ∑' i, f i = f 0 + ∑' i, f (i + 1) :=
  tsum_eq_zero_add' ENNReal.summable

noncomputable def xP (x : ℕ → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ := ∑' i, x i * q P i k
noncomputable def Up (j : ℕ) (x : ℕ → ℝ≥0∞) : ℝ≥0∞ := x (j - 1) * q P (j - 1) j
noncomputable def Dn (j : ℕ) (x : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m, x (m + j) * ∑ k ∈ Finset.range j, q P (m + j) k
noncomputable def Rr (j : ℕ) (x : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m, x (m + j) * ∑' l, q P (m + j) (l + j)

variable (hskip : ∀ i j, i + 1 < j → q P i j = 0)
include hskip

lemma I1 (x : ℕ → ℝ≥0∞) (j : ℕ) (hj : 1 ≤ j) :
    ∑' l, xP P x (l + j) = Up P j x + Rr P j x := by
  unfold xP Up Rr
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [esplit _ j]
  congr 1
  rw [Finset.sum_eq_single (j - 1)]
  · congr 1
    rw [tsum_eq_single 0]
    · simp
    · intro l hl
      exact hskip _ _ (by omega)
  · intro i hi hne
    rw [Finset.mem_range] at hi
    have : ∀ l, q P i (l + j) = 0 := fun l => hskip _ _ (by omega)
    simp [this]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

omit hskip in
lemma I2 (x : ℕ → ℝ≥0∞) (j : ℕ) :
    ∑' m, x (m + j) = Dn P j x + Rr P j x := by
  unfold Dn Rr
  rw [← ENNReal.tsum_add]
  refine tsum_congr (fun m => ?_)
  rw [← mul_add, ← esplit, q_rowsum, mul_one]

omit hskip in
lemma I3 (x : ℕ → ℝ≥0∞) : ∑' k, xP P x k = ∑' i, x i := by
  unfold xP
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, q_rowsum, mul_one]

omit hskip in
lemma shift_le (x : ℕ → ℝ≥0∞) (j : ℕ) : ∑' m, x (m + j) ≤ ∑' i, x i := by
  rw [esplit x j]; exact le_add_self

lemma tailcut (s : ℕ) (hs : 1 ≤ s) (x : ℕ → ℝ≥0∞) (hfin : ∑' i, x i ≠ ⊤)
    (htail : ∀ k, s ≤ k → xP P x k = x k) (j : ℕ) (hj : s ≤ j) : Up P j x = Dn P j x := by
  have h1 := I1 P hskip x j (by omega)
  have h2 := I2 P x j
  have e : ∑' l, xP P x (l + j) = ∑' l, x (l + j) :=
    tsum_congr (fun l => htail _ (by omega))
  rw [e, h2] at h1
  have hR : Rr P j x ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (le_trans ?_ (shift_le x j))
    rw [I2 P x j]; exact le_add_self
  exact ((ENNReal.add_left_inj hR).mp h1).symm

lemma allcut (x : ℕ → ℝ≥0∞) (hfin : ∑' i, x i ≠ ⊤)
    (hcut : ∀ j, 1 ≤ j → Up P j x = Dn P j x) (k : ℕ) : xP P x k = x k := by
  have hTU : ∀ j, ∑' l, xP P x (l + j) = ∑' l, x (l + j) := by
    intro j
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simpa using I3 P x
    · rw [I1 P hskip x j h, I2 P x j, hcut j h]
  have hT := esplit0 (fun l => xP P x (l + k))
  have hU := esplit0 (fun l => x (l + k))
  simp only [zero_add] at hT hU
  have e1 : ∀ l, l + 1 + k = l + (k + 1) := fun l => by omega
  simp only [e1] at hT hU
  rw [hTU k, hTU (k + 1)] at hT
  rw [hT] at hU
  have hfin' : ∑' l, x (l + (k + 1)) ≠ ⊤ := ne_top_of_le_ne_top hfin (shift_le x _)
  exact (ENNReal.add_left_inj hfin').mp hU


omit hskip in
lemma tail_col (s : ℕ) (L : ℝ≥0∞) (c : ℕ → ℝ≥0∞) (x : ℕ → ℝ≥0∞) (hs : 1 ≤ s)
    (htailq : ∀ i k, s ≤ k → q P i k = if k ≤ i + 1 then c (i + 1 - k) else 0)
    (hfix : ∑' m, L ^ m * c m = L)
    (hskip : ∀ i j, i + 1 < j → q P i j = 0)
    (hx : ∀ i, s - 1 ≤ i → x i = L ^ (i - (s - 1))) (k : ℕ) (hk : s ≤ k) :
    xP P x k = x k := by
  unfold xP
  rw [esplit _ (k - 1)]
  have h0 : ∑ i ∈ Finset.range (k - 1), x i * q P i k = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [hskip i k (by omega), mul_zero]
  rw [h0, zero_add]
  have e : ∀ m, x (m + (k - 1)) * q P (m + (k - 1)) k = L ^ (k - s) * (L ^ m * c m) := by
    intro m
    rw [hx _ (by omega), htailq _ _ hk, if_pos (by omega)]
    have e1 : m + (k - 1) - (s - 1) = m + (k - s) := by omega
    have e2 : m + (k - 1) + 1 - k = m := by omega
    rw [e1, e2, pow_add]; ring
  simp_rw [e]
  rw [ENNReal.tsum_mul_left, hfix, hx k (by omega), ← pow_succ]
  congr 1; omega

omit hskip in
lemma sum_fin (s : ℕ) (L : ℝ≥0∞) (hL : L < 1) (x : ℕ → ℝ≥0∞) (hxt : ∀ k, x k ≠ ⊤)
    (hx : ∀ i, s - 1 ≤ i → x i = L ^ (i - (s - 1))) : ∑' i, x i ≠ ⊤ := by
  rw [esplit x (s - 1)]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr (fun i _ => hxt i), ?_⟩
  have e : ∀ m, x (m + (s - 1)) = L ^ m := fun m => by
    rw [hx _ (by omega)]; congr 1; omega
  simp_rw [e]
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hL).ne'

omit hskip in
lemma Up_update (j i0 : ℕ) (v : ℝ≥0∞) (x : ℕ → ℝ≥0∞) (h : i0 < j - 1) :
    Up P j (Function.update x i0 v) = Up P j x := by
  unfold Up; rw [Function.update_of_ne (by omega)]

omit hskip in
lemma Dn_update (j i0 : ℕ) (v : ℝ≥0∞) (x : ℕ → ℝ≥0∞) (h : i0 < j) :
    Dn P j (Function.update x i0 v) = Dn P j x := by
  unfold Dn; congr 1; ext m; rw [Function.update_of_ne (by omega)]

lemma bdry (s : ℕ) (hs : 1 ≤ s) (L : ℝ≥0∞) (c : ℕ → ℝ≥0∞) (hL0 : L ≠ 0) (hL1 : L < 1)
    (htailq : ∀ i k, s ≤ k → q P i k = if k ≤ i + 1 then c (i + 1 - k) else 0)
    (hfix : ∑' m, L ^ m * c m = L)
    (hdown : ∀ j, 1 ≤ j → j < s → q P j 0 ≠ 0) (hup : ∀ i, q P i (i + 1) ≠ 0) :
    ∀ d, d ≤ s - 1 → ∃ x : ℕ → ℝ≥0∞, (∀ i, s - 1 ≤ i → x i = L ^ (i - (s - 1))) ∧
      (∀ k, x k ≠ ⊤) ∧ (∀ k, s - 1 - d ≤ k → x k ≠ 0) ∧
      (∀ j, s - d ≤ j → 1 ≤ j → Up P j x = Dn P j x)
  | 0, _ => by
      have hLt : L ≠ ⊤ := ne_top_of_lt hL1
      set x : ℕ → ℝ≥0∞ := fun i => if s - 1 ≤ i then L ^ (i - (s - 1)) else 0 with hxdef
      have hx1 : ∀ i, s - 1 ≤ i → x i = L ^ (i - (s - 1)) := fun i hi => by simp only [hxdef]; rw [if_pos hi]
      have hx2 : ∀ k, x k ≠ ⊤ := fun k => by
        simp only [hxdef]; split_ifs
        · exact ENNReal.pow_ne_top hLt
        · exact ENNReal.zero_ne_top
      refine ⟨x, hx1, hx2, fun k hk => ?_, fun j hj _ => ?_⟩
      · rw [hx1 k (by omega)]; exact pow_ne_zero _ hL0
      · exact tailcut P hskip s hs x (sum_fin s L hL1 x hx2 hx1)
          (tail_col P s L c x hs htailq hfix hskip hx1) j (by omega)
  | d + 1, hd => by
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ := bdry s hs L c hL0 hL1 htailq hfix hdown hup d (by omega)
      obtain ⟨j0, hj0d⟩ : ∃ j0, j0 = s - 1 - d := ⟨_, rfl⟩
      obtain ⟨i0, hi0d⟩ : ∃ i0, i0 = j0 - 1 := ⟨_, rfl⟩
      have hj0 : 1 ≤ j0 := by omega
      have hfin := sum_fin s L hL1 x hx2 hx1
      have hq0 : q P i0 j0 ≠ 0 := by
        have := hup i0; rwa [show i0 + 1 = j0 by omega] at this
      have hqt : q P i0 j0 ≠ ⊤ := ENNReal.ofReal_ne_top
      have hDt : Dn P j0 x ≠ ⊤ := by
        refine ne_top_of_le_ne_top hfin (le_trans ?_ (shift_le x j0))
        rw [I2 P x j0]; exact le_self_add
      have hD0 : Dn P j0 x ≠ 0 := by
        intro h
        have h0 := (ENNReal.tsum_eq_zero.mp h) 0
        simp only [zero_add] at h0
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact hx3 j0 (by omega) h1
        · have := (Finset.sum_eq_zero_iff.mp h1) 0 (Finset.mem_range.mpr hj0)
          exact hdown j0 hj0 (by omega) this
      refine ⟨Function.update x i0 (Dn P j0 x / q P i0 j0), fun i hi => ?_, fun k => ?_,
        fun k hk => ?_, fun j hj h1 => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hx1 i hi
      · by_cases hk : k = i0
        · rw [hk, Function.update_self]; exact ENNReal.div_ne_top hDt hq0
        · rw [Function.update_of_ne hk]; exact hx2 k
      · by_cases hk' : k = i0
        · rw [hk', Function.update_self]
          simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]; exact ⟨hD0, hqt⟩
        · rw [Function.update_of_ne hk']; exact hx3 k (by omega)
      · by_cases hjj : j = j0
        · rw [hjj, Dn_update P j0 i0 _ x (by omega)]
          unfold Up
          rw [show j0 - 1 = i0 by omega, Function.update_self, ENNReal.div_mul_cancel hq0 hqt]
        · rw [Up_update P j i0 _ x (by omega), Dn_update P j i0 _ x (by omega)]
          exact hx4 j (by omega) h1

lemma statB (s : ℕ) (hs : 1 ≤ s) (L : ℝ≥0∞) (c : ℕ → ℝ≥0∞) (hL0 : L ≠ 0) (hL1 : L < 1)
    (htailq : ∀ i k, s ≤ k → q P i k = if k ≤ i + 1 then c (i + 1 - k) else 0)
    (hfix : ∑' m, L ^ m * c m = L)
    (hdown : ∀ j, 1 ≤ j → j < s → q P j 0 ≠ 0) (hup : ∀ i, q P i (i + 1) ≠ 0) :
    ∃ x : ℕ → ℝ≥0∞, (∀ i, s - 1 ≤ i → x i = L ^ (i - (s - 1))) ∧
      (∀ k, x k ≠ ⊤) ∧ (∀ k, x k ≠ 0) ∧ ∑' i, x i ≠ ⊤ ∧ (∀ k, xP P x k = x k) := by
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ :=
    bdry P hskip s hs L c hL0 hL1 htailq hfix hdown hup (s - 1) le_rfl
  have hfin := sum_fin s L hL1 x hx2 hx1
  exact ⟨x, hx1, hx2, fun k => hx3 k (by omega), hfin,
    allcut P hskip x hfin (fun j hj => hx4 j (by omega) hj)⟩

end KQ4

namespace KQ4C

lemma gims_skip (s : ℕ) (A : Measure ℝ) (b : ℝ) (i j : ℕ) (h : i + 1 < j) :
    gimsMatrix s A b i j = 0 := by
  unfold gimsMatrix
  split_ifs <;> first | rfl | (exfalso; omega)

lemma gims_tail (s : ℕ) (A : Measure ℝ) (b : ℝ) (i k : ℕ) (hk : s ≤ k) :
    gimsMatrix s A b i k = if k ≤ i + 1 then paren A b s (i + 1 - k) else 0 := by
  unfold gimsMatrix; rw [if_pos hk]

lemma hexp (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / (n ! : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

variable {A : Measure ℝ}

lemma A_Ioi_pos (a : ℝ) (ha : 0 < a) (hA : IsInterarrivalLaw A a⁻¹) : 0 < A (Set.Ioi 0) := by
  by_contra h
  push Not at h
  have h0 : A (Set.Ioi 0) = 0 := nonpos_iff_eq_zero.mp h
  have hae : (fun x : ℝ => x) =ᵐ[A] 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hA.nonneg h0)
    simp only [Set.mem_ofPred_eq, Pi.zero_apply] at hx
    rcases lt_or_gt_of_ne hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hm := hA.mean
  rw [integral_congr_ae hae] at hm
  simp only [Pi.zero_apply, integral_zero, one_div, inv_inv] at hm
  linarith

lemma intOn_bdd (hA : IsProbabilityMeasure A) (g : ℝ → ℝ) (hgc : Continuous g) (C : ℝ)
    (hgb : ∀ u, 0 ≤ u → |g u| ≤ C) : IntegrableOn g (Set.Ici 0) A := by
  have : Integrable g (A.restrict (Set.Ici 0)) :=
    (integrable_const C).mono' hgc.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      rw [Real.norm_eq_abs]; exact hgb u hu)
  exact this

lemma pos_int (a : ℝ) (ha : 0 < a) (hA : IsInterarrivalLaw A a⁻¹) (g : ℝ → ℝ)
    (hgc : Continuous g) (hg0 : ∀ u, 0 ≤ u → 0 ≤ g u) (hg1 : ∀ u, 0 < u → 0 < g u)
    (hgb : ∀ u, 0 ≤ u → g u ≤ 1) : 0 < ∫ u in Set.Ici (0 : ℝ), g u ∂A := by
  haveI := hA.isProbability
  have hint : IntegrableOn g (Set.Ici 0) A :=
    intOn_bdd hA.isProbability g hgc 1 (fun u hu => by
      rw [abs_of_nonneg (hg0 u hu)]; exact hgb u hu)
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · refine lt_of_lt_of_le (A_Ioi_pos a ha hA) (measure_mono (fun u hu => ⟨?_, ?_⟩))
    · exact (hg1 u (Set.mem_Ioi.mp hu)).ne'
    · exact Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hu))
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu using hg0 u hu

lemma bracket_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹)
    (m : ℕ) (hm : 1 ≤ m) : 0 < bracket A b m m := by
  have e : bracket A b m m = ∫ u in Set.Ici (0 : ℝ), (1 - Real.exp (-u / b)) ^ m ∂A := by
    unfold bracket; congr 1; ext u; simp [deathProb]
  rw [e]
  refine pos_int a ha hA _ (by fun_prop) (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_)
  · have : Real.exp (-u / b) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := div_nonneg hu hb.le; linarith [neg_div b u])
    exact pow_nonneg (by linarith) _
  · have : Real.exp (-u / b) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by
        have := div_pos hu hb; rw [neg_div]; linarith)
    exact pow_pos (by linarith) _
  · have h1 : Real.exp (-u / b) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := div_nonneg hu hb.le; linarith [neg_div b u])
    have h2 : 0 < Real.exp (-u / b) := Real.exp_pos _
    exact pow_le_one₀ (by linarith) (by linarith)

lemma up_pos (s : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹)
    (i : ℕ) : 0 < gimsMatrix s A b i (i + 1) := by
  unfold gimsMatrix
  by_cases h : s ≤ i + 1
  · rw [if_pos h, if_pos le_rfl, Nat.sub_self]
    have e : paren A b s 0 = ∫ t in Set.Ici (0 : ℝ), Real.exp (-((s : ℝ) / b) * t) ∂A := by
      unfold paren serviceProb; congr 1; ext t; simp
    rw [e]
    have hμ : 0 ≤ (s : ℝ) / b := div_nonneg (Nat.cast_nonneg _) hb.le
    refine pos_int a ha hA _ (by fun_prop) (fun u _ => (Real.exp_pos _).le)
      (fun u _ => Real.exp_pos _) (fun u hu => Real.exp_le_one_iff.mpr ?_)
    nlinarith
  · rw [if_neg h, if_pos (by omega), if_pos le_rfl, Nat.sub_self]
    have e : bracket A b 0 (i + 1) =
        ∫ u in Set.Ici (0 : ℝ), Real.exp (-((i + 1 : ℕ) : ℝ) * u / b) ∂A := by
      unfold bracket; congr 1; ext u; simp [deathProb]
    rw [e]
    refine pos_int a ha hA _ (by fun_prop) (fun u _ => (Real.exp_pos _).le)
      (fun u _ => Real.exp_pos _) (fun u hu => Real.exp_le_one_iff.mpr ?_)
    have : 0 ≤ ((i + 1 : ℕ) : ℝ) * u / b := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hb.le
    rw [neg_mul, neg_div]; linarith

lemma p00_pos (s : ℕ) (hs : 1 ≤ s) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : IsInterarrivalLaw A a⁻¹) : 0 < gimsMatrix s A b 0 0 := by
  unfold gimsMatrix
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  exact bracket_pos a b ha hb hA 1 le_rfl

lemma down_pos (s : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : IsInterarrivalLaw A a⁻¹) (j : ℕ) (hj : j < s) : 0 < gimsMatrix s A b j 0 := by
  unfold gimsMatrix
  rw [if_neg (by omega), if_pos hj, if_pos (by omega), Nat.sub_zero]
  exact bracket_pos a b ha hb hA (j + 1) (by omega)

/-- `∑ λ^m (m | s) = F(λ) = λ`. -/
lemma fixed_point (s : ℕ) (a b : ℝ) (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hF : F s A b lam = lam) :
    ∑' m, (ENNReal.ofReal lam) ^ m * ENNReal.ofReal (paren A b s m) = ENNReal.ofReal lam := by
  haveI := hA.isProbability
  set μ : ℝ := (s : ℝ) / b with hμdef
  have hμ : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) hb.le
  set f : ℕ → ℝ → ℝ := fun m t => Real.exp (-μ * t) * ((lam * (μ * t)) ^ m / (m ! : ℝ)) with hf
  have hfc : ∀ m, Continuous (f m) := fun m => by simp only [hf]; fun_prop
  have hf0 : ∀ m t, 0 ≤ t → 0 ≤ f m t := fun m t ht => by
    simp only [hf]; positivity
  -- each term
  have hterm : ∀ m, (ENNReal.ofReal lam) ^ m * ENNReal.ofReal (paren A b s m) =
      ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (f m t) ∂A := by
    intro m
    have e1 : lam ^ m * paren A b s m = ∫ t in Set.Ici (0 : ℝ), f m t ∂A := by
      unfold paren serviceProb
      rw [← integral_const_mul]
      congr 1; ext t; simp only [hf, hμdef]; rw [mul_pow]; ring
    rw [← ENNReal.ofReal_pow hlam, ← ENNReal.ofReal_mul (pow_nonneg hlam _), e1]
    refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
    · refine (integrable_const (1 : ℝ)).mono' (hfc m).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 m t ht)]
      -- f m t ≤ exp(-μt) * exp(lam μ t) ≤ 1
      have hx : 0 ≤ lam * (μ * t) := mul_nonneg hlam (mul_nonneg hμ ht)
      have h1 : (lam * (μ * t)) ^ m / (m ! : ℝ) ≤ Real.exp (lam * (μ * t)) := by
        have := Real.sum_le_exp_of_nonneg hx (m + 1)
        refine le_trans ?_ this
        rw [Finset.sum_range_succ]
        have : 0 ≤ ∑ i ∈ Finset.range m, (lam * (μ * t)) ^ i / (i ! : ℝ) :=
          Finset.sum_nonneg (fun i _ => by positivity)
        linarith
      simp only [hf]
      calc Real.exp (-μ * t) * ((lam * (μ * t)) ^ m / (m ! : ℝ))
          ≤ Real.exp (-μ * t) * Real.exp (lam * (μ * t)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Real.exp (-(1 - lam) * (μ * t)) := by rw [← Real.exp_add]; ring_nf
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by
            have := mul_nonneg (sub_nonneg.mpr hlam1) (mul_nonneg hμ ht)
            linarith)
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht using hf0 m t ht
  simp_rw [hterm]
  rw [← lintegral_tsum (fun m => ((hfc m).measurable.ennreal_ofReal).aemeasurable)]
  have hinside : ∀ t, 0 ≤ t → ∑' m, ENNReal.ofReal (f m t) =
      ENNReal.ofReal (Real.exp (-(1 - lam) * s * t / b)) := by
    intro t ht
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => hf0 m t ht)
      ((Real.summable_pow_div_factorial _).mul_left _)]
    congr 1
    simp only [hf]
    rw [tsum_mul_left, ← hexp, ← Real.exp_add]
    congr 1; simp only [hμdef]; field_simp; ring
  rw [setLIntegral_congr_fun measurableSet_Ici (fun t ht => hinside t ht)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · unfold F at hF; rw [hF]
  · refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ (1 - lam) * s * t / b :=
      div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hlam1) (Nat.cast_nonneg _)) ht) hb.le
    have e : -(1 - lam) * s * t / b = -((1 - lam) * s * t / b) := by ring
    rw [e]; linarith
  · filter_upwards with t using (Real.exp_pos _).le

end KQ4C

namespace KQ4D

lemma hexp (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / (n ! : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma erlang_deriv (μ : ℝ) : ∀ (m : ℕ) (x : ℝ), HasDerivAt
    (fun x => Real.exp (-μ * x) * ∑ r ∈ Finset.range (m + 1), (μ * x) ^ r / (r ! : ℝ))
    (-(μ * (μ * x) ^ m / (m ! : ℝ) * Real.exp (-μ * x))) x
  | 0, x => by
      have h := ((hasDerivAt_id x).const_mul (-μ)).exp
      simp only [zero_add, Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, mul_one, id] at h ⊢
      convert h using 1; ring
  | m + 1, x => by
      have e : (fun x => Real.exp (-μ * x) *
            ∑ r ∈ Finset.range (m + 1 + 1), (μ * x) ^ r / (r ! : ℝ)) =
          fun x => Real.exp (-μ * x) * ∑ r ∈ Finset.range (m + 1), (μ * x) ^ r / (r ! : ℝ) +
            Real.exp (-μ * x) * ((μ * x) ^ (m + 1) / ((m + 1) ! : ℝ)) := by
        funext x; rw [Finset.sum_range_succ, mul_add]
      rw [e]
      have h1 := erlang_deriv μ m x
      have hE : HasDerivAt (fun x => Real.exp (-μ * x)) (Real.exp (-μ * x) * (-μ)) x := by
        have := ((hasDerivAt_id x).const_mul (-μ)).exp
        simpa using this
      have hP : HasDerivAt (fun x => (μ * x) ^ (m + 1) / ((m + 1) ! : ℝ))
          (((m + 1 : ℕ) : ℝ) * (μ * x) ^ m * μ / ((m + 1) ! : ℝ)) x := by
        have := (((hasDerivAt_id x).const_mul μ).pow (m + 1)).div_const ((m + 1) ! : ℝ)
        simpa using this
      refine HasDerivAt.congr_deriv (h1.add (hE.mul hP)) ?_
      rw [Nat.factorial_succ]; push_cast
      field_simp
      ring

lemma erlang_surv (μ : ℝ) (m : ℕ) (t : ℝ) : completionsCDF μ (m + 1) t =
    1 - Real.exp (-μ * t) * ∑ r ∈ Finset.range (m + 1), (μ * t) ^ r / (r ! : ℝ) := by
  simp only [completionsCDF]
  have hint : IntervalIntegrable
      (fun x => -(μ * (μ * x) ^ m / (m ! : ℝ) * Real.exp (-μ * x))) volume 0 t :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => erlang_deriv μ m x) hint
  rw [intervalIntegral.integral_neg] at h
  have h0 : Real.exp (-μ * 0) * ∑ r ∈ Finset.range (m + 1), (μ * 0) ^ r / (r ! : ℝ) = 1 := by
    simp [Finset.sum_range_succ']
  rw [h0] at h
  linarith

lemma surv_bounds (μ t : ℝ) (hμ : 0 ≤ μ) (ht : 0 ≤ t) (m : ℕ) :
    0 ≤ Real.exp (-μ * t) * ∑ r ∈ Finset.range (m + 1), (μ * t) ^ r / (r ! : ℝ) ∧
    Real.exp (-μ * t) * ∑ r ∈ Finset.range (m + 1), (μ * t) ^ r / (r ! : ℝ) ≤ 1 := by
  have hx : 0 ≤ μ * t := mul_nonneg hμ ht
  have hS0 : 0 ≤ ∑ r ∈ Finset.range (m + 1), (μ * t) ^ r / (r ! : ℝ) :=
    Finset.sum_nonneg (fun r _ => by positivity)
  refine ⟨mul_nonneg (Real.exp_pos _).le hS0, ?_⟩
  have h1 := Real.sum_le_exp_of_nonneg hx (m + 1)
  calc Real.exp (-μ * t) * ∑ r ∈ Finset.range (m + 1), (μ * t) ^ r / (r ! : ℝ)
      ≤ Real.exp (-μ * t) * Real.exp (μ * t) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma laws (s : ℕ) (hs : 1 ≤ s) (b : ℝ) (hb : 0 < b) (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1)
    (π : ℕ → ℝ) (hπ0 : ∀ j, 0 ≤ π j) (hπ1 : HasSum π 1) (C : ℝ) (hC : 0 < C)
    (htail : ∀ k, π (s - 1 + k) = C * lam ^ k) :
    (queueLaw s π 0 < 1 ∧
        ∀ n : ℕ, 1 ≤ n → queueLaw s π n = (1 - queueLaw s π 0) * ((1 - lam) * lam ^ (n - 1))) ∧
      (waitCDF s b π 0 < 1 ∧
        ∀ t : ℝ, 0 ≤ t →
          1 - waitCDF s b π t =
            (1 - waitCDF s b π 0) * Real.exp (-t / (b / (s * (1 - lam))))) := by
  obtain ⟨hl0, hl1⟩ := hlam
  have h1l : 0 < 1 - lam := by linarith
  have hgeo : ∀ j, ∑' m, lam ^ (m + j) = lam ^ j * (1 - lam)⁻¹ := fun j => by
    simp_rw [pow_add]; rw [tsum_mul_right, tsum_geometric_of_lt_one hl0.le hl1]; ring
  -- queue length
  have hq : queueLaw s π 0 = ∑ i ∈ Finset.range (s + 1), π i := by simp [queueLaw]
  have hQ0 : 1 - queueLaw s π 0 = C * (lam ^ 2 * (1 - lam)⁻¹) := by
    have hsp := Summable.sum_add_tsum_nat_add' (f := π) (k := s + 1)
      ((summable_nat_add_iff (f := π) (s + 1)).mpr hπ1.summable)
    rw [hπ1.tsum_eq] at hsp
    have e : ∀ m, π (m + (s + 1)) = C * lam ^ (m + 2) := fun m => by
      rw [show m + (s + 1) = s - 1 + (m + 2) by omega, htail]
    simp_rw [e] at hsp
    rw [tsum_mul_left, hgeo 2] at hsp
    rw [hq]; linarith
  have hQpos : 0 < C * (lam ^ 2 * (1 - lam)⁻¹) := by positivity
  -- waiting time
  set μ : ℝ := (s : ℝ) / b with hμdef
  have hμ : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) hb.le
  have hEb : ∀ k t, 0 ≤ t → 0 ≤ completionsCDF μ k t ∧ completionsCDF μ k t ≤ 1 := by
    intro k t ht
    rcases k with _ | k
    · simp [completionsCDF]
    · rw [erlang_surv]
      have := surv_bounds μ t hμ ht k
      constructor <;> linarith [this.1, this.2]
  have hW : ∀ t, 0 ≤ t → 1 - waitCDF s b π t =
      C * (lam * (1 - lam)⁻¹) * Real.exp (-(1 - lam) * μ * t) := by
    intro t ht
    unfold waitCDF
    rw [← hμdef]
    have hsW : Summable (fun i => π i * completionsCDF μ (i + 1 - s) t) :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hπ0 i) (hEb _ t ht).1)
        (fun i => mul_le_of_le_one_right (hπ0 i) (hEb _ t ht).2) hπ1.summable
    have hdiff := hπ1.sub hsW.hasSum
    have hsh := Summable.sum_add_tsum_nat_add'
      (f := fun i => π i - π i * completionsCDF μ (i + 1 - s) t) (k := s)
      ((summable_nat_add_iff (f := fun i => π i - π i * completionsCDF μ (i + 1 - s) t) s).mpr
        hdiff.summable)
    rw [hdiff.tsum_eq] at hsh
    have hz : ∑ i ∈ Finset.range s, (π i - π i * completionsCDF μ (i + 1 - s) t) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [show i + 1 - s = 0 by omega]; simp [completionsCDF]
    have e : ∀ m, π (m + s) - π (m + s) * completionsCDF μ (m + s + 1 - s) t =
        C * Real.exp (-μ * t) *
          (lam ^ (m + 1) * ∑ r ∈ Finset.range (m + 1), (μ * t) ^ r / (r ! : ℝ)) := by
      intro m
      rw [show m + s + 1 - s = m + 1 by omega, erlang_surv,
        show m + s = s - 1 + (m + 1) by omega, htail]
      ring
    rw [hz, zero_add] at hsh
    simp_rw [e] at hsh
    rw [tsum_mul_left] at hsh
    have hcau : ∑' m, lam ^ (m + 1) * ∑ r ∈ Finset.range (m + 1), (μ * t) ^ r / (r ! : ℝ) =
        Real.exp (lam * (μ * t)) * (lam * (1 - lam)⁻¹) := by
      have hx : 0 ≤ lam * (μ * t) := mul_nonneg hl0.le (mul_nonneg hμ ht)
      have hf : Summable (fun k => ‖(lam * (μ * t)) ^ k / (k ! : ℝ)‖) := by
        refine (Real.summable_pow_div_factorial (lam * (μ * t))).congr (fun k => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hg : Summable (fun j : ℕ => ‖lam ^ (j + 1)‖) := by
        refine ((summable_geometric_of_lt_one hl0.le hl1).mul_left lam).congr (fun j => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_succ]; ring
      have hc := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
      rw [← hexp, hgeo 1, pow_one] at hc
      rw [hc]
      refine tsum_congr (fun m => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have : lam ^ (m + 1) = lam ^ k * lam ^ (m - k + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [this, mul_pow]; ring
    rw [hcau] at hsh
    rw [← hsh, show -(1 - lam) * μ * t = -μ * t + lam * (μ * t) by ring, Real.exp_add]
    ring
  have hW0 := hW 0 le_rfl
  simp only [mul_zero, Real.exp_zero, mul_one] at hW0
  refine ⟨⟨by linarith, fun n hn => ?_⟩, ⟨?_, fun t ht => ?_⟩⟩
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hQ0]
    have e1 : queueLaw s π (n' + 1) = C * lam ^ (n' + 2) := by
      simp only [queueLaw, Nat.add_one_ne_zero, if_false]
      rw [show s + (n' + 1) = s - 1 + (n' + 2) by omega, htail]
    rw [e1, Nat.add_sub_cancel]
    field_simp
    ring
  · have : 0 < C * (lam * (1 - lam)⁻¹) := by positivity
    linarith
  · rw [hW t ht, hW0]
    congr 2
    rw [hμdef]
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    field_simp

end KQ4D

namespace KQ4

open QueueingFundamentals.Foundations

variable (P : TransitionMatrix)

lemma step_ge (n a l c : ℕ) : P.p a l * P.stepProb n l c ≤ P.stepProb (n + 1) a c := by
  rw [stepProb_eq, stepProb_eq]
  have h : q P a l * Pn P n l c ≤ Pn P (n + 1) a c := by
    simp only [Pn]; exact ENNReal.le_tsum (f := fun k => q P a k * Pn P n k c) l
  have := ENNReal.toReal_mono (Pn_ne_top P (n + 1) a c) h
  rwa [ENNReal.toReal_mul, q, ENNReal.toReal_ofReal (P.nonneg a l)] at this

lemma climb (hup : ∀ a, 0 < P.p a (a + 1)) : ∀ m a, 0 < P.stepProb m a (a + m)
  | 0, a => by simp [TransitionMatrix.stepProb]
  | m + 1, a => by
      have h := climb hup m (a + 1)
      have h2 := step_ge P m a (a + 1) (a + 1 + m)
      rw [show a + (m + 1) = a + 1 + m by omega]
      exact lt_of_lt_of_le (mul_pos (hup a) h) h2

lemma stay (h00 : 0 < P.p 0 0) (hup : ∀ a, 0 < P.p a (a + 1)) :
    ∀ k i, 0 < P.stepProb (k + i) 0 i
  | 0, i => by simpa using climb P hup i 0
  | k + 1, i => by
      rw [show k + 1 + i = (k + i) + 1 by omega]
      exact lt_of_lt_of_le (mul_pos h00 (stay h00 hup k i)) (step_ge P (k + i) 0 0 i)

lemma reach0 (h00 : 0 < P.p 0 0) (hup : ∀ a, 0 < P.p a (a + 1)) :
    ∀ i j, ∃ m, 0 < P.stepProb m 0 i ∧ 0 < P.stepProb m 0 j := fun i j =>
  ⟨j + i, stay P h00 hup j i, by rw [add_comm]; exact stay P h00 hup i j⟩

end KQ4

open MeasureTheory Filter Topology QueueingFundamentals.Foundations QueueingFundamentals.GM1 KendallQueues.GIMs in
theorem solution (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (hρ : rho s a b < 1)
    (P : TransitionMatrix) (hP : P.p = gimsMatrix s A b)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hF : F s A b lam = lam) :
    ∃ π : ℕ → ℝ, HasSum π 1 ∧
      (∀ i j, Tendsto (fun n => P.stepProb n i j) atTop (𝓝 (π j))) ∧
      (queueLaw s π 0 < 1 ∧
        ∀ n : ℕ, 1 ≤ n → queueLaw s π n = (1 - queueLaw s π 0) * ((1 - lam) * lam ^ (n - 1))) ∧
      (waitCDF s b π 0 < 1 ∧
        ∀ t : ℝ, 0 ≤ t →
          1 - waitCDF s b π t =
            (1 - waitCDF s b π 0) * Real.exp (-t / (b / (s * (1 - lam))))) := by
  obtain ⟨hl0, hl1⟩ := hlam
  have hq : ∀ i j, KQ4.q P i j = ENNReal.ofReal (gimsMatrix s A b i j) := fun i j => by
    simp [KQ4.q, hP]
  have hskip : ∀ i j, i + 1 < j → KQ4.q P i j = 0 := fun i j h => by
    rw [hq, KQ4C.gims_skip s A b i j h, ENNReal.ofReal_zero]
  have htailq : ∀ i k, s ≤ k → KQ4.q P i k =
      if k ≤ i + 1 then ENNReal.ofReal (paren A b s (i + 1 - k)) else 0 := fun i k hk => by
    rw [hq, KQ4C.gims_tail s A b i k hk]; split_ifs <;> simp
  have hfix := KQ4C.fixed_point s a b hb hA lam hl0.le hl1.le hF
  have hdown : ∀ j, 1 ≤ j → j < s → KQ4.q P j 0 ≠ 0 := fun j _ hj => by
    rw [hq]; exact (ENNReal.ofReal_pos.mpr (KQ4C.down_pos s a b ha hb hA j hj)).ne'
  have hup : ∀ i, KQ4.q P i (i + 1) ≠ 0 := fun i => by
    rw [hq]; exact (ENNReal.ofReal_pos.mpr (KQ4C.up_pos s a b ha hb hA i)).ne'
  have hL0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hl0).ne'
  have hL1 : ENNReal.ofReal lam < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hl1
  obtain ⟨x, hx1, hx2, hx3, hfin, hxP⟩ :=
    KQ4.statB P hskip s hs (ENNReal.ofReal lam) _ hL0 hL1 htailq hfix hdown hup
  have hS0 : ∑' i, x i ≠ 0 := fun h => hx3 0 (ENNReal.tsum_eq_zero.mp h 0)
  have hSr : 0 < (∑' i, x i).toReal := ENNReal.toReal_pos hS0 hfin
  obtain ⟨π, hπ⟩ : ∃ π : ℕ → ℝ, π = fun k => (x k).toReal / (∑' i, x i).toReal := ⟨_, rfl⟩
  have hπk : ∀ k, π k = (x k).toReal / (∑' i, x i).toReal := fun k => by rw [hπ]
  have hπ0 : ∀ j, 0 ≤ π j := fun j => by rw [hπk]; exact div_nonneg ENNReal.toReal_nonneg hSr.le
  have hπ1 : HasSum π 1 := by
    have h1 : HasSum (fun k => (x k).toReal) (∑' i, x i).toReal := by
      rw [ENNReal.tsum_toReal_eq hx2]; exact (ENNReal.summable_toReal hfin).hasSum
    have h2 := h1.div_const (∑' i, x i).toReal
    rw [div_self hSr.ne'] at h2
    rw [hπ]; exact h2
  have hst : ∀ j, HasSum (fun i => π i * P.p i j) (π j) := by
    intro j
    have hj := hxP j
    unfold KQ4.xP at hj
    have hne : ∀ i, x i * KQ4.q P i j ≠ ⊤ := fun i =>
      ENNReal.mul_ne_top (hx2 i) ENNReal.ofReal_ne_top
    have h2 : HasSum (fun i => (x i * KQ4.q P i j).toReal) (x j).toReal := by
      rw [← hj, ENNReal.tsum_toReal_eq hne]
      exact (ENNReal.summable_toReal (hj ▸ hx2 j)).hasSum
    have h3 := h2.div_const (∑' i, x i).toReal
    have e : (fun i => π i * P.p i j) =
        fun i => (x i * KQ4.q P i j).toReal / (∑' i, x i).toReal := by
      ext i
      rw [hπk, ENNReal.toReal_mul, KQ4.q, ENNReal.toReal_ofReal (P.nonneg i j)]; ring
    rw [e, hπk]; exact h3
  have hz : 0 < π 0 := by
    rw [hπk]; exact div_pos (ENNReal.toReal_pos (hx3 0) (hx2 0)) hSr
  have h00 : 0 < P.p 0 0 := by rw [hP]; exact KQ4C.p00_pos s hs a b ha hb hA
  have hup' : ∀ i, 0 < P.p i (i + 1) := fun i => by rw [hP]; exact KQ4C.up_pos s a b ha hb hA i
  have hconv := KQ4.converge P 0 π hπ0 hπ1 hst hz (KQ4.reach0 P h00 hup')
  have htail : ∀ k, π (s - 1 + k) = (1 / (∑' i, x i).toReal) * lam ^ k := fun k => by
    rw [hπk, hx1 _ (by omega), show s - 1 + k - (s - 1) = k by omega, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hl0.le]
    ring
  have hlaws := KQ4D.laws s hs b hb lam ⟨hl0, hl1⟩ π hπ0 hπ1 _ (by positivity) htail
  exact ⟨π, hπ1, hconv, hlaws.1, hlaws.2⟩
