-- Prove2me | solution 1 for MatrixAnalytic.MinimalSolutions.g_riccati_minimal_solutions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:25:14.377911+00:00
-- url     : https://prove2.me/submissions/e017b5e8-6807-47a3-b16e-bd8a935efe04

import Mathlib
import Theorems.Thm_MatrixAnalytic_MinimalSolutions_UG_minimal
import Theorems.Thm_MatrixAnalytic_MinimalSolutions_linear_progression
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
open MatrixAnalytic.MinimalSolutions
lemma p2m_mm_assoc {ι : Type*} (X Y Z : ι → ι → ℝ≥0∞) : matMulE (matMulE X Y) Z = matMulE X (matMulE Y Z) := by
  funext i j; unfold matMulE; simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]; rw [ENNReal.tsum_comm]; refine tsum_congr fun a => tsum_congr fun b => ?_; ring
lemma p2m_mm_add_left {ι : Type*} (X Y Z : ι → ι → ℝ≥0∞) : matMulE (X + Y) Z = matMulE X Z + matMulE Y Z := by
  funext i j; unfold matMulE; simp only [Pi.add_apply, add_mul, ENNReal.tsum_add]
lemma p2m_mm_add_right {ι : Type*} (X Y Z : ι → ι → ℝ≥0∞) : matMulE X (Y + Z) = matMulE X Y + matMulE X Z := by
  funext i j; unfold matMulE; simp only [Pi.add_apply, mul_add, ENNReal.tsum_add]
lemma p2m_one_mm {ι : Type*} [DecidableEq ι] (X : ι → ι → ℝ≥0∞) : matMulE matOneE X = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]
  simp
lemma p2m_mm_one {ι : Type*} [DecidableEq ι] (X : ι → ι → ℝ≥0∞) : matMulE X matOneE = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single j (by intro b hb; simp [hb])]
  simp
lemma p2m_pow_comm {α : Type*} [DecidableEq α] (U : α → α → ℝ≥0∞) : ∀ n, matMulE U (matPowE U n) = matMulE (matPowE U n) U := by
  intro n; induction n with
  | zero => simp only [matPowE]; rw [p2m_mm_one, p2m_one_mm]
  | succ n ih => simp only [matPowE]; rw [← p2m_mm_assoc, ih]
lemma p2m_S_left {α : Type*} [DecidableEq α] (U : α → α → ℝ≥0∞) : seriesInvE U = matOneE + matMulE U (seriesInvE U) := by
  funext i j; unfold seriesInvE; rw [tsum_eq_zero_add' ENNReal.summable]; simp only [Pi.add_apply]; congr 1
  show ∑' n, matMulE (matPowE U n) U i j = _
  simp_rw [← p2m_pow_comm U]; unfold matMulE; rw [ENNReal.tsum_comm]; simp_rw [ENNReal.tsum_mul_left]
lemma p2m_mm_mono {ι : Type*} (X X' Y Y' : ι → ι → ℝ≥0∞) (hX : ∀ i j, X i j ≤ X' i j) (hY : ∀ i j, Y i j ≤ Y' i j) : ∀ i j, matMulE X Y i j ≤ matMulE X' Y' i j := by
  intro i j; unfold matMulE; exact ENNReal.tsum_le_tsum fun k => mul_le_mul' (hX i k) (hY k j)
lemma p2m_S_mono {ι : Type*} [DecidableEq ι] (U W : ι → ι → ℝ≥0∞) (h : ∀ i j, U i j ≤ W i j) : ∀ i j, seriesInvE U i j ≤ seriesInvE W i j := by
  have hp : ∀ n i j, matPowE U n i j ≤ matPowE W n i j := by intro n; induction n with | zero => intro i j; exact le_rfl | succ n ih => intro i j; exact p2m_mm_mono (matPowE U n) (matPowE W n) U W ih h i j
  intro i j; exact ENNReal.tsum_le_tsum fun n => hp n i j
lemma p2m_super_S {ι : Type*} [DecidableEq ι] (a z w : ι → ι → ℝ≥0∞) (h : ∀ i j, a i j + matMulE z w i j ≤ z i j) : ∀ i j, matMulE a (seriesInvE w) i j ≤ z i j := by
  let q (K : ℕ) : ι → ι → ℝ≥0∞ := fun i j => ∑ n ∈ Finset.range K, matPowE w n i j
  have hk : ∀ K i j, matMulE a (q K) i j ≤ z i j := by
    intro K; induction K with
    | zero => intro i j; simp [q, matMulE]
    | succ K ih =>
      intro i j
      have e : q (K + 1) = matOneE + matMulE (q K) w := by
        funext k l; change (∑ n ∈ Finset.range (K + 1), matPowE w n k l) = _; rw [Finset.sum_range_succ']; simp only [q, matPowE, Pi.add_apply]; rw [add_comm]; congr 1; unfold matMulE; rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]; simp_rw [Finset.sum_mul]
      rw [e, p2m_mm_add_right, p2m_mm_one, ← p2m_mm_assoc]
      have hm := p2m_mm_mono (matMulE a (q K)) z w w ih (fun _ _ => le_rfl) i j
      exact le_trans (add_le_add (le_rfl : a i j ≤ a i j) hm) (h i j)
  intro i j
  have e : matMulE a (seriesInvE w) i j = ∑' n, matMulE a (matPowE w n) i j := by unfold matMulE seriesInvE; simp_rw [← ENNReal.tsum_mul_left]; rw [ENNReal.tsum_comm]
  rw [e]; refine ENNReal.tsum_le_of_sum_range_le fun K => le_trans (le_of_eq ?_) (hk K i j)
  unfold matMulE q; rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]; simp_rw [Finset.mul_sum]
def p2mT {ι : Type*} (M : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ := fun i j => M j i
lemma p2mT_mul {ι : Type*} (X Y : ι → ι → ℝ≥0∞) : p2mT (matMulE X Y) = matMulE (p2mT Y) (p2mT X) := by
  funext i j; unfold p2mT matMulE; exact tsum_congr fun k => by ring
lemma p2mT_pow {ι : Type*} [DecidableEq ι] (U : ι → ι → ℝ≥0∞) : ∀ n, p2mT (matPowE U n) = matPowE (p2mT U) n := by
  intro n; induction n with
  | zero => ext i j; simp [p2mT, matPowE, matOneE, eq_comm]
  | succ n ih => simp only [matPowE, p2mT_mul, ih]; rw [p2m_pow_comm (p2mT U) n]
lemma p2mT_series {ι : Type*} [DecidableEq ι] (U : ι → ι → ℝ≥0∞) : p2mT (seriesInvE U) = seriesInvE (p2mT U) := by
  funext i j; change (∑' n, matPowE U n j i) = ∑' n, matPowE (p2mT U) n i j
  exact tsum_congr fun n => congrFun (congrFun (p2mT_pow U n) i) j
lemma p2m_super_left_series {ι : Type*} [DecidableEq ι] (a z w : ι → ι → ℝ≥0∞) (h : ∀ i j, a i j + matMulE w z i j ≤ z i j) : ∀ i j, matMulE (seriesInvE w) a i j ≤ z i j := by
  intro i j
  have ht : ∀ r s, p2mT a r s + matMulE (p2mT z) (p2mT w) r s ≤ p2mT z r s := by intro r s; simpa [p2mT, ← p2mT_mul] using h s r
  have hs := p2m_super_S (p2mT a) (p2mT z) (p2mT w) ht j i
  have heq : matMulE (seriesInvE w) a i j = matMulE (p2mT a) (seriesInvE (p2mT w)) j i := by
    rw [← p2mT_series w]; unfold matMulE p2mT; exact tsum_congr fun k => by ring
  exact le_trans (le_of_eq heq) hs

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matG (qbdP B A₀ A₁ A₂) = ennMat A₂ + matMulE (ennMat A₁) (matG (qbdP B A₀ A₁ A₂)) +
        matMulE (ennMat A₀) (matMulE (matG (qbdP B A₀ A₁ A₂)) (matG (qbdP B A₀ A₁ A₂))) ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = ennMat A₂ + matMulE (ennMat A₁) (ennMat Y) +
          matMulE (ennMat A₀) (matMulE (ennMat Y) (ennMat Y)) →
        ∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≤ ennMat Y i j := by
  let P := qbdP B A₀ A₁ A₂
  rcases UG_minimal B A₀ A₁ A₂ hP hirr with ⟨hGfinite, _hSeriesFinite, hU, hGseries, _hPairMinimal⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [P] using hGfinite
  · have hGstep : matG P = ennMat A₂ + matMulE (matU P) (matG P) := by
      calc
        matG P = matMulE (seriesInvE (matU P)) (ennMat A₂) := hGseries
        _ = matMulE (matOneE + matMulE (matU P) (seriesInvE (matU P))) (ennMat A₂) := by rw [← p2m_S_left]
        _ = ennMat A₂ + matMulE (matU P) (matG P) := by rw [p2m_mm_add_left, p2m_one_mm, p2m_mm_assoc, hGseries]
    calc
      matG P = ennMat A₂ + matMulE (matU P) (matG P) := hGstep
      _ = ennMat A₂ + matMulE (ennMat A₁ + matMulE (ennMat A₀) (matG P)) (matG P) := by rw [hU]
      _ = ennMat A₂ + matMulE (ennMat A₁) (matG P) + matMulE (ennMat A₀) (matMulE (matG P) (matG P)) := by rw [p2m_mm_add_left, p2m_mm_assoc, ← add_assoc]
  · intro Y hY hRic i j
    let X : ι → ι → ℝ≥0∞ := ennMat A₁ + matMulE (ennMat A₀) (ennMat Y)
    have hfixed : ennMat A₂ + matMulE X (ennMat Y) = ennMat Y := by
      change ennMat A₂ + matMulE (ennMat A₁ + matMulE (ennMat A₀) (ennMat Y)) (ennMat Y) = ennMat Y
      calc
        _ = ennMat A₂ + matMulE (ennMat A₁) (ennMat Y) + matMulE (ennMat A₀) (matMulE (ennMat Y) (ennMat Y)) := by rw [p2m_mm_add_left, p2m_mm_assoc, ← add_assoc]
        _ = ennMat Y := hRic.symm
    have hSeriesBound : ∀ i j, matMulE (seriesInvE X) (ennMat A₂) i j ≤ ennMat Y i j := p2m_super_left_series (ennMat A₂) (ennMat Y) X (fun r s => le_of_eq (congrFun (congrFun hfixed r) s))
    rcases linear_progression B A₀ A₁ A₂ hP hirr with ⟨hU1, hUnext, hGk, _hMonotone, _hUlim, hGlim⟩
    have hSeq : ∀ k, 1 ≤ k → (∀ i j, matUk P k i j ≤ X i j) ∧ (∀ i j, matGk P k i j ≤ ennMat Y i j) := by
      intro k; induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk
          by_cases hk1 : k = 1
          · subst k
            have hU1bound : ∀ i j, matUk P 1 i j ≤ X i j := by
              intro r s; rw [hU1]; change ennMat A₁ r s ≤ ennMat A₁ r s + matMulE (ennMat A₀) (ennMat Y) r s
              exact le_add_of_nonneg_right (by positivity)
            have hSmono := p2m_S_mono (matUk P 1) X hU1bound
            have hG1 : matGk P 1 = matMulE (seriesInvE (matUk P 1)) (ennMat A₂) := (hGk 1 (by norm_num)).2
            refine ⟨hU1bound, ?_⟩; intro r s
            calc
              matGk P 1 r s = matMulE (seriesInvE (matUk P 1)) (ennMat A₂) r s := congrFun (congrFun hG1 r) s
              _ ≤ matMulE (seriesInvE X) (ennMat A₂) r s := p2m_mm_mono _ _ _ _ hSmono (fun _ _ => le_rfl) r s
              _ ≤ ennMat Y r s := hSeriesBound r s
          · have hkgt : 1 < k := by omega
            let n := k - 1
            have hn : 1 ≤ n := by dsimp [n]; omega
            have hnk : n + 1 = k := by dsimp [n]; omega
            have hprev := ih n (by dsimp [n]; omega) hn
            have hUcurrent : matUk P k = ennMat A₁ + matMulE (ennMat A₀) (matGk P n) := by simpa [hnk] using hUnext n hn
            have hUbound : ∀ r s, matUk P k r s ≤ X r s := by
              intro r s; rw [hUcurrent]
              have hm := p2m_mm_mono (ennMat A₀) (ennMat A₀) (matGk P n) (ennMat Y) (fun _ _ => le_rfl) hprev.2 r s
              simpa [X] using add_le_add (le_rfl : ennMat A₁ r s ≤ ennMat A₁ r s) hm
            have hGcurrent : matGk P k = matMulE (seriesInvE (matUk P k)) (ennMat A₂) := (hGk k hk).2
            have hSmono := p2m_S_mono (matUk P k) X hUbound
            refine ⟨hUbound, ?_⟩; intro r s
            calc
              matGk P k r s = matMulE (seriesInvE (matUk P k)) (ennMat A₂) r s := congrFun (congrFun hGcurrent r) s
              _ ≤ matMulE (seriesInvE X) (ennMat A₂) r s := p2m_mm_mono _ _ _ _ hSmono (fun _ _ => le_rfl) r s
              _ ≤ ennMat Y r s := hSeriesBound r s
    exact le_of_tendsto (hGlim i j) (Filter.eventually_atTop.2 ⟨1, fun k hk => (hSeq k hk).2 i j⟩)
