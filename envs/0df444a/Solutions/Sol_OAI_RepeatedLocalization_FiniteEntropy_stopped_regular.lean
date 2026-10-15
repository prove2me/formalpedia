-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.stopped_regular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:10:39.481528+00:00
-- url     : https://prove2.me/submissions/6fb82072-3347-40f9-9fb3-0eebb2b9f4b9

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/FirstHeavy.lean:L143-L173
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.stopped_regular. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells

-- ---- from OAI.Probability.Localization.Cells ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma cellWidth_pos {n J : ℕ} (hn : 0 < n) : 0 < cellWidth n J := by
  unfold cellWidth
  positivity

lemma cellSet_eq_pi {n : ℕ} (Q : Cell n) :
    cellSet Q = Set.pi univ (fun i => Ico (cellLower Q i) (cellLower Q i + cellWidth n Q.1)) := by
  ext z
  simp only [cellSet, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ico]
  congr! 3
  simp only [cellLower, cellWidth]
  ring

lemma measurableSet_cellSet {n : ℕ} (Q : Cell n) : MeasurableSet (cellSet Q) := by
  rw [cellSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma cellCenter_mem {n : ℕ} (hn : 0 < n) (Q : Cell n) : cellCenter Q ∈ cellSet Q := by
  rw [cellSet_eq_pi]
  intro i hi
  have h := cellWidth_pos (J := Q.1) hn
  simp only [mem_Ico, cellCenter]
  constructor <;> linarith

lemma cellIndex_eq_of_mem {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : cellIndex Q.1 z = Q.2 := by
  funext i
  apply Fin.ext
  simp only [cellSet, mem_ofPred_eq, neg_div] at hz
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^Q.1 := by positivity
  let x : ℝ := (z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^Q.1)
  have hl : (Q.2 i : ℝ) ≤ x := by
    apply (div_le_iff₀ hd).mp
    linarith [(hz i).1]
  have hu : x < (Q.2 i : ℝ) + 1 := by
    apply (lt_div_iff₀ hd).mp
    linarith [(hz i).2]
  have hf : ⌊x⌋₊ = (Q.2 i).val := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg _) hl)).mpr ⟨hl, hu⟩
  change ⌊x⌋₊ % 2^Q.1 = (Q.2 i).val
  rw [hf, Nat.mod_eq_of_lt (Q.2 i).isLt]

lemma cell_ext {n : ℕ} {Q R : Cell n} (h : Q.1 = R.1)
    (hi : ∀ i,(Q.2 i).val = (R.2 i).val) : Q = R := by
  rcases Q with ⟨J,a⟩
  rcases R with ⟨K,b⟩
  dsimp at h hi
  subst K
  congr 1
  funext i
  exact Fin.ext (hi i)

lemma cellAt_eq_of_mem {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : cellAt Q.1 z = Q := by
  apply cell_ext (Q := cellAt Q.1 z) (R := Q) rfl
  have h := cellIndex_eq_of_mem hn Q hz
  intro i
  exact congrArg Fin.val (congrFun h i)

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.FirstHeavy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma Descendant.refl {n : ℕ} (Q : Cell n) : Descendant Q Q := ⟨le_rfl,Subset.rfl⟩

lemma Descendant.trans {n : ℕ} {Q R S : Cell n} (hQR : Descendant Q R) (hRS : Descendant R S) :
    Descendant Q S := ⟨hQR.1.trans hRS.1,hRS.2.trans hQR.2⟩

lemma cell_eq_of_level_point {n : ℕ} (hn : 0 < n) {Q R : Cell n} (h : Q.1 = R.1)
    {z : Coordinate n} (hzQ : z ∈ cellSet Q) (hzR : z ∈ cellSet R) : Q = R := by
  have h₁ := cellAt_eq_of_mem hn Q hzQ
  have h₂ := cellAt_eq_of_mem hn R hzR
  rw [h] at h₁
  exact h₁.symm.trans h₂

lemma Descendant.eq_of_level {n : ℕ} (hn : 0 < n) {Q R : Cell n}
    (h : Descendant Q R) (hlev : Q.1 = R.1) : Q = R :=
  cell_eq_of_level_point hn hlev (h.2 (cellCenter_mem hn R)) (cellCenter_mem hn R)

lemma exists_firstHeavy_ancestor {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    {Q R : Cell n} (hR : Heavy P Q R) :
    ∃ E : Cell n,FirstHeavy P Q E ∧ Descendant E R := by
  classical
  have hex : ∃ J : ℕ,∃ E : Cell n,Heavy P Q E ∧ Descendant E R ∧ E.1 = J :=
    ⟨R.1,R,hR,Descendant.refl R,rfl⟩
  obtain ⟨E,hE,hER,hlev⟩ := Nat.find_spec hex
  refine ⟨E,⟨hE,?_⟩,hER⟩
  intro F hF hFE
  have hmin := Nat.find_min' hex (show ∃ E : Cell n,Heavy P Q E ∧ Descendant E R ∧ E.1 = F.1 from
    ⟨F,hF,hFE.trans hER,rfl⟩)
  rw [← hlev] at hmin
  exact hFE.eq_of_level hn (le_antisymm hFE.1 hmin)

lemma heavy_disjoint_residual {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    {Q R : Cell n} (hR : Heavy P Q R) : Disjoint (residual P Q) (cellSet R) := by
  obtain ⟨E,hE,hER⟩ := exists_firstHeavy_ancestor hn P hR
  apply Set.disjoint_left.mpr
  intro z hz hzR
  exact hz.2 (Set.mem_iUnion.mpr ⟨⟨E,hE⟩,hER.2 hzR⟩)

lemma stopped_regular {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hq : (1/2:ℝ) ≤ (P (residual P Q)).toReal) :
    Regular (ProbabilityTheory.cond P (residual P Q)) Q := by
  have hq0 : P (residual P Q) ≠ 0 := by
    intro hzero
    rw [hzero, ENNReal.toReal_zero] at hq
    norm_num at hq
  have hp := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hq0
  let := hp
  refine ⟨?_,?_⟩
  · apply le_antisymm prob_le_one
    have hself := ProbabilityTheory.cond_apply_self (μ := P) hq0 (measure_ne_top _ _)
    rw [← hself]
    exact measure_mono Set.sdiff_subset
  · intro R hQR hlev
    by_cases hR : Heavy P Q R
    · have hd := heavy_disjoint_residual hn P hR
      rw [ProbabilityTheory.cond_apply' (measurableSet_cellSet R),Set.disjoint_iff_inter_eq_empty.mp hd]
      simp only [measure_empty,mul_zero,ENNReal.toReal_zero]
      exact mul_nonneg (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le
    · have hm : (P (cellSet R)).toReal ≤ threshold n (R.1-Q.1) := by
        exact le_of_not_gt (fun h => hR ⟨hQR,hlev,h⟩)
      rw [ProbabilityTheory.cond_apply' (measurableSet_cellSet R),ENNReal.toReal_mul,ENNReal.toReal_inv]
      have hinter : (P (residual P Q ∩ cellSet R)).toReal ≤ (P (cellSet R)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right)
      have hpos : 0 < (P (residual P Q)).toReal := by linarith
      have hinv : ((P (residual P Q)).toReal)⁻¹ ≤ 2 := by
        apply (inv_le_comm₀ hpos (by norm_num)).mpr
        simpa only [one_div] using hq
      exact (mul_le_mul_of_nonneg_left (hinter.trans hm) (inv_nonneg.mpr hpos.le)).trans
        (mul_le_mul_of_nonneg_right hinv (Real.rpow_pos_of_pos (by norm_num) _).le)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hq : (1/2:ℝ) ≤ (P (residual P Q)).toReal) :
    Regular (ProbabilityTheory.cond P (residual P Q)) Q := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.stopped_regular hn P Q hq
    | exact OAI.RepeatedLocalization.FiniteEntropy.stopped_regular
    | (apply OAI.RepeatedLocalization.FiniteEntropy.stopped_regular <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.stopped_regular <;> assumption)
