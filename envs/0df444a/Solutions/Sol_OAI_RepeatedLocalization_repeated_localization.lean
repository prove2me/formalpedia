-- Prove2me | solution 1 for OAI.RepeatedLocalization.repeated_localization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:26:48.995854+00:00
-- url     : https://prove2.me/submissions/3100ef4a-1e03-4e12-a7f5-62d4dbb5a1fb

import Mathlib
import Definitions.Def_GaussianInformation
import Definitions.Def_OAIQWRLC000
import Theorems.Thm_OAI_RepeatedLocalization_actual_uniform_blockCost

section
-- module Solutions.OAIQW_RepeatedLocalization.Compat
namespace OAI
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434


end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.Localization_Cells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma cellWidth_pos {n J : ℕ} (hn : 0 < n) : 0 < cellWidth n J := by
  unfold cellWidth
  positivity

lemma measurableSet_cellSet {n : ℕ} (Q : Cell n) : MeasurableSet (cellSet Q) := by
  rw [cellSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma measurable_cellIndex {n : ℕ} (J : ℕ) : Measurable (cellIndex (n := n) J) := by
  apply Measurable.of_eval
  intro i
  let f : ℕ → Fin (2^J) := fun v => ⟨v % 2^J, Nat.mod_lt _ (pow_pos (by norm_num) J)⟩
  exact (measurable_of_countable f).comp
    (((measurable_pi_apply i).add_const _).mul_const _).nat_floor

lemma measurable_cellAt {n : ℕ} (J : ℕ) : Measurable (cellAt (n := n) J) := by
  exact (measurable_of_countable (fun a : Fin n → Fin (2^J) => (⟨J, a⟩ : Cell n))).comp
    (measurable_cellIndex J)

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

lemma mem_cellAt {n : ℕ} (hn : 0 < n) (J : ℕ) {z : Coordinate n}
    (hz : z ∈ initialCube n) : z ∈ cellSet (cellAt J z) := by
  intro i
  have hi := hz i (mem_univ i)
  simp only [mem_Ico, neg_div] at hi
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^J := by positivity
  let x : ℝ := (z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^J)
  have hx : 0 ≤ x := mul_nonneg (by linarith [hi.1]) hd.le
  have hxu : x < (2 : ℝ)^J := by
    have hw : 2 * (1 / (2 * Real.sqrt n)) = 1 / Real.sqrt n := by ring
    have hza : z i + 1 / (2 * Real.sqrt n) < 1 / Real.sqrt n := by linarith [hi.2]
    have hb := mul_lt_mul_of_pos_right hza hd
    dsimp [x]
    have he : 1 / Real.sqrt n * (Real.sqrt n * (2 : ℝ)^J) = (2 : ℝ)^J := by field_simp
    rwa [he] at hb
  have hfloor : ⌊x⌋₊ < 2^J := by
    apply (Nat.floor_lt hx).mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hxu
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one x
  have hl' := (div_le_iff₀ hd).mpr hl
  have hu' := (lt_div_iff₀ hd).mpr hu
  change -1 / (2 * Real.sqrt n) + (⌊x⌋₊ % 2^J : ℕ) / (Real.sqrt n * (2 : ℝ)^J) ≤ z i ∧
    z i < -1 / (2 * Real.sqrt n) + ((⌊x⌋₊ % 2^J : ℕ) + 1) / (Real.sqrt n * (2 : ℝ)^J)
  rw [Nat.mod_eq_of_lt hfloor]
  simp only [neg_div]
  constructor <;> linarith

lemma cellSet_disjoint {n J : ℕ} (hn : 0 < n) {a b : Fin n → Fin (2^J)} (hab : a ≠ b) :
    Disjoint (cellSet ⟨J, a⟩) (cellSet ⟨J, b⟩) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  exact hab ((cellIndex_eq_of_mem hn ⟨J, a⟩ hza).symm.trans (cellIndex_eq_of_mem hn ⟨J, b⟩ hzb))

lemma cellWidth_add (n J l : ℕ) :
    cellWidth n (J + l) = cellWidth n J / (2 : ℝ)^l := by
  simp only [cellWidth, pow_add]
  ring

lemma childCell_lower {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) (i : Fin n) :
    cellLower (childCell Q l a) i = cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) := by
  simp only [cellLower, cellWidth, childCell, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    pow_add]
  have ht : (2 : ℝ)^l ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

lemma childCell_subset {n : ℕ} (hn : 0 < n) (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) :
    cellSet (childCell Q l a) ⊆ cellSet Q := by
  rw [cellSet_eq_pi, cellSet_eq_pi]
  intro z hz i hi
  have hz' := hz i hi
  have hw := cellWidth_pos (J := Q.1+l) hn
  have hidx : (a i : ℝ) + 1 ≤ (2 : ℝ)^l := by exact_mod_cast (a i).isLt
  have he : cellWidth n (Q.1+l) * (2 : ℝ)^l = cellWidth n Q.1 := by
    rw [cellWidth_add, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]
  dsimp only at hz'
  rw [childCell_lower] at hz'
  change cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) ≤ z i ∧
    z i < cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) + cellWidth n (Q.1+l) at hz'
  have hu := mul_le_mul_of_nonneg_left hidx hw.le
  rw [he] at hu
  have ha : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  exact ⟨by nlinarith [hz'.1], by nlinarith [hz'.2]⟩

lemma cell_ext {n : ℕ} {Q R : Cell n} (h : Q.1 = R.1)
    (hi : ∀ i,(Q.2 i).val = (R.2 i).val) : Q = R := by
  rcases Q with ⟨J,a⟩
  rcases R with ⟨K,b⟩
  dsimp at h hi
  subst K
  congr 1
  funext i
  exact Fin.ext (hi i)

lemma child_ancestorCell {n : ℕ} (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) :
    childCell (ancestorCell Q J hJ) (Q.1-J)
      (fun i => ⟨(Q.2 i).val % 2^(Q.1-J),Nat.mod_lt _ (by positivity)⟩) = Q := by
  apply cell_ext (Nat.add_sub_of_le hJ)
  intro i
  change (Q.2 i).val / 2^(Q.1-J) * 2^(Q.1-J) + (Q.2 i).val % 2^(Q.1-J) = (Q.2 i).val
  simpa only [Nat.mul_comm] using Nat.div_add_mod (Q.2 i).val (2^(Q.1-J))

lemma cellSet_subset_ancestor {n : ℕ} (hn : 0 < n) (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) :
    cellSet Q ⊆ cellSet (ancestorCell Q J hJ) := by
  have h := childCell_subset hn (ancestorCell Q J hJ) (Q.1-J)
    (fun i => ⟨(Q.2 i).val % 2^(Q.1-J),Nat.mod_lt _ (by positivity)⟩)
  rwa [child_ancestorCell] at h

lemma cellAt_eq_of_mem {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : cellAt Q.1 z = Q := by
  apply cell_ext (Q := cellAt Q.1 z) (R := Q) rfl
  have h := cellIndex_eq_of_mem hn Q hz
  intro i
  exact congrArg Fin.val (congrFun h i)

lemma cellAt_nested {n : ℕ} (hn : 0 < n) {J K : ℕ} (hJK : J ≤ K)
    {z : Coordinate n} (hz : z ∈ initialCube n) : cellSet (cellAt K z) ⊆ cellSet (cellAt J z) := by
  have hsub := cellSet_subset_ancestor hn (cellAt K z) J hJK
  have hmem := hsub (mem_cellAt hn K hz)
  have h := cellAt_eq_of_mem hn (ancestorCell (cellAt K z) J hJK) hmem
  change cellAt J z = ancestorCell (cellAt K z) J hJK at h
  rwa [← h] at hsub

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ChartGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

lemma tubeConstant_ge_one : 1 ≤ tubeConstant := by
  unfold tubeConstant
  nlinarith [le_max_left (1 : ℝ) gridConstant]

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

lemma continuous_xlog : Continuous xlog := Real.continuous_mul_log
lemma xlog_zero : xlog 0 = 0 := by simp [xlog]
lemma xlog_one : xlog 1 = 0 := by simp [xlog]
lemma xlog_mul (x y : ℝ) : xlog (x*y) = y*xlog x+x*xlog y := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog_def, neg_mul] at h
  dsimp [xlog]
  linarith

lemma xlog_lower_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    xlog y + (Real.log y+1)*(x-y) ≤ xlog x := by
  have h := Real.self_sub_one_le_mul_log (div_nonneg hx hy.le)
  by_cases hx0 : x = 0
  · simp only [hx0, xlog]
    nlinarith
  rw [Real.log_div hx0 hy.ne'] at h
  have H := mul_le_mul_of_nonneg_left h hy.le
  dsimp [xlog]
  field_simp at H
  nlinarith

lemma integrable_bounded_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hC x)

lemma integrable_xlog_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) : Integrable (fun x => xlog (p x)) μ := by
  have hr : Set.range p ⊆ Icc (0:ℝ) 1 := by rintro _ ⟨x,rfl⟩; exact ⟨hp0 x,hp1 x⟩
  obtain ⟨C,hC⟩ := (isCompact_Icc.image continuous_xlog).isBounded.exists_norm_le
  apply integrable_bounded_measurable μ _ (continuous_xlog.measurable.comp hp)
  intro x
  simpa only [Real.norm_eq_abs, Function.comp_apply] using
    hC _ (Set.mem_image_of_mem _ (hr (Set.mem_range_self x)))

lemma scoreMass_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp0 : ∀ x, 0 ≤ p x) : 0 ≤ scoreMass μ p :=
  integral_nonneg hp0

lemma infoContribution_zero_mass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (hP : scoreMass μ p = 0) :
    infoContribution μ p = 0 := by
  have hi := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hz : p =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hp0 hi).mp hP
  have h : (fun x => xlog (p x)) =ᵐ[μ] 0 := by filter_upwards [hz] with x hx; simp [hx, xlog_zero]
  simp [infoContribution, hP, xlog_zero, integral_congr_ae h]

lemma infoContribution_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) : 0 ≤ infoContribution μ p := by
  have hP := scoreMass_nonneg μ p hp0
  by_cases hz : scoreMass μ p = 0
  · rw [infoContribution_zero_mass μ p hp hp0 hp1 hz]
  have hpos : 0 < scoreMass μ p := lt_of_le_of_ne hP (Ne.symm hz)
  have hip := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hil := integrable_xlog_probability μ p hp hp0 hp1
  have h := integral_mono ((integrable_const _).add
    ((hip.sub (integrable_const _)).const_mul _)) hil (fun x => xlog_lower_tangent (hp0 x) hpos)
  have hiq : Integrable (fun x => (Real.log (scoreMass μ p)+1)*(p x-scoreMass μ p)) μ :=
    (hip.sub (integrable_const _)).const_mul _
  have hadd := integral_add (integrable_const (xlog (scoreMass μ p))) hiq
  simp only [Pi.add_apply, Pi.sub_apply] at h hadd
  rw [hadd, integral_const_mul] at h
  have hsub := integral_sub hip (integrable_const (scoreMass μ p))
  rw [hsub] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, scoreMass,
    sub_self, mul_zero, add_zero] at h
  dsimp [infoContribution, scoreMass]
  linarith

lemma log_ratio_lower {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 < P) (hz : b = 0 → a = 0) :
    a*(Real.log P+1)-P*b ≤ a*Real.log (a/b) := by
  by_cases hb0 : b = 0
  · simp [hb0,hz hb0]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have h := xlog_lower_tangent (div_nonneg ha hb) hP
  have H := mul_le_mul_of_nonneg_left h hb
  dsimp [xlog] at H
  field_simp at H
  nlinarith

lemma log_ratio_mul {a b : ℝ} (hb : b ≠ 0) :
    a*Real.log (a/b) = xlog a-a*Real.log b := by
  by_cases ha : a = 0
  · simp [ha,xlog_zero]
  rw [Real.log_div ha hb]
  simp [xlog,mul_sub]

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_LabelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma labelVolumeConstant_ge_one : 1 ≤ labelVolumeConstant := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hp : 1 ≤ Real.sqrt Real.pi := (Real.le_sqrt (by norm_num) Real.pi_pos.le).mpr (by nlinarith [Real.pi_gt_three])
  unfold labelVolumeConstant
  nlinarith

lemma blockInformationConstant_pos : 0 < blockInformationConstant := by
  have hT := tubeConstant_ge_one
  have hV := labelVolumeConstant_ge_one
  have h : 1 ≤ 4*tubeConstant*labelVolumeConstant := by nlinarith
  have := Real.log_nonneg h
  unfold blockInformationConstant
  linarith

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_HeavyCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

lemma heavyThreshold_zero (n : ℕ) : heavyThreshold n 0 = 1 := by simp [heavyThreshold]
lemma heavyThreshold_add (n j l : ℕ) : heavyThreshold n (j+l) = heavyThreshold n j*heavyThreshold n l := by
  unfold heavyThreshold
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  simp only [Nat.cast_add]
  ring

lemma deepHeavyDepth_le {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) (z : Coordinate n) :
    deepHeavyDepth μ Q D z ≤ D := by
  unfold deepHeavyDepth
  apply Finset.sup'_le
  intro j hj
  have hj' := Finset.mem_range.mp hj
  split_ifs <;> omega

lemma le_deepHeavyDepth {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) (z : Coordinate n)
    {j : ℕ} (hj : j ≤ D) (heavy : heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z))) :
    j ≤ deepHeavyDepth μ Q D z := by
  have h := Finset.le_sup' (s := Finset.range (D+1))
    (fun j => if heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z)) then j else 0)
    (Finset.mem_range.mpr (show j < D+1 by omega))
  simpa only [ite_eq_left heavy,deepHeavyDepth] using h

lemma measurable_deepHeavyDepth {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) :
    Measurable (deepHeavyDepth μ Q D) := by
  classical
  apply Finset.measurable_range_sup''
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_le measurable_const ((measurable_of_countable (fun R : Cell n => μ.real (cellSet R))).comp (measurable_cellAt _))

lemma deepHeavyDepth_heavy {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    (Q : Cell n) (hQ : μ.real (cellSet Q) = 1) (D : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    heavyThreshold n (deepHeavyDepth μ Q D z) ≤ μ.real (cellSet (cellAt (Q.1+deepHeavyDepth μ Q D z) z)) := by
  obtain ⟨j,_,he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := D))
    (fun j => if heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z)) then j else 0)
  change deepHeavyDepth μ Q D z = _ at he
  split_ifs at he with hh
  · simpa only [he] using hh
  · rw [he,heavyThreshold_zero,Nat.add_zero,cellAt_eq_of_mem hn Q hz,hQ]

lemma measurable_cellAt_variable {n : ℕ} (J : Coordinate n → ℕ) (hJ : Measurable J) :
    Measurable (fun z => cellAt (J z) z) := by
  have h : Measurable (fun x : ℕ × Coordinate n => cellAt x.1 x.2) := by
    apply measurable_from_prod_countable_right
    intro j
    exact measurable_cellAt j
  exact h.comp (hJ.prodMk measurable_id)

lemma measurable_deepHeavyCell {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) :
    Measurable (deepHeavyCell μ Q D) := by
  classical
  unfold deepHeavyCell
  apply Measurable.ite (measurableSet_cellSet Q) _ measurable_const
  apply measurable_cellAt_variable
  exact measurable_const.add (measurable_deepHeavyDepth μ Q D)

lemma deepHeavyCell_mem {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    z ∈ cellSet (deepHeavyCell μ Q D z) := by
  rw [deepHeavyCell,ite_eq_left hz]
  exact mem_cellAt hn _ (cellSet_subset_initialCube hn Q hz)

lemma deepHeavyCell_subset {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (z : Coordinate n) : cellSet (deepHeavyCell μ Q D z) ⊆ cellSet Q := by
  classical
  by_cases hz : z ∈ cellSet Q
  · rw [deepHeavyCell,ite_eq_left hz]
    have h := cellAt_nested hn (show Q.1 ≤ Q.1+deepHeavyDepth μ Q D z by omega) (cellSet_subset_initialCube hn Q hz)
    rwa [cellAt_eq_of_mem hn Q hz] at h
  · simp only [deepHeavyCell,ite_eq_right hz,Subset.rfl]

lemma deepHeavyCell_level {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    (deepHeavyCell μ Q D z).1 = Q.1+deepHeavyDepth μ Q D z := by
  simp only [deepHeavyCell,ite_eq_left hz,cellAt]

lemma finite_cells_bounded_level (n D : ℕ) : {Q : Cell n | Q.1 ≤ D}.Finite := by
  have h : {Q : Cell n | Q.1 ≤ D} ⊆ ⋃ j : Fin (D+1), Set.range (fun a : Fin n → Fin (2^j.val) => (⟨j.val,a⟩ : Cell n)) := by
    rintro ⟨j,a⟩ hj
    exact Set.mem_iUnion.mpr ⟨⟨j,by simpa using Nat.lt_succ_iff.mpr hj⟩,⟨a,rfl⟩⟩
  exact (Set.finite_iUnion (fun _ => Set.finite_range _)).subset h

lemma finite_range_deepHeavyCell {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) :
    (Set.range (deepHeavyCell μ Q D)).Finite := by
  apply (finite_cells_bounded_level n (Q.1+D)).subset
  rintro _ ⟨z,rfl⟩
  change (deepHeavyCell μ Q D z).1 ≤ Q.1+D
  unfold deepHeavyCell
  split_ifs
  · change Q.1+deepHeavyDepth μ Q D z ≤ Q.1+D
    exact Nat.add_le_add_left (deepHeavyDepth_le μ Q D z) Q.1
  · omega

lemma heavyThreshold_pow (n j : ℕ) : heavyThreshold n j = (heavyThreshold n 1)^j := by
  induction j with
  | zero => simp [heavyThreshold_zero]
  | succ j ih => rw [heavyThreshold_add,ih,pow_succ]

lemma heavyThreshold_tendsto_zero {n : ℕ} (hn : 0 < n) :
    Filter.Tendsto (heavyThreshold n) Filter.atTop (nhds 0) := by
  have hb : heavyThreshold n 1 < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have : (0:ℝ) < n := by exact_mod_cast hn
    simp only [Nat.cast_one,mul_one]
    linarith
  convert tendsto_pow_atTop_nhds_zero_of_lt_one (heavyThreshold_pos n 1).le hb using 1
  funext j
  exact heavyThreshold_pow n j

lemma exists_heavy_cutoff {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ R : Cell n,μ.real (cellSet R) ≤ C*(1/2:ℝ)^(n*R.1)) (Q : Cell n) :
    ∃ D : ℕ,∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j →
      μ.real (cellSet R) < heavyThreshold n j := by
  have ht : Filter.Tendsto (fun j => C*heavyThreshold n j) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C (heavyThreshold_tendsto_zero hn)
  obtain ⟨D,hD⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))
  refine ⟨D,fun j hj R hR => ?_⟩
  have hpow : (1/2:ℝ)^(n*R.1) ≤ (1/2:ℝ)^(n*j) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    apply Nat.mul_le_mul_left
    omega
  have hd := (hdom R).trans (mul_le_mul_of_nonneg_left hpow hC)
  rw [← heavyThreshold_sq] at hd
  have hsmall := hD j hj.le
  have hm := mul_lt_mul_of_pos_right hsmall (heavyThreshold_pos n j)
  nlinarith

lemma deepHeavyDepth_maximal {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ)
    (hD : ∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j → μ.real (cellSet R) < heavyThreshold n j)
    (z : Coordinate n) {j : ℕ} (h : heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z))) :
    j ≤ deepHeavyDepth μ Q D z := by
  apply le_deepHeavyDepth
  · by_contra hj
    exact (not_le_of_gt (hD j (by omega) (cellAt (Q.1+j) z) rfl)) h
  · exact h

lemma selected_inter_heavy_descendant_empty {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ)
    (hD : ∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j → μ.real (cellSet R) < heavyThreshold n j)
    {R R' : Cell n} {j l : ℕ} (hR : R.1 = Q.1+j) (hR' : R'.1 = R.1+l)
    (hl : 0 < l) (heavy : heavyThreshold n (j+l) ≤ μ.real (cellSet R')) :
    {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R} ∩ cellSet R' = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨⟨hz,he⟩,hz'⟩
  have he' : Q.1+deepHeavyDepth μ Q D z = Q.1+j := by
    simpa only [deepHeavyCell_level μ Q D hz, hR] using congrArg Sigma.fst he
  have hcan : cellAt (Q.1+(j+l)) z = R' := by
    have hlev : Q.1+(j+l) = R'.1 := by omega
    rw [hlev,cellAt_eq_of_mem hn R' hz']
  have hmax := deepHeavyDepth_maximal μ Q D hD z (show heavyThreshold n (j+l) ≤ μ.real (cellSet (cellAt (Q.1+(j+l)) z)) by rwa [hcan])
  omega

lemma measurable_heavySelectionEvent {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (R : Cell n) :
    MeasurableSet {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R} := by
  exact (measurableSet_cellSet Q).inter ((measurable_deepHeavyCell μ Q D) (measurableSet_singleton R))

lemma selected_posterior_spread {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ] (Q : Cell n) (D : ℕ)
    (hD : ∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j → μ.real (cellSet R) < heavyThreshold n j)
    {R : Cell n} {j : ℕ} (hR : R.1 = Q.1+j)
    (hP : 0 < μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R}) :
    DyadicSpread (cond μ {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R}) R
      (max 1 (heavyThreshold n j / μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R})) := by
  let S := {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R}
  have hS := measurable_heavySelectionEvent μ Q D R
  have hSn : μ S ≠ 0 := by
    intro h
    have hz : μ.real S = 0 := by simp [measureReal_def,h]
    exact (ne_of_gt hP) hz
  have : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure_of_finite hSn (measure_ne_top _ _)
  intro l R' hR' _
  have hB0 : 0 ≤ max 1 (heavyThreshold n j/μ.real S) := le_trans (by norm_num) (le_max_left _ _)
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_nonneg hB0 (heavyThreshold_pos n l).le)).mpr
  change (cond μ S).real (cellSet R') ≤ max 1 (heavyThreshold n j/μ.real S)*heavyThreshold n l
  by_cases hl : l = 0
  · rw [hl,heavyThreshold_zero,mul_one]
    exact (measureReal_mono (Set.subset_univ _) ).trans (by simp)
  · have hbound : μ.real (S ∩ cellSet R') ≤ heavyThreshold n (j+l) := by
      by_cases hh : heavyThreshold n (j+l) ≤ μ.real (cellSet R')
      · have he := selected_inter_heavy_descendant_empty hn μ Q D hD hR hR' (by omega) hh
        rw [show S ∩ cellSet R' = ∅ from he]
        simp only [measureReal_empty]
        exact (heavyThreshold_pos n (j+l)).le
      · exact (measureReal_mono Set.inter_subset_right).trans (le_of_not_ge hh)
    rw [measureReal_def,cond_apply hS,ENNReal.toReal_mul,ENNReal.toReal_inv]
    change (μ.real S)⁻¹*μ.real (S ∩ cellSet R') ≤ _
    calc
      _ ≤ (μ.real S)⁻¹*heavyThreshold n (j+l) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hP.le)
      _ = (heavyThreshold n j/μ.real S)*heavyThreshold n l := by rw [heavyThreshold_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (heavyThreshold_pos n l).le

lemma cellSet_disjoint_of_level_eq {n : ℕ} (hn : 0 < n) {R R' : Cell n}
    (h : R.1 = R'.1) (hne : R ≠ R') : Disjoint (cellSet R) (cellSet R') := by
  rcases R with ⟨J,a⟩
  rcases R' with ⟨K,b⟩
  dsimp at h
  subst K
  apply cellSet_disjoint hn
  intro hab
  exact hne (congrArg (Sigma.mk J) hab)

lemma heavy_cell_weight_budget {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    [IsProbabilityMeasure μ] (Q : Cell n) (D : ℕ) (s : Finset (Cell n))
    (hlo : ∀ R ∈ s,Q.1 ≤ R.1) (hhi : ∀ R ∈ s,R.1 ≤ Q.1+D)
    (hheavy : ∀ R ∈ s,heavyThreshold n (R.1-Q.1) ≤ μ.real (cellSet R))
    (g : ℕ → ℝ) (hg : ∀ j,0 ≤ g j) (hgs : ∑ j ∈ Finset.range (D+1),g j ≤ 1) :
    (∑ R ∈ s,heavyThreshold n (R.1-Q.1)*g (R.1-Q.1)) ≤ 1 := by
  classical
  have hm : ∀ R ∈ s,R.1-Q.1 ∈ Finset.range (D+1) := by
    intro R hR
    apply Finset.mem_range.mpr
    have := hhi R hR
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hgs
  let sj := s.filter (fun R => R.1-Q.1 = j)
  have hin : ∀ R ∈ sj,R.1 = Q.1+j := by
    intro R hR
    have h := Finset.mem_filter.mp hR
    have hl := hlo R h.1
    omega
  have hd : (↑sj : Set (Cell n)).PairwiseDisjoint cellSet := by
    intro R hR R' hR' hne
    exact cellSet_disjoint_of_level_eq hn ((hin R hR).trans (hin R' hR').symm) hne
  have hsum : ∑ R ∈ sj,μ.real (cellSet R) ≤ 1 := by
    simpa using sum_measureReal_le_measureReal_univ
      (μ := μ) (fun R _ => measurableSet_cellSet R) hd
  calc
    _ ≤ ∑ R ∈ sj,μ.real (cellSet R)*g j := by
      apply Finset.sum_le_sum
      intro R hR
      have he := (Finset.mem_filter.mp hR).2
      rw [he]
      exact mul_le_mul_of_nonneg_right (by simpa only [he] using hheavy R (Finset.mem_filter.mp hR).1) (hg j)
    _ = (∑ R ∈ sj,μ.real (cellSet R))*g j := (Finset.sum_mul ..).symm
    _ ≤ 1*g j := mul_le_mul_of_nonneg_right hsum (hg j)
    _ = g j := one_mul _

lemma heavy_selection_range_properties {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) (Q : Cell n) (hQ : μ.real (cellSet Q) = 1) (D : ℕ)
    {R : Cell n} (hR : R ∈ Set.range (deepHeavyCell μ Q D)) :
    Q.1 ≤ R.1 ∧ R.1 ≤ Q.1+D ∧ heavyThreshold n (R.1-Q.1) ≤ μ.real (cellSet R) := by
  rcases hR with ⟨z,rfl⟩
  by_cases hz : z ∈ cellSet Q
  · have hl := deepHeavyCell_level μ Q D hz
    have he : (deepHeavyCell μ Q D z).1-Q.1 = deepHeavyDepth μ Q D z := by omega
    refine ⟨by omega,by have := deepHeavyDepth_le μ Q D z; omega,?_⟩
    rw [he,deepHeavyCell,ite_eq_left hz]
    exact deepHeavyDepth_heavy hn μ Q hQ D hz
  · simp only [deepHeavyCell,ite_eq_right hz,Nat.sub_self,heavyThreshold_zero,hQ,le_refl,and_true]
    exact ⟨trivial, Nat.le_add_right _ _⟩

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_PosteriorChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

lemma scorePosterior_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) (hP : 0 < scoreMass μ p) :
    IsProbabilityMeasure (scorePosterior μ p) := by
  have hi := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa [abs_of_nonneg (hp0 x)] using hp1 x)
  refine ⟨?_⟩
  rw [scorePosterior,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (ae_of_all _ (fun x => div_nonneg (hp0 x) hP.le)),
    integral_div]
  change ENNReal.ofReal (scoreMass μ p/scoreMass μ p) = 1
  simp [hP.ne']

lemma integral_scorePosterior {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x)
    (hP : 0 < scoreMass μ p) (f : α → ℝ) :
    (∫ x,f x ∂scorePosterior μ p) = (∫ x,p x*f x ∂μ)/scoreMass μ p := by
  rw [scorePosterior,integral_withDensity_eq_integral_toReal_smul (hp.div_const _).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hp0 _) hP.le),smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact integral_div _ _

lemma scorePosterior_apply_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp1 : ∀ x,p x ≤ 1)
    (hP : 0 < scoreMass μ p) (s : Set α) (hs : MeasurableSet s) :
    scorePosterior μ p s ≤ ENNReal.ofReal (1/scoreMass μ p)*μ s := by
  rw [scorePosterior,withDensity_apply _ hs]
  calc
    _ ≤ ∫⁻ _ in s,ENNReal.ofReal (1/scoreMass μ p) ∂μ := lintegral_mono (fun x =>
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hp1 x) hP.le))
    _ = _ := by simp

lemma scoreMass_posterior_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x)
    (hP : 0 < scoreMass μ p) (q : α → ℝ) :
    scoreMass μ (fun x => p x*q x) = scoreMass μ p*scoreMass (scorePosterior μ p) q := by
  change (∫ x,p x*q x ∂μ) = scoreMass μ p*(∫ x,q x ∂scorePosterior μ p)
  rw [integral_scorePosterior μ p hp hp0 hP]
  field_simp

lemma infoContribution_split {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1)
    (q : ι → α → ℝ) (hq : ∀ i,Measurable (q i)) (hq0 : ∀ i x,0 ≤ q i x)
    (hq1 : ∀ i x,q i x ≤ 1) (hqs : ∀ x,∑ i,q i x = 1) (hP : 0 < scoreMass μ p) :
    (∑ i,infoContribution μ (fun x => p x*q i x)) =
      infoContribution μ p+scoreMass μ p*finiteInformation (scorePosterior μ p) q := by
  have := scorePosterior_probability μ p hp hp0 hp1 hP
  let ν := scorePosterior μ p
  have hip := integrable_xlog_probability μ p hp hp0 hp1
  have hipq (i : ι) : Integrable (fun x => q i x*xlog (p x)) μ :=
    hip.bdd_mul (hq i).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hq0 i x)] using hq1 i x))
  have hiqp (i : ι) : Integrable (fun x => p x*xlog (q i x)) μ :=
    (integrable_xlog_probability μ (q i) (hq i) (hq0 i) (hq1 i)).bdd_mul
      hp.aestronglyMeasurable (ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hp0 x)] using hp1 x))
  have hm (i : ι) := scoreMass_posterior_mul μ p hp hp0 hP (q i)
  have hx (i : ι) : (∫ x,p x*xlog (q i x) ∂μ) =
      scoreMass μ p*(∫ x,xlog (q i x) ∂ν) := by
    rw [integral_scorePosterior μ p hp hp0 hP]
    field_simp
  have hsum : ∑ i,scoreMass ν (q i) = 1 := by
    unfold scoreMass
    rw [← integral_finsetSum]
    · simp [hqs]
    · intro i hi
      exact integrable_bounded_measurable ν (q i) (hq i) (C := 1)
        (fun x => by simpa only [abs_of_nonneg (hq0 i x)] using hq1 i x)
  have hfirst : (∑ i,∫ x,q i x*xlog (p x) ∂μ) = ∫ x,xlog (p x) ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hipq i)]
    simp_rw [← Finset.sum_mul,hqs,one_mul]
  unfold finiteInformation
  simp only [infoContribution]
  dsimp only [ν] at hx hsum
  simp_rw [xlog_mul,integral_add (hipq _) (hiqp _),hx,hm,xlog_mul]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    ← Finset.sum_mul,hsum,one_mul,hfirst]
  ring

lemma infoContribution_split_zero {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1)
    (q : ι → α → ℝ) (hq : ∀ i,Measurable (q i)) (hq0 : ∀ i x,0 ≤ q i x)
    (hq1 : ∀ i x,q i x ≤ 1) (hP : scoreMass μ p = 0) :
    (∑ i,infoContribution μ (fun x => p x*q i x)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hpi : ∀ x,p x*q i x ≤ 1 := fun x => (mul_le_mul (hp1 x) (hq1 i x) (hq0 i x) (by norm_num)).trans_eq (one_mul 1)
  apply infoContribution_zero_mass μ _ (hp.mul (hq i)) (fun x => mul_nonneg (hp0 x) (hq0 i x)) hpi
  have hn : 0 ≤ scoreMass μ (fun x => p x*q i x) := scoreMass_nonneg _ _ (fun x => mul_nonneg (hp0 x) (hq0 i x))
  have hi1 := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hi2 := integrable_bounded_measurable μ (fun x => p x*q i x) (hp.mul (hq i)) (C := 1)
    (fun x => by rw [abs_of_nonneg (mul_nonneg (hp0 x) (hq0 i x))]; exact hpi x)
  have hh : scoreMass μ (fun x => p x*q i x) ≤ scoreMass μ p :=
    integral_mono hi2 hi1 (fun x => by simpa using mul_le_mul_of_nonneg_left (hq1 i x) (hp0 x))
  change scoreMass μ (fun x => p x*q i x) = 0
  linarith

namespace FiniteChannel
variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]

lemma le_one (p : FiniteChannel α ι) (i : ι) (x : α) : p.prob i x ≤ 1 := by
  rw [← p.total x]
  exact Finset.single_le_sum (fun j _ => p.nonneg j x) (Finset.mem_univ _)

lemma integrable (p : FiniteChannel α ι) (μ : Measure α) [IsFiniteMeasure μ] (i : ι) :
    Integrable (p.prob i) μ := integrable_bounded_measurable μ _ (p.measurable i) (C := 1)
      (fun x => by rw [abs_of_nonneg (p.nonneg i x)]; exact p.le_one i x)

lemma mass_total (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ i,scoreMass μ (p.prob i) = 1 := by
  unfold scoreMass
  rw [← integral_finsetSum _ (fun i _ => p.integrable μ i)]
  simp [p.total]

lemma information_bind (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ)
    (μ : Measure α) [IsProbabilityMeasure μ] :
    finiteInformation μ (p.bind q).prob = finiteInformation μ p.prob+
      ∑ i,scoreMass μ (p.prob i)*finiteInformation (scorePosterior μ (p.prob i)) (q i).prob := by
  unfold finiteInformation
  rw [Fintype.sum_prod_type]
  have he (i : ι) :
      (∑ j,infoContribution μ (fun x => p.prob i x*(q i).prob j x)) =
        infoContribution μ (p.prob i)+scoreMass μ (p.prob i)*finiteInformation (scorePosterior μ (p.prob i)) (q i).prob := by
    by_cases h : scoreMass μ (p.prob i) = 0
    · rw [infoContribution_split_zero μ _ (p.measurable i) (p.nonneg i) (p.le_one i)
        _ (q i).measurable (q i).nonneg (q i).le_one h,
        infoContribution_zero_mass μ _ (p.measurable i) (p.nonneg i) (p.le_one i) h,h]
      simp
    · exact infoContribution_split μ _ (p.measurable i) (p.nonneg i) (p.le_one i)
        _ (q i).measurable (q i).nonneg (q i).le_one (q i).total
          (lt_of_le_of_ne (scoreMass_nonneg μ _ (p.nonneg i)) (Ne.symm h))
  change (∑ i,∑ j,infoContribution μ (fun x => p.prob i x*(q i).prob j x)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  rfl

lemma deterministic_information [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (f : α → κ) (hf : Measurable f) (μ : Measure α) :
    finiteInformation μ (deterministic f hf).prob =
      -∑ i,xlog (scoreMass μ ((deterministic f hf).prob i)) := by
  unfold finiteInformation infoContribution
  have he (i : κ) : (fun x => xlog ((deterministic f hf).prob i x)) = 0 := by
    funext x
    dsimp [deterministic]
    split_ifs <;> simp [xlog]
  simp only [he]
  simp

end FiniteChannel

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ChannelProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma scorePosterior_assoc {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p q : α → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (_hq0 : ∀ x,0 ≤ q x)
    (hP : 0 < scoreMass μ p) (_hQ : 0 < scoreMass (scorePosterior μ p) q) :
    scorePosterior (scorePosterior μ p) q = scorePosterior μ (fun x => p x*q x) := by
  have hm := scoreMass_posterior_mul μ p hp hp0 hP q
  unfold scorePosterior
  rw [← withDensity_mul _ (hp.div_const _).ennreal_ofReal (hq.div_const _).ennreal_ofReal]
  apply congrArg (Measure.withDensity μ)
  funext x
  change ENNReal.ofReal (p x/scoreMass μ p)*ENNReal.ofReal (q x/scoreMass (scorePosterior μ p) q) = _
  rw [← ENNReal.ofReal_mul (div_nonneg (hp0 x) hP.le),hm]
  congr 1
  ring

lemma scoreMass_indicator_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) :
    scoreMass μ (S.indicator (fun _ => (1:ℝ))) = μ.real S := by
  rw [scoreMass,integral_indicator hS]
  simp

lemma scorePosterior_indicator_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (S : Set α) (hS : MeasurableSet S) (hP : 0 < μ.real S) :
    scorePosterior μ (S.indicator (fun _ => (1:ℝ))) = cond μ S := by
  rw [scorePosterior,scoreMass_indicator_one μ S hS]
  have he : (fun x => ENNReal.ofReal (S.indicator (fun _ => (1:ℝ)) x/μ.real S)) =
      S.indicator (fun _ => ENNReal.ofReal (1/μ.real S)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he,withDensity_indicator hS,MeasureTheory.withDensity_const,ProbabilityTheory.cond]
  congr 1
  rw [one_div,ENNReal.ofReal_inv_of_pos hP,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma scorePosterior_congr_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p q : α → ℝ} (h : p =ᵐ[μ] q) : scorePosterior μ p = scorePosterior μ q := by
  have hm : scoreMass μ p = scoreMass μ q := integral_congr_ae h
  unfold scorePosterior
  rw [hm]
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

lemma scorePosterior_null_iff {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hP : 0 < scoreMass μ p)
    (S : Set α) (hS : MeasurableSet S) :
    scorePosterior μ p S = 0 ↔ ∀ᵐ x ∂μ,x ∈ S → p x = 0 := by
  rw [scorePosterior,withDensity_apply _ hS,lintegral_eq_zero_iff' (hp.div_const _).ennreal_ofReal.aemeasurable]
  change (∀ᵐ x ∂μ.restrict S, ENNReal.ofReal (p x / scoreMass μ p) = 0) ↔ _
  rw [ae_restrict_iff' hS]
  apply Filter.eventually_congr
  filter_upwards [] with x
  constructor
  · intro hx hxs
    have h : p x/scoreMass μ p ≤ 0 := ENNReal.ofReal_eq_zero.mp (hx hxs)
    exact le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ hP).mp h) (hp0 x)
  · intro hx hxs
    simp [hx hxs]

lemma infoContribution_support_lower {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ)
    (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1)
    (S : Set α) (hS : MeasurableSet S) (hSpos : 0 < μ.real S)
    (hz : ∀ᵐ x ∂μ,x ∉ S → p x = 0) :
    -scoreMass μ p*Real.log (μ.real S) ≤ infoContribution μ p := by
  have hip := integrable_bounded_measurable μ p hp (C := 1)
    (fun x => by rw [abs_of_nonneg (hp0 x)]; exact hp1 x)
  have hix := integrable_xlog_probability μ p hp hp0 hp1
  have hpint : ∫ x in S,p x ∂μ = scoreMass μ p := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    by_cases h : x ∈ S <;> simp [h,hx]
  have hxint : ∫ x in S,xlog (p x) ∂μ = ∫ x,xlog (p x) ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    by_cases h : x ∈ S <;> simp [h,hx,xlog_zero]
  by_cases hP : scoreMass μ p = 0
  · rw [hP,neg_zero,zero_mul]
    exact infoContribution_nonneg μ p hp hp0 hp1
  have hPp : 0 < scoreMass μ p := lt_of_le_of_ne (scoreMass_nonneg μ p hp0) (Ne.symm hP)
  let y := scoreMass μ p/μ.real S
  have hy : 0 < y := div_pos hPp hSpos
  have h := integral_mono (μ := μ.restrict S) ((integrable_const (xlog y)).add (((hip.restrict.sub (integrable_const y))).const_mul (Real.log y+1)))
    hix.restrict (fun x => xlog_lower_tangent (hp0 x) hy)
  change (∫ x in S, xlog y+(Real.log y+1)*(p x-y) ∂μ) ≤ ∫ x in S,xlog (p x) ∂μ at h
  rw [integral_add (f := fun _ => xlog y) (g := fun x => (Real.log y+1)*(p x-y)) (integrable_const _) ((hip.restrict.sub (integrable_const y)).const_mul _),
    integral_const_mul,integral_sub hip.restrict (integrable_const y),hpint,hxint] at h
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter] at h
  have hey : μ.real S*y = scoreMass μ p := by dsimp [y]; field_simp
  rw [hey,sub_self,mul_zero,add_zero] at h
  have he : μ.real S*xlog y = xlog (scoreMass μ p)-scoreMass μ p*Real.log (μ.real S) := by
    unfold xlog
    dsimp [y]
    rw [Real.log_div hPp.ne' hSpos.ne']
    field_simp
  rw [he] at h
  unfold infoContribution
  linarith

lemma scorePosterior_of_mass_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (h : scoreMass μ p = 0) : scorePosterior μ p = 0 := by
  simp [scorePosterior,h]

lemma scoreMass_mul_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (hq0 : ∀ x,0 ≤ q x) (hp1 : ∀ x,p x ≤ 1) (hq1 : ∀ x,q x ≤ 1) :
    scoreMass μ (fun x => p x*q x) ≤ scoreMass μ p := by
  have hpq1 : ∀ x,p x*q x ≤ 1 := fun x =>
    (mul_le_mul (hp1 x) (hq1 x) (hq0 x) (by norm_num)).trans_eq (one_mul 1)
  apply integral_mono
    (integrable_bounded_measurable μ _ (hp.mul hq) (C := 1) (fun x => by
      change |p x*q x| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (hp0 x) (hq0 x))]; exact hpq1 x))
    (integrable_bounded_measurable μ _ hp (C := 1) (fun x => by rw [abs_of_nonneg (hp0 x)]; exact hp1 x))
  intro x
  simpa using mul_le_mul_of_nonneg_left (hq1 x) (hp0 x)

lemma scoreMass_mul_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (hq0 : ∀ x,0 ≤ q x) (hp1 : ∀ x,p x ≤ 1) (hq1 : ∀ x,q x ≤ 1) :
    scoreMass μ (fun x => p x*q x) = scoreMass μ p*scoreMass (scorePosterior μ p) q := by
  by_cases h : scoreMass μ p = 0
  · rw [h,zero_mul]
    exact le_antisymm (by simpa only [h] using scoreMass_mul_le μ p q hp hq hp0 hq0 hp1 hq1)
      (scoreMass_nonneg μ _ (fun x => mul_nonneg (hp0 x) (hq0 x)))
  · exact (scoreMass_posterior_mul μ p hp hp0
      (lt_of_le_of_ne (scoreMass_nonneg μ p hp0) (Ne.symm h)) q)

namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {κ : ι → Type*} [∀ i,Fintype (κ i)]

lemma information_dbind (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsProbabilityMeasure μ] :
    finiteInformation μ (p.dbind q).prob = finiteInformation μ p.prob+
      ∑ i,scoreMass μ (p.prob i)*finiteInformation (scorePosterior μ (p.prob i)) (q i).prob := by
  unfold finiteInformation
  rw [Fintype.sum_sigma]
  have he (i : ι) :
      (∑ j,infoContribution μ (fun x => p.prob i x*(q i).prob j x)) =
        infoContribution μ (p.prob i)+scoreMass μ (p.prob i)*finiteInformation (scorePosterior μ (p.prob i)) (q i).prob := by
    by_cases h : scoreMass μ (p.prob i) = 0
    · rw [infoContribution_split_zero μ _ (p.measurable i) (p.nonneg i) (p.le_one i)
        _ (q i).measurable (q i).nonneg (q i).le_one h,
        infoContribution_zero_mass μ _ (p.measurable i) (p.nonneg i) (p.le_one i) h,h]
      simp
    · exact infoContribution_split μ _ (p.measurable i) (p.nonneg i) (p.le_one i)
        _ (q i).measurable (q i).nonneg (q i).le_one (q i).total
          (lt_of_le_of_ne (scoreMass_nonneg μ _ (p.nonneg i)) (Ne.symm h))
  change (∑ i,∑ j,infoContribution μ (fun x => p.prob i x*(q i).prob j x)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  rfl

lemma mass_dbind (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : Sigma κ) :
    scoreMass μ ((p.dbind q).prob i) = scoreMass μ (p.prob i.1)*
      scoreMass (scorePosterior μ (p.prob i.1)) ((q i.1).prob i.2) :=
  scoreMass_mul_eq μ _ _ (p.measurable i.1) ((q i.1).measurable i.2)
    (p.nonneg i.1) ((q i.1).nonneg i.2) (p.le_one i.1) ((q i.1).le_one i.2)

lemma coarsen_dbind_fst (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i)) :
    ((p.dbind q).coarsen Sigma.fst).prob = p.prob := by
  classical
  funext i x
  simp only [coarsen,dbind,Fintype.sum_sigma]
  change (∑ a, ∑ b, if a = i then p.prob a x*(q a).prob b x else 0) = _
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp [← Finset.mul_sum,FiniteChannel.total]

lemma coarsen_comp {κ η : Type*} [Fintype κ] [Fintype η]
    (p : FiniteChannel α ι) (f : ι → κ) (g : κ → η) :
    ((p.coarsen f).coarsen g).prob = (p.coarsen (g ∘ f)).prob := by
  classical
  funext k x
  simp only [coarsen,Function.comp_apply]
  have hex (j : κ) : (if g j = k then ∑ i,if f i = j then p.prob i x else 0 else 0) =
      ∑ i,if g j = k then if f i = j then p.prob i x else 0 else 0 := by
    by_cases h : g j = k <;> simp [h]
  simp_rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun j => if g j = k then if f i = j then p.prob i x else 0 else 0) =
      (fun j => if f i = j then if g (f i) = k then p.prob i x else 0 else 0) := by
    funext j
    by_cases h : f i = j
    · subst j; simp
    · simp [h]
  rw [he]
  simp

end FiniteChannel

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_RefinementCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma finite_entropy_le_subprob_reference {ι : Type*} [Fintype ι]
    (p b : ι → ℝ) (hp : ∀ i,0 ≤ p i) (hpsum : ∑ i,p i = 1)
    (hb : ∀ i,0 < b i) (hbsum : ∑ i,b i ≤ 1) :
    -(∑ i,xlog (p i)) ≤ -∑ i,p i*Real.log (b i) := by
  have hi (i : ι) : p i-b i ≤ p i*Real.log (p i/b i) := by
    have h := log_ratio_lower (hp i) (hb i).le (by norm_num : (0:ℝ) < 1)
      (fun hz => False.elim ((hb i).ne' hz))
    simpa [xlog_one] using h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp_rw [log_ratio_mul (hb _).ne'] at hs
  simp only [Finset.sum_sub_distrib,hpsum] at hs
  linarith

lemma weighted_log_max_ratio_le {p θ g : ℝ} (hp : 0 ≤ p) (hθ : 0 < θ)
    (hg : 0 < g) (hg1 : g ≤ 1) :
    p*Real.log (max 1 (θ/p)) ≤ -p*Real.log g+g*θ := by
  by_cases hpz : p = 0
  · simp only [hpz,zero_mul,neg_zero,zero_add]
    positivity
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  by_cases hθp : θ ≤ p
  · rw [max_eq_left ((div_le_one hpp).mpr hθp),Real.log_one,mul_zero]
    have hl := Real.log_nonpos hg.le hg1
    have hd := mul_nonpos_of_nonneg_of_nonpos hp hl
    nlinarith [mul_pos hg hθ]
  · rw [max_eq_right ((one_le_div hpp).mpr (le_of_not_ge hθp))]
    have harg : 0 < θ*g/p := div_pos (mul_pos hθ hg) hpp
    have h := Real.log_le_sub_one_of_pos harg
    rw [Real.log_div (mul_pos hθ hg).ne' hpz,Real.log_mul hθ.ne' hg.ne'] at h
    rw [Real.log_div hθ.ne' hpz]
    have hh := mul_le_mul_of_nonneg_left h hp
    have he : p*(θ*g/p) = θ*g := by field_simp
    nlinarith

lemma finite_log_concentration_le {ι : Type*} [Fintype ι]
    (p θ g : ι → ℝ) (hp : ∀ i,0 ≤ p i) (hθ : ∀ i,0 < θ i)
    (hg : ∀ i,0 < g i) (hg1 : ∀ i,g i ≤ 1)
    (hbound : ∑ i,θ i*g i ≤ 1) :
    (∑ i,p i*Real.log (max 1 (θ i/p i))) ≤ -(∑ i,p i*Real.log (g i))+1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => weighted_log_max_ratio_le (hp i) (hθ i) (hg i) (hg1 i))
  simp only [Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib,mul_comm (g _) (θ _)] at h
  linarith

lemma depthGeometric_pos (j : ℕ) : 0 < depthGeometric j := by unfold depthGeometric; positivity
lemma depthGeometric_le_one (j : ℕ) : depthGeometric j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
lemma log_depthGeometric (j : ℕ) : Real.log (depthGeometric j) = -((j:ℝ)+1)*Real.log 2 := by
  simp only [depthGeometric,Real.log_pow,Real.log_div one_ne_zero (by norm_num : (2:ℝ) ≠ 0),
    Real.log_one,zero_sub,Nat.cast_add,Nat.cast_one]
  ring

lemma depthGeometric_sum_le_one (D : ℕ) : ∑ j ∈ Finset.range (D+1),depthGeometric j ≤ 1 := by
  have hsum : ∀ d,∑ j ∈ Finset.range d,depthGeometric j = 1-(1/2:ℝ)^d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [Finset.sum_range_succ,ih]; unfold depthGeometric; rw [pow_succ]; ring
  rw [hsum]
  have := pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) (D+1)
  linarith

lemma entropy_and_concentration_depth {ι : Type*} [Fintype ι]
    (n : ℕ) (p : ι → ℝ) (j : ι → ℕ) (hp : ∀ i,0 ≤ p i) (hpsum : ∑ i,p i = 1)
    (hbudget : ∑ i,(2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)*depthGeometric (j i) ≤ 1) :
    -(∑ i,xlog (p i)) ≤ ((n:ℝ)/2+1)*Real.log 2*(∑ i,p i*(j i:ℝ))+Real.log 2 ∧
    (∑ i,p i*Real.log (max 1 ((2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)/p i))) ≤
      Real.log 2*(∑ i,p i*(j i:ℝ))+Real.log 2+1 := by
  have hθ (i : ι) : 0 < (2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog (i : ι) : Real.log ((2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)*depthGeometric (j i)) =
      -((n:ℝ)/2+1)*Real.log 2*(j i:ℝ)-Real.log 2 := by
    rw [Real.log_mul (hθ i).ne' (depthGeometric_pos _).ne',Real.log_rpow (by norm_num : (0:ℝ) < 2),log_depthGeometric]
    ring
  have he := finite_entropy_le_subprob_reference p (fun i => (2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)*depthGeometric (j i))
    hp hpsum (fun i => mul_pos (hθ i) (depthGeometric_pos _)) hbudget
  have hb := finite_log_concentration_le p (fun i => (2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2))
    (fun i => depthGeometric (j i)) hp hθ (fun i => depthGeometric_pos _) (fun i => depthGeometric_le_one _) hbudget
  have halg (i : ι) : p i*(-((n:ℝ)/2+1)*Real.log 2*(j i:ℝ)-Real.log 2) =
      -(((n:ℝ)/2+1)*Real.log 2)*(p i*(j i:ℝ))-Real.log 2*p i := by ring
  have hbalg (i : ι) : p i*(-((j i:ℝ)+1)*Real.log 2) =
      -(Real.log 2)*(p i*(j i:ℝ))-Real.log 2*p i := by ring
  simp_rw [hlog,halg] at he
  simp_rw [log_depthGeometric,hbalg] at hb
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,hpsum,mul_one] at he hb
  constructor <;> linarith

attribute [instance] HeavyRefinement.finiteIndex

lemma exists_heavy_refinement {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ] (Q : Cell n)
    (hQ : μ (cellSet Q) = 1) {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ R : Cell n,μ.real (cellSet R) ≤ C*(1/2:ℝ)^(n*R.1)) :
    Nonempty (HeavyRefinement n μ Q) := by
  classical
  obtain ⟨D,hD⟩ := exists_heavy_cutoff hn μ hC hdom Q
  let s := (finite_range_deepHeavyCell μ Q D).toFinset
  let κ := {R : Cell n // R ∈ s}
  let f : Coordinate n → κ := fun z => ⟨deepHeavyCell μ Q D z,by
    simpa only [s,Set.Finite.mem_toFinset] using (Set.mem_range_self z (f := deepHeavyCell μ Q D))⟩
  have hf : Measurable f := (measurable_deepHeavyCell μ Q D).subtype_mk
  let q := FiniteChannel.deterministic f hf
  let j : κ → ℕ := fun i => i.val.1-Q.1
  let P : κ → ℝ := fun i => scoreMass μ (q.prob i)
  let B : κ → ℝ := fun i => max 1 (heavyThreshold n (j i)/P i)
  have hQa : ∀ᵐ z ∂μ,z ∈ cellSet Q := (mem_ae_iff_prob_eq_one (measurableSet_cellSet Q)).mpr hQ
  have hQr : μ.real (cellSet Q) = 1 := by simp [measureReal_def,hQ]
  have hprop (R : Cell n) (hR : R ∈ s) :=
    heavy_selection_range_properties hn μ Q hQr D (by simpa only [s,Set.Finite.mem_toFinset] using hR)
  have hbudget : ∑ i : κ,heavyThreshold n (j i)*depthGeometric (j i) ≤ 1 := by
    change (∑ i : {R : Cell n // R ∈ s}, heavyThreshold n (i.val.1-Q.1)*depthGeometric (i.val.1-Q.1)) ≤ 1
    rw [Finset.sum_coe_sort s (fun R : Cell n => heavyThreshold n (R.1-Q.1)*depthGeometric (R.1-Q.1))]
    exact heavy_cell_weight_budget hn μ Q D s (fun R hR => (hprop R hR).1)
      (fun R hR => (hprop R hR).2.1) (fun R hR => (hprop R hR).2.2)
      depthGeometric (fun j => (depthGeometric_pos j).le) (depthGeometric_sum_le_one D)
  have hest := entropy_and_concentration_depth n P j
    (fun i => scoreMass_nonneg μ _ (q.nonneg i)) (q.mass_total μ) hbudget
  have hev (i : κ) : q.prob i =ᵐ[μ]
      {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val}.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [hQa] with z hz
    have he : f z = i ↔ deepHeavyCell μ Q D z = i.val := Subtype.ext_iff
    simp [q,FiniteChannel.deterministic,he,hz,Set.indicator]
  have hmass (i : κ) : P i = μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val} := by
    change (∫ z,q.prob i z ∂μ) = _
    rw [integral_congr_ae (hev i)]
    exact scoreMass_indicator_one μ _ (measurable_heavySelectionEvent μ Q D i.val)
  refine ⟨{ Index := κ
            channel := q
            cell := Subtype.val
            B := B
            B_one := fun i => le_max_left _ _
            select := f
            select_fiber := fun i => hf (measurableSet_singleton i)
            chosen := fun i z hz => by
              by_contra h
              simp [q,FiniteChannel.deterministic,h] at hz
            cell_subset := fun i => by
              have hmem : i.val ∈ Set.range (deepHeavyCell μ Q D) := by
                simpa only [s,Set.Finite.mem_toFinset] using i.property
              obtain ⟨z,hz⟩ := hmem
              rw [← hz]
              exact deepHeavyCell_subset hn μ Q D z
            select_mem := fun z hz => deepHeavyCell_mem hn μ Q D hz
            level_ge := fun i => (hprop i.val i.property).1
            support := ?_
            spread := ?_
            entropy_bound := ?_
            concentration_bound := ?_ }⟩
  · intro i hi
    have := scorePosterior_probability μ _ (q.measurable i) (q.nonneg i) (q.le_one i) hi
    apply (prob_compl_eq_zero_iff (measurableSet_cellSet i.val)).mp
    apply (scorePosterior_null_iff μ _ (q.measurable i) (q.nonneg i) hi _ (measurableSet_cellSet i.val).compl).mpr
    filter_upwards [hQa] with z hz
    intro hnot
    have he : f z ≠ i := by
      intro he
      have hm := deepHeavyCell_mem hn μ Q D hz
      have hei : deepHeavyCell μ Q D z = i.val := congrArg Subtype.val he
      rw [hei] at hm
      exact hnot hm
    simp [q,FiniteChannel.deterministic,he]
  · intro i hi
    have hip : 0 < μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val} := by
      rw [← hmass]; exact hi
    have hposterior : scorePosterior μ (q.prob i) =
        cond μ {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val} := by
      rw [scorePosterior_congr_ae μ (hev i)]
      exact scorePosterior_indicator_one μ _ (measurable_heavySelectionEvent μ Q D i.val) hip
    rw [hposterior]
    have hlev : i.val.1 = Q.1+j i := by have := (hprop i.val i.property).1; dsimp [j]; omega
    dsimp [B]
    rw [hmass]
    exact selected_posterior_spread hn μ Q D hD hlev hip
  · rw [FiniteChannel.deterministic_information]
    exact hest.1
  · exact hest.2

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ChannelEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma integrable_xlog_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M) : Integrable (fun x => xlog (f x)) μ := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := M)).image continuous_xlog).isBounded.exists_norm_le
  apply integrable_bounded_measurable μ _ (continuous_xlog.measurable.comp hf)
  intro x
  simpa only [Real.norm_eq_abs,Function.comp_def] using hC _ (Set.mem_image_of_mem _ ⟨hf0 x,hfM x⟩)

lemma klDiv_withDensity_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    InformationTheory.klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x,xlog (f x) ∂μ) := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfM x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfM
  have hib : Integrable (fun x => InformationTheory.klFun (f x)) μ :=
    (hix.add (integrable_const 1)).sub hif
  have hfint : ∫ x,f x ∂μ = 1 := by
    have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
    exact (ENNReal.ofReal_eq_one.mp h)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous μ _)]
  have hrn := Measure.rnDeriv_withDensity μ hf.ennreal_ofReal
  have he : (fun x => ENNReal.ofReal (InformationTheory.klFun (((μ.withDensity
      (fun x => ENNReal.ofReal (f x))).rnDeriv μ x).toReal))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (InformationTheory.klFun (f x))) := by
    filter_upwards [hrn] with x hx
    rw [hx,ENNReal.toReal_ofReal (hf0 x)]
  rw [lintegral_congr_ae he,← ofReal_integral_eq_lintegral_ofReal hib
    (ae_of_all _ (fun x => InformationTheory.klFun_nonneg (hf0 x)))]
  congr 1
  change (∫ x,xlog (f x)+1-f x ∂μ) = _
  rw [integral_sub (f := fun x => xlog (f x)+1) (hix.add (integrable_const 1)) hif,
    integral_add hix (integrable_const 1),hfint]
  simp

lemma measurable_finite_eval {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : ι → α → ℝ)
    (hp : ∀ i,Measurable (p i)) : Measurable (fun x : α × ι => p x.2 x.1) := by
  classical
  have he : (fun x : α × ι => p x.2 x.1) =
      fun x => ∑ i,if x.2 = i then p i x.1 else 0 := by funext x; simp
  rw [he]
  apply Finset.measurable_sum
  intro i hi
  exact ((hp i).comp measurable_fst).piecewise (measurable_snd (measurableSet_singleton i)) measurable_const

namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_density (p : FiniteChannel α ι) :
    Measurable (fun x : α × ι => ENNReal.ofReal (p.prob x.2 x.1)) :=
  (measurable_finite_eval p.prob p.measurable).ennreal_ofReal

lemma lintegral_law (p : FiniteChannel α ι) (μ : Measure α) [SFinite μ]
    (f : α × ι → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x,f x ∂p.law μ = ∑ i,∫⁻ x,ENNReal.ofReal (p.prob i x)*f (x,i) ∂μ := by
  rw [law,lintegral_withDensity_eq_lintegral_mul _ p.measurable_density hf,
    lintegral_prod _ (p.measurable_density.mul hf).aemeasurable]
  simp_rw [lintegral_count,tsum_fintype]
  exact lintegral_finsetSum _ (fun i _ => ((p.measurable i).ennreal_ofReal.mul
    (hf.comp (show Measurable (fun x : α => (x,i)) from measurable_id.prodMk measurable_const))))

lemma lintegral_prob {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) [IsFiniteMeasure μ] (i : ι) :
    ∫⁻ x,ENNReal.ofReal (p.prob i x) ∂μ = ENNReal.ofReal (scoreMass μ (p.prob i)) :=
  (ofReal_integral_eq_lintegral_ofReal (p.integrable μ i) (ae_of_all _ (p.nonneg i))).symm

lemma density_total {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : FiniteChannel α ι) (x : α) :
    ∑ i,ENNReal.ofReal (p.prob i x) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.nonneg i x),p.total]
  simp

instance law_probability (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (p.law μ) := by
  constructor
  have h := p.lintegral_law μ (fun _ => 1) measurable_const
  simp only [lintegral_const,one_mul,mul_one] at h
  rw [h]
  simp_rw [p.lintegral_prob μ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => scoreMass_nonneg μ _ (p.nonneg i)),p.mass_total]
  simp

lemma law_fst (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    (p.law μ).map Prod.fst = μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_fst]
  rw [p.lintegral_law μ (fun x => f x.1) (hf.comp measurable_fst)]
  change (∑ i,∫⁻ x,ENNReal.ofReal (p.prob i x)*f x ∂μ) = _
  rw [← lintegral_finsetSum Finset.univ (f := fun i x => ENNReal.ofReal (p.prob i x)*f x)
    (fun i _ => ((p.measurable i).ennreal_ofReal.mul hf))]
  simp_rw [← Finset.sum_mul,p.density_total,one_mul]

lemma law_snd (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    (p.law μ).map Prod.snd = p.outputLaw μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_snd]
  rw [p.lintegral_law μ (fun x => f x.2) (hf.comp measurable_snd),
    outputLaw,lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) hf,
    lintegral_count,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  change (∫⁻ x,ENNReal.ofReal (p.prob i x)*f i ∂μ) = ENNReal.ofReal (scoreMass μ (p.prob i))*f i
  rw [lintegral_mul_const (f i) (p.measurable i).ennreal_ofReal, p.lintegral_prob]

instance outputLaw_probability (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (p.outputLaw μ) := by
  rw [← p.law_snd μ]
  exact (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance

lemma law_eq_sum (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    p.law μ = ∑ i, (μ.withDensity (fun x => ENNReal.ofReal (p.prob i x))).map (fun x => (x,i)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [p.lintegral_law μ _ hf,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_map (g := fun x : α => (x,i)) hf (measurable_id.prodMk measurable_const)]
  exact (lintegral_withDensity_eq_lintegral_mul μ (p.measurable i).ennreal_ofReal
    (hf.comp (show Measurable (fun x : α => (x,i)) from measurable_id.prodMk measurable_const))).symm

lemma measurable_likelihoodRatio (p : FiniteChannel α ι) (μ : Measure α) :
    Measurable (p.likelihoodRatio μ) :=
  measurable_finite_eval (fun i x => p.prob i x/scoreMass μ (p.prob i))
    (fun i => (p.measurable i).div_const _)

lemma likelihoodRatio_nonneg {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) (x : α × ι) :
    0 ≤ p.likelihoodRatio μ x := div_nonneg (p.nonneg _ _) (scoreMass_nonneg μ _ (p.nonneg _))

lemma likelihoodRatio_le {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) (x : α × ι) :
    p.likelihoodRatio μ x ≤ ∑ i,1/scoreMass μ (p.prob i) := by
  classical
  exact (div_le_div_of_nonneg_right (p.le_one _ _) (scoreMass_nonneg μ _ (p.nonneg _))).trans
    (Finset.single_le_sum (fun i _ => div_nonneg zero_le_one (scoreMass_nonneg μ _ (p.nonneg i))) (Finset.mem_univ x.2))

lemma law_eq_reference_density (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    p.law μ = (μ.prod (p.outputLaw μ)).withDensity (fun x => ENNReal.ofReal (p.likelihoodRatio μ x)) := by
  unfold outputLaw
  rw [prod_withDensity_right (measurable_of_countable _),
    ← withDensity_mul (μ.prod Measure.count)
      (f := fun z : α × ι => ENNReal.ofReal (scoreMass μ (p.prob z.2)))
      (g := fun z => ENNReal.ofReal (p.likelihoodRatio μ z))
      ((measurable_of_countable (fun i : ι => ENNReal.ofReal (scoreMass μ (p.prob i)))).comp measurable_snd) (p.measurable_likelihoodRatio μ).ennreal_ofReal]
  unfold law
  apply withDensity_congr_ae
  have he (i : ι) : ∀ᵐ x ∂μ, p.prob i x = scoreMass μ (p.prob i)*(p.prob i x/scoreMass μ (p.prob i)) := by
    by_cases h : scoreMass μ (p.prob i) = 0
    · have hz := (integral_eq_zero_iff_of_nonneg (p.nonneg i) (p.integrable μ i)).mp h
      filter_upwards [hz] with x hx
      simp [h,hx]
    · exact ae_of_all _ (fun x => by field_simp)
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun p.measurable_density
      (((measurable_of_countable (fun i : ι => ENNReal.ofReal (scoreMass μ (p.prob i)))).comp measurable_snd).mul
        (p.measurable_likelihoodRatio μ).ennreal_ofReal))).mpr
  · filter_upwards [ae_all_iff.mpr he] with x hx
    exact ae_of_all _ (fun i => by
      change ENNReal.ofReal (p.prob i x) = ENNReal.ofReal (scoreMass μ (p.prob i))*ENNReal.ofReal (p.prob i x/scoreMass μ (p.prob i))
      rw [← ENNReal.ofReal_mul (scoreMass_nonneg μ _ (p.nonneg i)),← hx i])

lemma integral_xlog_ratio {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
    scoreMass μ (p.prob i)*(∫ x,xlog (p.prob i x/scoreMass μ (p.prob i)) ∂μ) =
      infoContribution μ (p.prob i) := by
  by_cases h : scoreMass μ (p.prob i) = 0
  · rw [h,zero_mul,infoContribution_zero_mass μ _ (p.measurable i) (p.nonneg i) (p.le_one i) h]
  · have he (x : α) : scoreMass μ (p.prob i)*xlog (p.prob i x/scoreMass μ (p.prob i)) =
        xlog (p.prob i x)-p.prob i x*Real.log (scoreMass μ (p.prob i)) := by
      have hx := xlog_mul (p.prob i x/scoreMass μ (p.prob i)) (scoreMass μ (p.prob i))
      rw [div_mul_cancel₀ _ h] at hx
      unfold xlog at hx ⊢
      field_simp at hx ⊢
      linarith
    rw [← integral_const_mul]
    simp_rw [he]
    rw [integral_sub (integrable_xlog_probability μ _ (p.measurable i) (p.nonneg i) (p.le_one i))
      ((p.integrable μ i).mul_const _),integral_mul_const]
    rfl

lemma klDiv_law (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    InformationTheory.klDiv (p.law μ) (((p.law μ).map Prod.fst).prod ((p.law μ).map Prod.snd)) =
      ENNReal.ofReal (finiteInformation μ p.prob) := by
  rw [p.law_fst μ,p.law_snd μ]
  let ν := μ.prod (p.outputLaw μ)
  let F := p.likelihoodRatio μ
  have he : p.law μ = ν.withDensity (fun x => ENNReal.ofReal (F x)) := p.law_eq_reference_density μ
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (F x))) := he ▸ p.law_probability μ
  rw [he,klDiv_withDensity_bounded ν F (p.measurable_likelihoodRatio μ)
    (p.likelihoodRatio_nonneg μ) (p.likelihoodRatio_le μ)]
  congr 1
  have hix := integrable_xlog_bounded ν F (p.measurable_likelihoodRatio μ)
    (p.likelihoodRatio_nonneg μ) (p.likelihoodRatio_le μ)
  rw [integral_prod_symm _ hix]
  change (∫ i,(∫ x,xlog (p.prob i x/scoreMass μ (p.prob i)) ∂μ) ∂p.outputLaw μ) = _
  rw [outputLaw,integral_withDensity_eq_integral_toReal_smul (measurable_of_countable _)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),integral_count]
  simp only [ENNReal.toReal_ofReal (scoreMass_nonneg μ _ (p.nonneg _)),smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => p.integral_xlog_ratio μ i)

end FiniteChannel

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_StateExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

lemma expectation_const (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    p.expectation μ (fun _ => c) = c := by
  rw [expectation,← Finset.sum_mul,p.mass_total μ,one_mul]

lemma expectation_add (p : FiniteChannel α ι) (μ : Measure α) (f g : ι → ℝ) :
    p.expectation μ (fun i => f i+g i) = p.expectation μ f+p.expectation μ g := by
  simp [expectation,mul_add,Finset.sum_add_distrib]

lemma expectation_const_mul (p : FiniteChannel α ι) (μ : Measure α) (c : ℝ) (f : ι → ℝ) :
    p.expectation μ (fun i => c*f i) = c*p.expectation μ f := by
  simp only [expectation,Finset.mul_sum]; congr 1; funext i; ring

lemma expectation_mono (p : FiniteChannel α ι) (μ : Measure α) {f g : ι → ℝ} (h : ∀ i,f i ≤ g i) :
    p.expectation μ f ≤ p.expectation μ g :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (scoreMass_nonneg μ _ (p.nonneg i)))

lemma sum_mass_dbind {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : ι) :
    (∑ j,scoreMass μ ((p.dbind q).prob ⟨i,j⟩)) = scoreMass μ (p.prob i) := by
  unfold scoreMass
  rw [← integral_finsetSum _ (fun j _ => (p.dbind q).integrable μ ⟨i,j⟩)]
  simp [dbind,← Finset.mul_sum,FiniteChannel.total]

lemma expectation_dbind {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (f : Sigma κ → ℝ) :
    (p.dbind q).expectation μ f = p.expectation μ (fun i =>
      (q i).expectation (scorePosterior μ (p.prob i)) (fun j => f ⟨i,j⟩)) := by
  unfold expectation
  rw [Fintype.sum_sigma]
  simp_rw [p.mass_dbind q μ,mul_assoc,← Finset.mul_sum]

lemma expectation_dbind_fst {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (f : ι → ℝ) :
    (p.dbind q).expectation μ (fun i => f i.1) = p.expectation μ f := by
  unfold expectation
  rw [Fintype.sum_sigma]
  simp_rw [← Finset.sum_mul,p.sum_mass_dbind q μ]

lemma expectation_bind_fst {κ : Type*} [Fintype κ]
    (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ)
    (μ : Measure α) [IsFiniteMeasure μ] (f : ι → ℝ) :
    (p.bind q).expectation μ (fun i => f i.1) = p.expectation μ f := by
  have hm (i : ι) : (∑ j,scoreMass μ ((p.bind q).prob (i,j))) = scoreMass μ (p.prob i) := by
    unfold scoreMass
    rw [← integral_finsetSum _ (fun j _ => (p.bind q).integrable μ (i,j))]
    simp [bind,← Finset.mul_sum,FiniteChannel.total]
  unfold expectation
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul,hm]

lemma bind_positive_parent {κ : Type*} [Fintype κ]
    (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ)
    (μ : Measure α) [IsFiniteMeasure μ] (i : ι × κ)
    (hi : 0 < scoreMass μ ((p.bind q).prob i)) : 0 < scoreMass μ (p.prob i.1) :=
  hi.trans_le (scoreMass_mul_le μ _ _ (p.measurable i.1) ((q i.1).measurable i.2)
    (p.nonneg i.1) ((q i.1).nonneg i.2) (p.le_one i.1) ((q i.1).le_one i.2))

lemma dbind_positive_parent {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : Sigma κ)
    (hi : 0 < scoreMass μ ((p.dbind q).prob i)) : 0 < scoreMass μ (p.prob i.1) :=
  hi.trans_le (scoreMass_mul_le μ _ _ (p.measurable i.1) ((q i.1).measurable i.2)
    (p.nonneg i.1) ((q i.1).nonneg i.2) (p.le_one i.1) ((q i.1).le_one i.2))

lemma dbind_positive_conditional {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : Sigma κ)
    (hi : 0 < scoreMass μ ((p.dbind q).prob i)) :
    0 < scoreMass (scorePosterior μ (p.prob i.1)) ((q i.1).prob i.2) := by
  rw [p.mass_dbind q μ i] at hi
  exact (mul_pos_iff_of_pos_left (p.dbind_positive_parent q μ i (by rw [p.mass_dbind q μ i]; exact hi))).mp hi

end FiniteChannel

lemma zero_heavy_refinement (n : ℕ) (Q : Cell n) : Nonempty (HeavyRefinement n 0 Q) := by
  let q : FiniteChannel (Coordinate n) Unit := {
    prob := fun _ _ => 1
    measurable := fun _ => measurable_const
    nonneg := fun _ _ => zero_le_one
    total := fun _ => by simp }
  refine ⟨{ Index := Unit
            channel := q
            cell := fun _ => Q
            B := fun _ => 1
            B_one := fun _ => le_refl _
            select := fun _ => ()
            select_fiber := fun i => by simp only [Subsingleton.elim () i, Set.ofPred_true]; exact MeasurableSet.univ
            chosen := fun i z hz => Subsingleton.elim _ _
            cell_subset := fun _ => Subset.rfl
            select_mem := fun z hz => hz
            level_ge := fun _ => le_refl _
            support := ?_
            spread := ?_
            entropy_bound := ?_
            concentration_bound := ?_ }⟩
  · intro i hi; simp [scoreMass] at hi
  · intro i hi; simp [scoreMass] at hi
  · simp [finiteInformation,infoContribution,scoreMass,xlog_zero]
    exact Real.log_nonneg (by norm_num)
  · simp [scoreMass]
    positivity

attribute [instance] AnalysisState.finiteIndex

namespace AnalysisState
variable {n : ℕ}

lemma depth_nonneg (s : AnalysisState n) : 0 ≤ s.depth :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (scoreMass_nonneg _ _ (s.channel.nonneg i)) (Nat.cast_nonneg _))

lemma concentration_nonneg (s : AnalysisState n) : 0 ≤ s.concentration :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (scoreMass_nonneg _ _ (s.channel.nonneg i)) (Real.log_nonneg (s.B_one i)))

lemma information_lower (hn : 0 < n) (s : AnalysisState n) :
    (n:ℝ)*Real.log 2*s.depth ≤ s.information := by
  have := cubePrior_isProbabilityMeasure hn
  change (n:ℝ)*Real.log 2*(∑ i,scoreMass (cubePrior n) (s.channel.prob i)*((s.cell i).1:ℝ)) ≤
    ∑ i,infoContribution (cubePrior n) (s.channel.prob i)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : scoreMass (cubePrior n) (s.channel.prob i) = 0
  · simp only [h,zero_mul,mul_zero]
    exact infoContribution_nonneg _ _ (s.channel.measurable i) (s.channel.nonneg i) (s.channel.le_one i)
  have hP : 0 < scoreMass (cubePrior n) (s.channel.prob i) :=
    lt_of_le_of_ne (scoreMass_nonneg _ _ (s.channel.nonneg i)) (Ne.symm h)
  have := scorePosterior_probability _ _ (s.channel.measurable i) (s.channel.nonneg i) (s.channel.le_one i) hP
  have hval : (cubePrior n).real (cellSet (s.cell i)) = (1/2:ℝ)^(n*(s.cell i).1) := by
    rw [measureReal_def,cubePrior_cellSet hn,ENNReal.toReal_ofReal (by positivity)]
  have hz := (scorePosterior_null_iff (cubePrior n) _ (s.channel.measurable i) (s.channel.nonneg i) hP
    _ (measurableSet_cellSet (s.cell i)).compl).mp
      ((prob_compl_eq_zero_iff (measurableSet_cellSet (s.cell i))).mpr (s.support i hP))
  have hl := infoContribution_support_lower (cubePrior n) _ (s.channel.measurable i) (s.channel.nonneg i) (s.channel.le_one i)
    _ (measurableSet_cellSet (s.cell i)) (by rw [hval]; positivity) hz
  rw [hval,Real.log_pow] at hl
  have he : Real.log (1/2:ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  rw [he] at hl
  push_cast at hl
  nlinarith

lemma information_of_potential (hn : 8 ≤ n) (s : AnalysisState n) {A : ℝ}
    (h : s.potential ≤ A) : s.information ≤ 4*A := by
  have hl := s.information_lower (by omega)
  have hc := s.concentration_nonneg
  have hd := s.depth_nonneg
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hb : (((n:ℝ)/2+2)*Real.log 2)*s.depth ≤ (3/4:ℝ)*((n:ℝ)*Real.log 2*s.depth) := by
    nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-8 by linarith) (mul_nonneg hlog.le hd)]
  unfold potential at h
  linarith

end AnalysisState

lemma initialState_potential {n : ℕ} (hn : 0 < n) : (initialState hn).potential = 0 := by
  have := cubePrior_isProbabilityMeasure hn
  simp [initialState,AnalysisState.potential,AnalysisState.information,AnalysisState.concentration,
    AnalysisState.depth,FiniteChannel.expectation,finiteInformation,infoContribution,scoreMass,xlog_one,rootCell]

lemma posterior_cube_domination {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (p : FiniteChannel (Coordinate n) ι) (i : ι)
    (hi : 0 < scoreMass (cubePrior n) (p.prob i)) (R : Cell n) :
    (scorePosterior (cubePrior n) (p.prob i)).real (cellSet R) ≤
      (1/scoreMass (cubePrior n) (p.prob i))*(1/2:ℝ)^(n*R.1) := by
  have h := scorePosterior_apply_le (cubePrior n) _ (p.le_one i) hi _ (measurableSet_cellSet R)
  rw [cubePrior_cellSet hn] at h
  have he := ENNReal.toReal_mono (by finiteness) h
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/scoreMass (cubePrior n) (p.prob i)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1/2:ℝ)^(n*R.1))] using he

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_StateInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
namespace FiniteChannel

variable {α ι κ η : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ] [Fintype η]

lemma coarsen_equiv (p : FiniteChannel α ι) (e : ι ≃ κ) (j : κ) (x : α) :
    (p.coarsen e).prob j x = p.prob (e.symm j) x := by
  classical
  change (∑ i,if e i = j then p.prob i x else 0) = _
  have he (i : ι) : e i = j ↔ i = e.symm j := by
    constructor
    · intro h; simpa using congrArg e.symm h
    · intro h; rw [h]; simp
  simp_rw [he]
  simp

lemma coarsen_bind_map (p : FiniteChannel α ι) (f : ι → κ) (q : κ → FiniteChannel α η) :
    ((p.bind (fun i => q (f i))).coarsen (fun i => (f i.1,i.2))).prob =
      ((p.coarsen f).bind q).prob := by
  classical
  funext k x
  rcases k with ⟨k,v⟩
  simp only [coarsen,bind,Fintype.sum_prod_type,Prod.mk.injEq]
  have he (i : ι) : (∑ j : η,if f i = k ∧ j = v then p.prob i x*(q (f i)).prob j x else 0) =
      if f i = k then p.prob i x*(q k).prob v x else 0 := by
    by_cases h : f i = k <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : f i = k <;> simp [h]

end FiniteChannel

lemma historyChannel_succ {n N t : ℕ} (rules : Rules n N (t+1)) :
    (((historyChannel (initRules rules)).bind (fun w => blockChannel (rules (Fin.last t) w))).coarsen
      (appendHistoryEquiv N t)).prob = (historyChannel rules).prob := by
  funext w z
  obtain ⟨⟨h,v⟩,rfl⟩ := (appendHistoryEquiv N t).surjective w
  rw [FiniteChannel.coarsen_equiv]
  simp only [Equiv.symm_apply_apply]
  exact (historyLikelihood_snoc rules z h v).symm

lemma FiniteChannel.ext_prob {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {p q : FiniteChannel α ι} (h : p.prob = q.prob) : p = q := by
  cases p
  cases q
  cases h
  rfl

lemma experimentLaw_eq_law {n N t : ℕ} (hn : 0 < n) (rules : Rules n N t) :
    experimentLaw rules = (historyChannel rules).law (cubePrior n) := by
  have := cubePrior_isProbabilityMeasure hn
  rw [FiniteChannel.law_eq_sum]
  rfl

lemma mutualInformation_map_right {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (α × β)) [IsFiniteMeasure μ] (g : β → γ) (hg : Measurable g) :
    mutualInformation (μ.map (Prod.map id g)) ≤ mutualInformation μ := by
  have hm : Measurable (Prod.map (id : α → α) g) := measurable_id.prodMap hg
  have hf : (μ.map (Prod.map id g)).map Prod.fst = μ.map Prod.fst := by
    rw [Measure.map_map measurable_fst hm]
    rfl
  have hs : (μ.map (Prod.map id g)).map Prod.snd = (μ.map Prod.snd).map g := by
    rw [Measure.map_map measurable_snd hm,Measure.map_map hg measurable_snd]
    rfl
  have he : (μ.map Prod.fst).prod ((μ.map Prod.snd).map g) =
      ((μ.map Prod.fst).prod (μ.map Prod.snd)).map (Prod.map id g) := by
    simpa using Measure.map_prod_map (μ.map Prod.fst) (μ.map Prod.snd) measurable_id hg
  unfold mutualInformation
  rw [hf,hs,he]
  exact InformationTheory.klDiv_map_le _ _ hm

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma analysis_extension_realized {n N : ℕ} (hn : 0 < n) (s : AnalysisState n)
    (q : s.Index → FiniteChannel (Coordinate n) (Fin N)) (L : ℝ)
    (hcost : ∀ i,0 < scoreMass (cubePrior n) (s.channel.prob i) →
      finiteInformation (scorePosterior (cubePrior n) (s.channel.prob i)) (q i).prob ≤ L+Real.log (s.B i)) :
    ∃ s' : AnalysisState n, ∃ f : s'.Index → (s.Index × Fin N),
      (s'.channel.coarsen f).prob = (s.channel.bind q).prob ∧
      s'.potential ≤ s.potential+L+2*Real.log 2+1 ∧ Nonempty (ExtensionWitness s q s' f) := by
  classical
  let μ := cubePrior n
  have := cubePrior_isProbabilityMeasure hn
  let r := s.channel.bind q
  have hparentsupport (i : s.Index × Fin N) (hi : 0 < scoreMass μ (r.prob i)) :
      scorePosterior μ (r.prob i) (cellSet (s.cell i.1)) = 1 := by
    have hP := s.channel.bind_positive_parent q μ i hi
    have := scorePosterior_probability μ _ (r.measurable i) (r.nonneg i) (r.le_one i) hi
    have := scorePosterior_probability μ _ (s.channel.measurable i.1) (s.channel.nonneg i.1) (s.channel.le_one i.1) hP
    have hz := (scorePosterior_null_iff μ _ (s.channel.measurable i.1) (s.channel.nonneg i.1) hP
      _ (measurableSet_cellSet (s.cell i.1)).compl).mp
        ((prob_compl_eq_zero_iff (measurableSet_cellSet (s.cell i.1))).mpr (s.support i.1 hP))
    apply (prob_compl_eq_zero_iff (measurableSet_cellSet (s.cell i.1))).mp
    apply (scorePosterior_null_iff μ _ (r.measurable i) (r.nonneg i) hi _
      (measurableSet_cellSet (s.cell i.1)).compl).mpr
    filter_upwards [hz] with x hx
    intro hnot
    change s.channel.prob i.1 x*(q i.1).prob i.2 x = 0
    rw [hx hnot,zero_mul]
  have hex (i : s.Index × Fin N) : Nonempty (HeavyRefinement n (scorePosterior μ (r.prob i)) (s.cell i.1)) := by
    by_cases h : 0 < scoreMass μ (r.prob i)
    · have := scorePosterior_probability μ _ (r.measurable i) (r.nonneg i) (r.le_one i) h
      exact exists_heavy_refinement hn (scorePosterior μ (r.prob i)) (s.cell i.1) (hparentsupport i h)
        (div_nonneg zero_le_one h.le) (posterior_cube_domination hn r i h)
    · have hz : scoreMass μ (r.prob i) = 0 := le_antisymm (le_of_not_gt h) (scoreMass_nonneg μ _ (r.nonneg i))
      rw [scorePosterior_of_mass_zero μ _ hz]
      exact zero_heavy_refinement n (s.cell i.1)
  let R := fun i => Classical.choice (hex i)
  let a := r.dbind (fun i => (R i).channel)
  have hpost (i : Sigma (fun i => (R i).Index)) (hi : 0 < scoreMass μ (a.prob i)) :
      scorePosterior μ (a.prob i) = scorePosterior (scorePosterior μ (r.prob i.1)) ((R i.1).channel.prob i.2) :=
    (scorePosterior_assoc μ _ _ (r.measurable i.1) ((R i.1).channel.measurable i.2)
      (r.nonneg i.1) ((R i.1).channel.nonneg i.2)
      (r.dbind_positive_parent _ μ i hi) (r.dbind_positive_conditional _ μ i hi)).symm
  let s' : AnalysisState n := {
    Index := Sigma (fun i => (R i).Index)
    channel := a
    cell := fun i => (R i.1).cell i.2
    B := fun i => (R i.1).B i.2
    B_one := fun i => (R i.1).B_one i.2
    support := fun i hi => by
      rw [hpost i hi]
      exact (R i.1).support i.2 (r.dbind_positive_conditional _ μ i hi)
    spread := fun i hi => by
      rw [hpost i hi]
      exact (R i.1).spread i.2 (r.dbind_positive_conditional _ μ i hi) }
  refine ⟨s',Sigma.fst,?_,?_,?_⟩
  · exact r.coarsen_dbind_fst (fun i => (R i).channel)
  ·
    let δ := fun i j => (((R i).cell j).1-(s.cell i.1).1:ℕ)
    let D := r.expectation μ (fun i => (R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => δ i j))
    have hdepth : s'.depth = s.depth+D := by
      have he : (fun i : Sigma (fun i => (R i).Index) => (((R i.1).cell i.2).1:ℝ)) =
          fun i => ((s.cell i.1.1).1:ℝ)+(δ i.1 i.2:ℝ) := by
        funext i
        dsimp only [δ]
        rw [Nat.cast_sub ((R i.1).level_ge i.2)]
        ring
      change a.expectation μ _ = s.depth+D
      rw [he,FiniteChannel.expectation_add]
      change (r.dbind (fun i => (R i).channel)).expectation μ _ +
        (r.dbind (fun i => (R i).channel)).expectation μ _ = _
      rw [r.expectation_dbind_fst (fun i => (R i).channel) μ (fun i => ((s.cell i.1).1:ℝ)),
        r.expectation_dbind (fun i => (R i).channel) μ]
      change r.expectation μ (fun i => ((s.cell i.1).1:ℝ))+D = s.depth+D
      change (s.channel.bind q).expectation μ (fun i => ((s.cell i.1).1:ℝ))+D = s.depth+D
      rw [s.channel.expectation_bind_fst q μ (fun i => ((s.cell i).1:ℝ))]
      rfl
    have href (i : s.Index × Fin N) :
        finiteInformation (scorePosterior μ (r.prob i)) (R i).channel.prob+
          (R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => Real.log ((R i).B j)) ≤
        ((n:ℝ)/2+2)*Real.log 2*((R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => δ i j))+2*Real.log 2+1 := by
      have h1 := (R i).entropy_bound
      have h2 := (R i).concentration_bound
      change _ ≤ _ at h1
      change _ ≤ _ at h2
      dsimp only [FiniteChannel.expectation,δ]
      linarith
    have hrefsum := r.expectation_mono μ href
    rw [r.expectation_add μ] at hrefsum
    have hright : r.expectation μ (fun i =>
        ((n:ℝ)/2+2)*Real.log 2*((R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => δ i j))+2*Real.log 2+1) =
        ((n:ℝ)/2+2)*Real.log 2*D+2*Real.log 2+1 := by
      rw [r.expectation_add μ,r.expectation_add μ,r.expectation_const_mul μ,r.expectation_const μ,r.expectation_const μ]
    rw [hright] at hrefsum
    have hinfo : s'.information = finiteInformation μ r.prob+
        r.expectation μ (fun i => finiteInformation (scorePosterior μ (r.prob i)) (R i).channel.prob) :=
      r.information_dbind (fun i => (R i).channel) μ
    have hconc : s'.concentration = r.expectation μ (fun i =>
        (R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => Real.log ((R i).B j))) := r.expectation_dbind (fun i => (R i).channel) μ (fun i => Real.log ((R i.1).B i.2))
    have hblock : finiteInformation μ r.prob ≤ s.information+s.concentration+L := by
      rw [s.channel.information_bind q μ]
      have hs : (∑ i,scoreMass μ (s.channel.prob i)*finiteInformation (scorePosterior μ (s.channel.prob i)) (q i).prob) ≤
          s.channel.expectation μ (fun i => L+Real.log (s.B i)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : scoreMass μ (s.channel.prob i) = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left (hcost i
            (lt_of_le_of_ne (scoreMass_nonneg μ _ (s.channel.nonneg i)) (Ne.symm h)))
            (scoreMass_nonneg μ _ (s.channel.nonneg i))
      rw [s.channel.expectation_add μ,s.channel.expectation_const μ] at hs
      change _ ≤ L+s.concentration at hs
      change s.information+_ ≤ _
      linarith
    unfold AnalysisState.potential
    rw [hinfo,hconc,hdepth]
    linarith
  · refine ⟨{
      choose := fun i z => ⟨i,(R i).select z⟩
      choose_fiber := ?_
      erase_choose := fun _ _ => rfl
      chosen := ?_
      positive_parent := ?_
      contains := fun i z hz => (R i).select_mem z hz
      subset := fun j => (R j.1).cell_subset j.2 }⟩
    · intro i j
      obtain ⟨k,j⟩ := j
      by_cases h : i = k
      · subst i
        change MeasurableSet {z | (⟨k,(R k).select z⟩ : Sigma (fun i => (R i).Index)) = ⟨k,j⟩}
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using (R k).select_fiber j
      · have he : {z | (⟨i,(R i).select z⟩ : Sigma (fun i => (R i).Index)) = ⟨k,j⟩} = ∅ := by
          ext z
          simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
          intro h'
          exact h (congrArg Sigma.fst h')
        rw [he]
        exact MeasurableSet.empty
    · intro j z hz
      change 0 < r.prob j.1 z*(R j.1).channel.prob j.2 z at hz
      have hpos : 0 < (R j.1).channel.prob j.2 z :=
        pos_of_mul_pos_right hz (r.nonneg j.1 z)
      exact congrArg (Sigma.mk j.1) ((R j.1).chosen j.2 z hpos)
    · intro j z hz
      change 0 < (s.channel.prob j.1.1 z*(q j.1.1).prob j.1.2 z)*(R j.1).channel.prob j.2 z at hz
      have hr : 0 < s.channel.prob j.1.1 z*(q j.1.1).prob j.1.2 z :=
        pos_of_mul_pos_left hz ((R j.1).channel.nonneg j.2 z)
      exact pos_of_mul_pos_left hr ((q j.1.1).nonneg j.1.2 z)
end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma Realization.valid {n N t : ℕ} {s : AnalysisState n} {f : s.Index → History N t}
    (R : Realization s f) : ValidDisclosure R.Q := by
  refine ⟨R.Qmeas,R.Qfinite,?_,?_⟩
  · intro z hz w i
    rw [← R.trace_read]
    exact ⟨R.trace_below (R.read z w) i (R.read_mem z hz w),R.trace_cube _ i⟩
  · intro z hz w i j hij
    rw [← R.trace_read,← R.trace_read]
    exact R.trace_nested _ i j hij

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_TranscriptLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FiniteChannel
variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

lemma coarsen_density_sum {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (p : FiniteChannel α ι) (g : ι → κ) (x : α) (F : κ → ℝ≥0∞) :
    ∑ j, ENNReal.ofReal ((p.coarsen g).prob j x) * F j =
      ∑ i, ENNReal.ofReal (p.prob i x) * F (g i) := by
  classical
  change (∑ j,ENNReal.ofReal (∑ i,if g i = j then p.prob i x else 0)*F j) = _
  have hs (j : κ) : ENNReal.ofReal (∑ i,if g i = j then p.prob i x else 0) =
      ∑ i,ENNReal.ofReal (if g i = j then p.prob i x else 0) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by split <;> first | exact p.nonneg i x | rfl)
  simp_rw [hs,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [apply_ite ENNReal.ofReal,ENNReal.ofReal_zero,ite_mul,zero_mul]
  simp

lemma law_coarsen (p : FiniteChannel α ι) (g : ι → κ) (μ : Measure α) [IsProbabilityMeasure μ] :
    (p.coarsen g).law μ = (p.law μ).map (Prod.map id g) := by
  classical
  have hg : Measurable (Prod.map (id : α → α) g) := measurable_id.prodMap (measurable_of_countable g)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hg,(p.coarsen g).lintegral_law μ _ hF]
  change (∑ i,∫⁻ x,ENNReal.ofReal ((p.coarsen g).prob i x)*F (x,i) ∂μ) =
    ∫⁻ x,F (x.1,g x.2) ∂p.law μ
  rw [p.lintegral_law μ (fun x => F (x.1,g x.2)) (hF.comp hg)]
  rw [← lintegral_finsetSum Finset.univ (f := fun j x => ENNReal.ofReal ((p.coarsen g).prob j x)*F (x,j))
    (fun j _ => ((p.coarsen g).measurable j).ennreal_ofReal.mul (hF.comp (measurable_id.prodMk measurable_const))),
    ← lintegral_finsetSum Finset.univ (f := fun i x => ENNReal.ofReal (p.prob i x)*F (x,g i))
    (fun i _ => (p.measurable i).ennreal_ofReal.mul (hF.comp (measurable_id.prodMk measurable_const)))]
  apply lintegral_congr
  intro x
  exact p.coarsen_density_sum g x (fun j => F (x,j))

lemma positive_ae_law (p : FiniteChannel α ι) (μ : Measure α) :
    ∀ᵐ x ∂p.law μ, 0 < p.prob x.2 x.1 := by
  rw [law,MeasureTheory.ae_withDensity_iff p.measurable_density]
  exact ae_of_all _ (fun x hx => ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx))

lemma integral_law_snd (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ι → ℝ) : (∫ x,F x.2 ∂p.law μ) = p.expectation μ F := by
  rw [← integral_map measurable_snd.aemeasurable (measurable_of_countable F).aestronglyMeasurable,p.law_snd μ,
    outputLaw,integral_withDensity_eq_integral_toReal_smul (measurable_of_countable _)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),integral_count]
  simp only [ENNReal.toReal_ofReal (scoreMass_nonneg μ _ (p.nonneg _)),smul_eq_mul]
  rfl
end FiniteChannel

lemma Realization.transcript_meas {n N t : ℕ} {s : AnalysisState n} {f : s.Index → History N t}
    (R : Realization s f) : Measurable (transcriptMap R.Q) := by
  apply measurable_fst.prodMk
  apply measurable_snd.prodMk
  apply Measurable.of_eval
  intro i
  exact (R.Qmeas i).comp (measurable_fst.prodMk ((measurable_of_countable (fun w => through w i)).comp measurable_snd))

lemma Realization.augmented_eq {n N t : ℕ} (hn : 0 < n) {s : AnalysisState n}
    {f : s.Index → History N t} (R : Realization s f) (rules : Rules n N t)
    (he : s.channel.coarsen f = historyChannel rules) :
    augmentedLaw rules R.Q = (s.channel.law (cubePrior n)).map (Prod.map id (fun j => (f j,R.trace j))) := by
  have := cubePrior_isProbabilityMeasure hn
  rw [augmentedLaw,experimentLaw_eq_law hn,← he,s.channel.law_coarsen,
    Measure.map_map R.transcript_meas (measurable_id.prodMap (measurable_of_countable f))]
  apply Measure.map_congr
  filter_upwards [s.channel.positive_ae_law (cubePrior n)] with x hx
  have hc := R.chosen x.2 x.1 hx
  change (x.1,(f x.2,fun i => R.Q i x.1 (through (f x.2) i))) = (x.1,(f x.2,R.trace x.2))
  congr 2
  funext i
  exact (R.trace_read x.1 (f x.2) i).symm.trans (by rw [hc])

lemma Realization.information_le {n N t : ℕ} (hn : 0 < n) {s : AnalysisState n}
    {f : s.Index → History N t} (R : Realization s f) (rules : Rules n N t)
    (he : s.channel.coarsen f = historyChannel rules) :
    mutualInformation (augmentedLaw rules R.Q) ≤ ENNReal.ofReal s.information := by
  have := cubePrior_isProbabilityMeasure hn
  rw [R.augmented_eq hn rules he]
  exact (mutualInformation_map_right _ _ (measurable_of_countable _)).trans_eq (s.channel.klDiv_law _)

lemma Realization.level_eq {n N t : ℕ} (hn : 0 < n) {s : AnalysisState n}
    {f : s.Index → History N t} (R : Realization s f) (rules : Rules n N t)
    (he : s.channel.coarsen f = historyChannel rules) :
    (∫ x,(finalLevel R.Q x : ℝ) ∂experimentLaw rules) = s.depth := by
  have := cubePrior_isProbabilityMeasure hn
  have hlev : Measurable (fun x : Coordinate n × History N t => (finalLevel R.Q x : ℝ)) := by
    have hm := ((measurable_of_countable (fun j : s.Index => ((s.cell j).1 : ℝ))).comp R.read_meas)
    have heq : (fun x : Coordinate n × History N t => (finalLevel R.Q x : ℝ)) =
        (fun x => ((s.cell (R.read x.1 x.2)).1 : ℝ)) := by
      funext x
      rw [show x = (x.1,x.2) from rfl,R.depth_read]
    rw [heq]
    exact hm
  rw [experimentLaw_eq_law hn,← he,s.channel.law_coarsen,
    integral_map (measurable_id.prodMap (measurable_of_countable f)).aemeasurable hlev.aestronglyMeasurable]
  have hc : (fun x : Coordinate n × s.Index => (finalLevel R.Q (x.1,f x.2) : ℝ)) =ᵐ[s.channel.law (cubePrior n)]
      (fun x => ((s.cell x.2).1 : ℝ)) := by
    filter_upwards [s.channel.positive_ae_law (cubePrior n)] with x hx
    rw [R.depth_read,R.chosen x.2 x.1 hx]
  change (∫ x : Coordinate n × s.Index,(finalLevel R.Q (x.1,f x.2) : ℝ) ∂s.channel.law (cubePrior n)) = s.depth
  rw [integral_congr_ae hc]
  exact s.channel.integral_law_snd (cubePrior n) (fun j => ((s.cell j).1 : ℝ))
end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
lemma history_analysis_realized {n N t : ℕ} (hn : 0 < n) (rules : Rules n N t)
    (L : ℝ) (hcost : UniformBlockCost n N L) :
    ∃ s : AnalysisState n, ∃ f : s.Index → History N t,
      s.channel.coarsen f = historyChannel rules ∧
      s.potential ≤ (t:ℝ)*(L+2*Real.log 2+1) ∧ Nonempty (Realization s f) := by
  classical
  have := cubePrior_isProbabilityMeasure hn
  induction t with
  | zero =>
    refine ⟨initialState hn,(fun _ => Fin.elim0),?_,?_,⟨initialRealization hn⟩⟩
    · apply FiniteChannel.ext_prob
      funext w z
      have hw : (Fin.elim0 : History N 0) = w := Subsingleton.elim _ _
      simp only [initialState,FiniteChannel.coarsen,historyChannel,historyLikelihood,hw,
        Finset.prod_empty,Finset.univ_eq_empty,Finset.sum_const]
      norm_num [Finset.card_univ,Fintype.card_unique]
      change @Fintype.card Unit _ = 1
      exact Fintype.card_unique
    · rw [initialState_potential]; simp
  | succ t ih =>
    obtain ⟨s,f,hf,hs,⟨R⟩⟩ := ih (initRules rules)
    let r := fun w : History N t => blockChannel (rules (Fin.last t) w)
    let q := fun i : s.Index => r (f i)
    have H (i : s.Index) (hi : 0 < scoreMass (cubePrior n) (s.channel.prob i)) :
        finiteInformation (scorePosterior (cubePrior n) (s.channel.prob i)) (q i).prob ≤
          L+Real.log (s.B i) := by
      have hp := scorePosterior_probability (cubePrior n) _ (s.channel.measurable i)
        (s.channel.nonneg i) (s.channel.le_one i) hi
      exact hcost _ hp _ _ (s.support i hi) (s.B_one i) (s.spread i hi) (rules (Fin.last t) (f i))
    obtain ⟨s',g,hg,hs',⟨E⟩⟩ := analysis_extension_realized hn s q L H
    let F : s.Index × Fin N → History N t × Fin N := fun i => (f i.1,i.2)
    let f' := appendHistoryEquiv N t ∘ F ∘ g
    refine ⟨s',f',?_,?_,⟨extendRealization R E⟩⟩
    · apply FiniteChannel.ext_prob
      have hg' := FiniteChannel.ext_prob hg
      have hmap : (s.channel.bind q).coarsen F = (s.channel.coarsen f).bind r :=
        FiniteChannel.ext_prob (s.channel.coarsen_bind_map f r)
      calc
        (s'.channel.coarsen f').prob =
            (((s'.channel.coarsen g).coarsen F).coarsen (appendHistoryEquiv N t)).prob := by
          rw [FiniteChannel.coarsen_comp,FiniteChannel.coarsen_comp]
          rfl
        _ = (((historyChannel (initRules rules)).bind r).coarsen (appendHistoryEquiv N t)).prob := by
          rw [hg',hmap,hf]
        _ = (historyChannel rules).prob := historyChannel_succ rules
    · rw [Nat.cast_succ]
      linarith

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem repeated_localization_oai : MainStatement := by
  refine ⟨1/2,by norm_num,32,?_⟩
  intro C₀ hC₀
  let A := blockInformationConstant+C₀
  let K := 2*Real.log 2+1
  let D := A+K
  let C := 16*D
  have hA : 0 < A := add_pos blockInformationConstant_pos hC₀
  have hK : 0 < K := by dsimp [K]; positivity
  have hD : 0 < D := add_pos hA hK
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n N t hn hN rules halphabet
  have hn0 : 0 < n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let L := A*(n+1)
  have hc : UniformBlockCost n N L := actual_uniform_blockCost hn hN halphabet
  obtain ⟨s,f,hf,hs,⟨R⟩⟩ := history_analysis_realized hn0 rules L hc
  have hi := s.information_of_potential (show 8 ≤ n by omega) hs
  have hLK : L+2*Real.log 2+1 ≤ D*(n+1) := by
    dsimp [L,D,K]
    have hnnonneg : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hK.le hnnonneg]
  have hinfo : s.information ≤ 4*(t:ℝ)*D*(n+1) := by
    have H := mul_le_mul_of_nonneg_left hLK (by positivity : 0 ≤ 4*(t:ℝ))
    nlinarith
  have hDt : 0 ≤ D*(t:ℝ) := mul_nonneg hD.le (Nat.cast_nonneg t)
  have hfinal : s.information ≤ C*(n+1)*t := by
    apply hinfo.trans
    dsimp [C]
    nlinarith [mul_nonneg hDt (show 0 ≤ (n:ℝ)+1 by positivity)]
  refine ⟨R.Q,R.valid,?_,?_⟩
  · exact (R.information_le hn0 rules hf).trans (ENNReal.ofReal_le_ofReal hfinal)
  · rw [R.level_eq hn0 rules hf]
    have hhalf : (1/2:ℝ) ≤ Real.log 2 := by
      have H := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
      norm_num at H ⊢
      exact H
    have hd := s.depth_nonneg
    have hl := s.information_lower hn0
    have hsmall : (n:ℝ)/2*s.depth ≤ s.information := by
      have H := mul_le_mul_of_nonneg_right hhalf (mul_nonneg (Nat.cast_nonneg n) hd)
      nlinarith
    apply le_of_mul_le_mul_left (a := (n:ℝ)/2) (a0 := by positivity)
    calc
      (n:ℝ)/2*s.depth ≤ s.information := hsmall
      _ ≤ 4*(t:ℝ)*D*(n+1) := hinfo
      _ ≤ (n:ℝ)/2*(C*t) := by
        dsimp [C]
        nlinarith [mul_nonneg hDt (sub_nonneg.mpr hnR)]
end RepeatedLocalization

end OAI
end

theorem solution : type_of% @OAI.RepeatedLocalization.repeated_localization_oai := @OAI.RepeatedLocalization.repeated_localization_oai
