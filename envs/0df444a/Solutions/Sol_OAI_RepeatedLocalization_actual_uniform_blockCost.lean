-- Prove2me | solution 1 for OAI.RepeatedLocalization.actual_uniform_blockCost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:26:47.551141+00:00
-- url     : https://prove2.me/submissions/989dddb3-609c-4e37-b053-5d801ccb29b5

import Mathlib
import Definitions.Def_GaussianInformation
import Definitions.Def_OAIQWRLC000
import Theorems.Thm_OAI_RepeatedLocalization_log_sum_inequality

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
-- module Solutions.OAIQW_RepeatedLocalization.Localization_Experiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma measurable_chart (n : ℕ) : Measurable (@chart n) :=
  (continuous_chart n).measurable

end RepeatedLocalization

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

lemma cellCenter_mem {n : ℕ} (hn : 0 < n) (Q : Cell n) : cellCenter Q ∈ cellSet Q := by
  rw [cellSet_eq_pi]
  intro i hi
  have h := cellWidth_pos (J := Q.1) hn
  simp only [mem_Ico, cellCenter]
  constructor <;> linarith

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

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_BallVolume
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

lemma euclidean_unitBall_volume_le (n : ℕ) (hn : 0 < n) :
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
      (Real.exp 1 * Real.sqrt Real.pi / Real.sqrt n) ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(n : ℝ) * ‖x‖ ^ 2)) volume := by
    by_contra hh
    have hz := integral_undef hh
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hnR] at hz
    exact (ne_of_gt (Real.rpow_pos_of_pos (div_pos Real.pi_pos hnR) _)) hz
  have hbase : volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
      Real.exp (-(n : ℝ)) ≤ (Real.pi / n) ^ ((n : ℝ) / 2) := by
    calc
      _ = ∫ x : EuclideanSpace ℝ (Fin n) in ball 0 1, Real.exp (-(n : ℝ)) :=
        (setIntegral_const _).symm
      _ ≤ ∫ x : EuclideanSpace ℝ (Fin n) in ball 0 1,
          Real.exp (-(n : ℝ) * ‖x‖ ^ 2) := by
        apply setIntegral_mono_on
        · exact integrableOn_const measure_ball_lt_top.ne
        · exact hi.integrableOn
        · exact measurableSet_ball
        · intro x hx
          apply Real.exp_le_exp.mpr
          have hx' : ‖x‖ < 1 := by simpa using hx
          have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
          simpa using mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hnR.le)
      _ ≤ ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(n : ℝ) * ‖x‖ ^ 2) :=
        integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall
          (fun _ => (Real.exp_pos _).le)) hi
      _ = _ := by
        rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hnR,
          finrank_euclideanSpace, Fintype.card_fin]
  have hexp : Real.exp (-(n : ℝ)) > 0 := Real.exp_pos _
  have hsqrt : (Real.pi / n) ^ ((n : ℝ) / 2) =
      (Real.sqrt Real.pi / Real.sqrt n) ^ n := by
    have hex : (n : ℝ) / 2 = (1 / 2) * n := by ring
    rw [hex,
      Real.rpow_mul_natCast (div_pos Real.pi_pos hnR).le,
      ← Real.sqrt_eq_rpow, Real.sqrt_div (le_of_lt Real.pi_pos)]
  have he : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    simp
  calc
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
        (Real.pi / n) ^ ((n : ℝ) / 2) / Real.exp (-(n : ℝ)) :=
      (le_div_iff₀ hexp).mpr hbase
    _ = (Real.exp 1 * Real.sqrt Real.pi / Real.sqrt n)^n := by
      rw [hsqrt, Real.exp_neg, div_inv_eq_mul, he, ← mul_pow]
      congr 1
      ring

lemma euclidean_ball_volume_le (n : ℕ) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) ≤ (r * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n)^n := by
  have hv := volume.addHaar_ball_of_pos x hr
  have hreal : volume.real (ball x r) = r^n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    simp only [measureReal_def, hv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      finrank_euclideanSpace, Fintype.card_fin]
  rw [hreal]
  calc
    _ ≤ r^n * (Real.exp 1 * Real.sqrt Real.pi / Real.sqrt n)^n :=
      mul_le_mul_of_nonneg_left (euclidean_unitBall_volume_le n hn) (pow_nonneg hr.le _)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Covers
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
section Cover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma card_separated_le (s : Finset E) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ ((2 * R + δ) / δ) ^ Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hsmall : 0 < δ / 2 := by positivity
  have hlarge : 0 < R + δ / 2 := by positivity
  let A := ⋃ c ∈ s, ball c (δ / 2)
  have hdisj : (s : Set E).PairwiseDisjoint (fun c => ball c (δ / 2)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1
    ring
  have hsub : A ⊆ ball (0 : E) (R + δ / 2) := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    linarith [hs x hx]
  have hb : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2)^Module.finrank ℝ E) *
       μ (ball 0 1) ≤ ENNReal.ofReal ((R + δ / 2)^Module.finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hsmall, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball 0 (R + δ / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hlarge
  have hb' := (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne).mp hb
  have hbR : (s.card : ℝ) * (δ / 2)^Module.finrank ℝ E ≤
      (R + δ / 2)^Module.finrank ℝ E := by
    simpa [ENNReal.toReal_ofReal (pow_nonneg hsmall.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hlarge.le _) hb'
  calc
    (s.card : ℝ) ≤ (R + δ / 2)^Module.finrank ℝ E / (δ / 2)^Module.finrank ℝ E :=
      (le_div_iff₀ (pow_pos hsmall _)).mpr hbR
    _ = ((2 * R + δ) / δ)^Module.finrank ℝ E := by
      rw [← div_pow]
      congr 1
      field_simp

lemma exists_ball_cover_card_le {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset E, (∀ c ∈ s, ‖c‖ ≤ R) ∧
      (∀ x : E, ‖x‖ ≤ R → ∃ c ∈ s, dist x c ≤ δ) ∧
      (s.card : ℝ) ≤ ((2 * R + δ) / δ)^Module.finrank ℝ E := by
  classical
  let ε : ℝ≥0 := ⟨δ, hδ.le⟩
  let A := closedBall (0 : E) R
  have hεpos : 0 < ε := hδ
  have hε : ε ≠ 0 := ne_of_gt hεpos
  obtain ⟨N, _, hNfin, hNcov⟩ := Metric.exists_finite_isCover_of_isCompact
    (s := A) (ε := ε / 2) (by positivity) (isCompact_closedBall _ _)
  have hp : Metric.packingNumber ε A < ⊤ := by
    calc
      _ = Metric.packingNumber (2 * (ε / 2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε / 2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ N.encard := hNcov.externalCoveringNumber_le_encard
      _ < ⊤ := hNfin.encard_lt_top
  let S := Metric.maximalSeparatedSet ε A
  have hSfin : S.Finite := Set.encard_lt_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard < ⊤
    rw [Metric.encard_maximalSeparatedSet hp.ne]
    exact hp)
  have hSsub : ∀ c ∈ hSfin.toFinset, ‖c‖ ≤ R := by
    intro c hc
    have : c ∈ S := by simpa using hc
    simpa [A] using (Metric.maximalSeparatedSet_subset this)
  refine ⟨hSfin.toFinset, hSsub, ?_, card_separated_le _ hR hδ hSsub ?_⟩
  · intro x hx
    have hcov := Metric.isCover_iff_subset_iUnion_closedBall.mp
      (Metric.isCover_maximalSeparatedSet hp.ne)
    have hm : x ∈ A := by simpa [A] using hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcov hm)
    exact ⟨c, by simpa using hc, hxc⟩
  · intro c hc d hd hcd
    have hs := Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := A)
      (by simpa using hc) (by simpa using hd) hcd
    have ht := ENNReal.toReal_mono (edist_ne_top c d) hs.le
    change δ ≤ (edist c d).toReal at ht
    simpa [ε, edist_dist, dist_eq_norm] using ht

end Cover

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_GridSpread
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

lemma measurableSet_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    (h : ℝ) (a : Fin n → ℤ) : MeasurableSet (euclideanGridCell base h a) := by
  unfold euclideanGridCell
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
    (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin n → ℝ))
  exact (measurableSet_le (measurable_const (a := base i + h * a i)) hm).inter
    (measurableSet_lt hm (measurable_const (a := base i + h * (a i + 1))))

lemma volume_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    {h : ℝ} (hh : 0 ≤ h) (a : Fin n → ℤ) :
    volume (euclideanGridCell base h a) = ENNReal.ofReal (h ^ n) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (measurableSet_euclideanGridCell base h a).nullMeasurableSet]
  have he : WithLp.toLp 2 ⁻¹' euclideanGridCell base h a =
      Set.pi Set.univ (fun i => Ico (base i + h * a i) (base i + h * (a i + 1))) := by
    ext x
    simp [euclideanGridCell]
  rw [he, Real.volume_pi_Ico]
  have hf : ∀ i, base i + h * (a i + 1) - (base i + h * a i) = h := by
    intro i
    ring
  simp only [hf, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hh]

lemma euclideanGridCell_disjoint {n : ℕ} (base : Fin n → ℝ) {h : ℝ} (hh : 0 < h)
    {a b : Fin n → ℤ} (hab : a ≠ b) :
    Disjoint (euclideanGridCell base h a) (euclideanGridCell base h b) := by
  rw [Function.ne_iff] at hab
  obtain ⟨i, hi⟩ := hab
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain hl | hl := lt_or_gt_of_ne hi
  · have ht : (a i : ℝ) + 1 ≤ b i := by exact_mod_cast hl
    have hs := mul_le_mul_of_nonneg_left ht hh.le
    linarith [(hx i).2, (hy i).1]
  · have ht : (b i : ℝ) + 1 ≤ a i := by exact_mod_cast hl
    have hs := mul_le_mul_of_nonneg_left ht hh.le
    linarith [(hy i).2, (hx i).1]

lemma dist_le_of_mem_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    {h : ℝ} (hh : 0 ≤ h) (a : Fin n → ℤ)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ euclideanGridCell base h a)
    (hy : y ∈ euclideanGridCell base h a) : dist x y ≤ Real.sqrt n * h := by
  have hsq : ‖x - y‖ ^ 2 ≤ (n : ℝ) * h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin n, h^2 := Finset.sum_le_sum fun i _ => by
        have hx1 := (hx i).1
        have hx2 := (hx i).2
        have hy1 := (hy i).1
        have hy2 := (hy i).2
        change (x i - y i)^2 ≤ h^2
        have hab : |x i - y i| ≤ h := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
        nlinarith [sq_abs (x i - y i)]
      _ = _ := by simp
  rw [dist_eq_norm]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hn
  have hnn := Real.sqrt_nonneg (n : ℝ)
  have hm : 0 ≤ Real.sqrt n * h := mul_nonneg hnn hh
  nlinarith [norm_nonneg (x - y)]

lemma euclidean_closedBall_volume_le (n : ℕ) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    volume.real (closedBall x r) ≤
      (r * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n)^n := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [measureReal_def, volume.addHaar_closedBall_eq_addHaar_ball]
  exact euclidean_ball_volume_le n hn x hr

lemma grid_ball_count {n : ℕ} (hn : 0 < n) (base : Fin n → ℝ)
    {h R L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (_ : 0 ≤ L)
    (hscale : R ≤ L * (Real.sqrt n * h)) (c : EuclideanSpace ℝ (Fin n))
    (s : Finset (Fin n → ℤ))
    (hs : ∀ a ∈ s, (euclideanGridCell base h a ∩ closedBall c R).Nonempty) :
    (s.card : ℝ) ≤ ((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n := by
  classical
  let A := ⋃ a ∈ s, euclideanGridCell base h a
  have hsub : A ⊆ closedBall c (R + Real.sqrt n * h) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hya, hy⟩ := hs a ha
    have hdist := dist_le_of_mem_euclideanGridCell base hh.le a hxa hya
    exact (dist_triangle x y c).trans (add_le_add hdist hy) |>.trans_eq (add_comm _ _)
  have hmeasure : volume A = (s.card : ℝ≥0∞) * ENNReal.ofReal (h^n) := by
    rw [measure_biUnion_finset
      (fun a _ b _ hab => euclideanGridCell_disjoint base hh hab)
      (fun a _ => measurableSet_euclideanGridCell base h a)]
    simp [volume_euclideanGridCell base hh.le]
  have hra : 0 < R + Real.sqrt n * h := by positivity
  have hfin : volume (closedBall c (R + Real.sqrt n * h)) ≠ ∞ := measure_closedBall_lt_top.ne
  have hreal : (s.card : ℝ) * h^n ≤ volume.real (closedBall c (R + Real.sqrt n * h)) := by
    have hm := ENNReal.toReal_mono hfin (measure_mono hsub)
    rw [hmeasure] at hm
    simpa [measureReal_def, ENNReal.toReal_ofReal (pow_nonneg hh.le n)] using hm
  have hC : 0 ≤ Real.exp 1 * Real.sqrt Real.pi := by positivity
  have hn' : 0 < Real.sqrt (n : ℝ) := by positivity
  have hscaled : (R + Real.sqrt n * h) * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n ≤
      h * ((L + 1) * (Real.exp 1 * Real.sqrt Real.pi)) := by
    apply (div_le_iff₀ hn').mpr
    calc
      _ ≤ (L * (Real.sqrt n * h) + Real.sqrt n * h) * (Real.exp 1 * Real.sqrt Real.pi) :=
        mul_le_mul_of_nonneg_right (add_le_add hscale le_rfl) hC
      _ = _ := by ring
  have hcard := hreal.trans (euclidean_closedBall_volume_le n hn c hra)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤
    (R + Real.sqrt n * h) * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n) hscaled n
  have hfinal := hcard.trans hpow
  rw [mul_pow, mul_comm (h^n)] at hfinal
  exact (mul_le_mul_iff_left₀ (pow_pos hh n)).mp hfinal

lemma exists_mem_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ a : Fin n → ℤ, x ∈ euclideanGridCell base h a := by
  refine ⟨fun i => ⌊(x i - base i) / h⌋, fun i => ?_⟩
  have hl := (le_div_iff₀ hh).mp (Int.floor_le ((x i - base i) / h))
  have hu := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((x i - base i) / h))
  constructor <;> nlinarith

lemma finite_grid_hitting_ball {n : ℕ} (hn : 0 < n) (base : Fin n → ℝ)
    {h R L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hscale : R ≤ L * (Real.sqrt n * h)) (c : EuclideanSpace ℝ (Fin n)) :
    {a : Fin n → ℤ | (euclideanGridCell base h a ∩ closedBall c R).Nonempty}.Finite := by
  by_contra hinf
  let C := ((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
  have hb := grid_ball_count hn base hh hR hL hscale c s (fun a ha => hs ha)
  have hceil := Nat.le_ceil C
  rw [hcard, Nat.cast_add, Nat.cast_one] at hb
  dsimp [C] at hceil
  linarith

lemma measure_ball_le_of_grid {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} (hn : 0 < n) (ξ : α → EuclideanSpace ℝ (Fin n))
    (base : Fin n → ℝ) {h R L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hscale : R ≤ L * (Real.sqrt n * h)) (c : EuclideanSpace ℝ (Fin n))
    (b : ℝ≥0∞) (hgrid : ∀ a, μ (ξ ⁻¹' euclideanGridCell base h a) ≤ b) :
    μ (ξ ⁻¹' closedBall c R) ≤
      ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
  classical
  let hs := finite_grid_hitting_ball hn base hh hR hL hscale c
  let s := hs.toFinset
  have hsub : ξ ⁻¹' closedBall c R ⊆ ⋃ a ∈ s, ξ ⁻¹' euclideanGridCell base h a := by
    intro z hz
    obtain ⟨a, ha⟩ := exists_mem_euclideanGridCell base hh (ξ z)
    exact mem_iUnion₂.mpr ⟨a, hs.mem_toFinset.mpr ⟨ξ z, ha, hz⟩, ha⟩
  have hcard := grid_ball_count hn base hh hR hL hscale c s
    (fun a ha => hs.mem_toFinset.mp ha)
  calc
    μ (ξ ⁻¹' closedBall c R) ≤ μ (⋃ a ∈ s, ξ ⁻¹' euclideanGridCell base h a) := measure_mono hsub
    _ ≤ ∑ a ∈ s, μ (ξ ⁻¹' euclideanGridCell base h a) := measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ s, b := Finset.sum_le_sum fun a _ => hgrid a
    _ = (s.card : ℝ≥0∞) * b := by simp
    _ ≤ ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
      gcongr
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Tubes
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
section PlaneCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_affine_tube_cover (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset E,
      (∀ x : E, ‖x‖ ≤ R → infDist x (V : Set E) ≤ δ → ∃ c ∈ s, dist x c ≤ 2 * δ) ∧
      (s.card : ℝ) ≤ ((4 * R + 5 * δ) / δ)^Module.finrank ℝ V.direction := by
  classical
  by_cases hempty : {x : E | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ δ}.Nonempty
  · obtain ⟨x₀, hx₀n, hx₀d⟩ := hempty
    obtain ⟨v₀, hv₀V, hv₀d⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x₀
    have hn₀ : ‖v₀‖ ≤ R + δ := by
      have ht := dist_triangle v₀ x₀ 0
      rw [dist_zero_right, dist_zero_right, dist_comm v₀ x₀, ← hv₀d] at ht
      linarith
    obtain ⟨s, _, hcover, hcard⟩ := exists_ball_cover_card_le (E := V.direction)
      (R := 2 * (R + δ)) (δ := δ) (by positivity) hδ
    let f : V.direction ↪ E := ⟨fun v => (v : E) + v₀, by
      intro v w h
      exact Subtype.ext (add_right_cancel h)⟩
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hxn hxd
      obtain ⟨v, hvV, hvd⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x
      have hnv : ‖v‖ ≤ R + δ := by
        have ht := dist_triangle v x 0
        rw [dist_zero_right, dist_zero_right, dist_comm v x, ← hvd] at ht
        linarith
      let u : V.direction := ⟨v - v₀, V.vsub_mem_direction hvV hv₀V⟩
      have hnu : ‖u‖ ≤ 2 * (R + δ) := by
        change ‖v - v₀‖ ≤ _
        exact (norm_sub_le v v₀).trans (by linarith)
      obtain ⟨a, ha, hu⟩ := hcover u hnu
      refine ⟨f a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      have he : dist v (f a) = dist u a := by
        rw [dist_eq_norm, dist_eq_norm]
        change ‖v - ((a : E) + v₀)‖ = ‖(v - v₀) - (a : E)‖
        congr 1
        abel
      calc
        dist x (f a) ≤ dist x v + dist v (f a) := dist_triangle _ _ _
        _ ≤ δ + δ := add_le_add (hvd ▸ hxd) (he ▸ hu)
        _ = 2 * δ := by ring
    · simpa only [Finset.card_map, show 2 * (2 * (R + δ)) + δ = 4 * R + 5 * δ by ring] using hcard
  · refine ⟨∅, ?_, ?_⟩
    · intro x hxn hxd
      exact (hempty ⟨x, hxn, hxd⟩).elim
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity

lemma measure_affine_tube_le_of_grid {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} (hn : 0 < n) (a : α → E)
    (p : E → EuclideanSpace ℝ (Fin n)) (hp : LipschitzWith 1 p)
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (base : Fin n → ℝ) {h R δ L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : 0 ≤ L) (hscale : 2 * δ ≤ L * (Real.sqrt n * h))
    (b : ℝ≥0∞) (hgrid : ∀ v, μ ((p ∘ a) ⁻¹' euclideanGridCell base h v) ≤ b) :
    μ {z | ‖a z‖ ≤ R ∧ infDist (a z) (V : Set E) ≤ δ} ≤
      ENNReal.ofReal (((4 * R + 5 * δ) / δ)^Module.finrank ℝ V.direction) *
        ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_affine_tube_cover V hV hR hδ
  have hsub : {z | ‖a z‖ ≤ R ∧ infDist (a z) (V : Set E) ≤ δ} ⊆
      ⋃ c ∈ s, (p ∘ a) ⁻¹' closedBall (p c) (2 * δ) := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hs (a z) hz.1 hz.2
    refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    exact (show dist (p (a z)) (p c) ≤ dist (a z) c from by
      simpa using hp.dist_le_mul (a z) c).trans hzc
  have hball := fun c => measure_ball_le_of_grid μ hn (p ∘ a) base hh (by positivity)
    hL hscale (p c) b hgrid
  calc
    _ ≤ μ (⋃ c ∈ s, (p ∘ a) ⁻¹' closedBall (p c) (2 * δ)) := measure_mono hsub
    _ ≤ ∑ c ∈ s, μ ((p ∘ a) ⁻¹' closedBall (p c) (2 * δ)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ s, ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b :=
      Finset.sum_le_sum fun c _ => hball c
    _ = (s.card : ℝ≥0∞) *
        ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
      simp [mul_assoc]
    _ ≤ _ := by
      gcongr
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard

end PlaneCover

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

lemma norm_eCoordinate_le_half {n : ℕ} (hn : 0 < n) {z : Coordinate n}
    (hz : z ∈ initialCube n) : ‖eCoordinate z‖ ≤ 1/2 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq : ‖eCoordinate z‖^2 ≤ (1/2 : ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin n, (1 / (2 * Real.sqrt n))^2 := Finset.sum_le_sum fun i _ => by
        have hl := hz i (mem_univ i)
        simp only [mem_Ico, neg_div] at hl
        change (z i)^2 ≤ _
        have ha : |z i| ≤ 1 / (2 * Real.sqrt n) := abs_le.mpr ⟨hl.1, hl.2.le⟩
        nlinarith [sq_abs (z i), abs_nonneg (z i)]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n from Nat.cast_nonneg _)
        field_simp
        nlinarith
  nlinarith [norm_nonneg (eCoordinate z)]

lemma chart_height_lipschitz {E : Type*} [SeminormedAddCommGroup E]
    {x y : E} (hx : ‖x‖ ≤ 1/2) (hy : ‖y‖ ≤ 1/2) :
    |Real.sqrt (1 - ‖x‖^2) - Real.sqrt (1 - ‖y‖^2)| ≤ ‖x-y‖ := by
  have ax := norm_nonneg x
  have ay := norm_nonneg y
  have hx0 : 0 ≤ 1 - ‖x‖^2 := by nlinarith
  have hy0 : 0 ≤ 1 - ‖y‖^2 := by nlinarith
  have hx2 := Real.sq_sqrt hx0
  have hy2 := Real.sq_sqrt hy0
  have hx1 : 1/2 ≤ Real.sqrt (1 - ‖x‖^2) := by nlinarith [Real.sqrt_nonneg (1-‖x‖^2)]
  have hy1 : 1/2 ≤ Real.sqrt (1 - ‖y‖^2) := by nlinarith [Real.sqrt_nonneg (1-‖y‖^2)]
  have he : |Real.sqrt (1 - ‖x‖^2) - Real.sqrt (1 - ‖y‖^2)| *
      (Real.sqrt (1 - ‖x‖^2) + Real.sqrt (1 - ‖y‖^2)) =
      |‖y‖ - ‖x‖| * (‖y‖ + ‖x‖) := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (1 - ‖x‖^2) + Real.sqrt (1 - ‖y‖^2)),
      ← abs_mul, ← abs_of_nonneg (add_nonneg ay ax), ← abs_mul]
    congr 1
    nlinarith
  have hn := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  have hsum : ‖y‖ + ‖x‖ ≤ 1 := by linarith
  have hp := mul_le_mul hn hsum (add_nonneg ay ax) (norm_nonneg (x-y))
  have hab := abs_nonneg (Real.sqrt (1 - ‖x‖^2) - Real.sqrt (1 - ‖y‖^2))
  nlinarith

lemma eChart_dist_le {n : ℕ} (hn : 0 < n) {z w : Coordinate n}
    (hz : z ∈ initialCube n) (hw : w ∈ initialCube n) :
    dist (eChart z) (eChart w) ≤ 2 * dist (eCoordinate z) (eCoordinate w) := by
  have hheight := chart_height_lipschitz (norm_eCoordinate_le_half hn hz) (norm_eCoordinate_le_half hn hw)
  have hs : ‖eChart z - eChart w‖^2 = ‖eCoordinate z - eCoordinate w‖^2 +
      (Real.sqrt (1-‖eCoordinate z‖^2) - Real.sqrt (1-‖eCoordinate w‖^2))^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, eChart, eCoordinate,
      PiLp.sub_apply, chart, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [dist_eq_norm, dist_eq_norm]
  have ha := abs_nonneg (Real.sqrt (1-‖eCoordinate z‖^2) - Real.sqrt (1-‖eCoordinate w‖^2))
  have hb := norm_nonneg (eCoordinate z - eCoordinate w)
  have hc := norm_nonneg (eChart z - eChart w)
  nlinarith [sq_abs (Real.sqrt (1-‖eCoordinate z‖^2) - Real.sqrt (1-‖eCoordinate w‖^2))]

lemma firstCoordinates_lipschitz (n : ℕ) : LipschitzWith 1 (firstCoordinates (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hs : ‖firstCoordinates x - firstCoordinates y‖^2 ≤ ‖x-y‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n, (x i.castSucc - y i.castSucc)^2) ≤
      (∑ i : Fin n, (x i.castSucc - y i.castSucc)^2) + (x (Fin.last n)-y (Fin.last n))^2
    nlinarith [sq_nonneg (x (Fin.last n)-y (Fin.last n))]
  nlinarith [norm_nonneg (firstCoordinates x-firstCoordinates y), norm_nonneg (x-y)]

lemma normalizedChart_norm_le {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : ‖normalizedChart Q z‖ ≤ 2 := by
  have hchart := eChart_dist_le hn (cellSet_subset_initialCube hn Q hz)
    (cellSet_subset_initialCube hn Q (cellCenter_mem hn Q))
  have hgrid : ∀ w ∈ cellSet Q, eCoordinate w ∈ euclideanGridCell (cellLower Q) (cellWidth n Q.1) 0 := by
    intro w hw i
    rw [cellSet_eq_pi] at hw
    have hi := hw i (mem_univ i)
    simpa [euclideanGridCell, eCoordinate] using hi
  have hdiam := dist_le_of_mem_euclideanGridCell (cellLower Q) (cellWidth_pos hn).le 0
    (hgrid z hz) (hgrid _ (cellCenter_mem hn Q))
  have hp : 0 < (2 : ℝ)^Q.1 := by positivity
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have he : (2 : ℝ)^Q.1 * (Real.sqrt n * cellWidth n Q.1) = 1 := by
    unfold cellWidth
    field_simp
  unfold normalizedChart
  rw [norm_smul, Real.norm_of_nonneg hp.le, ← dist_eq_norm]
  calc
    _ ≤ (2 : ℝ)^Q.1 * (2 * (Real.sqrt n * cellWidth n Q.1)) :=
      mul_le_mul_of_nonneg_left (hchart.trans (mul_le_mul_of_nonneg_left hdiam (by norm_num))) hp.le
    _ = 2 := by nlinarith [he]

lemma normalizedChart_measurable {n : ℕ} (Q : Cell n) : Measurable (normalizedChart Q) := by
  unfold normalizedChart eChart
  have hc : Measurable (chart (n := n)) := measurable_chart n
  fun_prop

lemma normalizedGrid_mem_iff {n : ℕ} (Q : Cell n) (l : ℕ) (v : Fin n → ℤ) (z : Coordinate n) :
    firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v ↔
    ∀ i, cellLower Q i + cellWidth n (Q.1+l) * (v i : ℝ) ≤ z i ∧
      z i < cellLower Q i + cellWidth n (Q.1+l) * ((v i : ℝ)+1) := by
  have hp : 0 < (2 : ℝ)^Q.1 := by positivity
  have he (i : Fin n) : firstCoordinates (normalizedChart Q z) i =
      (2 : ℝ)^Q.1 * (z i - cellCenter Q i) := by
    simp [firstCoordinates, normalizedChart, eChart, chart]
  simp only [euclideanGridCell, mem_ofPred_eq, he, normalizedGridBase]
  apply forall_congr'
  intro i
  constructor
  · intro h
    constructor
    · have hh : (2 : ℝ)^Q.1 * (cellLower Q i + cellWidth n (Q.1+l)*(v i : ℝ) - cellCenter Q i) ≤
          (2 : ℝ)^Q.1 * (z i - cellCenter Q i) := by nlinarith [h.1]
      have hh' := (mul_le_mul_iff_right₀ hp).mp hh
      linarith
    · have hh : (2 : ℝ)^Q.1 * (z i - cellCenter Q i) <
          (2 : ℝ)^Q.1 * (cellLower Q i + cellWidth n (Q.1+l)*((v i : ℝ)+1) - cellCenter Q i) := by
        nlinarith [h.2]
      have hh' := (mul_lt_mul_iff_right₀ hp).mp hh
      linarith
  · intro h
    constructor
    · have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right h.1 (cellCenter Q i)) hp.le
      nlinarith
    · have hh := mul_lt_mul_of_pos_left (sub_lt_sub_right h.2 (cellCenter Q i)) hp
      nlinarith

lemma normalizedGrid_valid_of_inter {n : ℕ} (hn : 0 < n) (Q : Cell n) (l : ℕ)
    (v : Fin n → ℤ) {z : Coordinate n} (hz : z ∈ cellSet Q)
    (hg : firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v) : ∀ i, 0 ≤ v i ∧ v i < (2^l : ℕ) := by
  rw [normalizedGrid_mem_iff] at hg
  rw [cellSet_eq_pi] at hz
  intro i
  have hh := hz i (mem_univ i)
  dsimp only at hh
  have hw := cellWidth_pos (J := Q.1+l) hn
  have he : cellWidth n (Q.1+l) * (2 : ℝ)^l = cellWidth n Q.1 := by
    rw [cellWidth_add, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]
  have hlr : (-1 : ℝ) < (v i : ℝ) := by
    by_contra h
    have hb := mul_le_mul_of_nonneg_left (le_of_not_gt h) hw.le
    nlinarith [hh.1, (hg i).2]
  have hur : (v i : ℝ) < (2 : ℝ)^l := by
    by_contra h
    have hb := mul_le_mul_of_nonneg_left (le_of_not_gt h) hw.le
    nlinarith [hh.2, (hg i).1]
  constructor
  · have : (-1 : ℤ) < v i := by exact_mod_cast hlr
    omega
  · exact_mod_cast hur

lemma normalizedGrid_child_mem {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l))
    {z : Coordinate n}
    (hg : firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) (fun i => (a i).val)) :
    z ∈ cellSet (childCell Q l a) := by
  rw [normalizedGrid_mem_iff] at hg
  rw [cellSet_eq_pi]
  intro i hi
  dsimp only
  rw [childCell_lower]
  have h := hg i
  simp only [Int.cast_natCast] at h
  change cellLower Q i + cellWidth n (Q.1+l)*(a i : ℝ) ≤ z i ∧
    z i < cellLower Q i + cellWidth n (Q.1+l)*(a i : ℝ) + cellWidth n (Q.1+l)
  constructor <;> nlinarith [h.1, h.2]

lemma measure_normalizedGrid_le {n : ℕ} (hn : 0 < n) (Q : Cell n) (l : ℕ)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    (b : ℝ≥0∞) (hchild : ∀ a, μ (cellSet (childCell Q l a)) ≤ b) (v : Fin n → ℤ) :
    μ ((firstCoordinates ∘ normalizedChart Q) ⁻¹' euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v) ≤ b := by
  classical
  have hae : ∀ᵐ z ∂μ, z ∈ cellSet Q := by
    apply ae_iff.mpr
    exact hsupport
  by_cases hv : ∀ i, 0 ≤ v i ∧ v i < (2^l : ℕ)
  · let a : Fin n → Fin (2^l) := fun i => ⟨(v i).toNat, by
      exact (Int.toNat_lt (hv i).1).mpr (hv i).2⟩
    have he : (fun i => ((a i).val : ℤ)) = v := by
      funext i
      exact Int.toNat_of_nonneg (hv i).1
    refine (measure_mono_ae (hae.mono (fun z _ hg => ?_))).trans (hchild a)
    apply normalizedGrid_child_mem Q l a
    change firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v at hg
    simpa only [he] using hg
  · have hempty : μ ((firstCoordinates ∘ normalizedChart Q) ⁻¹' euclideanGridCell (normalizedGridBase Q)
        ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v) = 0 := by
      apply measure_mono_null (t := (cellSet Q)ᶜ) _ hsupport
      intro z hg hz
      exact hv (normalizedGrid_valid_of_inter hn Q l v hz hg)
    rw [hempty]
    exact bot_le

lemma DyadicSpread.child_floor {n : ℕ} (hn : 0 < n) {μ : Measure (Coordinate n)}
    {Q : Cell n} {B : ℝ} (hB : 0 ≤ B) (h : DyadicSpread μ Q B) (l : ℕ)
    (a : Fin n → Fin (2^l)) :
    μ (cellSet (childCell Q l a)) ≤ ENNReal.ofReal (B * (1/2 : ℝ)^((n/2)*l)) := by
  refine (h l (childCell Q l a) rfl (childCell_subset hn Q l a)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hB
  have hdiv : ((n/2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
  have he : -(n : ℝ) * l / 2 ≤ -(((n/2)*l : ℕ) : ℝ) := by
    simp only [Nat.cast_mul]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ l from Nat.cast_nonneg _) (sub_nonneg.mpr hdiv)]
  have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  simpa only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div, inv_pow] using hr

lemma gridConstant_nonneg : 0 ≤ gridConstant := by unfold gridConstant; positivity
lemma tubeConstant_ge_one : 1 ≤ tubeConstant := by
  unfold tubeConstant
  nlinarith [le_max_left (1 : ℝ) gridConstant]

lemma dyadic_tube_tail {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1)))) (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (e : ℕ) (he : Module.finrank ℝ V.direction + e ≤ n/2) (j : ℕ) :
    μ {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ (1/2 : ℝ)^j} ≤
      ENNReal.ofReal (B * tubeConstant^n * (1/2 : ℝ)^(e*j)) := by
  let δ : ℝ := (1/2 : ℝ)^j
  let q := Module.finrank ℝ V.direction
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hw : 0 < (2 : ℝ)^Q.1 * cellWidth n (Q.1+j) := mul_pos (by positivity) (cellWidth_pos hn)
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have hscale : Real.sqrt n * ((2 : ℝ)^Q.1 * cellWidth n (Q.1+j)) = δ := by
    dsimp [cellWidth, δ]
    rw [pow_add]
    simp only [one_div, inv_pow]
    field_simp
  have ht := measure_affine_tube_le_of_grid μ hn (normalizedChart Q) firstCoordinates
    (firstCoordinates_lipschitz n) V hV (normalizedGridBase Q) hw (by norm_num : (0:ℝ) ≤ 2)
    hd (by norm_num : (0:ℝ) ≤ 2) (by rw [hscale])
    (ENNReal.ofReal (B * δ^(n/2)))
    (fun v => measure_normalizedGrid_le hn Q j μ hsupport _
      (fun a => by simpa only [δ, ← pow_mul, Nat.mul_comm j (n/2)] using hspread.child_floor hn hB j a) v)
  have hae : ∀ᵐ z ∂μ, z ∈ cellSet Q := by exact ae_iff.mpr hsupport
  have hmono : μ {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ δ} ≤
      μ {z | ‖normalizedChart Q z‖ ≤ 2 ∧ infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ δ} := by
    apply measure_mono_ae
    exact hae.mono fun z hz hzd => ⟨normalizedChart_norm_le hn Q hz, hzd⟩
  refine (hmono.trans ht).trans ?_
  have hcn : 0 ≤ tubeConstant := le_trans (by norm_num) tubeConstant_ge_one
  have hg : 0 ≤ gridConstant := gridConstant_nonneg
  have hq : q ≤ n/2 := by dsimp [q]; omega
  have hqn : q ≤ n := hq.trans (Nat.div_le_self _ _)
  have hplane : ((4 * (2 : ℝ) + 5 * δ) / δ)^q ≤ ((13 : ℝ)/δ)^q := by
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff_of_pos_right hd).mpr
    linarith
  have hc : (13 : ℝ)^q * gridConstant^n ≤ tubeConstant^n := by
    calc
      _ ≤ (13 : ℝ)^n * (max 1 gridConstant)^n := by
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 13) hqn)
          (pow_le_pow_left₀ hg (le_max_right 1 gridConstant) n) (pow_nonneg hg _)
          (by positivity)
      _ = _ := by rw [← mul_pow]; rfl
  have hpow : δ^(n/2-q) ≤ δ^e := pow_le_pow_of_le_one hd.le hd1 (by omega)
  have hcancel : ((13 : ℝ)/δ)^q * δ^(n/2) = (13 : ℝ)^q * δ^(n/2-q) := by
    rw [pow_sub₀ δ hd.ne' hq, div_pow]
    ring
  have hreal : ((4 * (2 : ℝ) + 5 * δ)/δ)^q * gridConstant^n * (B * δ^(n/2)) ≤
      B * tubeConstant^n * δ^e := by
    calc
      _ ≤ ((13 : ℝ)/δ)^q * gridConstant^n * (B * δ^(n/2)) := by gcongr
      _ = B * gridConstant^n * (((13 : ℝ)/δ)^q * δ^(n/2)) := by ring
      _ = B * ((13 : ℝ)^q * gridConstant^n) * δ^(n/2-q) := by rw [hcancel]; ring
      _ ≤ B * tubeConstant^n * δ^e := by gcongr
  have hp : 0 ≤ ((4 * (2 : ℝ) + 5 * δ)/δ)^q := by positivity
  have hpg : 0 ≤ gridConstant^n := pow_nonneg hg _
  simp only [show (2:ℝ)+1=3 by norm_num]
  change ENNReal.ofReal (((4 * (2 : ℝ) + 5 * δ)/δ)^q) * ENNReal.ofReal (gridConstant^n) *
    ENNReal.ofReal (B * δ^(n/2)) ≤ _
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (mul_nonneg hp hpg)]
  convert ENNReal.ofReal_le_ofReal hreal using 1
  dsimp [δ]
  rw [← pow_mul, Nat.mul_comm j e]

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_SmallBalls
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

namespace RepeatedLocalization

private lemma inv_pow_dyadic_majorant (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (x⁻¹ ^ k) ≤ 1 + ∑' j : ℕ,
      ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := by
  by_cases hx0 : x = 0
  · simp [hx0, hk.ne']
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases hx1 : 1 ≤ x
  · have hle : ENNReal.ofReal (x⁻¹ ^ k) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_one₀ (inv_nonneg.mpr hx) ((inv_le_one₀ hxpos).mpr hx1)
    exact hle.trans (le_add_right le_rfl)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near_of_lt_one hxpos
    (le_of_not_ge hx1) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hbound : x⁻¹ ^ k ≤ (2 : ℝ) ^ ((j + 1) * k) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (inv_nonneg.mpr hx)
    have hinv := (inv_le_inv₀ hxpos (pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) (j+1))).mpr hj.le
    simpa only [one_div, inv_pow, inv_inv] using hinv
  calc
    ENNReal.ofReal (x⁻¹ ^ k) ≤ ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k)) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := by
      simp only [Set.indicator, Set.mem_ofPred_eq, hj', ite_true]
    _ ≤ ∑' j : ℕ, ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x :=
      ENNReal.le_tsum (f := fun index : ℕ =>
        ({point : ℝ | point ≤ (1 / 2 : ℝ) ^ index}).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((index + 1) * k))) x) j
    _ ≤ 1 + ∑' j : ℕ, ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := le_add_left le_rfl

private lemma dyadic_weight_product (j k : ℕ) :
    (2 : ℝ) ^ ((j + 1) * k) * (1 / 2 : ℝ) ^ ((k + 1) * j) =
      (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ j := by
  simp only [Nat.add_mul, one_mul, pow_add, one_div, inv_pow]
  have hpow : (2 : ℝ) ^ (k * j) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Nat.mul_comm j k]
  field_simp

theorem inverseMoment_of_dyadic_tails {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : α → ℝ) (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x)
    (k : ℕ) (hk : 0 < k) (A : ℝ≥0∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1 / 2 : ℝ) ^ j} ≤
      A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) :
    (∫⁻ x, ENNReal.ofReal ((D x)⁻¹ ^ k) ∂μ) ≤
      μ univ + A * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
  let S : ℕ → Set α := fun j => {x | D x ≤ (1 / 2 : ℝ) ^ j}
  let w : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hD measurable_const
  have hmeas : ∀ j, Measurable ((S j).indicator (fun _ => w j)) :=
    fun j => measurable_const.indicator (hS j)
  calc
    (∫⁻ x, ENNReal.ofReal ((D x)⁻¹ ^ k) ∂μ) ≤
        ∫⁻ x, (1 + ∑' j, (S j).indicator (fun _ => w j) x) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [S, w, Set.indicator, Set.mem_ofPred_eq] using
        inv_pow_dyadic_majorant (D x) (hD0 x) k hk
    _ = μ univ + ∑' j, w j * μ (S j) := by
      rw [lintegral_add_left measurable_const,
        lintegral_tsum (fun j => (hmeas j).aemeasurable)]
      simp only [lintegral_const, one_mul, lintegral_indicator (hS _), Measure.restrict_apply_univ]
    _ ≤ μ univ + ∑' j, w j * (A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) := by
      gcongr with j
      exact htail j
    _ = μ univ + ∑' j, (A * ENNReal.ofReal ((2 : ℝ) ^ k)) * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
      congr 1
      apply tsum_congr
      intro j
      dsimp [w]
      rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), dyadic_weight_product,
        ENNReal.ofReal_mul (by positivity)]
      ac_rfl
    _ = μ univ + A * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
      simp only [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)), ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div, ENNReal.one_sub_inv_two,
        inv_inv, pow_succ, ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k),
        ENNReal.ofReal_ofNat, mul_assoc]

theorem zeroSet_null_of_dyadic_tails {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : α → ℝ) (k : ℕ) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1 / 2 : ℝ) ^ j} ≤
      A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) :
    μ {x | D x = 0} = 0 := by
  have hr : ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have ht := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr hA)
  apply le_antisymm _ bot_le
  change μ {x | D x = 0} ≤ (0 : ℝ≥0∞)
  apply ge_of_tendsto' (show Tendsto
    (fun j : ℕ => A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) ^ j) atTop (𝓝 (0 : ℝ≥0∞)) from
    by simpa only [mul_zero] using ht)
  intro j
  calc
    μ {x | D x = 0} ≤ μ {x | D x ≤ (1 / 2 : ℝ) ^ j} := by
      apply measure_mono
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx]
      positivity
    _ ≤ A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j)) := htail j
    _ = A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) ^ j := by
      rw [pow_mul, ENNReal.ofReal_pow (by positivity)]

theorem weightedMeasure_apply_le_sqrt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h : α → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (s : Set α) (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal |h x|)) s ≤ μ s ^ (1 / 2 : ℝ) := by
  rw [withDensity_apply _ hs]
  have heq : (∫⁻ x in s, ENNReal.ofReal |h x| ∂μ) = eLpNorm h 1 (μ.restrict s) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [Real.enorm_eq_ofReal_abs]
  rw [heq]
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hh.aestronglyMeasurable (μ := μ.restrict s))
  have hn' : eLpNorm h 2 (μ.restrict s) ≤ 1 :=
    (eLpNorm_restrict_le h 2 μ s).trans hnorm
  calc
    eLpNorm h 1 (μ.restrict s) ≤ eLpNorm h 2 (μ.restrict s) * μ s ^ (1 / 2 : ℝ) := by
      convert hholder using 1
      norm_num
    _ ≤ 1 * μ s ^ (1 / 2 : ℝ) := by gcongr
    _ = μ s ^ (1 / 2 : ℝ) := one_mul _

theorem weightedMeasure_mass_le_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (h : α → ℝ) (hh : Measurable h)
    (hnorm : eLpNorm h 2 μ ≤ 1) :
    (μ.withDensity (fun x => ENNReal.ofReal |h x|)) univ ≤ 1 := by
  simpa using weightedMeasure_apply_le_sqrt μ h hh hnorm univ MeasurableSet.univ

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ConditionalMoments
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
namespace RepeatedLocalization
open Metric

lemma tubeWeightConstant_ne_top (n : ℕ) (B : ℝ) : tubeWeightConstant n B ≠ ∞ := by
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

lemma weighted_dyadic_tube_tail {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) (j : ℕ) :
    (μ.withDensity (fun z => ENNReal.ofReal |h z|))
      {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ (1/2:ℝ)^j}
      ≤ tubeWeightConstant n B * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j)) := by
  have hmeas := (continuous_infDist_pt (V : Set (EuclideanSpace ℝ (Fin (n+1))))).measurable.comp
    (normalizedChart_measurable Q)
  refine (weightedMeasure_apply_le_sqrt μ h hh hnorm _
    (measurableSet_le hmeas measurable_const)).trans ?_
  refine (ENNReal.rpow_le_rpow (dyadic_tube_tail hn Q μ hsupport hB hspread V hV _ he j)
    (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hB (pow_nonneg (le_trans (by norm_num) tubeConstant_ge_one) _)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  have hp : (1/2:ℝ)^(2*(k+1)*j) = ((1/2:ℝ)^((k+1)*j))^2 := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hp, ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

lemma weighted_affine_inverseMoment {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (hk : 0 < k) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) :
    (∫⁻ z, ENNReal.ofReal ((infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1)))))⁻¹ ^ k)
      ∂(μ.withDensity (fun z => ENNReal.ofReal |h z|))) ≤
      1 + tubeWeightConstant n B * ENNReal.ofReal ((2:ℝ)^(k+1)) := by
  refine (inverseMoment_of_dyadic_tails _ _
    ((continuous_infDist_pt _).measurable.comp (normalizedChart_measurable Q))
    (fun _ => infDist_nonneg) k hk _
    (weighted_dyadic_tube_tail hn Q μ hsupport hB hspread h hh hnorm V hV k he)).trans ?_
  gcongr
  exact weightedMeasure_mass_le_one μ h hh hnorm

lemma weighted_affine_zero_null {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) :
    (μ.withDensity (fun z => ENNReal.ofReal |h z|))
      {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) = 0} = 0 := by
  exact zeroSet_null_of_dyadic_tails _ _ k _ (tubeWeightConstant_ne_top n B)
    (weighted_dyadic_tube_tail hn Q μ hsupport hB hspread h hh hnorm V hV k he)

lemma weighted_affine_inverseMoment_ennreal {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (k : ℕ) (hk : 0 < k) (he : Module.finrank ℝ V.direction + 2*(k+1) ≤ n/2) :
    (∫⁻ z, (ENNReal.ofReal (infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1))))))⁻¹ ^ k
      ∂(μ.withDensity (fun z => ENNReal.ofReal |h z|))) ≤
      1 + tubeWeightConstant n B * ENNReal.ofReal ((2:ℝ)^(k+1)) := by
  have hzero : ∀ᵐ z ∂(μ.withDensity (fun z => ENNReal.ofReal |h z|)),
      infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using weighted_affine_zero_null hn Q μ hsupport hB hspread h hh hnorm V hV k he
  have heq : (fun z => (ENNReal.ofReal (infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1))))))⁻¹ ^ k) =ᵐ[μ.withDensity (fun z => ENNReal.ofReal |h z|)]
      (fun z => ENNReal.ofReal ((infDist (normalizedChart Q z)
      (V : Set (EuclideanSpace ℝ (Fin (n+1)))))⁻¹ ^ k)) := by
    filter_upwards [hzero] with z hz
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr infDist_nonneg),
      ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne infDist_nonneg hz.symm)]
  rw [lintegral_congr_ae heq]
  exact weighted_affine_inverseMoment hn Q μ hsupport hB hspread h hh hnorm V hV k hk he

end RepeatedLocalization

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_BoxKernels
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
namespace RepeatedLocalization

lemma lintegral_pi_product {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (m : ℕ) :
    (∫⁻ z : Fin m → α, ∏ i, f (z i) ∂Measure.pi (fun _ => μ)) = (∫⁻ z, f z ∂μ)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) 0).symm).lintegral_map_equiv]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.prod_univ_succ, Fin.zero_succAbove]
    change (∫⁻ z : α × (Fin m → α), f z.1 * ∏ i, f (z.2 i)
      ∂μ.prod (Measure.pi (fun _ => μ))) = _
    rw [lintegral_prod_mul (μ := μ) (ν := Measure.pi (fun _ : Fin m => μ))
      (g := fun z : Fin m → α => ∏ i, f (z i)) hf.aemeasurable (by
      exact (Finset.measurable_prod _ fun i _ => hf.comp (measurable_pi_apply i)).aemeasurable),
      ih, pow_succ']

lemma measurableSet_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) :
    MeasurableSet (closedBox c η) := by
  simp only [closedBox, ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le ((measurable_pi_apply i).sub measurable_const).abs measurable_const

lemma volume_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) (hη : 0 ≤ η) :
    volume (closedBox c η) = ENNReal.ofReal ((2*η)^k) := by
  have heq : closedBox c η = univ.pi (fun i => Icc (c i-η) (c i+η)) := by
    ext u
    simp only [closedBox, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_true_left,
      mem_Icc, abs_le]
    congr! 1
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [heq, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, show ∀ i, c i+η-(c i-η)=2*η from fun i => by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

lemma measurable_boxKernel {k : ℕ} (η : ℝ) :
    Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => boxKernel η p.1 p.2) := by
  have hs : MeasurableSet {p : (Fin k → ℝ) × (Fin k → ℝ) | ∀ i, |p.2 i-p.1 i| ≤ η} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)).abs measurable_const
  exact measurable_const.indicator hs

lemma boxKernel_le {k : ℕ} (η : ℝ) (c u : Fin k → ℝ) :
    boxKernel η c u ≤ boxScale k η := Set.indicator_le_self (closedBox c η) (fun _ => boxScale k η) u

lemma boxKernel_ne_zero_mem {k : ℕ} {η : ℝ} {c u : Fin k → ℝ}
    (h : boxKernel η c u ≠ 0) : u ∈ closedBox c η := by
  by_contra hu
  exact h (Set.indicator_of_notMem hu _)

lemma lintegral_boxKernel {k : ℕ} (η : ℝ) (hη : 0 < η) (c : Fin k → ℝ) :
    (∫⁻ u, boxKernel η c u) = 1 := by
  change (∫⁻ u, (closedBox c η).indicator (fun _ => boxScale k η) u) = 1
  rw [lintegral_indicator (measurableSet_closedBox c η), lintegral_const,
    Measure.restrict_apply_univ, volume_closedBox c η hη.le]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

lemma lintegral_boxKernel_product_le {k q : ℕ} (η : ℝ) (hη : 0 < η)
    (c : Fin (q+1) → Fin k → ℝ) :
    (∫⁻ u, ∏ i, boxKernel η (c i) u) ≤
      if ∀ (i : Fin q) r, |c i.succ r-c 0 r| ≤ 2*η then boxScale k η ^ q else 0 := by
  classical
  by_cases hd : ∀ (i : Fin q) r, |c i.succ r-c 0 r| ≤ 2*η
  · rw [ite_eq_left hd]
    calc
      _ ≤ ∫⁻ u, boxScale k η ^ q * boxKernel η (c 0) u := by
        apply lintegral_mono
        intro u
        dsimp only
        rw [Fin.prod_univ_succ, mul_comm]
        apply mul_le_mul_left
        simpa using Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin q)))
          (fun i _ => boxKernel_le η (c i.succ) u)
      _ = boxScale k η ^ q * ∫⁻ u, boxKernel η (c 0) u :=
        lintegral_const_mul _ ((measurable_boxKernel η).comp (measurable_const.prodMk measurable_id))
      _ = boxScale k η ^ q := by rw [lintegral_boxKernel η hη, mul_one]
  · rw [ite_eq_right hd]
    have hz : ∀ u, (∏ i, boxKernel η (c i) u) = 0 := by
      intro u
      by_contra hp
      have hall : ∀ i, u ∈ closedBox (c i) η := by
        intro i
        apply boxKernel_ne_zero_mem
        exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ _)
      apply hd
      intro i r
      have h0 := hall 0 r
      have hi := hall i.succ r
      have he := abs_sub_le (c i.succ r) (u r) (c 0 r)
      rw [abs_sub_comm (c i.succ r) (u r)] at he
      exact he.trans (by linarith)
    simp only [hz, lintegral_zero, le_refl]

end RepeatedLocalization

open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_GramVolume
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
namespace RepeatedLocalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_linearCombination {ι : Type*} [Fintype ι] (g : ι → E)
    (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, T i j • g i) = Tᵀ * Matrix.gram ℝ g * T := by
  ext i j
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma gramTriangular_expansion {q : ℕ} (f : Fin q → E) (j : Fin q) :
    f j = ∑ i, gramTriangular f i j • gramSchmidt ℝ f i := by
  rw [gramSchmidt_def'' ℝ f j]
  have hfin : (Finset.univ.filter fun i : Fin q => i < j) = Finset.Iio j := by
    ext i
    simp
  simp only [gramTriangular, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, hfin]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

lemma gramTriangular_det {q : ℕ} (f : Fin q → E) : (gramTriangular f).det = 1 := by
  have htri : (gramTriangular f).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp only [gramTriangular, ite_eq_right (ne_of_gt hij), ite_eq_right (not_lt.mpr (le_of_lt hij)),
      zero_add]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gramTriangular]

lemma gram_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Matrix.gram ℝ (gramSchmidt ℝ f) =
      Matrix.diagonal (fun i => ‖gramSchmidt ℝ f i‖ ^ 2) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h, gramSchmidt_orthogonal ℝ f h]

lemma gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    (Matrix.gram ℝ f).det = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
  have he : f = (fun j => ∑ i, gramTriangular f i j • gramSchmidt ℝ f i) :=
    funext (gramTriangular_expansion f)
  calc
    (Matrix.gram ℝ f).det =
        ((gramTriangular f)ᵀ * Matrix.gram ℝ (gramSchmidt ℝ f) * gramTriangular f).det := by
      conv_lhs => rw [he]
      rw [gram_linearCombination]
    _ = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        gramTriangular_det, one_mul, mul_one, gram_gramSchmidt, Matrix.det_diagonal,
        Finset.prod_pow]

lemma sqrt_gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Real.sqrt (Matrix.gram ℝ f).det = ∏ i, ‖gramSchmidt ℝ f i‖ := by
  rw [gram_det_eq_prod_gramSchmidt, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]

lemma gramSchmidt_real_def {q : ℕ} (f : Fin q → E) (j : Fin q) :
    gramSchmidt ℝ f j = f j - ∑ i ∈ Finset.Iio j,
      (⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2) • gramSchmidt ℝ f i := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using (gramSchmidt_def'' ℝ f j).symm

lemma measurable_gramSchmidt {q : ℕ} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (j : Fin q) :
    Measurable (fun f : Fin q → E => gramSchmidt ℝ f j) := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    simp_rw [gramSchmidt_real_def (j := j)]
    refine (measurable_pi_apply j).sub (Finset.measurable_sum _ fun i hi => ?_)
    have hmi := ih i (Finset.mem_Iio.mp hi)
    exact ((hmi.inner (measurable_pi_apply j)).div (hmi.norm.pow_const 2)).smul hmi

lemma gramSchmidt_residual_mem_span {q : ℕ} (f : Fin q → E) (j : Fin q) :
    f j - gramSchmidt ℝ f j ∈ Submodule.span ℝ (f '' Set.Iio j) := by
  rw [gramSchmidt_real_def, sub_sub_cancel]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [← span_gramSchmidt_Iio ℝ f j]
  exact Submodule.subset_span (mem_image_of_mem _ (Finset.mem_Iio.mp hi))

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ReplicaMoments
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
namespace RepeatedLocalization
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gramSchmidt_castSucc {q : ℕ} (f : Fin (q+1) → E) (j : Fin q) :
    gramSchmidt ℝ f j.castSucc = gramSchmidt ℝ (fun i => f i.castSucc) j := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    rw [gramSchmidt_real_def, gramSchmidt_real_def, Fin.sum_Iio_castSucc]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ih i (Finset.mem_Iio.mp hi)]

lemma replicaPlane_nonempty {q : ℕ} (b : E) (f : Fin q → E) :
    (replicaPlane b f : Set E).Nonempty := by
  exact ⟨b, AffineSubspace.self_mem_mk' _ _⟩

lemma replicaPlane_finrank_le {q : ℕ} (b : E) (f : Fin q → E) :
    Module.finrank ℝ (replicaPlane b f).direction ≤ q := by
  unfold replicaPlane
  rw [AffineSubspace.direction_mk']
  simpa [Set.finrank] using (finrank_range_le_card (R := ℝ) f)

lemma lastPlane_infDist_le {q : ℕ} (b : E) (f : Fin (q+1) → E) :
    infDist (f (Fin.last q) + b) (replicaPlane b (fun i => f i.castSucc) : Set E) ≤
      ‖gramSchmidt ℝ f (Fin.last q)‖ := by
  have hset : f '' Iio (Fin.last q) = range (fun i : Fin q => f i.castSucc) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, i.isLt, rfl⟩
  have hm := gramSchmidt_residual_mem_span f (Fin.last q)
  rw [hset] at hm
  have hpoint : f (Fin.last q) - gramSchmidt ℝ f (Fin.last q) + b ∈
      replicaPlane b (fun i => f i.castSucc) := by
    apply AffineSubspace.mem_mk'.mpr
    simpa using hm
  convert infDist_le_dist_of_mem (x := f (Fin.last q)+b) hpoint using 1
  rw [dist_eq_norm]
  congr 1
  abel

lemma gramInverseProduct_succ {q : ℕ} (k : ℕ) (f : Fin (q+1) → E) :
    gramInverseProduct k f = gramInverseProduct k (fun i => f i.castSucc) *
      (ENNReal.ofReal ‖gramSchmidt ℝ f (Fin.last q)‖)⁻¹ ^ k := by
  unfold gramInverseProduct
  rw [Fin.prod_univ_castSucc]
  simp_rw [gramSchmidt_castSucc]

lemma measurable_gramInverseProduct {q : ℕ} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (k : ℕ) :
    Measurable (gramInverseProduct (E := E) (q := q) k) := by
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gramSchmidt i).norm.ennreal_ofReal.inv.pow_const _

lemma lintegral_gramInverseProduct_le {α : Type*} [MeasurableSpace α]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) [SigmaFinite μ] (a : α → E) (ha : Measurable a)
    (k p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ E, (V : Set E).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z, (ENNReal.ofReal (infDist (a z) (V : Set E)))⁻¹ ^ k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) (b : E) :
    (∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b)
      ∂Measure.pi (fun _ => μ)) ≤ M^q := by
  induction q with
  | zero => simp [gramInverseProduct]
  | succ q ih =>
    have hq' : q ≤ p := by omega
    have hmeas : Measurable (fun z : Fin (q+1) → α =>
        gramInverseProduct k (fun i => a (z i)-b)) :=
      (measurable_gramInverseProduct k).comp
        (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i)).sub measurable_const)
    rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (q+1) => μ) (Fin.last q)).symm).lintegral_map_equiv]
    rw [lintegral_prod_symm _ (by
      exact (hmeas.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => α)
        (Fin.last q)).symm.measurable).aemeasurable)]
    have hlast : ∀ (z : Fin q → α),
        (∫⁻ x, gramInverseProduct k (fun i => a (Fin.snoc (α := fun _ : Fin (q+1) => α) z x i)-b) ∂μ) ≤
          gramInverseProduct k (fun i => a (z i)-b) * M := by
      intro z
      let V := replicaPlane b (fun i => a (z i)-b)
      have hV := replicaPlane_nonempty b (fun i => a (z i)-b)
      have hr := (replicaPlane_finrank_le b (fun i => a (z i)-b)).trans hq'
      calc
        _ ≤ ∫⁻ x, gramInverseProduct k (fun i => a (z i)-b) *
            (ENNReal.ofReal (infDist (a x) (V : Set E)))⁻¹ ^ k ∂μ := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [gramInverseProduct_succ]
          simp only [Fin.snoc_castSucc]
          apply mul_le_mul_right
          apply pow_le_pow_left'
          apply ENNReal.inv_le_inv.mpr
          apply ENNReal.ofReal_le_ofReal
          simpa only [V, Fin.snoc_last, Fin.snoc_castSucc, sub_add_cancel] using
            (lastPlane_infDist_le b (fun i => a (Fin.snoc (α := fun _ : Fin (q+1) => α) z x i)-b))
        _ = gramInverseProduct k (fun i => a (z i)-b) *
            ∫⁻ x, (ENNReal.ofReal (infDist (a x) (V : Set E)))⁻¹ ^ k ∂μ := by
          exact lintegral_const_mul _ (by
            exact ((((continuous_infDist_pt (V : Set E)).measurable.comp ha).ennreal_ofReal.inv).pow_const k))
        _ ≤ gramInverseProduct k (fun i => a (z i)-b) * M := mul_le_mul_right (hcond V hV hr) _
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_last]
    calc
      _ ≤ ∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b) * M
          ∂Measure.pi (fun _ => μ) := lintegral_mono hlast
      _ = (∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b)
          ∂Measure.pi (fun _ => μ)) * M := by
        exact lintegral_mul_const _ ((measurable_gramInverseProduct k).comp
          (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i)).sub measurable_const))
      _ ≤ M^q * M := mul_le_mul_left (ih (by omega)) M
      _ = M^(q+1) := (pow_succ _ _).symm

lemma gramInverseProduct_eq_inverseVolume {q : ℕ} (k : ℕ) (f : Fin q → E) :
    gramInverseProduct k f = (ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ f).det))⁻¹ ^ k := by
  rw [sqrt_gram_det_eq_prod_gramSchmidt,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
    ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr ENNReal.ofReal_ne_top),
    ← Finset.prod_pow]
  rfl

lemma lintegral_replicaInverse_le {α : Type*} [MeasurableSpace α]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) [SigmaFinite μ] (hμ : μ univ ≤ 1) (a : α → E) (ha : Measurable a)
    (k p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ E, (V : Set E).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z, (ENNReal.ofReal (infDist (a z) (V : Set E)))⁻¹ ^ k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) :
    (∫⁻ z : Fin (q+1) → α, gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))
      ∂Measure.pi (fun _ => μ)) ≤ M^q := by
  have hmeas : Measurable (fun z : Fin (q+1) → α =>
      gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))) :=
    (measurable_gramInverseProduct k).comp
      (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i.succ)).sub
        (ha.comp (measurable_pi_apply 0)))
  rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (q+1) => μ) 0).symm).lintegral_map_equiv]
  rw [lintegral_prod _ (by
    exact (hmeas.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => α) 0).symm.measurable).aemeasurable)]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove]
  calc
    _ ≤ ∫⁻ x, M^q ∂μ := lintegral_mono fun x =>
      lintegral_gramInverseProduct_le μ a ha k p M hcond q hq (a x)
    _ = M^q * μ univ := lintegral_const _
    _ ≤ M^q * 1 := mul_le_mul_right hμ _
    _ = M^q := mul_one _

end RepeatedLocalization

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_GaussianImages
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

lemma finiteProduct_le {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] {μ ν : ∀ i, Measure (E i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  have ho : (OuterMeasure.pi fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi fun i => (ν i).toOuterMeasure := by
    apply OuterMeasure.le_pi.mpr
    intro t ht
    exact (OuterMeasure.pi_pi_le _ _).trans
      (Finset.prod_le_prod' fun i _ => h i (t i))
  exact ho s

lemma standardGaussianPDF_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  change (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - 0)^2 / (2 * 1)) ≤ 1
  simp only [mul_one, sub_zero]
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hi : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have he : Real.exp (-(x^2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa using hi)

lemma standardGaussian_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  exact withDensity_mono (ae_of_all _ standardGaussianPDF_le_one)

lemma iidGaussian_le_volume (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => gaussianReal 0 1) ≤ (volume : Measure (ι → ℝ)) :=
  finiteProduct_le fun _ => standardGaussian_le_volume

lemma gaussian_square_map_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (Matrix.toLin' M) ≤
      ENNReal.ofReal (|M.det|⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hmap := Measure.map_mono (iidGaussian_le_volume ι)
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hM, abs_inv] at hmap
  exact hmap

open Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

lemma rectangularGaussian_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    (stdGaussian (EuclideanSpace ℝ κ)).map
      (LinearMap.toContinuousLinearMap A.toEuclideanLin) =
      multivariateGaussian 0 (A * Aᵀ) := by
  have hA : (A * Aᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose A
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian hA, innerSL_apply_apply ℝ,
      ← LinearMap.adjoint_toContinuousLinearMap,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      Matrix.conjTranspose_eq_transpose_of_trivial, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial]
    change (Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A * Aᵀ) *ᵥ y
    rw [dotProduct_comm (Aᵀ *ᵥ y)]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
    simp [Matrix.dotProduct_mulVec]

lemma rectangularGaussian_squareRoot_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (Matrix.toLin' A) =
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (Matrix.toLin' (CFC.sqrt (A * Aᵀ))) := by
  have he := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) => μ.map ofLp)
    (rectangularGaussian_eq A)
  unfold multivariateGaussian at he
  simp only [zero_add] at he
  rw [← map_pi_eq_stdGaussian, ← map_pi_eq_stdGaussian] at he
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at he
  exact he

lemma gaussian_rectangular_map_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (Matrix.toLin' A) ≤
      ENNReal.ofReal ((Real.sqrt (A * Aᵀ).det)⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hpos : (A * Aᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose A
  have hd : (CFC.sqrt (A * Aᵀ)).det = Real.sqrt (A * Aᵀ).det := by
    rw [hpos.det_sqrt, RCLike.sqrt_of_nonneg hpos.det_nonneg]
    rfl
  have hD : (CFC.sqrt (A * Aᵀ)).det ≠ 0 := by
    rw [hd]
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hpos.det_nonneg hA.symm)
  rw [rectangularGaussian_squareRoot_eq]
  convert gaussian_square_map_le (CFC.sqrt (A * Aᵀ)) hD using 1
  rw [hd, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma gaussian_rectangular_box_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) (η : ℝ) (hη : 0 ≤ η) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1))
      {x | ∀ i, |(A *ᵥ x) i| ≤ η} ≤
      ENNReal.ofReal ((Real.sqrt (A * Aᵀ).det)⁻¹ * (2 * η) ^ Fintype.card ι) := by
  have he : {x : κ → ℝ | ∀ i, |(A *ᵥ x) i| ≤ η} =
      (Matrix.toLin' A) ⁻¹' (Set.univ.pi fun _ : ι => Set.Icc (-η) η) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_true_left, Matrix.toLin'_apply, Set.mem_Icc, abs_le]
  rw [he, ← Measure.map_apply (Matrix.toLin' A).continuous_of_finiteDimensional.measurable
    (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc)]
  refine (gaussian_rectangular_map_le A hA _).trans_eq ?_
  rw [Measure.smul_apply, smul_eq_mul, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const,
    Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]

lemma gaussian_multirow_box_le {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) (η : ℝ) (hη : 0 ≤ η) :
    (Measure.pi (fun _ : ρ => Measure.pi (fun _ : κ => gaussianReal 0 1)))
      {X | ∀ r i, |(A *ᵥ X r) i| ≤ η} ≤
      ENNReal.ofReal (((Real.sqrt (A * Aᵀ).det)⁻¹ * (2 * η)^Fintype.card ι)^Fintype.card ρ) := by
  have he : {X : ρ → κ → ℝ | ∀ r i, |(A *ᵥ X r) i| ≤ η} =
      Set.univ.pi (fun _ : ρ => {x : κ → ℝ | ∀ i, |(A *ᵥ x) i| ≤ η}) := by
    ext x
    simp
  rw [he, Measure.pi_pi, ENNReal.ofReal_pow (by positivity)]
  simpa using Finset.prod_le_prod' (s := (Finset.univ : Finset ρ))
    (fun _ _ => gaussian_rectangular_box_le A hA η hη)

end RepeatedLocalization

namespace RepeatedLocalization
open Matrix WithLp
open scoped MatrixOrder RealInnerProductSpace

lemma gaussian_multirow_box_le_extended {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (hρ : 0 < Fintype.card ρ)
    (A : Matrix ι κ ℝ) (η : ℝ) (hη : 0 < η) :
    (Measure.pi (fun _ : ρ => Measure.pi (fun _ : κ => gaussianReal 0 1)))
      {X | ∀ r i, |(A *ᵥ X r) i| ≤ η} ≤
      (ENNReal.ofReal (Real.sqrt (A * Aᵀ).det))⁻¹ ^ Fintype.card ρ *
        ENNReal.ofReal ((2*η)^(Fintype.card ι * Fintype.card ρ)) := by
  by_cases hA : (A * Aᵀ).det ≠ 0
  · refine (gaussian_multirow_box_le A hA η hη.le).trans_eq ?_
    have hpos : (A * Aᵀ).PosSemidef := by
      simpa using Matrix.posSemidef_self_mul_conjTranspose A
    have hd : 0 < Real.sqrt (A * Aᵀ).det := Real.sqrt_pos.mpr
      (lt_of_le_of_ne hpos.det_nonneg hA.symm)
    rw [mul_pow, ← pow_mul, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hd]
  · simp only [not_ne_iff] at hA
    rw [hA, Real.sqrt_zero, ENNReal.ofReal_zero, ENNReal.inv_zero,
      ENNReal.top_pow hρ.ne', ENNReal.top_mul (by positivity)]
    exact le_top

lemma rowMatrix_gram {q d : ℕ} (f : Fin q → EuclideanSpace ℝ (Fin d)) :
    rowMatrix f * (rowMatrix f)ᵀ = Matrix.gram ℝ f := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowMatrix, Matrix.gram_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ProjectionMoments
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
open Metric Matrix WithLp

lemma continuous_projectVector {k d : ℕ} :
    Continuous (fun p : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) => projectVector p.1 p.2) := by
  unfold projectVector
  fun_prop

lemma projectVector_sub {k d : ℕ} (X : Fin k → Fin d → ℝ)
    (v w : EuclideanSpace ℝ (Fin d)) : projectVector X (v-w) = projectVector X v-projectVector X w := by
  ext r
  simp only [projectVector, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]

lemma projectVector_rowMatrix {k q d : ℕ} (X : Fin k → Fin d → ℝ)
    (v : Fin q → EuclideanSpace ℝ (Fin d)) (r : Fin k) (i : Fin q) :
    projectVector X (v i) r = (rowMatrix v *ᵥ X r) i := by
  simp only [projectVector, mulVec, dotProduct, rowMatrix]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma boxScale_cancel (k q : ℕ) (η : ℝ) (hη : 0 < η) :
    boxScale k η ^ q * ENNReal.ofReal ((4*η)^(q*k)) = ENNReal.ofReal ((2:ℝ)^(k*q)) := by
  have h2 : 0 < 2*η := by positivity
  have he : (4*η)^(q*k) = (2:ℝ)^(k*q)*((2*η)^k)^q := by
    rw [show (4:ℝ)*η=2*(2*η) by ring, mul_pow, ← pow_mul, Nat.mul_comm q k]
  rw [he, ENNReal.ofReal_mul (pow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (pow_nonneg h2.le _), boxScale, ← ENNReal.inv_pow,
    mul_left_comm, ENNReal.inv_mul_cancel (by positivity) (by finiteness), mul_one]

lemma fixedReplica_moment_le {k q d : ℕ} (hk : 0 < k)
    (η : ℝ) (hη : 0 < η) (v : Fin (q+1) → EuclideanSpace ℝ (Fin d)) :
    (∫⁻ p : (Fin k → Fin d → ℝ) × (Fin k → ℝ),
      ∏ i, boxKernel η (projectVector p.1 (v i)) p.2 ∂(gaussianRows k d).prod volume) ≤
      ENNReal.ofReal ((2:ℝ)^(k*q)) * gramInverseProduct k (fun i : Fin q => v i.succ-v 0) := by
  classical
  let diff := fun i : Fin q => v i.succ-v 0
  let D := {X : Fin k → Fin d → ℝ | ∀ (i : Fin q) r,
      |projectVector X (v i.succ) r-projectVector X (v 0) r| ≤ 2*η}
  have hD : MeasurableSet D := by
    dsimp only [D]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro r
    exact measurableSet_le
      ((((measurable_pi_apply r).comp (continuous_projectVector.measurable.comp
        (measurable_id.prodMk measurable_const))).sub
        ((measurable_pi_apply r).comp (continuous_projectVector.measurable.comp
          (measurable_id.prodMk measurable_const)))).abs) measurable_const
  have hdiff : D = {X : Fin k → Fin d → ℝ | ∀ r i, |(rowMatrix diff *ᵥ X r) i| ≤ 2*η} := by
    ext X
    simp only [D, Set.mem_ofPred_eq]
    rw [forall_comm]
    congr! 2
    simp only [← projectVector_rowMatrix, diff, projectVector_sub, Pi.sub_apply]
  have hprob : gaussianRows k d D ≤ gramInverseProduct k diff *
      ENNReal.ofReal ((4*η)^(q*k)) := by
    rw [hdiff, gramInverseProduct_eq_inverseVolume]
    simpa only [gaussianRows, Fintype.card_fin, rowMatrix_gram, show 2*(2*η)=4*η by ring] using
      gaussian_multirow_box_le_extended (ρ := Fin k) (by simpa using hk)
        (rowMatrix diff) (2*η) (by positivity)
  have hmeas : Measurable (fun p : (Fin k → Fin d → ℝ) × (Fin k → ℝ) =>
      ∏ i, boxKernel η (projectVector p.1 (v i)) p.2) := by
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_boxKernel η).comp
      ((continuous_projectVector.measurable.comp (measurable_fst.prodMk measurable_const)).prodMk measurable_snd)
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc
    _ ≤ ∫⁻ X, D.indicator (fun _ => boxScale k η ^ q) X ∂gaussianRows k d := by
      apply lintegral_mono
      intro X
      simpa only [Set.indicator, D, Set.mem_ofPred_eq] using
        lintegral_boxKernel_product_le η hη (fun i => projectVector X (v i))
    _ = boxScale k η ^ q * gaussianRows k d D := by
      rw [lintegral_indicator hD, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ boxScale k η ^ q * (gramInverseProduct k diff * ENNReal.ofReal ((4*η)^(q*k))) :=
      mul_le_mul_right hprob _
    _ = ENNReal.ofReal ((2:ℝ)^(k*q)) * gramInverseProduct k diff := by
      rw [mul_left_comm, boxScale_cancel k q η hη, mul_comm]

lemma measurable_projection_kernel {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (a : α → EuclideanSpace ℝ (Fin d)) (ha : Measurable a) (η : ℝ) :
    Measurable (fun p : ((Fin k → Fin d → ℝ) × (Fin k → ℝ)) × α =>
      boxKernel η (projectVector p.1.1 (a p.2)) p.1.2) :=
  (measurable_boxKernel η).comp
    ((continuous_projectVector.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk (ha.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_fst))

lemma measurable_replicated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : ℕ}
    (f : β × α → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun x : β × (Fin m → α) => ∏ i, f (x.1,x.2 i)) := by
  apply Finset.measurable_prod
  intro i hi
  exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_replica_kernel {α : Type*} [MeasurableSpace α] {k d m : ℕ}
    (a : α → EuclideanSpace ℝ (Fin d)) (ha : Measurable a) (η : ℝ) :
    Measurable (fun x : ((Fin k → Fin d → ℝ) × (Fin k → ℝ)) × (Fin m → α) =>
      ∏ i, boxKernel η (projectVector x.1.1 (a (x.2 i))) x.1.2) :=
  measurable_replicated _ (measurable_projection_kernel (k := k) (d := d) a ha η)

lemma smoothedProjection_moment_le {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (μ : Measure α) [SigmaFinite μ] (hμ : μ univ ≤ 1)
    (a : α → EuclideanSpace ℝ (Fin d)) (ha : Measurable a) (hk : 0 < k)
    (p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      (V : Set (EuclideanSpace ℝ (Fin d))).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z, (ENNReal.ofReal (infDist (a z) (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹ ^ k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) (η : ℝ) (hη : 0 < η) :
    (∫⁻ x, smoothedProjection (k := k) μ a η x ^ (q+1)
      ∂(gaussianRows k d).prod volume) ≤ ENNReal.ofReal ((2:ℝ)^(k*q))*M^q := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm := measurable_replica_kernel (k := k) (d := d) (m := q+1) a ha η
  calc
    _ = ∫⁻ x, ∫⁻ z : Fin (q+1) → α,
        ∏ i, boxKernel η (projectVector x.1 (a (z i))) x.2
        ∂Measure.pi (fun _ => μ) ∂(gaussianRows k d).prod volume := by
      apply lintegral_congr
      intro x
      exact (lintegral_pi_product μ _ ((measurable_projection_kernel (k := k) (d := d) a ha η).comp
        (measurable_const.prodMk measurable_id)) (q+1)).symm
    _ = ∫⁻ z : Fin (q+1) → α, ∫⁻ x,
        ∏ i, boxKernel η (projectVector x.1 (a (z i))) x.2
        ∂(gaussianRows k d).prod volume ∂Measure.pi (fun _ => μ) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ z : Fin (q+1) → α, ENNReal.ofReal ((2:ℝ)^(k*q)) *
        gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))
        ∂Measure.pi (fun _ => μ) := lintegral_mono fun z =>
      fixedReplica_moment_le hk η hη (fun i => a (z i))
    _ = ENNReal.ofReal ((2:ℝ)^(k*q)) * ∫⁻ z : Fin (q+1) → α,
        gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))
        ∂Measure.pi (fun _ => μ) := by
      apply lintegral_const_mul
      exact (measurable_gramInverseProduct k).comp
        (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i.succ)).sub
          (ha.comp (measurable_pi_apply 0)))
    _ ≤ ENNReal.ofReal ((2:ℝ)^(k*q))*M^q := mul_le_mul_right
      (lintegral_replicaInverse_le μ hμ a ha k p M hcond q hq) _

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_MixtureBounds
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

lemma smoothingWidth_pos (j : ℕ) : 0 < smoothingWidth j := by
  unfold smoothingWidth
  positivity

lemma smoothingWidth_tendsto : Tendsto smoothingWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma measurable_boxAverage {T : Type*} [MeasurableSpace T] {k : ℕ}
    (η : ℝ) (g : T × (Fin k → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    Measurable (boxAverage η g) := by
  have h : Measurable (fun p : (T × (Fin k → ℝ)) × (Fin k → ℝ) =>
      boxKernel η p.1.2 p.2 * g (p.1.1,p.2)) :=
    ((measurable_boxKernel η).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
      (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact h.lintegral_prod_right

lemma open_box_eventually {T : Type*} [PseudoMetricSpace T] {k : ℕ}
    (O : Set (T × (Fin k → ℝ))) (hO : IsOpen O) (p : T × (Fin k → ℝ))
    (hp : p ∈ O) : ∀ᶠ j in atTop, ∀ u ∈ closedBox p.2 (smoothingWidth j), (p.1,u) ∈ O := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hp)
  filter_upwards [smoothingWidth_tendsto.eventually (gt_mem_nhds hε)] with j hj
  intro u hu
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  apply max_lt
  · simpa using hε
  · apply lt_of_le_of_lt _ hj
    apply (dist_pi_le_iff (smoothingWidth_pos j).le).mpr
    intro i
    simpa only [Real.dist_eq] using hu i

lemma indicator_le_liminf_boxAverage {T : Type*} [PseudoMetricSpace T] {k : ℕ}
    (O : Set (T × (Fin k → ℝ))) (hO : IsOpen O) (p : T × (Fin k → ℝ)) :
    O.indicator (fun _ => (1:ℝ≥0∞)) p ≤
      liminf (fun j : ℕ => boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) p) atTop := by
  classical
  by_cases hp : p ∈ O
  · rw [Set.indicator_of_mem hp]
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [open_box_eventually O hO p hp] with j hj
    have he : boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) p = 1 := by
      calc
        _ = ∫⁻ u, boxKernel (smoothingWidth j) p.2 u := by
          apply lintegral_congr
          intro u
          by_cases hu : u ∈ closedBox p.2 (smoothingWidth j)
          · rw [Set.indicator_of_mem (hj u hu), mul_one]
          · rw [boxKernel, Set.indicator_of_notMem hu, zero_mul]
        _ = 1 := lintegral_boxKernel _ (smoothingWidth_pos j) _
    exact he.ge
  · rw [Set.indicator_of_notMem hp]
    exact zero_le

lemma measurable_mixture_kernel {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (b : T × E → Fin k → ℝ) (hb : Measurable b) (η : ℝ) :
    Measurable (fun p : (T × (Fin k → ℝ)) × E => boxKernel η (b (p.1.1,p.2)) p.1.2) :=
  (measurable_boxKernel η).comp
    ((hb.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst))

lemma measurable_mixtureDensity {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (μ : Measure E) [SFinite μ] (b : T × E → Fin k → ℝ) (hb : Measurable b) (η : ℝ) :
    Measurable (mixtureDensity μ b η) := (measurable_mixture_kernel b hb η).lintegral_prod_right

lemma lintegral_mixtureDensity_mul {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (σ : Measure T) [SFinite σ] (μ : Measure E) [SFinite μ]
    (b : T × E → Fin k → ℝ) (hb : Measurable b) (η : ℝ)
    (g : T × (Fin k → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p, mixtureDensity μ b η p * g p ∂σ.prod volume) =
      ∫⁻ q : T × E, boxAverage η g (q.1,b q) ∂σ.prod μ := by
  rw [lintegral_prod (μ := σ) (ν := volume)
      (fun p => mixtureDensity μ b η p * g p) (by
        exact ((measurable_mixtureDensity μ b hb η).mul hg).aemeasurable),
    lintegral_prod (μ := σ) (ν := μ) (fun q => boxAverage η g (q.1,b q)) (by
      exact ((measurable_boxAverage η g hg).comp (measurable_fst.prodMk hb)).aemeasurable)]
  apply lintegral_congr
  intro x
  have h : Measurable (fun p : (Fin k → ℝ) × E =>
      boxKernel η (b (x,p.2)) p.1 * g (x,p.1)) :=
    ((measurable_boxKernel η).comp
      ((hb.comp (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)).mul
      (hg.comp (measurable_const.prodMk measurable_fst))
  calc
    _ = ∫⁻ u, ∫⁻ z, boxKernel η (b (x,z)) u * g (x,u) ∂μ := by
      apply lintegral_congr
      intro u
      exact (lintegral_mul_const (g (x,u)) ((measurable_boxKernel η).comp
        ((hb.comp (measurable_const.prodMk measurable_id)).prodMk measurable_const))).symm
    _ = _ := lintegral_lintegral_swap h.aemeasurable

lemma measure_rpow_bound_of_open {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (ν ρ : Measure E) [ρ.OuterRegular] (K : ℝ≥0∞) (hK : K ≠ ∞)
    (r : ℝ) (hr : 0 ≤ r)
    (hopen : ∀ O : Set E, IsOpen O → ν O ≤ K*(ρ O)^r) (S : Set E) :
    ν S ≤ K*(ρ S)^r := by
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun j : ℕ => K*(ρ S+ENNReal.ofReal (1 / ((j:ℝ)+1)))^r)
      atTop (𝓝 (K*(ρ S)^r)) := by
    apply ENNReal.Tendsto.const_mul _ (Or.inr hK)
    simpa using ((tendsto_const_nhds.add ht).ennrpow_const r)
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  have he : ENNReal.ofReal (1/((j:ℝ)+1)) ≠ 0 := by positivity
  obtain ⟨O,hSO,hO,hρO⟩ := S.exists_isOpen_le_add ρ he
  exact (measure_mono hSO).trans ((hopen O hO).trans
    (mul_le_mul_right (ENNReal.rpow_le_rpow hρO hr) _))

lemma lintegral_holder_set_bound {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (F : E → ℝ≥0∞) (hF : Measurable F)
    {m : ℕ} (hm : 1 < m) (K : ℝ≥0∞)
    (hmoment : (∫⁻ p, F p ^ m ∂ρ) ≤ K)
    (S : Set E) (hS : MeasurableSet S) :
    (∫⁻ p in S, F p ∂ρ) ≤ K^(1/(m:ℝ))*(ρ S)^(1-1/(m:ℝ)) := by
  have hm' : (1:ℝ) < m := by exact_mod_cast hm
  have hconj : (m:ℝ).HolderConjugate ((m:ℝ)/(m-1)) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hm', ?_⟩
    field_simp
    ring
  have he : 1/((m:ℝ)/(m-1)) = 1-1/(m:ℝ) := by field_simp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ hconj hF.aemeasurable
    ((measurable_const.indicator hS).aemeasurable :
      AEMeasurable (S.indicator (fun _ => (1:ℝ≥0∞))) ρ)
  have hleft : (∫⁻ x, (F * S.indicator (fun _ => (1:ℝ≥0∞))) x ∂ρ) = ∫⁻ x in S, F x ∂ρ := by
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ S <;> simp [hx]
  have hright : (∫⁻ x, (S.indicator (fun _ => (1:ℝ≥0∞)) x)^((m:ℝ)/(m-1)) ∂ρ) = ρ S := by
    have hpos : 0 < (m:ℝ)/(m-1) := by positivity
    rw [← lintegral_indicator_one hS]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ S <;> simp [hx, hpos]
  rw [hleft, hright, he] at h
  simp only [ENNReal.rpow_natCast] at h
  exact h.trans (mul_le_mul_left (ENNReal.rpow_le_rpow hmoment (by positivity)) _)

lemma bounded_layer_cake {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (g : E → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂ν) = ∫⁻ t in Ioo (0:ℝ) 1, ν {x | t < g x} := by
  rw [lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hg0) hg.aemeasurable,
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  by_cases ht0 : 0 < t
  · by_cases ht1 : t < 1
    · simp [ht0, ht1]
    · have hz : {x | t < g x} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact not_lt.mpr ((hg1 x).trans (le_of_not_gt ht1))
      simp [ht0, ht1, hz]
  · simp [ht0]

lemma bounded_borel_test_of_measure_rpow_bound {E : Type*} [MeasurableSpace E]
    (ν ρ : Measure E) (K : ℝ≥0∞) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbound : ∀ S : Set E, MeasurableSet S → ν S ≤ K*(ρ S)^r)
    (g : E → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≤ K*(∫⁻ x, ENNReal.ofReal (g x) ∂ρ)^r := by
  have ht : Measurable (fun t : ℝ => ρ {x | t < g x}) := by
    apply Antitone.measurable
    intro s t hst
    exact measure_mono (fun x hx => lt_of_le_of_lt hst hx)
  rw [bounded_layer_cake ν g hg hg0 hg1, bounded_layer_cake ρ g hg hg0 hg1]
  calc
    _ ≤ ∫⁻ t in Ioo (0:ℝ) 1, K*(ρ {x | t < g x})^r := by
      apply lintegral_mono
      intro t
      exact hbound _ (measurableSet_lt measurable_const hg)
    _ = K * ∫⁻ t in Ioo (0:ℝ) 1, (ρ {x | t < g x})^r :=
      lintegral_const_mul _ (ht.pow_const r)
    _ ≤ K * ((∫⁻ t in Ioo (0:ℝ) 1, ρ {x | t < g x})^r *
        (∫⁻ t in Ioo (0:ℝ) 1, (1:ℝ≥0∞))^(1-r)) := by
      apply mul_le_mul_right
      simpa only [ENNReal.one_rpow, mul_one] using
        ENNReal.lintegral_mul_norm_pow_le (μ := volume.restrict (Ioo (0:ℝ) 1))
          (g := fun _ : ℝ => (1:ℝ≥0∞))
          ht.aemeasurable aemeasurable_const hr0 (sub_nonneg.mpr hr1) (by ring : r+(1-r)=1)
    _ = _ := by simp

lemma exactMixtureLaw_open_bound {T E : Type*} [PseudoMetricSpace T]
    [MeasurableSpace T] [BorelSpace T] [MeasurableSpace E] {k m : ℕ}
    (σ : Measure T) [SFinite σ] (μ : Measure E) [SFinite μ]
    (b : T × E → Fin k → ℝ) (hb : Measurable b) (hm : 1 < m) (K : ℝ≥0∞)
    (hK : ∀ η : ℝ, 0 < η →
      (∫⁻ p, mixtureDensity μ b η p ^ m ∂σ.prod volume) ≤ K)
    (O : Set (T × (Fin k → ℝ))) (hO : IsOpen O) :
    exactMixtureLaw σ μ b O ≤ K^(1/(m:ℝ))*((σ.prod volume) O)^(1-1/(m:ℝ)) := by
  have hmap : Measurable (fun q : T × E => (q.1,b q)) := measurable_fst.prodMk hb
  have hg : Measurable (O.indicator (fun _ => (1:ℝ≥0∞))) :=
    measurable_const.indicator hO.measurableSet
  have havg (j : ℕ) : Measurable (fun q : T × E =>
      boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) (q.1,b q)) :=
    (measurable_boxAverage _ _ hg).comp hmap
  calc
    _ = ∫⁻ q : T × E, O.indicator (fun _ => (1:ℝ≥0∞)) (q.1,b q) ∂σ.prod μ := by
      rw [← lintegral_indicator_one hO.measurableSet, exactMixtureLaw]
      exact lintegral_map hg hmap
    _ ≤ ∫⁻ q : T × E, liminf (fun j : ℕ =>
        boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) (q.1,b q)) atTop ∂σ.prod μ := by
      exact lintegral_mono (fun q => indicator_le_liminf_boxAverage O hO _)
    _ ≤ liminf (fun j : ℕ => ∫⁻ q : T × E,
        boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) (q.1,b q) ∂σ.prod μ) atTop :=
      lintegral_liminf_le havg
    _ ≤ _ := by
      refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
      apply Filter.Eventually.frequently
      apply Eventually.of_forall
      intro j
      rw [← lintegral_mixtureDensity_mul σ μ b hb _ _ hg]
      have he : (∫⁻ p, mixtureDensity μ b (smoothingWidth j) p *
          O.indicator (fun _ => (1:ℝ≥0∞)) p ∂σ.prod volume) =
          ∫⁻ p in O, mixtureDensity μ b (smoothingWidth j) p ∂σ.prod volume := by
        rw [← lintegral_indicator hO.measurableSet]
        apply lintegral_congr
        intro p
        by_cases hp : p ∈ O <;> simp [hp]
      rw [he]
      exact lintegral_holder_set_bound _ _ (measurable_mixtureDensity μ b hb _) hm K
        (hK _ (smoothingWidth_pos j)) O hO.measurableSet

lemma exactMixtureLaw_borel_test {T E : Type*} [PseudoMetricSpace T]
    [MeasurableSpace T] [BorelSpace T] [MeasurableSpace E] {k m : ℕ}
    (σ : Measure T) [SFinite σ] (μ : Measure E) [SFinite μ]
    [(σ.prod (volume : Measure (Fin k → ℝ))).OuterRegular]
    (b : T × E → Fin k → ℝ) (hb : Measurable b) (hm : 1 < m)
    (K : ℝ≥0∞) (hKfinite : K ≠ ∞)
    (hK : ∀ η : ℝ, 0 < η → (∫⁻ p, mixtureDensity μ b η p ^ m ∂σ.prod volume) ≤ K)
    (g : T × (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    (∫⁻ p, ENNReal.ofReal (g p) ∂exactMixtureLaw σ μ b) ≤
      K^(1/(m:ℝ))*(∫⁻ p, ENNReal.ofReal (g p) ∂σ.prod volume)^(1-1/(m:ℝ)) := by
  have hm' : (1:ℝ) < m := by exact_mod_cast hm
  have hr : 0 ≤ 1-1/(m:ℝ) := by
    rw [sub_nonneg]
    exact (div_le_one (by positivity)).mpr hm'.le
  apply bounded_borel_test_of_measure_rpow_bound _ _ _ _ hr (by exact sub_le_self _ (by positivity)) _ g hg hg0 hg1
  intro S hS
  exact measure_rpow_bound_of_open _ _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKfinite)
    _ hr (exactMixtureLaw_open_bound σ μ b hb hm K hK) S

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ProjectionTests
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

lemma weightedProjectionMoment_ne_top (n k m : ℕ) (B : ℝ) :
    weightedProjectionMoment n k m B ≠ ∞ := by
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.pow_ne_top
  exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (tubeWeightConstant_ne_top _ _) ENNReal.ofReal_ne_top⟩

lemma actual_smoothedProjection_moment {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    (∫⁻ x, smoothedProjection (k := k) (μ.withDensity (fun z => ENNReal.ofReal |h z|))
      (normalizedChart Q) η x ^ m ∂(gaussianRows k (n+1)).prod volume) ≤
      weightedProjectionMoment n k m B := by
  let ν := μ.withDensity (fun z => ENNReal.ofReal |h z|)
  have hν : ν univ ≤ 1 := weightedMeasure_mass_le_one μ h hh hnorm
  have : IsFiniteMeasure ν := ⟨hν.trans_lt (by simp)⟩
  have he : m-1+1 = m := by omega
  unfold weightedProjectionMoment
  rw [← he]
  have hm1 : m-1+1-1 = m-1 := by omega
  simp only [hm1]
  apply smoothedProjection_moment_le ν hν (normalizedChart Q) (normalizedChart_measurable Q)
    hk (m-2) _ _ (m-1) (by omega) η hη
  intro V hV hd
  exact weighted_affine_inverseMoment_ennreal hn Q μ hsupport hB hspread h hh hnorm V hV k hk
    (by omega)

lemma actual_projection_borel_test {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (g : (Fin k → Fin (n+1) → ℝ) × (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    (∫⁻ q, ENNReal.ofReal (g (q.1,projectVector q.1 (normalizedChart Q q.2)))
      ∂(gaussianRows k (n+1)).prod (μ.withDensity (fun z => ENNReal.ofReal |h z|))) ≤
      (weightedProjectionMoment n k m B)^(1/(m:ℝ)) *
        (∫⁻ p, ENNReal.ofReal (g p) ∂(gaussianRows k (n+1)).prod volume)^(1-1/(m:ℝ)) := by
  let ν := μ.withDensity (fun z => ENNReal.ofReal |h z|)
  have hν : ν univ ≤ 1 := weightedMeasure_mass_le_one μ h hh hnorm
  have : IsFiniteMeasure ν := ⟨hν.trans_lt (by simp)⟩
  have : IsProbabilityMeasure (gaussianRows k (n+1)) := by unfold gaussianRows; infer_instance
  have hb : Measurable (fun q : (Fin k → Fin (n+1) → ℝ) × Coordinate n =>
      projectVector q.1 (normalizedChart Q q.2)) :=
    continuous_projectVector.measurable.comp (measurable_fst.prodMk
      ((normalizedChart_measurable Q).comp measurable_snd))
  have : IsLocallyFiniteMeasure ((gaussianRows k (n+1)).prod (volume : Measure (Fin k → ℝ))) :=
    Measure.prod.instIsLocallyFiniteMeasure
  have H := exactMixtureLaw_borel_test (gaussianRows k (n+1)) ν _ hb hm
    (weightedProjectionMoment n k m B) (weightedProjectionMoment_ne_top _ _ _ _)
    (actual_smoothedProjection_moment hn hk hm hdim Q μ hsupport hB hspread h hh hnorm)
    g hg hg0 hg1
  simpa only [exactMixtureLaw, lintegral_map hg.ennreal_ofReal (measurable_fst.prodMk hb)] using H

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

lemma mul_log_div_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x/y) ≤ x^2/y-x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have h := Real.log_le_sub_one_of_pos (div_pos (lt_of_le_of_ne hx (Ne.symm hx0)) hy)
  have H := mul_le_mul_of_nonneg_left h hx
  simpa only [mul_sub, mul_one, pow_two, mul_div_assoc] using H

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

lemma xlog_upper_quadratic {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    xlog x ≤ x^2/a + (Real.log a-1)*x := by
  by_cases hz : x = 0
  · simp [hz,xlog_zero]
  have h := mul_log_div_le hx ha
  rw [Real.log_div hz ha.ne'] at h
  dsimp [xlog]
  nlinarith

lemma infoContribution_le_log_l2bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {L : ℝ} (hL : 0 < L) (hbound : (∫ x, (p x)^2 ∂μ) ≤ L^2) :
    infoContribution μ p ≤ 2*scoreMass μ p*(Real.log L-Real.log (scoreMass μ p)) := by
  have hP := scoreMass_nonneg μ p hp0
  by_cases hz : scoreMass μ p = 0
  · rw [infoContribution_zero_mass μ p hp hp0 hp1 hz,hz]; simp
  have hpos : 0 < scoreMass μ p := lt_of_le_of_ne hP (Ne.symm hz)
  let A := L^2 / scoreMass μ p
  have ha : 0 < A := div_pos (sq_pos_of_pos hL) hpos
  have hip := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hi2 : Integrable (fun x => (p x)^2) μ := by
    apply integrable_bounded_measurable μ _ (hp.pow_const 2) (C := 1)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hp0 x,hp1 x]
  have hil := integrable_xlog_probability μ p hp hp0 hp1
  have h := integral_mono hil ((hi2.div_const A).add (hip.const_mul (Real.log A-1)))
    (fun x => xlog_upper_quadratic (hp0 x) ha)
  have heq : (∫ x, (p x)^2/A+(Real.log A-1)*p x ∂μ) =
      (∫ x, (p x)^2 ∂μ)/A+(Real.log A-1)*scoreMass μ p := by
    rw [integral_add (hi2.div_const A) (hip.const_mul _),integral_div,integral_const_mul]
    rfl
  change (∫ x, xlog (p x) ∂μ) ≤ (∫ x, (p x)^2/A+(Real.log A-1)*p x ∂μ) at h
  rw [heq] at h
  have hb : (∫ x, (p x)^2 ∂μ)/A ≤ scoreMass μ p := by
    have h := div_le_div_of_nonneg_right hbound ha.le
    have he : L^2/A = scoreMass μ p := by dsimp [A]; field_simp
    exact he ▸ h
  have hlog : Real.log A = 2*Real.log L-Real.log (scoreMass μ p) := by
    simp [A,Real.log_div (pow_ne_zero _ hL.ne') hz,Real.log_pow]
  change (∫ x, xlog (p x) ∂μ) - scoreMass μ p * Real.log (scoreMass μ p) ≤ _
  rw [hlog] at h
  nlinarith

lemma finite_log_sum {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hb1 : ∑ i,b i = 1)
    (hz : ∀ i, b i = 0 → a i = 0) :
    xlog (∑ i,a i) ≤ ∑ i,a i * Real.log (a i/b i) :=
  log_sum_inequality a b ha hb hb1 hz

lemma log_ratio_mul {a b : ℝ} (hb : b ≠ 0) :
    a*Real.log (a/b) = xlog a-a*Real.log b := by
  by_cases ha : a = 0
  · simp [ha,xlog_zero]
  rw [Real.log_div ha hb]
  simp [xlog,mul_sub]

lemma neg_xlog_le_one {x : ℝ} (hx : 0 ≤ x) : -xlog x ≤ 1 := by
  have h := Real.self_sub_one_le_mul_log hx
  dsimp [xlog]
  linarith

lemma xlog_nonpos {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : xlog x ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos hx (Real.log_nonpos hx hx1)

lemma finite_entropy_mass_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    -(∑ i,xlog (a i)) ≤ (∑ i,a i)*Real.log (Fintype.card ι)-xlog (∑ i,a i) := by
  have hN : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := finite_log_sum a (fun _ => 1/(Fintype.card ι:ℝ)) ha
    (fun _ => by positivity) (by simp [hN.ne']) (fun _ hz => (ne_of_gt (one_div_pos.mpr hN) hz).elim)
  simp_rw [log_ratio_mul (by positivity : 1/(Fintype.card ι:ℝ) ≠ 0),Real.log_div one_ne_zero hN.ne',Real.log_one,zero_sub,
    mul_neg,sub_neg_eq_add,Finset.sum_add_distrib,← Finset.sum_mul] at h
  linarith

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ScoreBounds
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

lemma infoContribution_le_negative_xlog_mass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) :
    infoContribution μ p ≤ -xlog (scoreMass μ p) := by
  have h : (∫ x,xlog (p x) ∂μ) ≤ 0 := integral_nonpos (fun x => xlog_nonpos (hp0 x) (hp1 x))
  dsimp [infoContribution]
  linarith

lemma finiteInformation_le_entropy_mass {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (μ : Measure α) [IsFiniteMeasure μ] (p : ι → α → ℝ)
    (hp0 : ∀ i x,0 ≤ p i x) (hp1 : ∀ i x,p i x ≤ 1) :
    finiteInformation μ p ≤ (∑ i,scoreMass μ (p i))*Real.log (Fintype.card ι)-
      xlog (∑ i,scoreMass μ (p i)) := by
  calc
    _ ≤ ∑ i,-xlog (scoreMass μ (p i)) := Finset.sum_le_sum (fun i _ =>
      infoContribution_le_negative_xlog_mass μ _ (hp0 i) (hp1 i))
    _ = -(∑ i,xlog (scoreMass μ (p i))) := by simp
    _ ≤ _ := finite_entropy_mass_bound _ (fun i => scoreMass_nonneg μ _ (hp0 i))

lemma scoreMass_zero_of_sq_integral_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) (h : (∫ x,(p x)^2 ∂μ) ≤ 0) :
    scoreMass μ p = 0 := by
  have hi : Integrable (fun x => (p x)^2) μ := by
    apply integrable_bounded_measurable μ _ (hp.pow_const 2) (C := 1)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hp0 x,hp1 x]
  have hzero : (∫ x,(p x)^2 ∂μ) = 0 := le_antisymm h (integral_nonneg (fun _ => sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hzero
  have hpz : p =ᵐ[μ] 0 := by filter_upwards [hae] with x hx; simpa using hx
  simp [scoreMass,integral_congr_ae hpz]

lemma finiteInformation_good_bound {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ι → α → ℝ) (hp : ∀ i,Measurable (p i))
    (hp0 : ∀ i x,0 ≤ p i x) (hp1 : ∀ i x,p i x ≤ 1)
    (b : ι → ℝ) (hb0 : ∀ i,0 ≤ b i) (hb1 : ∑ i,b i = 1)
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ i,(∫ x,(p i x)^2 ∂μ) ≤ (A*(b i)^r)^2)
    (hmass : ∑ i,scoreMass μ (p i) ≤ 1) :
    finiteInformation μ p ≤ 2*Real.log A+(2-2*r)*Real.log (Fintype.card ι)-
      2*xlog (∑ i,scoreMass μ (p i)) := by
  let P := fun i => scoreMass μ (p i)
  have hP : ∀ i,0 ≤ P i := fun i => scoreMass_nonneg μ _ (hp0 i)
  have hz : ∀ i,b i = 0 → P i = 0 := by
    intro i hbi
    have h := hbound i
    simp only [hbi,Real.zero_rpow hr.ne',mul_zero,zero_pow (by norm_num : 2 ≠ 0)] at h
    exact scoreMass_zero_of_sq_integral_zero μ _ (hp i) (hp0 i) (hp1 i) h
  have hind (i : ι) : infoContribution μ (p i) ≤
      2*P i*Real.log A-2*r*(P i*Real.log (P i/b i))-(2-2*r)*xlog (P i) := by
    by_cases hPi : P i = 0
    · rw [infoContribution_zero_mass μ _ (hp i) (hp0 i) (hp1 i) hPi,hPi,xlog_zero]
      simp
    have hbi : 0 < b i := lt_of_le_of_ne (hb0 i) (Ne.symm (fun h => hPi (hz i h)))
    have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
    have hL : 0 < A*(b i)^r := mul_pos hAp (Real.rpow_pos_of_pos hbi r)
    have h := infoContribution_le_log_l2bound μ _ (hp i) (hp0 i) (hp1 i) hL (hbound i)
    rw [Real.log_mul hAp.ne' (Real.rpow_pos_of_pos hbi r).ne',Real.log_rpow hbi] at h
    rw [log_ratio_mul hbi.ne']
    dsimp only [xlog]
    change infoContribution μ (p i) ≤ 2*P i*(Real.log A+r*Real.log (b i)-Real.log (P i)) at h
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hind i)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul] at hsum
  have hls := finite_log_sum P b hP hb0 hb1 hz
  have hent := finite_entropy_mass_bound P hP
  have hc0 : 0 ≤ 2*r := by linarith
  have hc1 : 0 ≤ 2-2*r := by linarith
  have hc2 := mul_le_mul_of_nonneg_left hls hc0
  have hc3 := mul_le_mul_of_nonneg_left hent hc1
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogN : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := ι))
  have hmass' : ∑ i,P i ≤ 1 := hmass
  have h1 := mul_le_mul_of_nonneg_right hmass' hlogA
  have h2 := mul_le_mul_of_nonneg_right hmass' hlogN
  have h3 := mul_le_mul_of_nonneg_left h2 hc1
  change ∑ i,infoContribution μ (p i) ≤ _
  nlinarith

lemma binary_log_sum {a b P Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 < P) (hQ : 0 < Q) :
    xlog (a+b)-(a+b)*Real.log (P+Q) ≤
      xlog a-a*Real.log P+(xlog b-b*Real.log Q) := by
  have ht : 0 < P+Q := add_pos hP hQ
  have h := finite_log_sum (fun i : Fin 2 => if i = 0 then a else b)
    (fun i : Fin 2 => if i = 0 then P/(P+Q) else Q/(P+Q))
    (by intro i; split_ifs <;> assumption)
    (by intro i; split_ifs <;> positivity)
    (by simp [Fin.sum_univ_two]; field_simp)
    (by intro i; split_ifs
        · intro hz; exact ((div_pos hP ht).ne' hz).elim
        · intro hz; exact ((div_pos hQ ht).ne' hz).elim)
  simp only [Fin.sum_univ_two,ite_true,show (1 : Fin 2) ≠ 0 from by decide,ite_false] at h
  rw [log_ratio_mul (div_pos hP ht).ne',log_ratio_mul (div_pos hQ ht).ne',
    Real.log_div hP.ne' ht.ne',Real.log_div hQ.ne' ht.ne'] at h
  nlinarith

lemma infoContribution_add_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p q : α → ℝ)
    (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (hq0 : ∀ x,0 ≤ q x) (hpq1 : ∀ x,p x+q x ≤ 1) :
    infoContribution μ (fun x => p x+q x) ≤ infoContribution μ p+infoContribution μ q := by
  have hp1 : ∀ x,p x ≤ 1 := fun x => le_trans (le_add_of_nonneg_right (hq0 x)) (hpq1 x)
  have hq1 : ∀ x,q x ≤ 1 := fun x => le_trans (le_add_of_nonneg_left (hp0 x)) (hpq1 x)
  have hip := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa [abs_of_nonneg (hp0 x)] using hp1 x)
  have hiq := integrable_bounded_measurable μ q hq (C := 1) (fun x => by simpa [abs_of_nonneg (hq0 x)] using hq1 x)
  have hP := scoreMass_nonneg μ p hp0
  have hQ := scoreMass_nonneg μ q hq0
  have hmass : scoreMass μ (fun x => p x+q x) = scoreMass μ p+scoreMass μ q := integral_add hip hiq
  by_cases hP0 : scoreMass μ p = 0
  · have hz : p =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hp0 hip).mp hP0
    have hxl : (fun x => xlog (p x+q x)) =ᵐ[μ] (fun x => xlog (q x)) := by
      filter_upwards [hz] with x hx
      simp [hx]
    rw [infoContribution_zero_mass μ p hp hp0 hp1 hP0]
    simp only [infoContribution,integral_congr_ae hxl,hmass,hP0,zero_add,le_refl]
  by_cases hQ0 : scoreMass μ q = 0
  · have hz : q =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hq0 hiq).mp hQ0
    have hxl : (fun x => xlog (p x+q x)) =ᵐ[μ] (fun x => xlog (p x)) := by
      filter_upwards [hz] with x hx
      simp [hx]
    rw [infoContribution_zero_mass μ q hq hq0 hq1 hQ0]
    simp only [infoContribution,integral_congr_ae hxl,hmass,hQ0,add_zero,le_refl]
  have hPp : 0 < scoreMass μ p := lt_of_le_of_ne hP (Ne.symm hP0)
  have hQp : 0 < scoreMass μ q := lt_of_le_of_ne hQ (Ne.symm hQ0)
  have hilp := integrable_xlog_probability μ p hp hp0 hp1
  have hilq := integrable_xlog_probability μ q hq hq0 hq1
  have hilpq := integrable_xlog_probability μ (fun x => p x+q x) (hp.add hq)
    (fun x => add_nonneg (hp0 x) (hq0 x)) hpq1
  have h := integral_mono (hilpq.sub ((hip.add hiq).mul_const (Real.log (scoreMass μ p+scoreMass μ q))))
    ((hilp.sub (hip.mul_const (Real.log (scoreMass μ p)))).add (hilq.sub (hiq.mul_const (Real.log (scoreMass μ q)))))
    (fun x => binary_log_sum (hp0 x) (hq0 x) hPp hQp)
  change (∫ x, xlog (p x+q x)-(p x+q x)*Real.log (scoreMass μ p+scoreMass μ q) ∂μ) ≤
    ∫ x, (xlog (p x)-p x*Real.log (scoreMass μ p))+(xlog (q x)-q x*Real.log (scoreMass μ q)) ∂μ at h
  have hel : (∫ x, xlog (p x+q x)-(p x+q x)*Real.log (scoreMass μ p+scoreMass μ q) ∂μ) =
      (∫ x,xlog (p x+q x) ∂μ)-(∫ x,(p x+q x)*Real.log (scoreMass μ p+scoreMass μ q) ∂μ) :=
    integral_sub hilpq ((hip.add hiq).mul_const (Real.log (scoreMass μ p+scoreMass μ q)))
  have her : (∫ x, (xlog (p x)-p x*Real.log (scoreMass μ p))+(xlog (q x)-q x*Real.log (scoreMass μ q)) ∂μ) =
      (∫ x,xlog (p x)-p x*Real.log (scoreMass μ p) ∂μ)+(∫ x,xlog (q x)-q x*Real.log (scoreMass μ q) ∂μ) :=
    integral_add (hilp.sub (hip.mul_const (Real.log (scoreMass μ p)))) (hilq.sub (hiq.mul_const (Real.log (scoreMass μ q))))
  rw [hel,her,integral_sub hilp (hip.mul_const (Real.log (scoreMass μ p))), integral_sub hilq (hiq.mul_const (Real.log (scoreMass μ q)))] at h
  simp only [integral_mul_const,integral_add hip hiq] at h
  simpa only [infoContribution,xlog,scoreMass,integral_add hip hiq] using h

lemma finiteInformation_good_bad_bound {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (p q : ι → α → ℝ) (hp : ∀ i,Measurable (p i)) (hq : ∀ i,Measurable (q i))
    (hp0 : ∀ i x,0 ≤ p i x) (hq0 : ∀ i x,0 ≤ q i x)
    (hsum : ∀ x,∑ i,(p i x+q i x) = 1)
    (b : ι → ℝ) (hb0 : ∀ i,0 ≤ b i) (hb1 : ∑ i,b i = 1)
    {A r δ : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ i,(∫ x,(p i x)^2 ∂μ) ≤ (A*(b i)^r)^2)
    (hbad : ∑ i,scoreMass μ (q i) ≤ δ) :
    finiteInformation μ (fun i x => p i x+q i x) ≤
      2*Real.log A+(2-2*r+δ)*Real.log (Fintype.card ι)+3 := by
  have hpq1 : ∀ i x,p i x+q i x ≤ 1 := by
    intro i x
    rw [← hsum x]
    exact Finset.single_le_sum (fun j _ => add_nonneg (hp0 j x) (hq0 j x)) (Finset.mem_univ i)
  have hp1 : ∀ i x,p i x ≤ 1 := fun i x => le_trans (le_add_of_nonneg_right (hq0 i x)) (hpq1 i x)
  have hq1 : ∀ i x,q i x ≤ 1 := fun i x => le_trans (le_add_of_nonneg_left (hp0 i x)) (hpq1 i x)
  have hip : ∀ i,Integrable (p i) μ := fun i => integrable_bounded_measurable μ _ (hp i) (C := 1)
    (fun x => by simpa [abs_of_nonneg (hp0 i x)] using hp1 i x)
  have hiq : ∀ i,Integrable (q i) μ := fun i => integrable_bounded_measurable μ _ (hq i) (C := 1)
    (fun x => by simpa [abs_of_nonneg (hq0 i x)] using hq1 i x)
  have hmass : (∑ i,scoreMass μ (p i))+(∑ i,scoreMass μ (q i)) = 1 := by
    simp only [scoreMass,← integral_finsetSum _ (fun i _ => hip i),← integral_finsetSum _ (fun i _ => hiq i)]
    rw [← integral_add (integrable_finsetSum _ (fun i _ => hip i)) (integrable_finsetSum _ (fun i _ => hiq i))]
    simp_rw [← Finset.sum_add_distrib,hsum]
    simp
  have hPg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => scoreMass_nonneg μ _ (hp0 i))
  have hPb := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => scoreMass_nonneg μ _ (hq0 i))
  have hgood := finiteInformation_good_bound μ p hp hp0 hp1 b hb0 hb1 hA hr hr1 hbound (by linarith)
  have hbad' := finiteInformation_le_entropy_mass μ q hq0 hq1
  have hlogN : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := ι))
  have hb := mul_le_mul_of_nonneg_right hbad hlogN
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => infoContribution_add_le μ _ _ (hp i) (hq i) (hp0 i) (hq0 i) (hpq1 i))
  rw [Finset.sum_add_distrib] at h
  change finiteInformation μ (fun i x => p i x+q i x) ≤ finiteInformation μ p+finiteInformation μ q at h
  linarith [neg_xlog_le_one hPg,neg_xlog_le_one hPb]

lemma eLpNorm_eq_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ x,|f x| ≤ C) : eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x,(f x)^2 ∂μ)) := by
  have hmem : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun x => by simpa using hC x))
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞) hmem]
  simp only [ENNReal.toReal_ofNat,Real.norm_eq_abs,Real.rpow_two, sq_abs,Real.sqrt_eq_rpow,one_div]

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_QuadraticBounds
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
lemma l2bound_of_bounded_tests {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) {L : ℝ≥0∞}
    (hL : L ≠ ∞)
    (htest : ∀ h : α → ℝ, Measurable h → eLpNorm h 2 μ ≤ 1 →
      (∫⁻ x,ENNReal.ofReal |h x| *ENNReal.ofReal (p x) ∂μ) ≤ L) :
    (∫ x,(p x)^2 ∂μ) ≤ L.toReal^2 := by
  let S := ∫ x,(p x)^2 ∂μ
  have hS : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  by_cases hSz : S = 0
  · change S ≤ L.toReal^2
    rw [hSz]
    exact sq_nonneg _
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSp
  let h := fun x => p x/Real.sqrt S
  have hh : Measurable h := hp.div_const _
  have hh0 : ∀ x,0 ≤ h x := fun x => div_nonneg (hp0 x) hs.le
  have hhb : ∀ x,|h x| ≤ 1/Real.sqrt S := fun x => by
    rw [abs_of_nonneg (hh0 x)]
    exact div_le_div_of_nonneg_right (hp1 x) hs.le
  have hsqi : (∫ x,(h x)^2 ∂μ) = 1 := by
    simp_rw [h,div_pow]
    rw [integral_div,Real.sq_sqrt hS]
    exact div_self hSz
  have hnorm : eLpNorm h 2 μ ≤ 1 := by
    rw [eLpNorm_eq_sqrt_integral_sq μ h hh hhb,hsqi]
    simp
  have htest' := htest h hh hnorm
  have hiprod : Integrable (fun x => |h x| *p x) μ := by
    apply integrable_bounded_measurable μ _ (hh.abs.mul hp) (C := 1/Real.sqrt S)
    intro x
    change abs (|h x| * p x) ≤ 1/Real.sqrt S
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (hp0 x))]
    exact (mul_le_mul_of_nonneg_left (hp1 x) (abs_nonneg _)).trans (by simpa using hhb x)
  have hint : (∫ x,|h x| *p x ∂μ) = Real.sqrt S := by
    simp_rw [abs_of_nonneg (hh0 _)]
    have he : (fun x => h x*p x) = fun x => (p x)^2/Real.sqrt S := by funext x; dsimp [h]; ring
    rw [he,integral_div]
    change S/Real.sqrt S = Real.sqrt S
    rw [div_eq_iff hs.ne']
    simpa [pow_two] using (Real.sq_sqrt hS).symm
  have he : (∫⁻ x,ENNReal.ofReal |h x| *ENNReal.ofReal (p x) ∂μ) = ENNReal.ofReal (Real.sqrt S) := by
    simp_rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hiprod (ae_of_all _ (fun x => mul_nonneg (abs_nonneg _) (hp0 x))),hint]
  rw [he] at htest'
  have hreal := ENNReal.toReal_mono hL htest'
  rw [ENNReal.toReal_ofReal hs.le] at hreal
  have hsq : (Real.sqrt S)^2 ≤ L.toReal^2 := pow_le_pow_left₀ hs.le hreal 2
  rwa [Real.sq_sqrt hS] at hsq

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_GaussianTails
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
lemma gaussian_exp_square_integral :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2/4)) ∂gaussianReal 0 1) =
      ENNReal.ofReal (Real.sqrt 2) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul₀ (measurable_gaussianPDF _ _).aemeasurable (by fun_prop)]
  have he (x : ℝ) : gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (x^2/4)) =
      ENNReal.ofReal (Real.sqrt 2) * gaussianPDF 0 2 x := by
    simp only [gaussianPDF, gaussianPDFReal, NNReal.coe_one, NNReal.coe_ofNat,
      sub_zero, mul_one]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      mul_assoc, ← Real.exp_add]
    congr 1
    have hs : Real.sqrt (2*Real.pi*2) = Real.sqrt 2 * Real.sqrt (2*Real.pi) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    have hex : -x^2/2+x^2/4 = -x^2/(2*2) := by ring
    rw [hex, hs, mul_inv]
    field_simp
  simp only [Pi.mul_apply]
  simp_rw [he]
  rw [lintegral_const_mul _ (measurable_gaussianPDF _ _), lintegral_gaussianPDF_eq_one 0 (by norm_num), mul_one]

lemma sqrt_two_le_exp_half : Real.sqrt 2 ≤ Real.exp (1/2:ℝ) := by
  have h := Real.add_one_le_exp (1:ℝ)
  have he : (Real.exp (1/2:ℝ))^2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith [Real.exp_pos (1/2:ℝ), Real.sqrt_nonneg (2:ℝ)]

lemma gaussian_scalar_scaled_exp_le {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp ((s*x)^2/16)) ∂gaussianReal 0 1) ≤
      ENNReal.ofReal (Real.exp (1/2:ℝ)) := by
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2/4)) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hh : s^2 ≤ 4 := by nlinarith
      have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg x)
      nlinarith
    _ = ENNReal.ofReal (Real.sqrt 2) := gaussian_exp_square_integral
    _ ≤ _ := ENNReal.ofReal_le_ofReal sqrt_two_le_exp_half

lemma stdGaussian_inner_eq_scaled {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (innerSL ℝ v) =
      (gaussianReal 0 1).map (fun x : ℝ => ‖v‖*x) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one, innerSL_apply_norm]
  congr 1
  apply NNReal.eq
  simp only [Real.coe_toNNReal']
  simp

lemma stdGaussian_inner_exp_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((⟪v,x⟫)^2/16))
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ENNReal.ofReal (Real.exp (1/2:ℝ)) := by
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (x^2/16))) := by fun_prop
  change (∫⁻ x, ENNReal.ofReal (Real.exp (((innerSL ℝ v) x)^2/16)) ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ _
  rw [← lintegral_map hf (innerSL ℝ v).measurable, stdGaussian_inner_eq_scaled,
    lintegral_map hf (by fun_prop)]
  exact gaussian_scalar_scaled_exp_le (norm_nonneg v) hv

lemma iidGaussian_linear_exp_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    (∫⁻ x : Fin d → ℝ, ENNReal.ofReal (Real.exp ((∑ i,x i*v i)^2/16))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ ENNReal.ofReal (Real.exp (1/2:ℝ)) := by
  have h := stdGaussian_inner_exp_le v hv
  rw [← map_pi_eq_stdGaussian,lintegral_map (by fun_prop) (by fun_prop)] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial, WithLp.ofLp_toLp, mul_comm] using h

lemma gaussianRows_exp_square_le {k d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    (∫⁻ X, ENNReal.ofReal (Real.exp ((∑ r,(projectVector X v r)^2)/16)) ∂gaussianRows k d) ≤
      ENNReal.ofReal (Real.exp ((k:ℝ)/2)) := by
  have hfun (X : Fin k → Fin d → ℝ) :
      ENNReal.ofReal (Real.exp ((∑ r,(projectVector X v r)^2)/16)) =
        ∏ r, ENNReal.ofReal (Real.exp ((∑ i,X r i*v i)^2/16)) := by
    rw [Finset.sum_div,Real.exp_sum,ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    rfl
  simp_rw [hfun]
  rw [gaussianRows,lintegral_pi_product (Measure.pi (fun _ : Fin d => gaussianReal 0 1))
    (fun x : Fin d → ℝ => ENNReal.ofReal (Real.exp ((∑ i,x i*v i)^2/16))) (by fun_prop) k]
  have h := pow_le_pow_left' (iidGaussian_linear_exp_le v hv) k
  have he : ENNReal.ofReal (Real.exp (1/2:ℝ))^k = ENNReal.ofReal (Real.exp ((k:ℝ)/2)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 2
    ring
  exact he ▸ h

lemma gaussianRows_tail {k d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    gaussianRows k d {X | (16:ℝ)*k < ∑ r,(projectVector X v r)^2} ≤
      ENNReal.ofReal (Real.exp (-(k:ℝ)/2)) := by
  let f := fun X : Fin k → Fin d → ℝ => ENNReal.ofReal (Real.exp ((∑ r,(projectVector X v r)^2)/16))
  have hf : Measurable f := by dsimp [f,projectVector]; fun_prop
  have hsub : {X : Fin k → Fin d → ℝ | (16:ℝ)*k < ∑ r,(projectVector X v r)^2} ⊆
      {X | ENNReal.ofReal (Real.exp (k:ℝ)) ≤ f X} := by
    intro X hx
    change (16:ℝ)*k < ∑ r,(projectVector X v r)^2 at hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have hm := meas_ge_le_lintegral_div (μ := gaussianRows k d) hf.aemeasurable
    (by positivity : ENNReal.ofReal (Real.exp (k:ℝ)) ≠ 0) ENNReal.ofReal_ne_top
  have hbound := ENNReal.div_le_div_right (gaussianRows_exp_square_le (k := k) v hv) (ENNReal.ofReal (Real.exp (k:ℝ)))
  have he : ENNReal.ofReal (Real.exp ((k:ℝ)/2))/ENNReal.ofReal (Real.exp (k:ℝ)) =
      ENNReal.ofReal (Real.exp (-(k:ℝ)/2)) := by
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _),← Real.exp_sub]
    congr 2
    ring
  exact (measure_mono hsub).trans (hm.trans (he ▸ hbound))

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
lemma projection_constant_bound {n k m : ℕ} (hm : 1 < m) (hkn : k ≤ n)
    {B T V : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T) (hV : 1 ≤ V) {v : ℝ} (hv : 0 ≤ v) (hvV : v ≤ V^k) :
    ((2:ℝ)^(k*(m-1))*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1))^(m-1))^(1/(m:ℝ)) * v^(1-1/(m:ℝ)) ≤
      (4*T*V)^(n+1)*Real.sqrt B := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hV0 : 0 < V := lt_of_lt_of_le (by norm_num) hV
  have hm0 : (0:ℝ) < m := by exact_mod_cast lt_trans Nat.zero_lt_one hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm.le
  have hr : 0 ≤ 1-1/(m:ℝ) := sub_nonneg.mpr ((one_div_le_one_div_of_le (by norm_num) hm1).trans_eq (by norm_num))
  have hTn : 1 ≤ T^n := one_le_pow₀ hT
  have hU : 1 ≤ (B*T^n)^(1/2:ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
  have hbase : 1 ≤ (2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)) := by
    have hp : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have hp' : 1 ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    apply one_le_mul_of_one_le_of_one_le hp
    exact le_add_of_nonneg_right (by positivity)
  have he : ((2:ℝ)^(k*(m-1))*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1))^(m-1))^(1/(m:ℝ)) =
      ((2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)))^(((m-1:ℕ):ℝ)/(m:ℝ)) := by
    rw [pow_mul,← mul_pow,← Real.rpow_natCast_mul (by linarith : 0 ≤ (2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)))]
    congr 1
    ring
  have hroot := Real.rpow_le_self_of_one_le hbase (show ((m-1:ℕ):ℝ)/(m:ℝ) ≤ 1 by
    rw [div_le_one hm0]
    exact_mod_cast Nat.sub_le m 1)
  have hu : (B*T^n)^(1/2:ℝ) ≤ Real.sqrt B*T^n := by
    rw [Real.mul_rpow hB0.le (pow_nonneg hT0.le _),← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hTn (by norm_num)) (Real.sqrt_nonneg _)
  have hb : (2:ℝ)^k*(1+(B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1)) ≤ (4:ℝ)^(k+1)*(Real.sqrt B*T^n) := by
    have hp' : 1 ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    have hu0 : 0 ≤ (B*T^n)^(1/2:ℝ) := Real.rpow_nonneg (mul_nonneg hB0.le (pow_nonneg hT0.le _)) _
    calc
      _ ≤ (2:ℝ)^k*(2*((B*T^n)^(1/2:ℝ)*(2:ℝ)^(k+1))) := by gcongr; nlinarith
      _ = (4:ℝ)^(k+1)*(B*T^n)^(1/2:ℝ) := by
        have hp : (4:ℝ)^(k+1) = (2:ℝ)^(k+1)*(2:ℝ)^(k+1) := by rw [← mul_pow]; norm_num
        rw [hp,pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (by positivity)
  have hvb : v^(1-1/(m:ℝ)) ≤ V^k :=
    (Real.rpow_le_rpow hv hvV hr).trans (Real.rpow_le_self_of_one_le (one_le_pow₀ hV) (by have := one_div_nonneg.mpr hm0.le; linarith))
  rw [he]
  calc
    _ ≤ ((4:ℝ)^(k+1)*(Real.sqrt B*T^n))*V^k := mul_le_mul (hroot.trans hb) hvb (Real.rpow_nonneg hv _) (by positivity)
    _ ≤ ((4:ℝ)^(n+1)*(Real.sqrt B*T^(n+1)))*V^(n+1) := by
      have h4 : (4:ℝ)^(k+1) ≤ 4^(n+1) := pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hkn 1)
      have hTpow : T^n ≤ T^(n+1) := pow_le_pow_right₀ hT (Nat.le_succ n)
      have hVpow : V^k ≤ V^(n+1) := pow_le_pow_right₀ hV (by omega)
      exact mul_le_mul (mul_le_mul h4 (mul_le_mul_of_nonneg_left hTpow (Real.sqrt_nonneg B))
        (by positivity) (by positivity)) hVpow (by positivity) (by positivity)
    _ = _ := by rw [mul_pow,mul_pow]; ring

lemma lintegral_weighted_average {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (f : β × α → ℝ) (hf : Measurable f) (hf0 : ∀ q,0 ≤ f q) (hf1 : ∀ q,f q ≤ 1)
    (h : α → ℝ) (hh : Measurable h) :
    (∫⁻ q, ENNReal.ofReal (f q) ∂ν.prod (μ.withDensity (fun x => ENNReal.ofReal |h x|))) =
      ∫⁻ x,ENNReal.ofReal |h x| * ENNReal.ofReal (∫ y,f (y,x) ∂ν) ∂μ := by
  have : SFinite (μ.withDensity (fun x => ENNReal.ofReal |h x|)) := inferInstance
  rw [lintegral_prod_symm _ hf.ennreal_ofReal.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul μ hh.abs.ennreal_ofReal]
  · apply lintegral_congr
    intro x
    change ENNReal.ofReal |h x| * _ = ENNReal.ofReal |h x| * _
    congr 1
    have hi := integrable_bounded_measurable ν (fun y => f (y,x))
      (hf.comp (measurable_id.prodMk measurable_const)) (C := 1) (fun y => by simpa [abs_of_nonneg (hf0 _)] using hf1 (y,x))
    exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => hf0 (y,x)))).symm
  · exact hf.ennreal_ofReal.lintegral_prod_left'

lemma actual_good_score_l2bound {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (g : (Fin k → Fin (n+1) → ℝ) × (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hg0 : ∀ q,0 ≤ g q) (hg1 : ∀ q,g q ≤ 1)
    (hfinite : (∫⁻ q,ENNReal.ofReal (g q) ∂(gaussianRows k (n+1)).prod volume) ≠ ∞) :
    let p := fun z => ∫ X,g (X,projectVector X (normalizedChart Q z)) ∂gaussianRows k (n+1)
    (∫ z,(p z)^2 ∂μ) ≤
      ((weightedProjectionMoment n k m B)^(1/(m:ℝ)) *
        (∫⁻ q, ENNReal.ofReal (g q) ∂(gaussianRows k (n+1)).prod volume)^(1-1/(m:ℝ))).toReal^2 := by
  let f := fun q : (Fin k → Fin (n+1) → ℝ) × Coordinate n =>
    g (q.1,projectVector q.1 (normalizedChart Q q.2))
  have hf : Measurable f := hg.comp (measurable_fst.prodMk (continuous_projectVector.measurable.comp
    (measurable_fst.prodMk ((normalizedChart_measurable Q).comp measurable_snd))))
  let p := fun z => ∫ X,f (X,z) ∂gaussianRows k (n+1)
  have : IsProbabilityMeasure (gaussianRows k (n+1)) := by unfold gaussianRows; infer_instance
  have hp : Measurable p := hf.stronglyMeasurable.integral_prod_left'.measurable
  have hp0 : ∀ z,0 ≤ p z := fun _ => integral_nonneg (fun _ => hg0 _)
  have hp1 : ∀ z,p z ≤ 1 := by
    intro z
    have hi := integrable_bounded_measurable (gaussianRows k (n+1)) (fun X => f (X,z))
      (hf.comp (measurable_id.prodMk measurable_const)) (C := 1)
      (fun _ => by dsimp [f]; rw [abs_of_nonneg (hg0 _)]; exact hg1 _)
    simpa [p] using integral_mono hi (integrable_const (1:ℝ)) (fun X => hg1 (X,projectVector X (normalizedChart Q z)))
  refine l2bound_of_bounded_tests μ p hp hp0 hp1 ?_ ?_
  · apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (weightedProjectionMoment_ne_top _ _ _ _)
    · exact ENNReal.rpow_ne_top_of_nonneg (by
        have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm.le
        exact sub_nonneg.mpr ((one_div_le_one_div_of_le (by norm_num) hm1).trans_eq (by norm_num))) hfinite
  · intro h hh hnorm
    have H := actual_projection_borel_test hn hk hm hdim Q μ hsupport hB hspread h hh hnorm g hg hg0 hg1
    rw [lintegral_weighted_average μ (gaussianRows k (n+1)) f hf (fun _ => hg0 _) (fun _ => hg1 _) h hh] at H
    exact H

lemma measurableSet_goodLabels (k : ℕ) : MeasurableSet (goodLabels k) := by
  unfold goodLabels
  apply measurableSet_le _ measurable_const
  fun_prop

lemma goodLabels_eq_preimage (k : ℕ) : goodLabels k =
    (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (4*Real.sqrt k) := by
  ext u
  simp only [goodLabels,mem_ofPred_eq,mem_preimage,Metric.mem_closedBall,dist_zero_right]
  have he : ‖WithLp.toLp 2 u‖^2 = ∑ i,(u i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  have hs := Real.sq_sqrt (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hn := norm_nonneg (WithLp.toLp 2 u)
  have hp := Real.sqrt_nonneg (k:ℝ)
  constructor <;> intro h <;> nlinarith

lemma volume_goodLabels_ne_top (k : ℕ) : volume (goodLabels k) ≠ ∞ := by
  rw [goodLabels_eq_preimage,(PiLp.volume_preserving_toLp (Fin k)).measure_preimage (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet)]
  exact ne_of_lt (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) _).measure_lt_top

lemma volume_goodLabels_pos {k : ℕ} (hk : 0 < k) : 0 < volume (goodLabels k) := by
  rw [goodLabels_eq_preimage,(PiLp.volume_preserving_toLp (Fin k)).measure_preimage (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet)]
  apply lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin k)) (by positivity : 0 < 4*Real.sqrt (k:ℝ)))
  exact measure_mono Metric.ball_subset_closedBall

lemma labelVolumeConstant_ge_one : 1 ≤ labelVolumeConstant := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hp : 1 ≤ Real.sqrt Real.pi := (Real.le_sqrt (by norm_num) Real.pi_pos.le).mpr (by nlinarith [Real.pi_gt_three])
  unfold labelVolumeConstant
  nlinarith

lemma volume_goodLabels_le {k : ℕ} (hk : 0 < k) :
    volume.real (goodLabels k) ≤ labelVolumeConstant^k := by
  rw [measureReal_def,goodLabels_eq_preimage,
    (PiLp.volume_preserving_toLp (Fin k)).measure_preimage (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet)]
  have h := euclidean_closedBall_volume_le k hk (0 : EuclideanSpace ℝ (Fin k))
    (r := 4*Real.sqrt k) (by positivity)
  have hp : Real.sqrt (k:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  change volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (4*Real.sqrt k)) ≤ _
  refine h.trans_eq ?_
  unfold labelVolumeConstant
  congr 1
  field_simp

lemma normalized_label_tail {n k : ℕ} (hn : 0 < n) (Q : Cell n) {z : Coordinate n}
    (hz : z ∈ cellSet Q) :
    gaussianRows k (n+1) {X | projectVector X (normalizedChart Q z) ∉ goodLabels k} ≤
      ENNReal.ofReal (Real.exp (-(k:ℝ)/2)) := by
  simpa only [goodLabels,mem_ofPred_eq,not_le] using gaussianRows_tail (k := k)
    (normalizedChart Q z) (normalizedChart_norm_le hn Q hz)

lemma measurable_averagedScores {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [SFinite ν] (f : β × α → ι → ℝ) (hf : ∀ i,Measurable (fun q => f q i)) (i : ι) :
    Measurable (averagedScores ν f i) := (hf i).stronglyMeasurable.integral_prod_left'.measurable

lemma integrable_score_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : β × α → ℝ) (hf : Measurable f)
    (hf0 : ∀ q,0 ≤ f q) (hf1 : ∀ q,f q ≤ 1) (x : α) : Integrable (fun y => f (y,x)) ν :=
  integrable_bounded_measurable ν _ (hf.comp (measurable_id.prodMk measurable_const))
    (C := 1) (fun _ => by rw [abs_of_nonneg (hf0 _)]; exact hf1 _)

lemma averagedScores_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : β × α → ι → ℝ)
    (hf : ∀ i,Measurable (fun q => f q i)) (hf0 : ∀ q i,0 ≤ f q i) (hf1 : ∀ q i,f q i ≤ 1) :
    (∀ i x,0 ≤ averagedScores ν f i x) ∧ (∀ i x,averagedScores ν f i x ≤ 1) := by
  constructor
  · exact fun _ _ => integral_nonneg (fun _ => hf0 _ _)
  · intro i x
    simpa [averagedScores] using
      integral_mono (integrable_score_section ν _ (hf i) (fun _ => hf0 _ _) (fun _ => hf1 _ _) x)
        (integrable_const (1:ℝ)) (fun y => hf1 (y,x) i)

lemma averagedScores_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Fintype ι]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : β × α → ι → ℝ)
    (hf : ∀ i,Measurable (fun q => f q i)) (hf0 : ∀ q i,0 ≤ f q i) (hf1 : ∀ q i,f q i ≤ 1)
    (hfs : ∀ q,∑ i,f q i = 1) (x : α) : ∑ i,averagedScores ν f i x = 1 := by
  unfold averagedScores
  rw [← integral_finsetSum _ (fun i _ => integrable_score_section ν _ (hf i) (fun _ => hf0 _ _) (fun _ => hf1 _ _) x)]
  simp [hfs]

lemma measurableSet_goodRegion (k d : ℕ) : MeasurableSet (goodRegion k d) :=
  MeasurableSet.univ.prod (measurableSet_goodLabels k)

lemma reference_goodRegion_volume (k d : ℕ) :
    (gaussianRows k d).prod volume (goodRegion k d) = volume (goodLabels k) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  simp [goodRegion,Measure.prod_prod]

lemma gaussianRows_probability (k d : ℕ) : IsProbabilityMeasure (gaussianRows k d) := by
  unfold gaussianRows
  infer_instance

lemma finite_reference_scores {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (ν : Measure β) (S : Set β) (hS : MeasurableSet S) (hSf : ν S ≠ ∞) (hSp : 0 < ν S)
    (g : β → ι → ℝ) (hg : ∀ i,Measurable (fun x => g x i))
    (hg0 : ∀ x i,0 ≤ g x i) (hg1 : ∀ x i,g x i ≤ 1) (hgs : ∀ x,∑ i,g x i = 1) :
    let b := fun i => (∫ x in S,g x i ∂ν)/ν.real S
    (∀ i,0 ≤ b i) ∧ (∑ i,b i = 1) ∧
    (∀ i,(∫⁻ x,ENNReal.ofReal (S.indicator (fun x => g x i) x) ∂ν) = ENNReal.ofReal (ν.real S*b i)) := by
  have : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using lt_top_iff_ne_top.mpr hSf⟩
  have hV : 0 < ν.real S := ENNReal.toReal_pos hSp.ne' hSf
  have hi (i : ι) : Integrable (fun x => g x i) (ν.restrict S) :=
    integrable_bounded_measurable _ _ (hg i) (C := 1) (fun _ => by rw [abs_of_nonneg (hg0 _ _)]; exact hg1 _ _)
  dsimp only
  refine ⟨fun _ => div_nonneg (integral_nonneg (fun _ => hg0 _ _)) hV.le,?_,?_⟩
  · rw [← Finset.sum_div,← integral_finsetSum _ (fun i _ => hi i)]
    simp [hgs,measureReal_restrict_apply MeasurableSet.univ,hV.ne']
  · intro i
    have he : (fun x => ENNReal.ofReal (S.indicator (fun x => g x i) x)) = S.indicator (fun x => ENNReal.ofReal (g x i)) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    rw [he,lintegral_indicator hS]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ (fun _ => hg0 _ _))]
    congr 1
    field_simp

lemma weightedProjectionMoment_toReal {n k m : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    (weightedProjectionMoment n k m B).toReal =
      (2:ℝ)^(k*(m-1))*(1+(B*tubeConstant^n)^(1/2:ℝ)*(2:ℝ)^(k+1))^(m-1) := by
  unfold weightedProjectionMoment tubeWeightConstant
  rw [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_add (by simp)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_one,ENNReal.toReal_mul,← ENNReal.toReal_rpow]
  simp only [ENNReal.toReal_ofReal (pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) _),
    ENNReal.toReal_ofReal (mul_nonneg hB (pow_nonneg (show 0 ≤ tubeConstant by linarith [tubeConstant_ge_one]) _))]

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_BlockInformation
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
lemma normalized_block_information {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (hkn : k ≤ n) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 1 ≤ B) (hspread : DyadicSpread μ Q B)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : (Fin k → Fin (n+1) → ℝ) × (Fin k → ℝ) → ι → ℝ)
    (hg : ∀ i,Measurable (fun q => g q i)) (hg0 : ∀ q i,0 ≤ g q i)
    (hgs : ∀ q,∑ i,g q i = 1) :
    finiteInformation μ (fun i z => ∫ X,g (X,projectVector X (normalizedChart Q z)) i ∂gaussianRows k (n+1)) ≤
      blockInformationConstant*(n+1)+Real.log B+
        (2/(m:ℝ)+Real.exp (-(k:ℝ)/2))*Real.log (Fintype.card ι) := by
  classical
  let ν := gaussianRows k (n+1)
  let S := goodRegion k (n+1)
  have hS : MeasurableSet S := measurableSet_goodRegion _ _
  have : IsProbabilityMeasure ν := gaussianRows_probability _ _
  have hg1 : ∀ q i,g q i ≤ 1 := by
    intro q i
    rw [← hgs q]
    exact Finset.single_le_sum (fun j _ => hg0 q j) (Finset.mem_univ i)
  let a := fun q : (Fin k → Fin (n+1) → ℝ) × Coordinate n => (q.1,projectVector q.1 (normalizedChart Q q.2))
  have ha : Measurable a := measurable_fst.prodMk (continuous_projectVector.measurable.comp
    (measurable_fst.prodMk ((normalizedChart_measurable Q).comp measurable_snd)))
  let gp := fun q i => S.indicator (fun q => g q i) q
  let gq := fun q i => Sᶜ.indicator (fun q => g q i) q
  have hgp : ∀ i,Measurable (fun q => gp q i) := fun i => (hg i).indicator hS
  have hgq : ∀ i,Measurable (fun q => gq q i) := fun i => (hg i).indicator hS.compl
  have hgp0 : ∀ q i,0 ≤ gp q i := fun q _ => Set.indicator_nonneg (fun _ _ => hg0 _ _) q
  have hgq0 : ∀ q i,0 ≤ gq q i := fun q _ => Set.indicator_nonneg (fun _ _ => hg0 _ _) q
  have hgp1 : ∀ q i,gp q i ≤ 1 := by intro q i; by_cases h : q ∈ S <;> simp [gp,h,hg1]
  have hgq1 : ∀ q i,gq q i ≤ 1 := by intro q i; by_cases h : q ∈ S <;> simp [gq,h,hg1]
  let p := averagedScores ν (fun q i => gp (a q) i)
  let q := averagedScores ν (fun q i => gq (a q) i)
  have hp : ∀ i,Measurable (p i) := measurable_averagedScores _ _ (fun i => (hgp i).comp ha)
  have hq : ∀ i,Measurable (q i) := measurable_averagedScores _ _ (fun i => (hgq i).comp ha)
  have hpb := averagedScores_bounds ν (fun q i => gp (a q) i) (fun i => (hgp i).comp ha) (fun _ _ => hgp0 _ _) (fun _ _ => hgp1 _ _)
  have hqb := averagedScores_bounds ν (fun q i => gq (a q) i) (fun i => (hgq i).comp ha) (fun _ _ => hgq0 _ _) (fun _ _ => hgq1 _ _)
  have hpq : ∀ i z,p i z+q i z = ∫ X,g (X,projectVector X (normalizedChart Q z)) i ∂ν := by
    intro i z
    dsimp only [p,q,averagedScores]
    rw [← integral_add]
    rotate_left
    · exact integrable_score_section ν _ ((hgp i).comp ha) (fun _ => hgp0 _ _) (fun _ => hgp1 _ _) z
    · exact integrable_score_section ν _ ((hgq i).comp ha) (fun _ => hgq0 _ _) (fun _ => hgq1 _ _) z
    apply integral_congr_ae
    filter_upwards [] with X
    have he : gp (a (X,z)) i+gq (a (X,z)) i = g (a (X,z)) i := by
      by_cases h : a (X,z) ∈ S <;> simp [gp,gq,h]
    exact he
  have hpqs : ∀ z,∑ i,(p i z+q i z) = 1 := by
    intro z
    simp_rw [hpq]
    exact averagedScores_sum ν (fun q i => g (a q) i) (fun i => (hg i).comp ha) (fun _ _ => hg0 _ _) (fun _ _ => hg1 _ _) (fun _ => hgs _) z
  have hvol : ν.prod volume S = volume (goodLabels k) := reference_goodRegion_volume _ _
  let v := (ν.prod volume).real S
  have hvp : 0 < v := ENNReal.toReal_pos (by rw [hvol]; exact (volume_goodLabels_pos hk).ne') (by rw [hvol]; exact volume_goodLabels_ne_top _)
  let b := fun i => (∫ q in S,g q i ∂ν.prod volume)/v
  obtain ⟨hb0,hbs,hbi⟩ := finite_reference_scores (ν.prod volume) S hS
    (by rw [hvol]; exact volume_goodLabels_ne_top _) (by rw [hvol]; exact volume_goodLabels_pos hk) g hg hg0 hg1 hgs
  change (∀ i,0 ≤ b i) at hb0
  change (∑ i,b i = 1) at hbs
  change ∀ i,(∫⁻ q,ENNReal.ofReal (gp q i) ∂ν.prod volume) = ENNReal.ofReal (v*b i) at hbi
  let A := (4*tubeConstant*labelVolumeConstant)^(n+1)*Real.sqrt B
  let r : ℝ := 1-1/(m:ℝ)
  have hm0 : (0:ℝ) < m := by exact_mod_cast lt_trans Nat.zero_lt_one hm
  have hm1 : (1:ℝ) < m := by exact_mod_cast hm
  have hr : 0 < r := by dsimp [r]; rw [sub_pos]; exact (div_lt_one hm0).mpr hm1
  have hr1 : r ≤ 1 := by dsimp [r]; have := one_div_nonneg.mpr hm0.le; linarith
  have hbase : 1 ≤ 4*tubeConstant*labelVolumeConstant := by nlinarith [tubeConstant_ge_one,labelVolumeConstant_ge_one]
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase) ((Real.le_sqrt (by norm_num) (by linarith : 0 ≤ B)).mpr (by simpa using hB))
  have hbound : ∀ i,(∫ z,(p i z)^2 ∂μ) ≤ (A*(b i)^r)^2 := by
    intro i
    have H := actual_good_score_l2bound hn hk hm hdim Q μ hsupport (by linarith : 0 ≤ B) hspread
      (fun q => gp q i) (hgp i) (fun _ => hgp0 _ _) (fun _ => hgp1 _ _) (by rw [hbi i]; exact ENNReal.ofReal_ne_top)
    apply H.trans
    apply pow_le_pow_left₀ ENNReal.toReal_nonneg
    rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,hbi i,← ENNReal.toReal_rpow,ENNReal.toReal_ofReal (mul_nonneg hvp.le (hb0 i)),weightedProjectionMoment_toReal (by linarith)]
    rw [Real.mul_rpow hvp.le (hb0 i),← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hb0 i) _)
    exact projection_constant_bound hm hkn hB tubeConstant_ge_one labelVolumeConstant_ge_one hvp.le
      (by simpa only [v,measureReal_def,hvol] using volume_goodLabels_le hk)
  have hbad : ∑ i,scoreMass μ (q i) ≤ Real.exp (-(k:ℝ)/2) := by
    have hqi (i : ι) : Integrable (q i) μ := integrable_bounded_measurable μ _ (hq i) (C := 1)
      (fun z => by rw [abs_of_nonneg (hqb.1 i z)]; exact hqb.2 i z)
    unfold scoreMass
    rw [← integral_finsetSum _ (fun i _ => hqi i)]
    apply le_trans (integral_mono_ae (integrable_finsetSum _ (fun i _ => hqi i)) (integrable_const (Real.exp (-(k:ℝ)/2))) ?_) (by simp)
    have hsupp : ∀ᵐ z ∂μ,z ∈ cellSet Q := ae_iff.mpr hsupport
    filter_upwards [hsupp] with z hz
    change ∑ i,(∫ X,gq (a (X,z)) i ∂ν) ≤ Real.exp (-(k:ℝ)/2)
    rw [← integral_finsetSum]
    rotate_left
    · intro i _
      exact integrable_score_section ν _ ((hgq i).comp ha) (fun _ => hgq0 _ _) (fun _ => hgq1 _ _) z
    have he : (fun X => ∑ i,gq (a (X,z)) i) = {X | projectVector X (normalizedChart Q z) ∉ goodLabels k}.indicator (fun _ => (1:ℝ)) := by
      funext X
      by_cases h : projectVector X (normalizedChart Q z) ∈ goodLabels k
      · simp [gq,a,S,goodRegion,h]
      · simp [gq,a,S,goodRegion,h,hgs]
    rw [he,integral_indicator]
    · simp only [integral_const,smul_eq_mul,mul_one]
      apply ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
      simpa only [Measure.restrict_apply_univ] using (normalized_label_tail (k := k) hn Q hz)
    · exact ((measurableSet_goodLabels k).preimage (continuous_projectVector.measurable.comp (measurable_id.prodMk measurable_const))).compl
  have H := finiteInformation_good_bad_bound μ p q hp hq hpb.1 hqb.1 hpqs b hb0 hbs hA hr hr1 hbound hbad
  have hlogA : 2*Real.log A = 2*(n+1)*Real.log (4*tubeConstant*labelVolumeConstant)+Real.log B := by
    rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr (by linarith)).ne',Real.log_pow,Real.log_sqrt (by linarith)]
    push_cast
    ring
  simp_rw [hpq] at H
  rw [hlogA] at H
  dsimp only [r] at H
  dsimp only [ν] at H
  have he : 2-2*(1-1/(m:ℝ)) = 2/(m:ℝ) := by ring
  rw [he] at H
  unfold blockInformationConstant
  have hnn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

lemma exactLabel_normalization {n : ℕ} (Q : Cell n) (X : GaussianBlock n) (z : Coordinate n) :
    (fun r => (2:ℝ)^(- (Q.1:ℤ))*projectVector X (normalizedChart Q z) r+exactLabel X (cellCenter Q) r) =
      exactLabel X z := by
  funext r
  have hp : ((2:ℝ)^Q.1) ≠ 0 := by positivity
  simp only [projectVector,normalizedChart,PiLp.smul_apply,smul_eq_mul,PiLp.sub_apply,eChart,exactLabel]
  have he : ∑ j,X r j*((2:ℝ)^Q.1*(chart z j-chart (cellCenter Q) j)) =
      (2:ℝ)^Q.1*((∑ j,X r j*chart z j)-(∑ j,X r j*chart (cellCenter Q) j)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  simp only [_root_.zpow_neg,zpow_natCast]
  field_simp
  ring

lemma actual_block_information {n N : ℕ} (hn : 32 ≤ n) (hN : 1 ≤ N)
    (Q : Cell n) (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 1 ≤ B) (hspread : DyadicSpread μ Q B)
    (rule : BlockRule n N) :
    finiteInformation μ (fun w z => blockProbability rule z w) ≤
      blockInformationConstant*(n+1)+Real.log B+
        (2/(n/8:ℕ)+Real.exp (-(n/16:ℕ)/2))*Real.log N := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0,by omega⟩⟩
  let a : GaussianBlock n × Label n → GaussianBlock n × Label n :=
    fun q => (q.1,fun r => (2:ℝ)^(- (Q.1:ℤ))*q.2 r+exactLabel q.1 (cellCenter Q) r)
  have ha : Measurable a := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro r
    exact (measurable_const.mul (measurable_pi_apply r |>.comp measurable_snd)).add
      ((measurable_pi_apply r).comp ((continuous_exactLabel n).measurable.comp
        (measurable_fst.prodMk measurable_const)))
  let g := fun q w => rule.prob (a q) w
  have h := normalized_block_information (n := n) (k := n/16) (m := n/8)
    (by omega) (by omega) (by omega) (by omega) (by omega) Q μ hsupport hB hspread
    g (fun w => (rule.measurable_prob w).comp ha) (fun q w => rule.nonneg (a q) w)
    (fun q => rule.sum_one (a q))
  have heg (w : Fin N) (z : Coordinate n) (X : GaussianBlock n) :
      g (X,projectVector X (normalizedChart Q z)) w = rule.prob (X,exactLabel X z) w := by
    dsimp [g,a]
    rw [exactLabel_normalization]
  simp_rw [heg] at h
  simpa only [gaussianRows,gaussianBlockLaw,blockProbability,Fintype.card_fin] using h

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

lemma actual_uniform_blockCost_oai {n N : ℕ} (hn : 32 ≤ n) (hN : 1 ≤ N)
    {C₀ : ℝ} (halphabet : (2/(n/8:ℕ)+Real.exp (-(1/2:ℝ)*(n/16:ℕ)))*Real.log N ≤ C₀*(n+1)) :
    UniformBlockCost n N ((blockInformationConstant+C₀)*(n+1)) := by
  intro μ hμ Q B hsupport hB hspread rule
  have := hμ
  have hs : μ (cellSet Q)ᶜ = 0 := (prob_compl_eq_zero_iff (measurableSet_cellSet Q)).mpr hsupport
  have h := actual_block_information hn hN Q μ hs hB hspread rule
  have he : (-(n/16:ℕ)/2:ℝ) = -(1/2:ℝ)*(n/16:ℕ) := by ring
  rw [he] at h
  change finiteInformation μ (fun w z => blockProbability rule z w) ≤ _
  linarith

end RepeatedLocalization

end OAI
end

theorem solution : type_of% @OAI.RepeatedLocalization.actual_uniform_blockCost_oai := @OAI.RepeatedLocalization.actual_uniform_blockCost_oai
