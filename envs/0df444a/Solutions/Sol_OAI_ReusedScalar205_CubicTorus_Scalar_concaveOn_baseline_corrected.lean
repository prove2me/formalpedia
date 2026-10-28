-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:49:54.837862+00:00
-- url     : https://prove2.me/submissions/b4d13626-533b-4a4c-b188-02a040095fd4

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_concaveOn_sectionLength_corrected

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AtanPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace ReusedScalar205

noncomputable section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubicTorus.Nesting

lemma sqrt_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 < Real.sqrt (1 - x ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma sqrt_square_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).sqrt
    (ne_of_gt hp) using 1
  · rfl
  · dsimp
    ring

lemma cutoff_pos : 0 < cutoff := by
  unfold cutoff
  positivity

lemma cutoff_sq : cutoff ^ 2 = 48 / 49 := by
  norm_num [cutoff, div_pow]

lemma cutoff_lt_one : cutoff < 1 := by
  nlinarith [cutoff_sq, cutoff_pos]

lemma sqrt_cutoff : Real.sqrt (1 - cutoff ^ 2) = 1 / 7 := by
  rw [cutoff_sq]
  norm_num

lemma rawWeight_cutoff : rawWeight cutoff = ell := by
  rw [rawWeight, sqrt_cutoff, cutoff_sq]
  norm_num [lambda, ell]

lemma hasDerivAt_rawWeight {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt rawWeight
      (x * (49 * x ^ 2 - 48) / (50 * Real.sqrt (1 - x ^ 2) ^ 3)) x := by
  have hs := hasDerivAt_sqrt_one_sub_sq hx
  have hs0 := ne_of_gt (sqrt_pos_of_mem_Ioo hx)
  have hs2 := sqrt_square_of_mem_Ioo hx
  have hh := ((hasDerivAt_const x (1 : ℝ)).sub
    (((hasDerivAt_id x).pow 2).const_mul lambda)).div hs hs0
  convert hh using 1 <;> try rfl
  dsimp [lambda]
  field_simp
  linear_combination 98 * x * hs2

lemma continuousOn_rawWeight : ContinuousOn rawWeight (Icc 0 cutoff) := by
  have hs : ∀ x ∈ Icc 0 cutoff, Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro x hx
    apply ne_of_gt (Real.sqrt_pos.2 _)
    have hxl : x < 1 := lt_of_le_of_lt hx.2 cutoff_lt_one
    nlinarith [hx.1, sq_nonneg x]
  exact (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2))).div
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn) hs

end CubicTorus.Nesting

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Shape

lemma positive_quadratic_root {a : ℝ} (ha : 0 < a) :
    let r := 2 / (1 + Real.sqrt (1 + 4 * a / Real.pi))
    0 < r ∧ r < 1 ∧ a * r ^ 2 = Real.pi * (1 - r) := by
  have hp := Real.pi_pos
  have hr : 1 < 1 + 4 * a / Real.pi := by
    have : 0 < 4 * a / Real.pi := by positivity
    linarith
  have hs0 := Real.sqrt_nonneg (1 + 4 * a / Real.pi)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * a / Real.pi)
  have hs1 : 1 < Real.sqrt (1 + 4 * a / Real.pi) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 4 * a / Real.pi) := by linarith
  refine ⟨div_pos (by norm_num) hd, (div_lt_one hd).2 (by linarith), ?_⟩
  generalize hz : Real.sqrt (1 + 4 * a / Real.pi) = z at *
  field_simp at hs ⊢
  nlinarith

lemma t_spec {h : ℝ} (hh : 0 < h) :
    0 < t h ∧ t h < 1 ∧ h ^ 2 * t h ^ 2 = Real.pi * (1 - t h) := by
  exact positive_quadratic_root (sq_pos_of_pos hh)

end CubicTorus.Shape
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma nonneg_quadratic_sublevel {a r v : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hv : 0 ≤ v)
    (heq : r ^ 2 = a * (1 - r)) :
    v ^ 2 ≤ a * (1 - v) ↔ v ≤ r := by
  constructor
  · intro hn
    by_contra! hrv
    have hs := (sq_lt_sq₀ hr hv).2 hrv
    have hm := mul_le_mul_of_nonneg_left hrv.le ha
    nlinarith
  · intro hvr
    have hs := (sq_le_sq₀ hv hr).2 hvr
    have hm := mul_le_mul_of_nonneg_left hvr ha
    nlinarith

lemma rho_spec {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ rho k ∧ rho k < 1 ∧ (rho k) ^ 2 = Real.pi * k ^ 2 * (1 - rho k) := by
  let x := Real.sqrt Real.pi * k
  let z := Real.sqrt (1 + (Real.pi / 4) * k ^ 2)
  have hx : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = Real.pi * k ^ 2 := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have hz : 0 ≤ z := by positivity
  have hz2 : z ^ 2 = 1 + x ^ 2 / 4 := by
    dsimp [z]
    rw [Real.sq_sqrt (by positivity), hx2]
    ring
  have hzx : x / 2 < z := by nlinarith
  have heq : rho k = x * z - x ^ 2 / 2 := by
    dsimp [rho, x, z]
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  have hr : 0 ≤ rho k := by rw [heq]; nlinarith
  have hs : (rho k) ^ 2 = Real.pi * k ^ 2 * (1 - rho k) := by
    rw [heq, ← hx2]
    linear_combination x ^ 2 * hz2
  refine ⟨hr, ?_, hs⟩
  by_contra! hn
  have hm := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ Real.pi * k ^ 2) (by linarith : 1 - rho k ≤ 0)
  nlinarith

lemma rho_zero : rho 0 = 0 := by simp [rho]

lemma monotoneOn_rho : MonotoneOn rho (Ici 0) := by
  intro k hk K hK hkK
  obtain ⟨hr, hr1, hs⟩ := rho_spec hk
  obtain ⟨hR, _, hS⟩ := rho_spec hK
  apply (nonneg_quadratic_sublevel (by positivity : 0 ≤ Real.pi * K ^ 2) hR hr hS).1
  rw [hs]
  have hh := (sq_le_sq₀ hk hK).2 hkK
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh Real.pi_pos.le) (by linarith)

lemma rho_inverse_sublevel {v k : ℝ} (hv : v ∈ Ico 0 1) (hk : 0 ≤ k) :
    v / Real.sqrt (Real.pi * (1 - v)) ≤ k ↔ v ≤ rho k := by
  have hv1 : 0 < 1 - v := sub_pos.2 hv.2
  have hden : 0 < Real.sqrt (Real.pi * (1 - v)) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi * (1 - v) by positivity)
  rw [div_le_iff₀ hden]
  rw [← sq_le_sq₀ hv.1 (mul_nonneg hk hden.le)]
  rw [mul_pow, hs]
  have heq : k ^ 2 * (Real.pi * (1 - v)) = Real.pi * k ^ 2 * (1 - v) := by ring
  rw [heq]
  exact nonneg_quadratic_sublevel (by positivity : 0 ≤ Real.pi * k ^ 2)
    (rho_spec hk).1 hv.1 (rho_spec hk).2.2

lemma rho_at_inverse {h : ℝ} (hh : 0 < h) : rho (1 / h) = t h := by
  obtain ⟨ht, ht1, hs⟩ := t_spec hh
  obtain ⟨hr, _, hrs⟩ := rho_spec (show 0 ≤ (1 : ℝ) / h by positivity)
  have hts : (t h) ^ 2 = Real.pi * (1 / h) ^ 2 * (1 - t h) := by
    field_simp
    nlinarith only [hs]
  apply le_antisymm
  · exact (nonneg_quadratic_sublevel (by positivity) ht.le hr hts).1 hrs.le
  · exact (nonneg_quadratic_sublevel (by positivity) hr ht.le hrs).1 hts.le

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma div_min_positive {n a b : ℝ} (hn : 0 ≤ n) (ha : 0 < a) (hb : 0 < b) :
    n / min a b = max (n / a) (n / b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_left (div_le_div_of_nonneg_left hn ha hab)]
  · rw [min_eq_right hba, max_eq_right (div_le_div_of_nonneg_left hn hb hba)]

lemma fluxArgument_eq {h v : ℝ} (hh : 0 ≤ h) (hv : v ∈ Ico 0 1) :
    fluxArgument h v = max (h * Real.sqrt (v / Real.pi))
      (max (h * v) (h * (v / Real.sqrt (Real.pi * (1 - v))))) := by
  rcases eq_or_lt_of_le hv.1 with hzero | hv0
  · rw [← hzero]
    simp [fluxArgument, planarProfile]
  · have hA : 0 < Real.sqrt (Real.pi * v) := Real.sqrt_pos.2 (by positivity)
    have hB : 0 < Real.sqrt (Real.pi * (1 - v)) :=
      Real.sqrt_pos.2 (mul_pos Real.pi_pos (sub_pos.2 hv.2))
    have hmin : 0 < min (1 : ℝ) (Real.sqrt (Real.pi * (1 - v))) := lt_min (by norm_num) hB
    have hn : 0 ≤ h * v := mul_nonneg hh hv.1
    unfold fluxArgument planarProfile
    rw [div_min_positive hn hA hmin, div_min_positive hn (by norm_num) hB, div_one]
    have heq : h * v / Real.sqrt (Real.pi * v) = h * Real.sqrt (v / Real.pi) := by
      rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_div hv.1]
      calc
        _ = h * (v / Real.sqrt v) / Real.sqrt Real.pi := by ring
        _ = _ := by rw [Real.div_sqrt]; ring
    rw [heq]
    congr 2
    ring

lemma fluxArgument_nonneg {h v : ℝ} (hh : 0 ≤ h) (hv : 0 ≤ v) : 0 ≤ fluxArgument h v := by
  unfold fluxArgument planarProfile
  positivity

lemma fluxArgument_sublevel {h X v : ℝ} (hh : 0 < h) (hX : 0 ≤ X) (hv : v ∈ Ico 0 1) :
    fluxArgument h v ≤ X ↔ v ≤ min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
  have hk : 0 ≤ X / h := div_nonneg hX hh.le
  rw [fluxArgument_eq hh.le hv, max_le_iff, max_le_iff, le_min_iff, le_min_iff]
  have h1 : h * Real.sqrt (v / Real.pi) ≤ X ↔ v ≤ Real.pi * (X / h) ^ 2 := by
    rw [mul_comm h, ← le_div_iff₀ hh]
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hk, Real.sq_sqrt (div_nonneg hv.1 Real.pi_pos.le)]
    rw [div_le_iff₀ Real.pi_pos]
    rw [mul_comm]
  have h2 : h * v ≤ X ↔ v ≤ X / h := by rw [le_div_iff₀ hh, mul_comm]
  have h3 : h * (v / Real.sqrt (Real.pi * (1 - v))) ≤ X ↔ v ≤ rho (X / h) := by
    rw [mul_comm h, ← le_div_iff₀ hh, rho_inverse_sublevel hv hk]
  exact and_congr h1 (and_congr h2 h3)

theorem fluxArgument_sublevel_set {h X : ℝ} (hh : 0 < h) (hX : X ∈ Icc 0 cutoff) :
    {v ∈ Icc 0 (t h) | fluxArgument h v ≤ X} =
      Icc 0 (min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h)))) := by
  have ht := t_spec hh
  have hX1 : X ≤ 1 := hX.2.trans cutoff_lt_one.le
  have hr : rho (X / h) ≤ t h := by
    rw [← rho_at_inverse hh]
    exact monotoneOn_rho (div_nonneg hX.1 hh.le) (show 0 ≤ (1 : ℝ) / h by positivity)
      (div_le_div_of_nonneg_right hX1 hh.le)
  have hbound : min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) ≤ t h :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans hr
  ext v
  constructor
  · rintro ⟨hv, hq⟩
    exact ⟨hv.1, (fluxArgument_sublevel hh hX.1 ⟨hv.1, hv.2.trans_lt ht.2.1⟩).1 hq⟩
  · intro hv
    have hvt : v ≤ t h := hv.2.trans hbound
    exact ⟨⟨hv.1, hvt⟩, (fluxArgument_sublevel hh hX.1 ⟨hv.1, hvt.trans_lt ht.2.1⟩).2 hv.2⟩

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma density_nonneg {x : ℝ} (hx : x ∈ Icc 0 cutoff) : 0 ≤ density x := by
  have hs := pow_le_pow_left₀ hx.1 hx.2 2
  unfold density
  apply div_nonneg (mul_nonneg hx.1 _) (by positivity)
  nlinarith [cutoff_sq]

lemma continuousOn_density : ContinuousOn density (Icc 0 cutoff) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have hx1 : x < 1 := hx.2.trans_lt cutoff_lt_one
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2 hp)))

lemma hasDerivAt_neg_rawWeight {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y ↦ -rawWeight y) (density x) x := by
  convert (hasDerivAt_rawWeight hx).neg using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [density]
  ring

lemma integral_density_tail {q : ℝ} (hq : q ∈ Icc 0 cutoff) :
    (∫ X in q..cutoff, density X) = rawWeight q - ell := by
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hq.2
    (continuousOn_rawWeight.neg.mono (Icc_subset_Icc_left hq.1))
    (fun x (hx : x ∈ Ioo q cutoff) ↦
      hasDerivAt_neg_rawWeight ⟨hq.1.trans_lt hx.1, hx.2.trans cutoff_lt_one⟩)
    ((continuousOn_density.mono (Icc_subset_Icc_left hq.1)).intervalIntegrable_of_Icc hq.2)
  change (∫ X in q..cutoff, density X) = -rawWeight cutoff - -rawWeight q at heq
  rw [rawWeight_cutoff] at heq
  linarith

lemma integral_density : (∫ X in (0 : ℝ)..cutoff, density X) = 18 / 25 := by
  have heq := integral_density_tail ⟨le_rfl, cutoff_pos.le⟩
  norm_num [rawWeight, ell] at heq
  exact heq

lemma weight_layer_cake {q : ℝ} (hq : 0 ≤ q) :
    weight q = ell + ∫ X in Icc 0 cutoff, if q ≤ X then density X else 0 := by
  classical
  have hrewrite : (∫ X in Icc 0 cutoff, if q ≤ X then density X else 0) =
      ∫ X in (Ici q ∩ Icc 0 cutoff), density X := by
    change (∫ X in Icc 0 cutoff, (Ici q).indicator density X) = _
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  rw [hrewrite]
  have hinter : Ici q ∩ Icc 0 cutoff = Icc q cutoff := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · tauto
    · rintro ⟨hqx, hxd⟩
      exact ⟨hqx, hq.trans hqx, hxd⟩
  rw [hinter]
  by_cases hqd : q ≤ cutoff
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hqd,
      integral_density_tail ⟨hq, hqd⟩]
    simp [weight, min_eq_left hqd]
  · have hempty : Icc q cutoff = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hqd)
    rw [hempty, setIntegral_empty, add_zero, weight, min_eq_right (le_of_not_ge hqd), rawWeight_cutoff]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma measurable_fluxArgument (h : ℝ) : Measurable (fluxArgument h) := by
  unfold fluxArgument planarProfile
  fun_prop

lemma integral_flux_sublevel {h X : ℝ} (hh : 0 < h) (hX : X ∈ Icc 0 cutoff) :
    (∫ v in Icc 0 (t h), if fluxArgument h v ≤ X then density X else 0) =
      density X * min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
  classical
  let A := min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h)))
  have hA : 0 ≤ A := le_min (by positivity)
    (le_min (div_nonneg hX.1 hh.le) (rho_spec (div_nonneg hX.1 hh.le)).1)
  have hms : MeasurableSet {v | fluxArgument h v ≤ X} :=
    measurableSet_le (measurable_fluxArgument h) measurable_const
  change (∫ v in Icc 0 (t h), {v | fluxArgument h v ≤ X}.indicator (fun _ ↦ density X) v) = _
  rw [integral_indicator hms, Measure.restrict_restrict hms]
  have hs : {v | fluxArgument h v ≤ X} ∩ Icc 0 (t h) = Icc 0 A := by
    rw [inter_comm]
    exact fluxArgument_sublevel_set hh hX
  rw [hs, setIntegral_const, measureReal_def, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal hA, smul_eq_mul, mul_comm]

theorem baseline_layer_cake {h : ℝ} (hh : 0 < h) :
    baseline h + 1 = lambda * h / Real.pi + ell * t h +
      ∫ X in (0 : ℝ)..cutoff,
        density X * min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
  classical
  let μ := volume.restrict (Icc 0 (t h))
  let ν := volume.restrict (Icc 0 cutoff)
  let F : ℝ × ℝ → ℝ := fun z ↦ if fluxArgument h z.1 ≤ z.2 then density z.2 else 0
  have hm : MeasurableSet {z : ℝ × ℝ | fluxArgument h z.1 ≤ z.2} :=
    measurableSet_le ((measurable_fluxArgument h).comp measurable_fst) measurable_snd
  have hF : Integrable F (μ.prod ν) := by
    exact (continuousOn_density.integrableOn_Icc.comp_snd μ).indicator hm
  have heq : (∫ v in Icc 0 (t h), weight (fluxArgument h v)) =
      ell * t h + ∫ X in Icc 0 cutoff,
        density X * min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h))) := by
    calc
      _ = ∫ v in Icc 0 (t h), ell + ∫ X in Icc 0 cutoff, F (v, X) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro v hv
        exact weight_layer_cake (fluxArgument_nonneg hh.le hv.1)
      _ = (∫ v in Icc 0 (t h), ell) + ∫ v in Icc 0 (t h), ∫ X in Icc 0 cutoff, F (v, X) :=
        integral_add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
          hF.integral_prod_left
      _ = ell * t h + ∫ v in Icc 0 (t h), ∫ X in Icc 0 cutoff, F (v, X) := by
        rw [setIntegral_const, measureReal_def, Real.volume_Icc, sub_zero,
          ENNReal.toReal_ofReal (t_spec hh).1.le, smul_eq_mul, mul_comm (t h)]
      _ = ell * t h + ∫ X in Icc 0 cutoff, ∫ v in Icc 0 (t h), F (v, X) := by
        congr 1
        exact integral_integral_swap hF
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro X hX
        exact integral_flux_sublevel hh hX
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (t_spec hh).1.le] at heq
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le cutoff_pos.le] at heq
  unfold baseline
  change lambda * h / Real.pi + (∫ v in (0 : ℝ)..t h, weight (fluxArgument h v)) - 1 + 1 = _
  rw [heq]
  ring

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma rhoRoot_pos (k : ℝ) : 0 < rhoRoot k := by unfold rhoRoot; positivity
lemma rhoRoot_sq (k : ℝ) : rhoRoot k ^ 2 = Real.pi * k ^ 2 + 4 := by
  exact Real.sq_sqrt (by positivity)
lemma rhoDen_pos (k : ℝ) : 0 < rhoDen k := by
  have hs := rhoRoot_pos k
  have hs2 := rhoRoot_sq k
  have ha : (Real.sqrt Real.pi * k) ^ 2 = Real.pi * k ^ 2 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  by_contra! hn
  change rhoRoot k + Real.sqrt Real.pi * k ≤ 0 at hn
  have hk : 0 ≤ -(Real.sqrt Real.pi * k) := by linarith
  have hsq := (sq_le_sq₀ hs.le hk).2 (show rhoRoot k ≤ -(Real.sqrt Real.pi * k) by linarith)
  rw [neg_sq, ha, hs2] at hsq
  linarith

end CubicTorus.Scalar
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar
open Set MeasureTheory Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma rho_rational (k : ℝ) : rho k = 2 * Real.sqrt Real.pi * k / rhoDen k := by
  have hs : rhoRoot k = 2 * Real.sqrt (1 + Real.pi * k ^ 2 / 4) := by
    have h1 := rhoRoot_sq k
    have h2 := Real.sq_sqrt (show 0 ≤ 1 + Real.pi * k ^ 2 / 4 by positivity)
    have h3 := rhoRoot_pos k
    have h4 := Real.sqrt_nonneg (1 + Real.pi * k ^ 2 / 4)
    nlinarith
  have ha := Real.sq_sqrt Real.pi_pos.le
  have hd := ne_of_gt (rhoDen_pos k)
  apply (eq_div_iff hd).2
  unfold rho rhoDen
  rw [hs, show Real.pi / 4 * k ^ 2 = Real.pi * k ^ 2 / 4 by ring]
  have hz := Real.sq_sqrt (show 0 ≤ 1 + Real.pi * k ^ 2 / 4 by positivity)
  linear_combination Real.sqrt Real.pi * k * 2 * hz +
    k ^ 2 * Real.sqrt (1 + Real.pi * k ^ 2 / 4) * ha

lemma hasDerivAt_rhoRoot (k : ℝ) :
    HasDerivAt rhoRoot (Real.pi * k / rhoRoot k) k := by
  convert ((((hasDerivAt_id k).pow 2).const_mul Real.pi).add_const 4).sqrt
    (by positivity : Real.pi * k ^ 2 + 4 ≠ 0) using 1 <;> try rfl
  dsimp [rhoRoot]
  ring

lemma hasDerivAt_rho (k : ℝ) : HasDerivAt rho (rhoSlope k) k := by
  have heq : rho = fun k ↦ 2 * Real.sqrt Real.pi * k / rhoDen k := funext rho_rational
  rw [heq]
  have hh := ((hasDerivAt_id k).const_mul (2 * Real.sqrt Real.pi)).div
    ((hasDerivAt_rhoRoot k).add ((hasDerivAt_id k).const_mul (Real.sqrt Real.pi)))
    (ne_of_gt (rhoDen_pos k))
  convert hh using 1 <;> try rfl
  dsimp [rhoSlope, rhoDen]
  have hs := ne_of_gt (rhoRoot_pos k)
  have hd : rhoRoot k + Real.sqrt Real.pi * k ≠ 0 := ne_of_gt (rhoDen_pos k)
  field_simp
  linear_combination -2 * rhoRoot_sq k

lemma continuous_rho : Continuous rho :=
  continuous_iff_continuousAt.2 (fun k ↦ (hasDerivAt_rho k).continuousAt)

lemma contDiff_rho {n : WithTop ℕ∞} : ContDiff ℝ n rho := by
  unfold rho
  have hs : ContDiff ℝ n (fun k : ℝ ↦ Real.sqrt (1 + Real.pi / 4 * k ^ 2)) :=
    (by fun_prop : ContDiff ℝ n (fun k : ℝ ↦ 1 + Real.pi / 4 * k ^ 2)).sqrt
      (fun k ↦ by positivity)
  exact ((contDiff_const.mul contDiff_id).mul hs).sub
    (contDiff_const.mul (contDiff_id.pow 2))

lemma antitoneOn_rhoSlope : AntitoneOn rhoSlope (Ici 0) := by
  intro k hk K hK hkK
  change 0 ≤ k at hk
  change 0 ≤ K at hK
  have hroot : rhoRoot k ≤ rhoRoot K := Real.sqrt_le_sqrt
    (add_le_add (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hk hK).2 hkK) Real.pi_pos.le) le_rfl)
  have hden : rhoDen k ≤ rhoDen K := add_le_add hroot
    (mul_le_mul_of_nonneg_left hkK (Real.sqrt_nonneg _))
  have hprod : rhoRoot k * rhoDen k ^ 2 ≤ rhoRoot K * rhoDen K ^ 2 :=
    mul_le_mul hroot (pow_le_pow_left₀ (rhoDen_pos k).le hden 2)
      (sq_nonneg _) (rhoRoot_pos K).le
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos (rhoRoot_pos k) (sq_pos_of_pos (rhoDen_pos k))) hprod

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma deriv_rho_eq : deriv rho = rhoSlope := funext (fun k ↦ (hasDerivAt_rho k).deriv)

lemma concaveOn_rho : ConcaveOn ℝ (Ici 0) rho := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) continuous_rho.continuousOn
    (fun k _ ↦ (hasDerivAt_rho k).differentiableAt.differentiableWithinAt)
  rw [deriv_rho_eq]
  exact antitoneOn_rhoSlope.mono interior_subset

lemma mul_rhoSlope_le {k : ℝ} (hk : 0 ≤ k) : k * rhoSlope k ≤ rho k := by
  rcases eq_or_lt_of_le hk with hzero | hpos
  · rw [← hzero, rho_zero, zero_mul]
  · have hs := concaveOn_rho.deriv_le_slope (show 0 ∈ Ici (0 : ℝ) by simp)
      hk hpos (hasDerivAt_rho k).differentiableAt
    rw [slope_def_field, rho_zero, sub_zero, sub_zero, deriv_rho_eq] at hs
    simpa only [mul_comm] using (le_div_iff₀ hpos).1 hs

lemma second_deriv_rho_nonpos {k : ℝ} (hk : 0 < k) : deriv (deriv rho) k ≤ 0 := by
  rw [deriv_rho_eq]
  have hh := antitoneOn_rhoSlope.derivWithin_nonpos (x := k)
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hk)] at hh
  exact hh

lemma hasDerivAt_divParam (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (fun h ↦ X / h) (-X / h ^ 2) h := by
  convert (hasDerivAt_const h X).div (hasDerivAt_id h) hh using 1 <;> try rfl
  simp

lemma hasDerivAt_divParamSlope (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (fun h ↦ -X / h ^ 2) (2 * X / h ^ 3) h := by
  convert (hasDerivAt_const h (-X)).div ((hasDerivAt_id h).pow 2) (pow_ne_zero 2 hh) using 1 <;> try rfl
  dsimp
  field_simp
  ring

lemma second_deriv_comp_div {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ f (X / H))) h =
      deriv (deriv f) (X / h) * (X / h ^ 2) ^ 2 + deriv f (X / h) * (2 * X / h ^ 3) := by
  have heq : deriv (fun H ↦ f (X / H)) =ᶠ[𝓝 h]
      (fun H ↦ deriv f (X / H) * (-X / H ^ 2)) := by
    filter_upwards [eventually_ne_nhds hh] with H hH
    exact (((hf.contDiffAt.differentiableAt (by norm_num)).hasDerivAt).comp H
      (hasDerivAt_divParam X hH)).deriv
  rw [heq.deriv_eq]
  have hfd : DifferentiableAt ℝ (deriv f) (X / h) :=
    ((hf.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hd := ((hfd.hasDerivAt.comp h (hasDerivAt_divParam X hh)).mul
    (hasDerivAt_divParamSlope X hh)).deriv
  convert hd using 1 <;> try rfl
  dsimp only [Function.comp_apply]
  ring

lemma rho_comp_div_second_bound {X h : ℝ} (hX : 0 < X) (hh : 0 < h) :
    deriv (deriv (fun H ↦ rho (X / H))) h ≤ 2 / h ^ 2 := by
  rw [second_deriv_comp_div contDiff_rho X (ne_of_gt hh)]
  have hk := div_pos hX hh
  have hn := mul_nonpos_of_nonpos_of_nonneg (second_deriv_rho_nonpos hk) (sq_nonneg (X / h ^ 2))
  have hb := (mul_rhoSlope_le hk.le).trans (rho_spec hk.le).2.1.le
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 2 / h ^ 2 by positivity)
  rw [deriv_rho_eq] at hn ⊢
  have heq : X / h * rhoSlope (X / h) * (2 / h ^ 2) = rhoSlope (X / h) * (2 * X / h ^ 3) := by
    field_simp
  rw [heq] at hm
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

lemma second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  rw [hz] at hneg
  exact (lt_irrefl 0) hneg

lemma second_deriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y => f y - g y)) x =
      deriv (deriv f) x - deriv (deriv g) x := by
  have heq : deriv (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => deriv f y - deriv g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact deriv_sub (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_sub
    ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

lemma jet_comparison {I C F : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (hF : ContDiffAt ℝ 2 F x)
    (hm : IsLocalMin (fun y => I y - F y) x) :
    deriv C x = deriv F x ∧ deriv (deriv F) x ≤ deriv (deriv C) x := by
  have hmc : IsLocalMin (fun y => C y - F y) x := by
    filter_upwards [hm, hs.above] with y hy habove
    change C x - F x ≤ C y - F y
    rw [hs.contact]
    linarith
  have h1 := hmc.deriv_eq_zero
  change deriv (C - F) x = 0 at h1
  rw [deriv_sub (hs.smooth.differentiableAt (by norm_num))
    (hF.differentiableAt (by norm_num))] at h1
  have h2 := second_deriv_nonneg_of_local_min hmc (hs.smooth.continuousAt.sub hF.continuousAt)
  rw [second_deriv_sub hs.smooth hF] at h2
  exact ⟨sub_eq_zero.mp h1, sub_nonneg.mp h2⟩

lemma second_deriv_quadratic (α β γ x : ℝ) :
    deriv (deriv (fun y => α * y ^ 2 + β * y + γ)) x = 2 * α := by
  have hd (y : ℝ) : HasDerivAt (fun z => α * z ^ 2 + β * z + γ) (2 * α * y + β) y := by
    convert! (((hasDerivAt_pow 2 y).const_mul α).add
      ((hasDerivAt_id y).const_mul β)).add_const γ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdeq : deriv (fun y => α * y ^ 2 + β * y + γ) = (fun y => 2 * α * y + β) := by
    funext y
    exact (hd y).deriv
  rw [hdeq]
  have hd2 : HasDerivAt (fun y : ℝ => 2 * α * y + β) (2 * α) x := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul (2 * α)).add_const β
  exact hd2.deriv

theorem chord_below_of_upper_support {I : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) :
    ∀ x ∈ Icc a b, I a + (x - a) * (I b - I a) / (b - a) ≤ I x := by
  intro c hc
  by_contra! hgap
  let m := (I b - I a) / (b - a)
  let L := fun x : ℝ => I a + (x - a) * m
  have hLa : L a = I a := by simp [L]
  have hLb : L b = I b := by
    dsimp [L, m]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hgap' : I c < L c := by simpa [L, m, mul_div_assoc] using hgap
  have hca : a < c := by
    refine lt_of_le_of_ne hc.1 ?_
    intro heq
    subst c
    rw [hLa] at hgap'
    exact (lt_irrefl _ hgap')
  have hcb : c < b := by
    refine lt_of_le_of_ne hc.2 ?_
    intro heq
    subst c
    rw [hLb] at hgap'
    exact (lt_irrefl _ hgap')
  let ε := (L c - I c) / (2 * ((c - a) * (b - c)))
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap')
    (mul_pos (by norm_num) (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hcb)))
  let F := fun x : ℝ => ε * x ^ 2 + (m - ε * (a + b)) * x +
    (I a - a * m + ε * a * b)
  have hF_eq (x : ℝ) : F x = L x + ε * (x - a) * (x - b) := by dsimp [F, L]; ring
  have hFa : F a = I a := by rw [hF_eq, hLa]; ring
  have hFb : F b = I b := by rw [hF_eq, hLb]; ring
  have hFc : I c < F c := by
    have hprod : ε * (c - a) * (b - c) = (L c - I c) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt (sub_pos.mpr hca), ne_of_gt (sub_pos.mpr hcb)]
    rw [hF_eq]
    nlinarith
  have hF : ContDiff ℝ 2 F := by dsimp [F]; fun_prop
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab.le) (hI.sub hF.continuous.continuousOn)
  have hneg : I x - F x < 0 := lt_of_le_of_lt (hmin hc) (sub_neg.mpr hFc)
  have hxa : a < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro heq
    subst x
    rw [hFa, sub_self] at hneg
    exact lt_irrefl _ hneg
  have hxb : x < b := by
    refine lt_of_le_of_ne hx.2 ?_
    intro heq
    subst x
    rw [hFb, sub_self] at hneg
    exact lt_irrefl _ hneg
  obtain ⟨C, hC, hC''⟩ := hsupport x ⟨hxa, hxb⟩
  have hj := (jet_comparison hC hF.contDiffAt
    (hmin.isLocalMin (Icc_mem_nhds hxa hxb))).2
  have hF'' : deriv (deriv F) x = 2 * ε := second_deriv_quadratic _ _ _ _
  rw [hF''] at hj
  linarith

end CubicTorus.Reduction

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

theorem concaveOn_of_upper_support {I : ℝ → ℝ} {a b : ℝ}
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) : ConcaveOn ℝ (Icc a b) I := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc a b)
  intro x y z hx hz hxy hyz
  have hsub : Icc x z ⊆ Icc a b := Icc_subset_Icc hx.1 hz.2
  have hc := chord_below_of_upper_support (hxy.trans hyz) (hI.mono hsub)
    (fun t ht ↦ hsupport t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hz.2⟩) y ⟨hxy.le, hyz.le⟩
  have hdiv : (y - x) * (I z - I x) / (z - x) ≤ I y - I x := by linarith only [hc]
  have hm := (div_le_iff₀ (sub_pos.2 (hxy.trans hyz))).1 hdiv
  apply (div_le_div_iff₀ (sub_pos.2 hyz) (sub_pos.2 hxy)).2
  nlinarith only [hm]

lemma UpperSupport.sub_quadratic {I C : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (K : ℝ) :
    UpperSupport (fun y ↦ I y - K / 2 * y ^ 2) (fun y ↦ C y - K / 2 * y ^ 2) x := by
  refine ⟨hs.smooth.sub (by fun_prop), ?_, ?_⟩
  · rw [hs.contact]
  · filter_upwards [hs.above] with y hy
    exact sub_le_sub_right hy _

lemma second_deriv_half_quadratic (K x : ℝ) :
    deriv (deriv (fun y : ℝ ↦ K / 2 * y ^ 2)) x = K := by
  simp

theorem concaveOn_sub_quadratic_of_support {I : ℝ → ℝ} {a b K : ℝ}
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ K) :
    ConcaveOn ℝ (Icc a b) (fun y ↦ I y - K / 2 * y ^ 2) := by
  apply concaveOn_of_upper_support (hI.sub (by fun_prop))
  intro x hx
  obtain ⟨C, hC, hCK⟩ := hsupport x hx
  refine ⟨_, hC.sub_quadratic K, ?_⟩
  rw [second_deriv_sub hC.smooth (by fun_prop), second_deriv_half_quadratic]
  linarith

end CubicTorus.Reduction

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma contDiffAt_rho_comp_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ContDiffAt ℝ 2 (fun H ↦ rho (X / H)) h :=
  contDiff_rho.contDiffAt.comp h (contDiffAt_const.div contDiffAt_id hh)

lemma continuous_sectionLength_X (h : ℝ) : Continuous (fun X ↦ sectionLength X h) := by
  unfold sectionLength
  exact ((continuous_const.mul ((continuous_id.div_const h).pow 2)).inf
    ((continuous_id.div_const h).inf (continuous_rho.comp (continuous_id.div_const h))))

lemma concaveOn_rho_div_corrected {X a b : ℝ} (hX : 0 < X) (ha : 0 < a) :
    ConcaveOn ℝ (Icc a b) (fun h ↦ rho (X / h) - h ^ 2 / a ^ 2) := by
  have hc := concaveOn_sub_quadratic_of_support (I := fun h ↦ rho (X / h))
    (a := a) (b := b) (K := 2 / a ^ 2)
    (continuous_rho.comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun h hh ↦ ne_of_gt (ha.trans_le hh.1))))
    (fun h hh ↦ ?_)
  · convert hc using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    ring
  · refine ⟨fun H ↦ rho (X / H), ⟨contDiffAt_rho_comp_div X (ne_of_gt (ha.trans hh.1)),
      rfl, Filter.Eventually.of_forall (fun _ ↦ le_rfl)⟩, ?_⟩
    exact (rho_comp_div_second_bound hX (ha.trans hh.1)).trans
      (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
        (pow_le_pow_left₀ ha.le hh.1.le 2))

open MeasureTheory

lemma baseline_layer_cake_set {h : ℝ} (hh : 0 < h) :
    baseline h + 1 = lambda * h / Real.pi + ell * t h +
      ∫ X in Icc 0 cutoff, density X * sectionLength X h := by
  have heq := baseline_layer_cake hh
  rw [intervalIntegral.integral_of_le cutoff_pos.le, ← integral_Icc_eq_integral_Ioc] at heq
  exact heq

theorem concaveOn_baseline_corrected_oai {a b : ℝ} (ha : 0 < a) :
    ConcaveOn ℝ (Icc a b) (fun h ↦ baseline h - h ^ 2 / a ^ 2) := by
  have ht : ConcaveOn ℝ (Icc a b) (fun h ↦ t h - h ^ 2 / a ^ 2) :=
    (concaveOn_rho_div_corrected (X := 1) (by norm_num) ha).congr
      (fun h hh ↦ by dsimp; rw [rho_at_inverse (ha.trans_le hh.1)])
  have hint : ConcaveOn ℝ (Icc a b)
      (fun h ↦ ∫ X in Icc 0 cutoff, density X * (sectionLength X h - h ^ 2 / a ^ 2)) := by
    apply integral_concaveOn_of_integrand_ae (convex_Icc a b)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with X hX
      exact (concaveOn_sectionLength_corrected hX.1 ha).smul (density_nonneg hX)
    · intro h _
      exact (continuousOn_density.mul
        ((continuous_sectionLength_X h).continuousOn.sub continuousOn_const)).integrableOn_Icc
  have hlin : ConcaveOn ℝ (Icc a b) (fun h ↦ lambda * h / Real.pi) := by
    convert (concaveOn_id (𝕜 := ℝ) (convex_Icc a b)).smul
      (show 0 ≤ lambda / Real.pi by dsimp [lambda]; positivity) using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    dsimp
    ring
  have hc := ((hlin.add (ht.smul (show 0 ≤ ell by norm_num [ell]))).add hint).add_const (-1)
  apply hc.congr
  intro h hh
  have hI : IntegrableOn (fun X ↦ density X * sectionLength X h) (Icc 0 cutoff) :=
    (continuousOn_density.mul (continuous_sectionLength_X h).continuousOn).integrableOn_Icc
  have hW : IntegrableOn (fun X ↦ density X * (h ^ 2 / a ^ 2)) (Icc 0 cutoff) :=
    continuousOn_density.integrableOn_Icc.mul_const (h ^ 2 / a ^ 2)
  have hmass : (∫ X in Icc 0 cutoff, density X) = 18 / 25 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le cutoff_pos.le]
    exact integral_density
  have heq := baseline_layer_cake_set (ha.trans_le hh.1)
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_sub]
  rw [integral_sub hI hW, integral_mul_const, hmass]
  dsimp [ell] at *
  linarith only [heq]

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected_oai
