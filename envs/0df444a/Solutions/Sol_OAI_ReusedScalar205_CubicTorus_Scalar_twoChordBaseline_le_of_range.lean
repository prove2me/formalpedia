-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:51:45.262809+00:00
-- url     : https://prove2.me/submissions/c06a9d04-05be-49f8-bfe5-76c80c611c9e

import Mathlib
import Definitions.Def_OAIQ079A003

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

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma continuous_sectionLength_X (h : ℝ) : Continuous (fun X ↦ sectionLength X h) := by
  unfold sectionLength
  exact ((continuous_const.mul ((continuous_id.div_const h).pow 2)).inf
    ((continuous_id.div_const h).inf (continuous_rho.comp (continuous_id.div_const h))))

open MeasureTheory

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_GainBounds
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

lemma planar_switches : 0 < 1 / Real.pi ∧ 1 / Real.pi < 1 - 1 / Real.pi ∧ 1 - 1 / Real.pi < 1 := by
  have hp := Real.pi_pos
  have hi : 1 / Real.pi < (1 / 2 : ℝ) := (div_lt_div_iff₀ hp (by norm_num)).2 (by linarith [Real.pi_gt_three])
  have hi0 : 0 < 1 / Real.pi := by positivity
  exact ⟨hi0, by linarith, by linarith⟩

lemma le_rho_of_le_switch {k : ℝ} (hk : 0 ≤ k) (hb : k ≤ 1 - 1 / Real.pi) : k ≤ rho k := by
  have h1 : 1 ≤ Real.pi * (1 - k) := by
    have := (le_sub_iff_add_le).1 hb
    have hm := mul_le_mul_of_nonneg_left this Real.pi_pos.le
    rw [mul_add, mul_one_div_cancel Real.pi_pos.ne'] at hm
    linarith
  apply (nonneg_quadratic_sublevel (by positivity : 0 ≤ Real.pi * k ^ 2)
    (rho_spec hk).1 hk (rho_spec hk).2.2).1
  have hm := mul_le_mul_of_nonneg_right h1 (sq_nonneg k)
  nlinarith only [hm]

lemma rho_le_of_switch_le {k : ℝ} (hk : 0 ≤ k) (hb : 1 - 1 / Real.pi ≤ k) : rho k ≤ k := by
  have h1 : Real.pi * (1 - k) ≤ 1 := by
    have hh : 1 ≤ k + 1 / Real.pi := by linarith
    have hm := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
    rw [mul_add, mul_one_div_cancel Real.pi_pos.ne'] at hm
    linarith
  by_contra! hn
  obtain ⟨hr, _, heq⟩ := rho_spec hk
  have hs := (sq_lt_sq₀ hk hr).2 hn
  have hm1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg k)
  have hm2 := mul_le_mul_of_nonneg_left (show 1 - rho k ≤ 1 - k by linarith)
    (show 0 ≤ Real.pi * k ^ 2 by positivity)
  nlinarith only [hs, heq, hm1, hm2]

lemma minSection_quadratic {k : ℝ} (hk : 0 ≤ k) (ha : k ≤ 1 / Real.pi) :
    min (Real.pi * k ^ 2) (min k (rho k)) = Real.pi * k ^ 2 := by
  have hpk := (le_div_iff₀ Real.pi_pos).1 ha
  have hkq : Real.pi * k ^ 2 ≤ k := by nlinarith [mul_le_mul_of_nonneg_right hpk hk]
  exact min_eq_left (le_min hkq (hkq.trans (le_rho_of_le_switch hk (ha.trans planar_switches.2.1.le))))

lemma minSection_linear {k : ℝ} (ha : 1 / Real.pi ≤ k) (hb : k ≤ 1 - 1 / Real.pi) :
    min (Real.pi * k ^ 2) (min k (rho k)) = k := by
  have hk : 0 ≤ k := planar_switches.1.le.trans ha
  have hpk := (div_le_iff₀ Real.pi_pos).1 ha
  have hkq : k ≤ Real.pi * k ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hpk hk]
  rw [min_eq_left (le_rho_of_le_switch hk hb), min_eq_right hkq]

lemma minSection_rho {k : ℝ} (hb : 1 - 1 / Real.pi ≤ k) :
    min (Real.pi * k ^ 2) (min k (rho k)) = rho k := by
  have ha := planar_switches.2.1.le.trans hb
  have hk : 0 ≤ k := planar_switches.1.le.trans ha
  have hpk := (div_le_iff₀ Real.pi_pos).1 ha
  have hkq : k ≤ Real.pi * k ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hpk hk]
  have hrk := rho_le_of_switch_le hk hb
  rw [min_eq_right hrk, min_eq_right (hrk.trans hkq)]

lemma beta_pos {x : ℝ} (hx : x ∈ Ioo (-1) 1) : 0 < beta x := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1, hx.2]

lemma beta_sq {x : ℝ} (hx : x ∈ Icc (-1) 1) : beta x ^ 2 = 1 - x ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1, hx.2]

lemma hasDerivAt_beta {x : ℝ} (hx : x ∈ Ioo (-1) 1) : HasDerivAt beta (-x / beta x) x := by
  have hsq : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  convert ((Real.hasDerivAt_sqrt hsq.ne').comp x (((hasDerivAt_id x).pow 2).const_sub 1)) using 1 <;> try rfl
  dsimp [beta]
  ring

lemma hasDerivAt_J₀ {x : ℝ} (hx : x ∈ Ioo 0 1) : HasDerivAt J₀ (density x) x := by
  convert (hasDerivAt_rawWeight hx).const_sub 1 using 1 <;> try rfl
  dsimp [density]
  ring

lemma hasDerivAt_J₁ {x : ℝ} (hx : x ∈ Ioo 0 1) : HasDerivAt J₁ (x * density x) x := by
  have hx' : x ∈ Ioo (-1) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hb := beta_sq ⟨hx'.1.le, hx'.2.le⟩
  have hb0 := beta_pos hx'
  have hd := (((Real.hasDerivAt_arcsin (by linarith [hx.1]) hx.2.ne).const_mul (51 / 100)).sub
    (((hasDerivAt_id x).const_mul (49 / 100)).mul (hasDerivAt_beta hx'))).sub
      ((hasDerivAt_id x).div ((hasDerivAt_beta hx').const_mul 50) (by positivity))
  convert hd using 1 <;> try rfl
  change x * (x * (48 - 49 * x ^ 2) / (50 * beta x ^ 3)) = _
  have hbX := congrArg (fun z ↦ x ^ 2 * z) hb
  have hbB := congrArg (fun z ↦ beta x ^ 2 * z) hb
  change _ = (51 / 100 : ℝ) * (1 / beta x) -
    ((49 / 100 : ℝ) * 1 * beta x + (49 / 100 : ℝ) * x * (-x / beta x)) -
      (1 * (50 * beta x) - x * (50 * (-x / beta x))) / (50 * beta x) ^ 2
  field_simp
  nlinarith only [hb, hbX, hbB]

lemma hasDerivAt_J₂ {x : ℝ} (hx : x ∈ Ioo 0 1) : HasDerivAt J₂ (x ^ 2 * density x) x := by
  have hx' : x ∈ Ioo (-1) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hb := beta_sq ⟨hx'.1.le, hx'.2.le⟩
  have hb0 := beta_pos hx'
  have hbd := hasDerivAt_beta hx'
  have hd := (((hbd.const_sub (2 / 3)).add ((hbd.pow 3).div_const 3)).const_mul (49 / 50)).sub
    (((((hasDerivAt_id x).pow 2).div hbd hb0.ne').sub_const 2).add (hbd.const_mul 2) |>.div_const 50)
  convert hd using 1 <;> try rfl
  change x ^ 2 * (x * (48 - 49 * x ^ 2) / (50 * beta x ^ 3)) = _
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply] at *
  change _ = (49 / 50 : ℝ) * (-(-x / beta x) + (3 * beta x ^ 2 * (-x / beta x)) / 3) -
    ((2 * x * 1 * beta x - x ^ 2 * (-x / beta x)) / beta x ^ 2 + 2 * (-x / beta x)) / 50
  have hbX := congrArg (fun z ↦ x ^ 3 * z) hb
  have hbB := congrArg (fun z ↦ x * beta x ^ 2 * z) hb
  field_simp
  nlinarith only [hbX, hbB]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma continuous_beta : Continuous beta := by unfold beta; fun_prop

lemma beta_ne_zero_on {x : ℝ} (hx : x ∈ Icc 0 cutoff) : beta x ≠ 0 :=
  (beta_pos ⟨by linarith [hx.1], hx.2.trans_lt cutoff_lt_one⟩).ne'

lemma continuousOn_J₀ : ContinuousOn J₀ (Icc 0 cutoff) :=
  continuousOn_const.sub continuousOn_rawWeight

lemma continuousOn_J₁ : ContinuousOn J₁ (Icc 0 cutoff) := by
  unfold J₁
  apply ContinuousOn.sub
  · exact (continuousOn_const.mul Real.continuous_arcsin.continuousOn).sub
      ((continuousOn_const.mul continuousOn_id).mul continuous_beta.continuousOn)
  · exact continuousOn_id.div (continuousOn_const.mul continuous_beta.continuousOn)
      (fun x hx ↦ mul_ne_zero (by norm_num) (beta_ne_zero_on hx))

lemma continuousOn_J₂ : ContinuousOn J₂ (Icc 0 cutoff) := by
  unfold J₂
  apply ContinuousOn.sub
  · exact continuousOn_const.mul ((continuousOn_const.sub continuous_beta.continuousOn).add
      ((continuous_beta.pow 3).continuousOn.div_const 3))
  · apply ContinuousOn.div_const
    apply ContinuousOn.add
    · exact ((continuousOn_id.pow 2).div continuous_beta.continuousOn
        (fun _ hx ↦ beta_ne_zero_on hx)).sub continuousOn_const
    · exact continuousOn_const.mul continuous_beta.continuousOn

lemma moment_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ cutoff) :
    (∫ x in a..b, density x) = J₀ b - J₀ a ∧
    (∫ x in a..b, x * density x) = J₁ b - J₁ a ∧
    (∫ x in a..b, x ^ 2 * density x) = J₂ b - J₂ a := by
  have hsub : Icc a b ⊆ Icc 0 cutoff := Icc_subset_Icc ha hb
  have hd : ContinuousOn density (Icc a b) := continuousOn_density.mono hsub
  have hx {x : ℝ} (hx : x ∈ Ioo a b) : x ∈ Ioo 0 1 :=
    ⟨ha.trans_lt hx.1, hx.2.trans_le hb |>.trans cutoff_lt_one⟩
  refine ⟨intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_J₀.mono hsub) (fun _ hh ↦ hasDerivAt_J₀ (hx hh))
    (hd.intervalIntegrable_of_Icc hab), ?_, ?_⟩
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (continuousOn_J₁.mono hsub) (fun _ hh ↦ hasDerivAt_J₁ (hx hh))
      ((continuousOn_id.mul hd).intervalIntegrable_of_Icc hab)
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (continuousOn_J₂.mono hsub) (fun _ hh ↦ hasDerivAt_J₂ (hx hh))
      (((continuousOn_id.pow 2).mul hd).intervalIntegrable_of_Icc hab)

lemma moments_zero : J₀ 0 = 0 ∧ J₁ 0 = 0 ∧ J₂ 0 = 0 := by
  norm_num [J₀, J₁, J₂, rawWeight, beta]

lemma rhoChord_le {h a b x : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a < b)
    (hx : x ∈ Icc a b) : rhoChord h a b x ≤ rho (x / h) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hη : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
  have hc := concaveOn_rho.2 (show a / h ∈ Ici 0 from div_nonneg ha hh.le)
    (show b / h ∈ Ici 0 from div_nonneg (ha.trans hab.le) hh.le)
    (div_nonneg (sub_nonneg.2 hx.2) hba.le) (div_nonneg (sub_nonneg.2 hx.1) hba.le) hη
  simp only [smul_eq_mul] at hc
  have ht : (b - x) / (b - a) * (a / h) + (x - a) / (b - a) * (b / h) = x / h := by
    field_simp
    ring
  rw [ht] at hc
  have heq : rhoChord h a b x = (b - x) / (b - a) * rho (a / h) +
      (x - a) / (b - a) * rho (b / h) := by unfold rhoChord; ring
  rw [heq]
  exact hc

lemma integral_rhoChord {h a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ cutoff) :
    (∫ x in a..b, density x * rhoChord h a b x) = chordMoment h a b := by
  obtain ⟨h₀, h₁, _⟩ := moment_integral ha hab hb
  have hd := continuousOn_density.mono (Icc_subset_Icc ha hb)
  have hdi : IntervalIntegrable density volume a b := hd.intervalIntegrable_of_Icc hab
  have hxi : IntervalIntegrable (fun x ↦ x * density x) volume a b :=
    (continuousOn_id.mul hd).intervalIntegrable_of_Icc hab
  have heq : (fun x ↦ density x * rhoChord h a b x) =
      (fun x ↦ ((b * rho (a / h) - a * rho (b / h)) * density x +
        (rho (b / h) - rho (a / h)) * (x * density x)) / (b - a)) := by
    funext x
    unfold rhoChord
    ring
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_add
    (hdi.const_mul _) (hxi.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h₀, h₁]
  rfl

lemma section_density_integrable (h : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ cutoff) :
    IntervalIntegrable (fun x ↦ density x * sectionLength x h) volume a b :=
  ((continuousOn_density.mono (Icc_subset_Icc ha hb)).mul
    (continuous_sectionLength_X h).continuousOn).intervalIntegrable_of_Icc hab

lemma integral_section_quadratic {h : ℝ} (hh : 0 < h) (hx : h / Real.pi ≤ cutoff) :
    (∫ x in (0 : ℝ)..h / Real.pi, density x * sectionLength x h) =
      Real.pi / h ^ 2 * J₂ (h / Real.pi) := by
  have hx0 : 0 ≤ h / Real.pi := div_nonneg hh.le Real.pi_pos.le
  have hi := (moment_integral (a := 0) le_rfl hx0 hx).2.2
  rw [moments_zero.2.2, sub_zero] at hi
  calc
    _ = ∫ x in (0 : ℝ)..h / Real.pi, (Real.pi / h ^ 2) * (x ^ 2 * density x) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hx0]
      intro x hxx
      have hq : x / h ≤ 1 / Real.pi := by
        apply (div_le_div_iff₀ hh Real.pi_pos).2
        have := (le_div_iff₀ Real.pi_pos).1 hxx.2
        linarith
      change density x * sectionLength x h = _
      rw [sectionLength, minSection_quadratic (div_nonneg hxx.1 hh.le) hq]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, hi]

lemma integral_section_linear {h y : ℝ} (hh : 0 < h)
    (hxy : h / Real.pi ≤ y) (hy : y ≤ cutoff) (hys : y ≤ h * (1 - 1 / Real.pi)) :
    (∫ x in h / Real.pi..y, density x * sectionLength x h) =
      (J₁ y - J₁ (h / Real.pi)) / h := by
  have hx0 : 0 ≤ h / Real.pi := div_nonneg hh.le Real.pi_pos.le
  have hi := (moment_integral hx0 hxy hy).2.1
  calc
    _ = ∫ x in h / Real.pi..y, (x * density x) / h := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hxy]
      intro x hxx
      have ha : 1 / Real.pi ≤ x / h := by
        apply (div_le_div_iff₀ Real.pi_pos hh).2
        have := (div_le_iff₀ Real.pi_pos).1 hxx.1
        linarith
      have hb : x / h ≤ 1 - 1 / Real.pi := (div_le_iff₀ hh).2 (by nlinarith [hxx.2])
      change density x * sectionLength x h = _
      rw [sectionLength, minSection_linear ha hb]
      ring
    _ = _ := by rw [intervalIntegral.integral_div, hi]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma integral_section_chord {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ cutoff) (hsa : h * (1 - 1 / Real.pi) ≤ a) :
    chordMoment h a b ≤ ∫ x in a..b, density x * sectionLength x h := by
  rw [← integral_rhoChord ha hab hb]
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hd := continuousOn_density.mono (Icc_subset_Icc ha hb)
  have hch : Continuous (fun x ↦ rhoChord h a b x) := by unfold rhoChord; fun_prop
  apply intervalIntegral.integral_mono_on hab
    ((hd.mul hch.continuousOn).intervalIntegrable_of_Icc hab)
    (section_density_integrable h ha hab hb)
  intro x hx
  have hxs : 1 - 1 / Real.pi ≤ x / h := (le_div_iff₀ hh).2 (by nlinarith [hx.1])
  rw [sectionLength, minSection_rho hxs]
  exact mul_le_mul_of_nonneg_left (rhoChord_le hh ha hab' hx) (density_nonneg ⟨ha.trans hx.1, hx.2.trans hb⟩)

lemma twoChordBaseline_le {h : ℝ} (hh : 0 < h)
    (hy : h * (1 - 1 / Real.pi) ≤ cutoff) : twoChordBaseline h ≤ baseline h := by
  let x := h / Real.pi
  let y := h * (1 - 1 / Real.pi)
  let z := (y + cutoff) / 2
  let F := fun X ↦ density X * sectionLength X h
  have hx0 : 0 ≤ x := div_nonneg hh.le Real.pi_pos.le
  have hxy : x ≤ y := by
    have hm := mul_le_mul_of_nonneg_left planar_switches.2.1.le hh.le
    simpa only [mul_one_div] using hm
  have hyz : y ≤ z := by dsimp [z]; linarith
  have hzD : z ≤ cutoff := by dsimp [z]; linarith
  have h0y : 0 ≤ y := hx0.trans hxy
  have h0z : 0 ≤ z := h0y.trans hyz
  have h0xI := section_density_integrable h (a := 0) le_rfl hx0 (hxy.trans hy)
  have hxyI := section_density_integrable h hx0 hxy hy
  have hyzI := section_density_integrable h h0y hyz hzD
  have hzDI := section_density_integrable h h0z hzD le_rfl
  have hi1 := intervalIntegral.integral_add_adjacent_intervals h0xI hxyI
  have hi2 := intervalIntegral.integral_add_adjacent_intervals (h0xI.trans hxyI) hyzI
  have hi3 := intervalIntegral.integral_add_adjacent_intervals ((h0xI.trans hxyI).trans hyzI) hzDI
  have hq := integral_section_quadratic hh (hxy.trans hy)
  have hl := integral_section_linear hh hxy hy (show y ≤ h * (1 - 1 / Real.pi) from le_rfl)
  have hc1 := integral_section_chord hh h0y hyz hzD (show h * (1 - 1 / Real.pi) ≤ y from le_rfl)
  have hc2 := integral_section_chord hh h0z hzD le_rfl (show h * (1 - 1 / Real.pi) ≤ z from hyz)
  have heq := baseline_layer_cake hh
  change baseline h + 1 = lambda * h / Real.pi + ell * t h + ∫ X in (0 : ℝ)..cutoff, F X at heq
  change (∫ X in (0 : ℝ)..x, F X) + (∫ X in x..y, F X) = ∫ X in (0 : ℝ)..y, F X at hi1
  change (∫ X in (0 : ℝ)..y, F X) + (∫ X in y..z, F X) = ∫ X in (0 : ℝ)..z, F X at hi2
  change (∫ X in (0 : ℝ)..z, F X) + (∫ X in z..cutoff, F X) = ∫ X in (0 : ℝ)..cutoff, F X at hi3
  change (∫ X in (0 : ℝ)..x, F X) = Real.pi / h ^ 2 * J₂ x at hq
  change (∫ X in x..y, F X) = (J₁ y - J₁ x) / h at hl
  change chordMoment h y z ≤ ∫ X in y..z, F X at hc1
  change chordMoment h z cutoff ≤ ∫ X in z..cutoff, F X at hc2
  change lambda * h / Real.pi + ell * t h - 1 + Real.pi / h ^ 2 * J₂ x +
    (J₁ y - J₁ x) / h + chordMoment h y z + chordMoment h z cutoff ≤ baseline h
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma coarse_switch_bounds : (17 / 25 : ℝ) ≤ 1 - 1 / Real.pi ∧
    1 - 1 / Real.pi ≤ 15 / 22 := by
  constructor
  · have hp : (25 / 8 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    have hi : 1 / Real.pi ≤ (8 / 25 : ℝ) := (div_le_iff₀ Real.pi_pos).2 (by linarith)
    linarith
  · have hp : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
    have hi : (7 / 22 : ℝ) ≤ 1 / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by linarith)
    linarith

lemma coarse_cutoff_bounds : (49 / 50 : ℝ) ≤ cutoff ∧ cutoff ≤ 99 / 100 := by
  constructor <;> nlinarith [cutoff_pos, cutoff_sq]

lemma twoChordBaseline_le_of_range_oai {h : ℝ} (hh : 0 < h) (hu : h ≤ 71 / 50) :
    twoChordBaseline h ≤ baseline h := by
  apply twoChordBaseline_le hh
  have he := mul_le_mul_of_nonneg_left coarse_switch_bounds.2 hh.le
  nlinarith [coarse_cutoff_bounds.1]

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range_oai
