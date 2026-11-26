-- Prove2me | solution 1 for LogLogJam.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:25:52.207934+00:00
-- url     : https://prove2.me/submissions/9b6b1617-5205-4982-a7d8-2be90420ada6

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

open MeasureTheory Filter LogLogJam
open scoped ENNReal Topology

private theorem sigmaPositive {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (hp : ∀ x, 0 < u x) (hm : Measurable u)
    (hn : ∫⁻ x, ENNReal.ofReal (u x) ∂μ = 1) : SigmaFinite μ := by
  let r (n : ℕ) := ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hr n : r n ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  refine ⟨⟨⟨(fun n => {x | r n ≤ ENNReal.ofReal (u x)}), fun _ => Set.mem_univ _, ?_, ?_⟩⟩⟩
  · intro n
    have h := meas_ge_le_lintegral_div (μ := μ) hm.ennreal_ofReal.aemeasurable (hr n) ENNReal.ofReal_ne_top
    rw [hn] at h
    exact h.trans_lt (ENNReal.div_lt_top (by simp) (hr n))
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hp x)
    exact Set.mem_iUnion.mpr ⟨n, ENNReal.ofReal_le_ofReal hn.le⟩

/-- Orthogonality of a centered conditional score to a constant. Cancellation
uses the integrable linear term, even when the quadratic information is infinite. -/
private theorem centered_square {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (b db : Y → ℝ) (k : ℝ) (hb : ∀ y, 0 < b y) (hm : Measurable b)
    (hd : Measurable db) (hn : ∫⁻ y, ENNReal.ofReal (b y) ∂ν = 1)
    (hi : Integrable db ν) (hz : ∫ y, db y ∂ν = 0) :
    ∫⁻ y, ENNReal.ofReal (b y * (k + db y / b y)^2) ∂ν =
      ENNReal.ofReal (k^2) + ∫⁻ y, ENNReal.ofReal (b y * (db y / b y)^2) ∂ν := by
  let c (y : Y) := 2*k*db y
  have hci : Integrable c ν := hi.const_mul _
  have hcm : Measurable c := measurable_const.mul hd
  have hcz : ∫ y, c y ∂ν = 0 := by simp only [c, integral_const_mul, hz, mul_zero]
  have hp : (∫⁻ y, ENNReal.ofReal (c y) ∂ν) ≠ ⊤ := hci.lintegral_lt_top.ne
  have hm' : (∫⁻ y, ENNReal.ofReal (-c y) ∂ν) ≠ ⊤ := hci.neg.lintegral_lt_top.ne
  have hpm : (∫⁻ y, ENNReal.ofReal (c y) ∂ν) = ∫⁻ y, ENNReal.ofReal (-c y) ∂ν := by
    apply (ENNReal.toReal_eq_toReal_iff' hp hm').mp
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hci] at hcz
    linarith
  apply (ENNReal.add_left_inj hm').mp
  have hnegm : Measurable (fun y => ENNReal.ofReal (-c y)) := hcm.neg.ennreal_ofReal
  conv_lhs => rw [← lintegral_add_right _ hnegm]
  conv_rhs => rw [← hpm]
  have hbase : ENNReal.ofReal (k^2) = ∫⁻ y, ENNReal.ofReal (k^2 * b y) ∂ν := by
    simp_rw [ENNReal.ofReal_mul (sq_nonneg k)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hn, mul_one]
  have hbm : Measurable (fun y => ENNReal.ofReal (k^2 * b y)) := (measurable_const.mul hm).ennreal_ofReal
  rw [hbase, ← lintegral_add_left hbm,
    ← lintegral_add_right _ hcm.ennreal_ofReal]
  apply lintegral_congr
  intro y
  have hby := (hb y).le
  have hh : b y * (k + db y / b y)^2 =
      k^2 * b y + b y * (db y / b y)^2 + c y := by
    dsimp [c]; field_simp [ne_of_gt (hb y)]; ring
  have hcross : max (c y) 0 - max (-c y) 0 = c y := by grind
  have hcplus : ENNReal.ofReal (c y) = ENNReal.ofReal (max (c y) 0) := by simp
  have hcminus : ENNReal.ofReal (-c y) = ENNReal.ofReal (max (-c y) 0) := by simp
  rw [hcplus, hcminus, ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _)]
  congr 1
  linarith

theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) (a : ℝ → X → ℝ) (b : ℝ → X → Y → ℝ) (θ : ℝ)
    (ha : ∀ θ x, 0 < a θ x) (hb : ∀ θ x y, 0 < b θ x y)
    (hda : ∀ x, DifferentiableAt ℝ (fun θ' => a θ' x) θ)
    (hdb : ∀ x y, DifferentiableAt ℝ (fun θ' => b θ' x y) θ)
    (hma : Measurable (a θ)) (hmb : Measurable (Function.uncurry (b θ)))
    (hmda : Measurable (fun x => deriv (fun θ' => a θ' x) θ))
    (hmdb : Measurable (Function.uncurry fun x y => deriv (fun θ' => b θ' x y) θ))
    (hanorm : ∫⁻ x, ENNReal.ofReal (a θ x) ∂μ = 1)
    (hbnorm : ∀ x, ∫⁻ y, ENNReal.ofReal (b θ x y) ∂ν = 1)
    (hint : ∀ x, Integrable (fun y => deriv (fun θ' => b θ' x y) θ) ν)
    (hzero : ∀ x, ∫ y, deriv (fun θ' => b θ' x y) θ ∂ν = 0) :
    fisherInfo (μ.prod ν) (fun θ' p => a θ' p.1 * b θ' p.1 p.2) θ =
      fisherInfo μ a θ + ∫⁻ x, ENNReal.ofReal (a θ x) * fisherInfo ν (fun θ' y => b θ' x y) θ ∂μ := by
  classical
  have ex : Nonempty X := by
    by_contra h
    haveI : IsEmpty X := not_nonempty_iff.mp h
    simpa using hanorm
  obtain ⟨x₀⟩ := ex
  letI : SigmaFinite ν := sigmaPositive ν (b θ x₀) (hb θ x₀)
    (hmb.comp (measurable_const.prodMk measurable_id)) (hbnorm x₀)
  let u := fun x => deriv (fun t => a t x) θ / a θ x
  let v := fun x y => deriv (fun t => b t x y) θ / b θ x y
  have hmu : Measurable u := hmda.div hma
  have hmv : Measurable (Function.uncurry v) := hmdb.div hmb
  have hla x : deriv (fun t => Real.log (a t x)) θ = u x :=
    ((hda x).hasDerivAt.log (ha θ x).ne').deriv
  have hlb x y : deriv (fun t => Real.log (b t x y)) θ = v x y :=
    ((hdb x y).hasDerivAt.log (hb θ x y).ne').deriv
  have hlab (x : X) (y : Y) :
      deriv (fun t => Real.log (a t x * b t x y)) θ = u x + v x y := by
    have h := (((hda x).hasDerivAt.mul (hdb x y).hasDerivAt).log
      (mul_ne_zero (ha θ x).ne' (hb θ x y).ne')).deriv
    simp only [Pi.mul_apply] at h
    rw [h]
    dsimp [u,v]
    field_simp [(ha θ x).ne', (hb θ x y).ne']
    <;> ring
  simp only [fisherInfo, hla, hlb, hlab]
  rw [lintegral_prod _ (by
    apply Measurable.aemeasurable
    exact (((hma.comp measurable_fst).mul hmb).ennreal_ofReal).mul
      (((hmu.comp measurable_fst).add hmv).pow_const 2).ennreal_ofReal)]
  have hrow x :
      (∫⁻ y, ENNReal.ofReal (a θ x * b θ x y) * ENNReal.ofReal ((u x + v x y)^2) ∂ν) =
      ENNReal.ofReal (a θ x) * ENNReal.ofReal ((u x)^2) +
        ENNReal.ofReal (a θ x) * ∫⁻ y, ENNReal.ofReal (b θ x y) * ENNReal.ofReal ((v x y)^2) ∂ν := by
    simp_rw [ENNReal.ofReal_mul (ha θ x).le, mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_add]
    congr 1
    have hc := centered_square ν (b θ x) (fun y => deriv (fun t => b t x y) θ) (u x)
      (hb θ x) (hmb.comp (measurable_const.prodMk measurable_id))
      (hmdb.comp (measurable_const.prodMk measurable_id)) (hbnorm x) (hint x) (hzero x)
    simpa only [ENNReal.ofReal_mul (hb θ x _).le, v] using hc
  simp_rw [hrow]
  apply lintegral_add_left
  exact hma.ennreal_ofReal.mul (hmu.pow_const 2).ennreal_ofReal
