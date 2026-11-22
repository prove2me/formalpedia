-- Prove2me | solution 1 for NoHair.TwoCentre.isotropic_electrovac_and_decay
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:45:08.072281+00:00
-- url     : https://prove2.me/submissions/c89f8a50-e834-42f1-83ac-bc1165b666fc

import Definitions.Def_NoHair_TwoCentreIsotropic
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair NoHair.KNE Set Filter Topology

namespace NoHair.TwoCentre.Isotropic

noncomputable section

def disp (c : ℝ) (i : Fin 4) (y : E4) : ℝ := ![0, y 1 - c, y 2, y 3] i
def delta (i k : Fin 4) : ℝ := if i = k ∧ i ≠ 0 then 1 else 0
def radius (c : ℝ) (y : E4) := Real.sqrt (squaredDistance c y)
def poleGrad (c : ℝ) (i : Fin 4) (y : E4) : ℝ := -disp c i y / radius c y ^ 3
def poleHess (c : ℝ) (i k : Fin 4) (y : E4) : ℝ :=
  -delta i k / radius c y ^ 3 + 3 * disp c i y * disp c k y / radius c y ^ 5
def grad (i : Fin 4) (y : E4) := poleGrad (-1) i y + poleGrad 1 i y
def hess (i k : Fin 4) (y : E4) := poleHess (-1) i k y + poleHess 1 i k y

theorem exterior_open : IsOpen exterior := by
  have hs (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  exact (isOpen_lt continuous_const (hs (-1))).inter (isOpen_lt continuous_const (hs 1))

theorem U_pos (y : E4) : 0 < harmonicPotential y := by
  have hn (c : ℝ) : 0 ≤ inverseDistance c y := by unfold inverseDistance; positivity
  unfold harmonicPotential
  linarith [hn (-1), hn 1]

theorem cp_congr {f g : E4 → ℝ} {y : E4} (h : f =ᶠ[𝓝 y] g) (i : Fin 4) :
    coordPartial f i y = coordPartial g i y := by
  unfold coordPartial
  rw [h.fderiv_eq]

private theorem diff_disp (c : ℝ) (i : Fin 4) (y : E4) :
    HasCP (disp c i) y (delta i) := by
  fin_cases i
  · exact (HasCP.cst 0 y).congr_d (by intro k; simp [delta])
  · apply ((hasCP_coord y 1).sub (HasCP.cst c y)).congr_d
    intro k
    fin_cases k <;> norm_num [delta, coordBasis, PiLp.single_apply]
  · apply (hasCP_coord y 2).congr_d
    intro k
    fin_cases k <;> norm_num [delta, coordBasis, PiLp.single_apply] <;> decide
  · apply (hasCP_coord y 3).congr_d
    intro k
    fin_cases k <;> norm_num [delta, coordBasis, PiLp.single_apply] <;> decide

private theorem diff_sqrt {f : E4 → ℝ} {y : E4} {df : Fin 4 → ℝ}
    (h : HasCP f y df) (hne : f y ≠ 0) :
    HasCP (fun z => Real.sqrt (f z)) y (fun i => df i / (2 * Real.sqrt (f y))) := by
  refine ⟨h.diff.sqrt hne, ?_⟩
  intro i
  have hn : f (y + (0 : ℝ) • coordBasis i) ≠ 0 := by simpa using hne
  simpa only [zero_smul, add_zero] using (h.line i).sqrt hn

private theorem diff_radius (c : ℝ) {y : E4} (hy : 0 < squaredDistance c y) :
    HasCP (radius c) y (fun k => disp c k y / radius c y) := by
  have h : HasCP (squaredDistance c) y (fun k => 2 * disp c k y) := by
    apply ((((diff_disp c 1 y).pow 2).add ((diff_disp c 2 y).pow 2)).add
      ((diff_disp c 3 y).pow 2)).congr_d
    intro k
    fin_cases k <;> simp [disp, delta]
  apply (diff_sqrt h hy.ne').congr_d
  intro k
  unfold radius
  ring

private theorem diff_pole (c : ℝ) {y : E4} (hy : 0 < squaredDistance c y) :
    HasCP (inverseDistance c) y (fun k => poleGrad c k y) := by
  have hr : 0 < radius c y := Real.sqrt_pos.2 hy
  apply ((HasCP.cst 1 y).div (diff_radius c hy) hr.ne').congr_d
  intro k
  unfold poleGrad
  field_simp [hr.ne']
  ring

private theorem diff_poleGrad (c : ℝ) (i : Fin 4) {y : E4} (hy : 0 < squaredDistance c y) :
    HasCP (poleGrad c i) y (fun k => poleHess c i k y) := by
  have hr : 0 < radius c y := Real.sqrt_pos.2 hy
  apply ((diff_disp c i y).neg.div ((diff_radius c hy).pow 3) (pow_ne_zero 3 hr.ne')).congr_d
  intro k
  unfold poleHess
  field_simp [hr.ne']
  ring

theorem diff_U {y : E4} (hy : y ∈ exterior) :
    HasCP harmonicPotential y (fun k => grad k y) := by
  apply (((HasCP.cst 1 y).add (diff_pole (-1) hy.1)).add (diff_pole 1 hy.2)).congr_d
  intro k
  simp [grad]

theorem diff_grad (i : Fin 4) {y : E4} (hy : y ∈ exterior) :
    HasCP (grad i) y (fun k => hess i k y) :=
  (diff_poleGrad (-1) i hy.1).add (diff_poleGrad 1 i hy.2)

theorem grad_time (y : E4) : grad 0 y = 0 := by simp [grad, poleGrad, disp]

theorem hess_time (i : Fin 4) (y : E4) : hess 0 i y = 0 := by
  simp [hess, poleHess, delta, disp]

theorem hess_symm (i k : Fin 4) (y : E4) : hess i k y = hess k i y := by
  have hd : delta i k = delta k i := by
    by_cases h : i = k
    · rw [h]
    · simp [delta, h, Ne.symm h]
  simp only [hess, poleHess, hd]
  ring

private theorem pole_trace (c : ℝ) {y : E4} (hy : 0 < squaredDistance c y) :
    poleHess c 1 1 y + poleHess c 2 2 y + poleHess c 3 3 y = 0 := by
  have hr : 0 < radius c y := Real.sqrt_pos.2 hy
  have hs : radius c y ^ 2 = (y 1 - c) ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt hy.le
  change -1 / radius c y ^ 3 + 3 * (y 1 - c) * (y 1 - c) / radius c y ^ 5 +
    (-1 / radius c y ^ 3 + 3 * y 2 * y 2 / radius c y ^ 5) +
    (-1 / radius c y ^ 3 + 3 * y 3 * y 3 / radius c y ^ 5) = 0
  field_simp [hr.ne']
  linear_combination -3 * hs

theorem laplace_U {y : E4} (hy : y ∈ exterior) : hess 1 1 y + hess 2 2 y + hess 3 3 y = 0 := by
  unfold hess
  linarith [pole_trace (-1) hy.1, pole_trace 1 hy.2]

theorem field_values {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    field y i j = (if i = 0 then grad j y / harmonicPotential y ^ 2 else 0) -
      (if j = 0 then grad i y / harmonicPotential y ^ 2 else 0) := by
  have hd (k : Fin 4) : coordPartial electricPotential k y = -grad k y / harmonicPotential y ^ 2 := by
    have h := ((HasCP.cst 1 y).div (diff_U hy) (U_pos y).ne').eq k
    change coordPartial (fun w => 1 / harmonicPotential w) k y = _
    simpa only [zero_mul, one_mul, zero_sub] using h
  simp only [field, hd]
  split_ifs <;> ring

end
end NoHair.TwoCentre.Isotropic

open NoHair NoHair.KNE Set Filter Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic

noncomputable section

def inverseEntry (u : ℝ) (i : Fin 4) : ℝ := if i = 0 then -u ^ 2 else 1 / u ^ 2

theorem inverse_metric (y : E4) :
    invMetric isotropicMetric y = Matrix.diagonal (inverseEntry (harmonicPotential y)) := by
  apply Matrix.inv_eq_right_inv
  rw [isotropicMetric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  have hn := (U_pos y).ne'
  by_cases hi : i = 0 <;> simp [inverseEntry, hi, hn]

theorem metric_volume (y : E4) :
    Real.sqrt |(isotropicMetric y).det| = harmonicPotential y ^ 2 := by
  have hn := (U_pos y).ne'
  have hd : (isotropicMetric y).det = -(harmonicPotential y ^ 4) := by
    rw [isotropicMetric, Matrix.det_diagonal, Fin.prod_univ_four]
    simp (config := {decide := true})
    field_simp
  rw [hd, abs_neg, abs_of_nonneg (by positivity), show harmonicPotential y ^ 4 =
    (harmonicPotential y ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem raised (y : E4) (i j : Fin 4) :
    raiseBoth isotropicMetric field y i j =
      inverseEntry (harmonicPotential y) i * inverseEntry (harmonicPotential y) j * field y i j := by
  classical
  simp [raiseBoth, inverse_metric, Matrix.diagonal_apply, ite_mul, mul_ite, mul_assoc]

private theorem densitized {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    Real.sqrt |(isotropicMetric y).det| * raiseBoth isotropicMetric field y i j =
      (if j = 0 then grad i y else 0) - (if i = 0 then grad j y else 0) := by
  have h := (U_pos y).ne'
  rw [metric_volume, raised, field_values hy]
  unfold inverseEntry
  split_ifs <;> subst_vars <;> field_simp [h] <;> ring

private def electricGrad (i : Fin 4) (y : E4) := grad i y / harmonicPotential y ^ 2
private def electricHess (i k : Fin 4) (y : E4) :=
  hess i k y / harmonicPotential y ^ 2 - 2 * grad i y * grad k y / harmonicPotential y ^ 3

private theorem diff_electricGrad (i : Fin 4) {y : E4} (hy : y ∈ exterior) :
    HasCP (electricGrad i) y (fun k => electricHess i k y) := by
  have h := (U_pos y).ne'
  apply ((diff_grad i hy).div ((diff_U hy).pow 2) (pow_ne_zero 2 h)).congr_d
  intro k
  unfold electricHess
  field_simp [h]
  ring

private theorem electricHess_symm (i k : Fin 4) (y : E4) :
    electricHess i k y = electricHess k i y := by
  unfold electricHess
  rw [hess_symm i k]
  ring

private theorem dfield {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    coordPartial (fun z => field z i j) k y =
      (if i = 0 then electricHess j k y else 0) - (if j = 0 then electricHess i k y else 0) := by
  have hh : (fun z => field z i j) =ᶠ[𝓝 y] (fun z =>
      (if i = 0 then electricGrad j z else 0) - (if j = 0 then electricGrad i z else 0)) :=
    by filter_upwards [exterior_open.mem_nhds hy] with z hz using field_values hz i j
  rw [cp_congr hh]
  split_ifs
  · exact ((diff_electricGrad j hy).sub (diff_electricGrad i hy)).eq k
  · exact ((diff_electricGrad j hy).sub (HasCP.cst 0 y)).eq k
  · exact ((HasCP.cst 0 y).sub (diff_electricGrad i hy)).eq k
  · exact ((HasCP.cst 0 y).sub (HasCP.cst 0 y)).eq k

private theorem dflux {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    coordPartial (fun z => Real.sqrt |(isotropicMetric z).det| * raiseBoth isotropicMetric field z i j) i y =
      (if j = 0 then hess i i y else 0) - (if i = 0 then hess j i y else 0) := by
  have hh : (fun z => Real.sqrt |(isotropicMetric z).det| * raiseBoth isotropicMetric field z i j) =ᶠ[𝓝 y]
      (fun z => (if j = 0 then grad i z else 0) - (if i = 0 then grad j z else 0)) :=
    by filter_upwards [exterior_open.mem_nhds hy] with z hz using densitized hz i j
  rw [cp_congr hh]
  split_ifs
  · exact ((diff_grad i hy).sub (diff_grad j hy)).eq i
  · exact ((diff_grad i hy).sub (HasCP.cst 0 y)).eq i
  · exact ((HasCP.cst 0 y).sub (diff_grad j hy)).eq i
  · exact ((HasCP.cst 0 y).sub (HasCP.cst 0 y)).eq i

theorem maxwell_equations {y : E4} (hy : y ∈ exterior) :
    (∀ ν, ∑ μ, coordPartial
      (fun z => Real.sqrt |(isotropicMetric z).det| * raiseBoth isotropicMetric field z μ ν) μ y = 0) ∧
    (∀ l μ ν, coordPartial (fun z => field z μ ν) l y + coordPartial (fun z => field z ν l) μ y
      + coordPartial (fun z => field z l μ) ν y = 0) := by
  constructor
  · intro ν
    simp only [dflux hy, Fin.sum_univ_four]
    have ht (i) : hess i 0 y = 0 := (hess_symm i 0 y).trans (hess_time i y)
    by_cases h : ν = 0 <;> simp (config := {decide := true}) [h, ht, laplace_U hy]
  · intro l μ ν
    simp only [dfield hy]
    rw [electricHess_symm ν l, electricHess_symm μ l, electricHess_symm ν μ]
    split_ifs <;> ring

end
end NoHair.TwoCentre.Isotropic

open NoHair NoHair.KNE Set Filter Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic

noncomputable section

def metricSlope (u : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 2 / u ^ 3 else 2 * u) else 0

theorem dmetric {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    coordPartial (fun z => isotropicMetric z i j) k y =
      metricSlope (harmonicPotential y) i j * grad k y := by
  simp only [isotropicMetric, Matrix.diagonal_apply, metricSlope]
  split_ifs
  · have hn := (U_pos y).ne'
    have h := (((HasCP.cst 1 y).div ((diff_U hy).pow 2) (pow_ne_zero 2 hn)).neg).eq k
    rw [h]
    field_simp
    ring
  · rw [((diff_U hy).pow 2).eq k]
    ring
  · exact ((HasCP.cst 0 y).eq k).trans (zero_mul _).symm

/-- The connection coefficients are linear combinations of gradient components
divided by U, except Γⁱ₀₀ whose denominator is U⁵. -/
def gammaNumerator (p : Fin 4 → ℝ) (i j k : Fin 4) : ℝ :=
  if i = 0 then -((if j = 0 then p k else 0) + (if k = 0 then p j else 0))
  else if j = 0 then (if k = 0 then -p i else 0)
  else if k = 0 then 0
  else (if i = k then p j else 0) + (if i = j then p k else 0) - (if j = k then p i else 0)

def gammaPower (i j k : Fin 4) : ℕ := if i ≠ 0 ∧ j = 0 ∧ k = 0 then 5 else 1

def gammaValue (u : ℝ) (p : Fin 4 → ℝ) (i j k : Fin 4) : ℝ :=
  gammaNumerator p i j k / u ^ gammaPower i j k

def gammaDerivative (u : ℝ) (p hp : Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  let n := gammaPower i j k
  (gammaNumerator hp i j k * u ^ n -
    gammaNumerator p i j k * (n * u ^ (n - 1) * p l)) / (u ^ n) ^ 2

theorem christoffel_value {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    christoffel isotropicMetric y i j k =
      gammaValue (harmonicPotential y) (fun l => grad l y) i j k := by
  have hn := (U_pos y).ne'
  simp only [christoffel, inverse_metric, Matrix.diagonal_apply, dmetric hy]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp (config := {decide := true}) [metricSlope, inverseEntry, gammaValue, gammaNumerator,
      gammaPower, grad_time] <;> field_simp [hn]

private theorem diff_numerator {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    HasCP (fun z => gammaNumerator (fun l => grad l z) i j k) y
      (fun s => gammaNumerator (fun l => hess l s y) i j k) := by
  unfold gammaNumerator
  split_ifs <;> repeat' first
    | exact diff_grad _ hy
    | exact HasCP.cst 0 _
    | apply HasCP.neg
    | apply HasCP.sub
    | apply HasCP.add

theorem dchristoffel {y : E4} (hy : y ∈ exterior) (i j k l : Fin 4) :
    coordPartial (fun z => christoffel isotropicMetric z i j k) l y =
      gammaDerivative (harmonicPotential y) (fun s => grad s y) (fun s => hess s l y) i j k l := by
  have he : (fun z => christoffel isotropicMetric z i j k) =ᶠ[𝓝 y]
      (fun z => gammaValue (harmonicPotential z) (fun s => grad s z) i j k) := by
    filter_upwards [exterior_open.mem_nhds hy] with z hz using christoffel_value hz i j k
  rw [cp_congr he]
  exact ((diff_numerator hy i j k).div ((diff_U hy).pow (gammaPower i j k))
    (pow_ne_zero _ (U_pos y).ne')).eq l

end
end NoHair.TwoCentre.Isotropic

open NoHair Set Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic

noncomputable section

private def gradSq (p : Fin 4 → ℝ) := p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2

private def ricciValue (u : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 then (if j = 0 then gradSq p / u ^ 6 else 0)
  else if j = 0 then 0 else ((if i = j then gradSq p else 0) - 2 * p i * p j) / u ^ 2

set_option maxHeartbeats 4500000 in
private theorem ricci_formula {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    ricci isotropicMetric y i j = ricciValue (harmonicPotential y) (fun k => grad k y) i j := by
  have hu := (U_pos y).ne'
  have ht (k) : hess k 0 y = 0 := (hess_symm k 0 y).trans (hess_time k y)
  have h21 := hess_symm 2 1 y
  have h31 := hess_symm 3 1 y
  have h32 := hess_symm 3 2 y
  have h33 : hess 3 3 y = -(hess 1 1 y + hess 2 2 y) := by linarith [laplace_U hy]
  simp only [ricci, riemann, dchristoffel hy, christoffel_value hy]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [Fin.sum_univ_four, gammaDerivative, gammaValue, gammaPower,
      gammaNumerator, ricciValue, gradSq, grad_time, ht, hess_time, h21, h31, h32, h33] <;>
    field_simp [hu] <;> ring

private theorem scalar_zero {y : E4} (hy : y ∈ exterior) : scalarCurvature isotropicMetric y = 0 := by
  have hu := (U_pos y).ne'
  simp (config := {decide := true}) [scalarCurvature, Fin.sum_univ_four, inverse_metric,
    Matrix.diagonal_apply, inverseEntry, ricci_formula hy, ricciValue, gradSq]
  field_simp [hu]
  ring

set_option maxHeartbeats 1800000 in
private theorem source_formula {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    maxwellSource isotropicMetric field y i j =
      ricciValue (harmonicPotential y) (fun k => grad k y) i j := by
  have hu := (U_pos y).ne'
  simp only [maxwellSource, inverse_metric, raised, field_values hy]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [Fin.sum_univ_four, Matrix.diagonal_apply, isotropicMetric,
      inverseEntry, ricciValue, gradSq, grad_time] <;> field_simp [hu] <;> ring

/-- The exact coordinate Einstein–Maxwell equations of the no-hair mission hold
throughout the two-centre isotropic exterior. -/
theorem exterior_electrovac (y : E4) (hy : y ∈ exterior) :
    EinsteinMaxwellAt isotropicMetric field y := by
  refine ⟨?_, maxwell_equations hy⟩
  intro i j
  rw [einsteinTensor, scalar_zero hy, mul_zero, zero_mul, sub_zero, ricci_formula hy, source_formula hy]

end
end NoHair.TwoCentre.Isotropic

open NoHair NoHair.KNE Set Matrix

namespace NoHair.TwoCentre.Isotropic

noncomputable section

private theorem radius_from_infinity {y : E4} (hr : 2 < spatialRadius y)
    {c : ℝ} (hc : c = -1 ∨ c = 1) : spatialRadius y / 2 ≤ radius c y := by
  have hr2 : spatialRadius y ^ 2 = y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hd2 : radius c y ^ 2 = (y 1 - c) ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt (by unfold squaredDistance; positivity)
  have hd : 0 ≤ radius c y := Real.sqrt_nonneg _
  have hx : |y 1| ≤ spatialRadius y := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y 2), sq_nonneg (y 3)]
  have hfar : spatialRadius y - 1 ≤ radius c y := by
    rcases hc with rfl | rfl <;> nlinarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  linarith

private theorem displacement_le (c : ℝ) (i : Fin 4) (y : E4) : |disp c i y| ≤ radius c y := by
  have hr : 0 ≤ radius c y := Real.sqrt_nonneg _
  have hr2 : radius c y ^ 2 = (y 1 - c) ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt (by unfold squaredDistance; positivity)
  have h1 : (y 1 - c) ^ 2 ≤ radius c y ^ 2 := by nlinarith [sq_nonneg (y 2), sq_nonneg (y 3)]
  have h2 : y 2 ^ 2 ≤ radius c y ^ 2 := by nlinarith [sq_nonneg (y 1 - c), sq_nonneg (y 3)]
  have h3 : y 3 ^ 2 ≤ radius c y ^ 2 := by nlinarith [sq_nonneg (y 1 - c), sq_nonneg (y 2)]
  fin_cases i
  · simpa [disp] using hr
  · change |y 1 - c| ≤ _
    rwa [← sq_le_sq₀ (abs_nonneg _) hr, sq_abs]
  · change |y 2| ≤ _
    rwa [← sq_le_sq₀ (abs_nonneg _) hr, sq_abs]
  · change |y 3| ≤ _
    rwa [← sq_le_sq₀ (abs_nonneg _) hr, sq_abs]

private theorem far_pole_bounds {y : E4} (hr : 2 < spatialRadius y) {c : ℝ}
    (hc : c = -1 ∨ c = 1) :
    0 < squaredDistance c y ∧ inverseDistance c y ≤ 2 / spatialRadius y ∧
    ∀ i, |poleGrad c i y| ≤ 4 / spatialRadius y ^ 2 := by
  have h := radius_from_infinity hr hc
  have hd : 0 < radius c y := by linarith
  have hR : 0 < spatialRadius y := by linarith
  refine ⟨Real.sqrt_pos.mp hd, ?_, ?_⟩
  · change 1 / radius c y ≤ _
    apply (div_le_div_iff₀ hd hR).2
    linarith
  · intro i
    rw [poleGrad, abs_div, abs_neg, abs_of_pos (pow_pos hd _)]
    calc
      _ ≤ radius c y / radius c y ^ 3 := div_le_div_of_nonneg_right (displacement_le _ _ _) (by positivity)
      _ = 1 / radius c y ^ 2 := by field_simp [hd.ne']
      _ ≤ _ := (div_le_div_iff₀ (pow_pos hd 2) (pow_pos hR 2)).2 (by
        nlinarith [sq_le_sq' (by linarith : -(2 * radius c y) ≤ spatialRadius y)
          (by linarith : spatialRadius y ≤ 2 * radius c y)])

theorem asymptotic_decay {y : E4} (hr : 2 < spatialRadius y) :
    y ∈ exterior ∧ ∀ i j k,
    |isotropicMetric y i j - minkowski i j| ≤ 64 / spatialRadius y ∧
    |coordPartial (fun z => isotropicMetric z i j) k y| ≤ 64 / spatialRadius y ^ 2 ∧
    |field y i j| ≤ 64 / spatialRadius y ^ 2 := by
  obtain ⟨h₁, hI₁, hG₁⟩ := far_pole_bounds hr (c := -1) (Or.inl rfl)
  obtain ⟨h₂, hI₂, hG₂⟩ := far_pole_bounds hr (c := 1) (Or.inr rfl)
  have he : y ∈ exterior := ⟨h₁, h₂⟩
  have hR : 0 < spatialRadius y := by linarith
  have hU : 1 ≤ harmonicPotential y := by
    unfold harmonicPotential inverseDistance
    have h (c : ℝ) : 0 ≤ 1 / Real.sqrt (squaredDistance c y) := by positivity
    linarith [h (-1), h 1]
  have hU' : harmonicPotential y - 1 ≤ 4 / spatialRadius y := by
    unfold harmonicPotential
    simp only [div_eq_mul_inv] at hI₁ hI₂ ⊢
    linarith
  have h3 : harmonicPotential y ≤ 3 := by
    linarith [(div_lt_iff₀ hR).2 (by linarith : (4 : ℝ) < 2 * spatialRadius y)]
  have hgrad (i) : |grad i y| ≤ 8 / spatialRadius y ^ 2 := by
    unfold grad
    calc
      _ ≤ |poleGrad (-1) i y| + |poleGrad 1 i y| := abs_add_le _ _
      _ ≤ 4 / spatialRadius y ^ 2 + 4 / spatialRadius y ^ 2 := add_le_add (hG₁ i) (hG₂ i)
      _ = _ := by ring
  have hsq : 1 ≤ harmonicPotential y ^ 2 := by nlinarith [sq_nonneg (harmonicPotential y - 1)]
  have hcube : 1 ≤ harmonicPotential y ^ 3 := by
    simpa [pow_succ] using mul_le_mul hsq hU (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg _)
  have hmetric : harmonicPotential y ^ 2 - 1 ≤ 64 / spatialRadius y := by
    have hprod := mul_le_mul_of_nonneg_left (show harmonicPotential y + 1 ≤ 4 by linarith) (sub_nonneg.mpr hU)
    simp only [div_eq_mul_inv] at hU' ⊢
    nlinarith [inv_nonneg.mpr hR.le]
  have htmetric : |-(1 / harmonicPotential y ^ 2) - -1| ≤ 64 / spatialRadius y := by
    have hU0 := (U_pos y).ne'
    have heq : -(1 / harmonicPotential y ^ 2) - -1 =
        (harmonicPotential y ^ 2 - 1) / harmonicPotential y ^ 2 := by field_simp; ring
    rw [heq, abs_of_nonneg (by positivity : 0 ≤ (harmonicPotential y ^ 2 - 1) / harmonicPotential y ^ 2)]
    exact (div_le_self (sub_nonneg.mpr hsq) hsq).trans hmetric
  have hquot (i) : |grad i y / harmonicPotential y ^ 2| ≤ 8 / spatialRadius y ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (harmonicPotential y))]
    exact (div_le_self (abs_nonneg _) hsq).trans (hgrad i)
  refine ⟨he, ?_⟩
  intro i j k
  refine ⟨?_, ?_, ?_⟩
  · by_cases hij : i = j
    · subst j
      fin_cases i
      · exact htmetric
      all_goals change |harmonicPotential y ^ 2 - 1| ≤ _; rwa [abs_of_nonneg (sub_nonneg.mpr hsq)]
    · simp [isotropicMetric, minkowski, hij]
      positivity
  · rw [dmetric he, abs_mul]
    have hcoef : |metricSlope (harmonicPotential y) i j| ≤ 6 := by
      unfold metricSlope
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
        linarith [div_le_self (by norm_num : (0 : ℝ) ≤ 2) hcube]
      · rw [abs_of_nonneg (by positivity : 0 ≤ 2 * harmonicPotential y)]
        linarith
      · norm_num
    have hp := mul_le_mul hcoef (hgrad k) (abs_nonneg _) (by norm_num)
    simp only [div_eq_mul_inv] at hp ⊢
    linarith [inv_nonneg.mpr (sq_nonneg (spatialRadius y))]
  · rw [field_values he]
    have hd : 0 ≤ 8 / spatialRadius y ^ 2 := by positivity
    have hi : |if i = 0 then grad j y / harmonicPotential y ^ 2 else 0| ≤ 8 / spatialRadius y ^ 2 := by
      split_ifs; exact hquot j; simpa using hd
    have hj : |if j = 0 then grad i y / harmonicPotential y ^ 2 else 0| ≤ 8 / spatialRadius y ^ 2 := by
      split_ifs; exact hquot i; simpa using hd
    apply (abs_sub _ _).trans
    apply (add_le_add hi hj).trans
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

end
end NoHair.TwoCentre.Isotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Isotropic

theorem solution :
    (∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric field y) ∧
    (∀ y : E4, 2 < spatialRadius y → y ∈ exterior ∧ ∀ i j k,
      |isotropicMetric y i j - minkowski i j| ≤ 64 / spatialRadius y ∧
      |coordPartial (fun z => isotropicMetric z i j) k y| ≤ 64 / spatialRadius y ^ 2 ∧
      |field y i j| ≤ 64 / spatialRadius y ^ 2) :=
  ⟨fun y hy => exterior_electrovac y hy, fun _ hy => asymptotic_decay hy⟩
