-- Prove2me | solution 1 for NoHair.ingoing_areal_angular_ricci
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:23:51.457041+00:00
-- url     : https://prove2.me/submissions/00e21c83-4d20-4bb9-99a9-8fb13e79268a

import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair NoHair.KNE Filter
open scoped Topology BigOperators

noncomputable section

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

private lemma fourIndices (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> decide

private def polar (A : ℝ → ℝ) (y : E4) : Mat :=
  !![-A (y 1), 1, 0, 0; 1, 0, 0, 0; 0, 0, y 1 ^ 2 / (1 - y 2 ^ 2), 0;
     0, 0, 0, y 1 ^ 2 * (1 - y 2 ^ 2)]

private def inversePolar (a r z : ℝ) : Mat :=
  !![0, 1, 0, 0; 1, a, 0, 0; 0, 0, (1 - z ^ 2) / r ^ 2, 0;
     0, 0, 0, 1 / (r ^ 2 * (1 - z ^ 2))]

private lemma polarInverse (A : ℝ → ℝ) (y : E4) (hr : y 1 ≠ 0)
    (hz : 1 - y 2 ^ 2 ≠ 0) : invMetric (polar A) y = inversePolar (A (y 1)) (y 1) (y 2) := by
  apply Matrix.inv_eq_right_inv
  let Id4 : Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  have identity : (1 : Mat) = Id4 := by
    ext i j
    rcases fourIndices i with rfl | rfl | rfl | rfl <;>
      rcases fourIndices j with rfl | rfl | rfl | rfl <;> rfl
  rw [identity]
  ext i j
  rcases fourIndices i with rfl | rfl | rfl | rfl <;>
    rcases fourIndices j with rfl | rfl | rfl | rfl <;>
    simp only [polar, inversePolar, Id4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val] <;> norm_num [Matrix.cons_val] <;>
    try field_simp [hr, hz]
  all_goals try ring

private lemma lapseCP (A : ℝ → ℝ) (y : E4) (ha : DifferentiableAt ℝ A (y 1)) :
    HasCP (fun x : E4 => A (x 1)) y (fun k => deriv A (y 1) * coordBasis k 1) := by
  refine ⟨ha.comp y (hasCP_coord y 1).diff, fun k => ?_⟩
  have d := (hasCP_coord y 1).line k
  have h := (show HasDerivAt A (deriv A (y 1)) ((y + (0 : ℝ) • coordBasis k) 1) by
    simpa using ha.hasDerivAt).comp 0 d
  exact h

private def partialPolar (a' r z dr dz : ℝ) : Mat :=
  let s := 1 - z ^ 2
  let ds := 0 - 2 * z ^ 1 * dz
  let dh := 2 * r ^ 1 * dr
  !![-(a' * dr), 0, 0, 0; 0, 0, 0, 0; 0, 0, (dh * s - r ^ 2 * ds) / s ^ 2, 0;
     0, 0, 0, dh * s + r ^ 2 * ds]

private lemma polarPartial (A : ℝ → ℝ) (y : E4) (ha : DifferentiableAt ℝ A (y 1))
    (hz : 1 - y 2 ^ 2 ≠ 0) (i j d : Fin 4) :
    coordPartial (fun w => polar A w i j) d y =
      partialPolar (deriv A (y 1)) (y 1) (y 2) (coordBasis d 1) (coordBasis d 2) i j := by
  have h := (hasCP_coord y 1).pow 2
  have s := (HasCP.cst 1 y).sub ((hasCP_coord y 2).pow 2)
  have h22 := (h.div s hz).eq d
  have h33 := (h.mul s).eq d
  fin_cases i <;> fin_cases j <;> first
    | exact (HasCP.cst 0 y).eq d
    | exact (HasCP.cst 1 y).eq d
    | exact (lapseCP A y ha).neg.eq d
    | exact h22
    | exact h33

private def connection (a da r z : ℝ) : Fin 4 → Mat :=
  let s := 1 - z ^ 2
  ![!![da / 2, 0, 0, 0; 0, 0, 0, 0; 0, 0, -r / s, 0; 0, 0, 0, -(r * s)],
    !![a * da / 2, -da / 2, 0, 0; -da / 2, 0, 0, 0;
       0, 0, -(a * r) / s, 0; 0, 0, 0, -(a * r * s)],
    !![0, 0, 0, 0; 0, 0, 1 / r, 0; 0, 1 / r, z / s, 0; 0, 0, 0, z * s],
    !![0, 0, 0, 0; 0, 0, 0, 1 / r; 0, 0, 0, -z / s; 0, 1 / r, -z / s, 0]]

private lemma basisRadial (i : Fin 4) : coordBasis i 1 = (![0, 1, 0, 0] : Fin 4 → ℝ) i := by
  fin_cases i <;> rfl

private lemma basisLatitude (i : Fin 4) : coordBasis i 2 = (![0, 0, 1, 0] : Fin 4 → ℝ) i := by
  fin_cases i <;> rfl

set_option maxHeartbeats 2000000 in
private lemma polarConnection (A : ℝ → ℝ) (y : E4) (hr : y 1 ≠ 0)
    (hz : 1 - y 2 ^ 2 ≠ 0) (ha : DifferentiableAt ℝ A (y 1)) (i j k : Fin 4) :
    christoffel (polar A) y i j k = connection (A (y 1)) (deriv A (y 1)) (y 1) (y 2) i j k := by
  simp only [christoffel, polarInverse A y hr hz, polarPartial A y ha hz, Fin.sum_univ_four]
  rcases fourIndices i with rfl | rfl | rfl | rfl <;>
    rcases fourIndices j with rfl | rfl | rfl | rfl <;>
    rcases fourIndices k with rfl | rfl | rfl | rfl <;>
    simp only [connection, inversePolar, partialPolar, basisRadial, basisLatitude,
      Matrix.of_apply, Matrix.cons_val] <;> norm_num [Matrix.cons_val] <;>
    try field_simp [hr, hz]
  all_goals ring

theorem solution (A : ℝ → ℝ) (R r : ℝ) (hr : 0 < r) (hR : R < r)
    (hA : ∀ s, R < s → DifferentiableAt ℝ A s) :
    let G := fun y : E4 => !![-A (y 1), 1, 0, 0;
      1, 0, 0, 0; 0, 0, y 1 ^ 2 / (1 - y 2 ^ 2), 0;
      0, 0, 0, y 1 ^ 2 * (1 - y 2 ^ 2)]
    ricci G (WithLp.toLp 2 ![0, r, 0, 0]) 3 3 = 1 - A r - r * deriv A r := by
  let y : E4 := WithLp.toLp 2 ![0, r, 0, 0]
  have yr : y 1 = r := rfl
  have yz : y 2 = 0 := rfl
  change ricci (polar A) y 3 3 = _
  have hc1 : Continuous (fun w : E4 => w 1) := by fun_prop
  have hcz : Continuous (fun w : E4 => 1 - w 2 ^ 2) := by fun_prop
  have nz : 1 - y 2 ^ 2 ≠ 0 := by norm_num [yz]
  have eR : ∀ᶠ w in 𝓝 y, R < w 1 := hc1.continuousAt.tendsto.eventually (eventually_gt_nhds (yr.symm ▸ hR))
  have er : ∀ᶠ w in 𝓝 y, w 1 ≠ 0 := hc1.continuousAt.eventually_ne (yr.symm ▸ hr.ne')
  have ez : ∀ᶠ w in 𝓝 y, 1 - w 2 ^ 2 ≠ 0 := hcz.continuousAt.eventually_ne nz
  let Γ := fun (w : E4) => connection (A (w 1)) (deriv A (w 1)) (w 1) (w 2)
  have conn (i j k : Fin 4) : christoffel (polar A) y i j k = Γ y i j k :=
    polarConnection A y (yr.symm ▸ hr.ne') nz (hA _ (yr.symm ▸ hR)) i j k
  have cp (i j k d : Fin 4) : coordPartial (fun w => christoffel (polar A) w i j k) d y =
      coordPartial (fun w => Γ w i j k) d y := by
    have ev : (fun w => christoffel (polar A) w i j k) =ᶠ[𝓝 y] fun w => Γ w i j k := by
      filter_upwards [eR, er, ez] with w hR' hr' hz'
      exact polarConnection A w hr' hz' (hA _ hR') i j k
    exact congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis d)) ev.fderiv_eq
  have diag (i : Fin 4) : coordPartial (fun w => christoffel (polar A) w i i 3) 3 y = 0 := by
    rw [cp]
    fin_cases i <;> exact (HasCP.cst 0 y).eq 3
  have divΓ : (∑ i, coordPartial (fun w => christoffel (polar A) w i 3 3) i y) =
      1 - A r - r * deriv A r := by
    have hRad := hasCP_coord y 1
    have hLat := hasCP_coord y 2
    have s := (HasCP.cst 1 y).sub (hLat.pow 2)
    have ha := lapseCP A y (hA _ (yr.symm ▸ hR))
    simp only [Fin.sum_univ_four, cp]
    change coordPartial (fun w : E4 => -(w 1 * (1 - w 2 ^ 2))) 0 y +
      coordPartial (fun w : E4 => -(A (w 1) * w 1 * (1 - w 2 ^ 2))) 1 y +
      coordPartial (fun w : E4 => w 2 * (1 - w 2 ^ 2)) 2 y +
      coordPartial (fun _ : E4 => (0 : ℝ)) 3 y = _
    rw [(hRad.mul s).neg.eq 0, ((ha.mul hRad).mul s).neg.eq 1, (hLat.mul s).eq 2,
      (HasCP.cst 0 y).eq 3]
    norm_num [yr, yz, coordBasis, PiLp.single_apply] <;> ring
  have products : (∑ i, ∑ l, (christoffel (polar A) y i i l * christoffel (polar A) y l 3 3
      - christoffel (polar A) y i 3 l * christoffel (polar A) y l i 3)) = 0 := by
    simp only [conn, Fin.sum_univ_four, Γ, connection, yr, yz, Matrix.of_apply, Matrix.cons_val]
    norm_num <;> ring
  simp only [ricci, riemann, diag, sub_zero, Finset.sum_add_distrib]
  rw [divΓ, products, add_zero]
