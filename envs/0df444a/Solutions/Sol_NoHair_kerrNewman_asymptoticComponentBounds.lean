-- Prove2me | solution 1 for NoHair.kerrNewman_asymptoticComponentBounds
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:16:17.780905+00:00
-- url     : https://prove2.me/submissions/18ce3ce1-1149-4af7-839a-6e948fcd8e87

import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set
open scoped BigOperators

noncomputable section

private abbrev Params := Fin 5 → ℝ

private def cube : Set Params := Icc (fun _ => -1) (fun _ => 1)

private theorem uniform_bound {ι : Type} [Fintype ι] (f : ι → Params → ℝ)
    (hf : ∀ i, Continuous (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i q, q ∈ cube → |f i q| ≤ C := by
  classical
  have ex (i : ι) : ∃ c : ℝ, ∀ q ∈ cube, |f i q| ≤ c := by
    obtain ⟨c, hc⟩ := (show IsCompact cube from isCompact_Icc).bddAbove_image (hf i).abs.continuousOn
    exact ⟨c, fun q hq => hc ⟨q, hq, rfl⟩⟩
  choose c hc using ex
  refine ⟨∑ i, |c i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro i q hq
  exact (hc i q hq).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)))

-- q consists of reciprocal radius, the three spatial components of k, and r²W.
private def atoms (r X Y Z W : ℝ) : Params := ![1/r, X, Y, Z, r^2 * W]
private def direction (q : Params) := Kv (q 1) (q 2) (q 3)
private def prof (m e : ℝ) (q : Params) := (2*m - e^2*q 0) * q 4
private def dDirection (a : ℝ) (q : Params) := dKt (a*q 0) 1 (q 1) (q 2) (q 3) (q 4)
private def dProf (m a e : ℝ) (q : Params) (k : Fin 4) :=
  dfA (a*q 0) m 0 1 (q 1) (q 2) (q 3) (q 4) k +
  e^2*q 0 * dfA (a*q 0) 0 1 1 (q 1) (q 2) (q 3) (q 4) k
private def dPot (a e : ℝ) (q : Params) := dHA (a*q 0) e 1 (q 1) (q 2) (q 3) (q 4)

private def scaledMetric (m e : ℝ) (i j : Fin 4) (q : Params) :=
  prof m e q * direction q i * direction q j
private def scaledGradient (m a e : ℝ) (i j k : Fin 4) (q : Params) :=
  dProf m a e q k * direction q i * direction q j
  + prof m e q * dDirection a q i k * direction q j
  + prof m e q * direction q i * dDirection a q j k
private def scaledPotentialDerivative (a e : ℝ) (i j : Fin 4) (q : Params) :=
  dPot a e q i * direction q j + e*q 4 * dDirection a q j i
private def scaledField (a e : ℝ) (i j : Fin 4) (q : Params) :=
  scaledPotentialDerivative a e i j q - scaledPotentialDerivative a e j i q

private theorem coefficient_bound (m a e : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q ∈ cube, (∀ i j, |scaledMetric m e i j q| ≤ C) ∧
      (∀ i j k, |scaledGradient m a e i j k q| ≤ C) ∧
      (∀ i j, |scaledField a e i j q| ≤ C) := by
  have hd (i : Fin 4) : Continuous (fun q => direction q i) := by
    fin_cases i <;> simp [direction, Kv] <;> fun_prop
  have hf : Continuous (prof m e) := by unfold prof; fun_prop
  have hdk (i j : Fin 4) : Continuous (fun q => dDirection a q i j) := by
    fin_cases i <;> fin_cases j <;> simp [dDirection, dKt] <;> fun_prop
  have hdf (i : Fin 4) : Continuous (fun q => dProf m a e q i) := by
    fin_cases i <;> simp [dProf, dfA] <;> fun_prop
  have hdh (i : Fin 4) : Continuous (fun q => dPot a e q i) := by
    fin_cases i <;> simp [dPot, dHA] <;> fun_prop
  have h1 (i j : Fin 4) : Continuous (scaledMetric m e i j) := ((hf.mul (hd i)).mul (hd j))
  have h2 (i j k : Fin 4) : Continuous (scaledGradient m a e i j k) :=
    ((((hdf k).mul (hd i)).mul (hd j)).add ((hf.mul (hdk i k)).mul (hd j))).add
      ((hf.mul (hd i)).mul (hdk j k))
  have ha (i j : Fin 4) : Continuous (scaledPotentialDerivative a e i j) :=
    ((hdh i).mul (hd j)).add ((continuous_const.mul (continuous_apply 4)).mul (hdk j i))
  have h3 (i j : Fin 4) : Continuous (scaledField a e i j) := (ha i j).sub (ha j i)
  obtain ⟨C1, hp1, hb1⟩ := uniform_bound (fun ij : Fin 4 × Fin 4 => scaledMetric m e ij.1 ij.2)
    (fun ij => h1 ij.1 ij.2)
  obtain ⟨C2, hp2, hb2⟩ := uniform_bound (fun ijk : Fin 4 × Fin 4 × Fin 4 =>
    scaledGradient m a e ijk.1 ijk.2.1 ijk.2.2) (fun ijk => h2 ijk.1 ijk.2.1 ijk.2.2)
  obtain ⟨C3, hp3, hb3⟩ := uniform_bound (fun ij : Fin 4 × Fin 4 => scaledField a e ij.1 ij.2)
    (fun ij => h3 ij.1 ij.2)
  refine ⟨C1+C2+C3, by linarith, fun q hq => ⟨?_, ?_, ?_⟩⟩
  · exact fun i j => (hb1 (i,j) q hq).trans (by linarith)
  · exact fun i j k => (hb2 (i,j,k) q hq).trans (by linarith)
  · exact fun i j => (hb3 (i,j) q hq).trans (by linarith)

-- The component formulas from the coordinate field equations are homogeneous
-- after separating the mass term from the term linear in charge squared.
private theorem scaled_identities (m a e r X Y Z W : ℝ) (hr : r ≠ 0) :
    let q := atoms r X Y Z W
    (∀ i j, scaledMetric m e i j q = r * (fA a m e r W * Kv X Y Z i * Kv X Y Z j)) ∧
    (∀ i j k, scaledGradient m a e i j k q = r^2 * dgA a m e r X Y Z W i j k) ∧
    (∀ i j, scaledField a e i j q = r^2 * FS a e r X Y Z W i j) := by
  let q := atoms r X Y Z W
  have hk (i : Fin 4) : direction q i = Kv X Y Z i := rfl
  have hf : prof m e q = r * fA a m e r W := by
    simp [prof, q, atoms, fA]
    field_simp [hr] <;> ring
  have hH : e*q 4 = r * HA a e r W := by
    change e*(r^2*W) = r * (e*r*W)
    ring
  have hdk (i j : Fin 4) : dDirection a q i j = r * dKt a r X Y Z W i j := by
    fin_cases i <;> fin_cases j <;> simp [dDirection, q, atoms, dKt] <;> field_simp [hr] <;> ring
  have hdf (k : Fin 4) : dProf m a e q k = r^2 * dfA a m e r X Y Z W k := by
    fin_cases k <;> simp [dProf, q, atoms, dfA] <;> field_simp [hr] <;> ring
  have hdh (k : Fin 4) : dPot a e q k = r^2 * dHA a e r X Y Z W k := by
    fin_cases k <;> simp [dPot, q, atoms, dHA] <;> field_simp [hr] <;> ring
  change (∀ i j, scaledMetric m e i j q = _) ∧ (∀ i j k, scaledGradient m a e i j k q = _) ∧
    (∀ i j, scaledField a e i j q = _)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [scaledMetric, hf, hk]
    ring
  · intro i j k
    simp only [scaledGradient, dgA, hdf, hf, hk, hdk]
    ring
  · intro i j
    simp only [scaledField, scaledPotentialDerivative, FS, hdh, hH, hdk, hk]
    ring

private theorem component_formulas (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    let r := ksRadius a y
    let X := ksNull a y 1
    let Y := ksNull a y 2
    let Z := ksNull a y 3
    let W := Wf a y
    (∀ i j, kerrNewmanMetric m a e y i j - minkowski i j = fA a m e r W * Kv X Y Z i * Kv X Y Z j) ∧
    (∀ i j, kerrNewmanField a e y i j = FS a e r X Y Z W i j) := by
  have hk (i : Fin 4) : ksNull a y i = Kv (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) i :=
    congrFun (ksNull_eq_Kv a y) i
  have hh : e * ksRadius a y ^ 3 / (ksRadius a y ^ 4 + a^2 * y 3 ^ 2) =
      HA a e (ksRadius a y) (Wf a y) := by
    rw [ks_x3 a y hy]
    unfold HA Wf
    have hs : ksRadius a y ^ 2 + a ^ 2 * ksNull a y 3 ^ 2 ≠ 0 := by positivity
    have hD : ksRadius a y ^ 4 + a ^ 2 * (ksRadius a y * ksNull a y 3) ^ 2 ≠ 0 := by positivity
    field_simp <;> ring
  constructor
  · intro i j
    unfold kerrNewmanMetric
    rw [profile_eq m a e y hy, hk i, hk j]
    ring
  · intro i j
    have hp (k l : Fin 4) := ((hasCP_H a e y hy).mul (hasCP_K a y hy l)).eq k
    unfold kerrNewmanField
    change coordPartial (fun w => e * ksRadius a w ^ 3 / (ksRadius a w ^ 4 + a ^ 2 * w 3 ^ 2) * ksNull a w j) i y -
      coordPartial (fun w => e * ksRadius a w ^ 3 / (ksRadius a w ^ 4 + a ^ 2 * w 3 ^ 2) * ksNull a w i) j y = _
    rw [hp i j, hp j i]
    beta_reduce
    rw [hh, hk i, hk j]
    rfl

private theorem radius_comparison (a : ℝ) (y : E4) (hy : 2*(|a|+1) < spatialRadius y) :
    1 ≤ ksRadius a y ∧ spatialRadius y ≤ 2*ksRadius a y := by
  let ρ := spatialRadius y
  let r := ksRadius a y
  let c := y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a^2
  let s := Real.sqrt (c^2 + 4*a^2*y 3^2)
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ^2 = y 1^2 + y 2^2 + y 3^2 := Real.sq_sqrt (by positivity)
  have hs : |c| ≤ s := calc
    |c| = Real.sqrt (c^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ s := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (a*y 3)])
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = (c+s)/2 := Real.sq_sqrt (by linarith [neg_abs_le c])
  have hc : ρ^2 - a^2 ≤ r^2 := by
    rw [hρ2, hr2]
    change c ≤ (c+s)/2
    linarith [le_abs_self c]
  change 2*(|a|+1) < ρ at hy
  have hlarge : 2*|a| ≤ ρ := by linarith
  have ha : (2*|a|)^2 ≤ ρ^2 := (sq_le_sq₀ (by positivity) hρ).mpr hlarge
  rw [mul_pow, sq_abs] at ha
  have hRatio : ρ ≤ 2*r := (sq_le_sq₀ hρ (by positivity)).mp (by nlinarith only [ha, hc, sq_nonneg ρ])
  exact ⟨by linarith [abs_nonneg a], hRatio⟩

private theorem atoms_in_cube (a : ℝ) (y : E4) (h1 : 1 ≤ ksRadius a y) :
    atoms (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) ∈ cube := by
  let r := ksRadius a y
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one h1
  have hu : -1 ≤ 1/r ∧ 1/r ≤ 1 := ⟨by linarith [one_div_pos.mpr hr], (div_le_iff₀ hr).mpr (by linarith)⟩
  have hrel := ks_rel a y hr
  have unit (t : ℝ) (ht : t^2 ≤ 1) : -1 ≤ t ∧ t ≤ 1 := by
    constructor <;> nlinarith only [ht, sq_nonneg (t+1), sq_nonneg (t-1)]
  have hX := unit (ksNull a y 1) (by nlinarith only [hrel, sq_nonneg (ksNull a y 2), sq_nonneg (ksNull a y 3)])
  have hY := unit (ksNull a y 2) (by nlinarith only [hrel, sq_nonneg (ksNull a y 1), sq_nonneg (ksNull a y 3)])
  have hZ := unit (ksNull a y 3) (by nlinarith only [hrel, sq_nonneg (ksNull a y 1), sq_nonneg (ksNull a y 2)])
  have hs : 0 < r^2 + a^2 * ksNull a y 3 ^ 2 := by positivity
  have hv : -1 ≤ r^2 * Wf a y ∧ r^2 * Wf a y ≤ 1 := by
    change -1 ≤ r^2*(1/(r^2 + a^2*ksNull a y 3^2)) ∧ r^2*(1/(r^2 + a^2*ksNull a y 3^2)) ≤ 1
    rw [mul_one_div]
    constructor
    · linarith [div_nonneg (sq_nonneg r) hs.le]
    · apply (div_le_iff₀ hs).mpr
      nlinarith only [sq_nonneg (a*ksNull a y 3)]
  constructor <;> intro i <;> fin_cases i <;> simp only [atoms, Matrix.cons_val] <;> tauto

private theorem decay_one {d r ρ C : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r) (hc : ρ ≤ 2*r)
    (hC : 0 ≤ C) (hd : |r*d| ≤ C) : |d| ≤ 4*C / ρ := by
  rw [abs_mul, abs_of_nonneg hr] at hd
  apply (le_div_iff₀ hρ).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hc (abs_nonneg d), hd, hC]

private theorem decay_two {d r ρ C : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r) (hc : ρ ≤ 2*r)
    (hd : |r^2*d| ≤ C) : |d| ≤ 4*C / ρ^2 := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg r)] at hd
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  have hc2 := (sq_le_sq₀ hρ.le (show 0 ≤ 2*r by positivity)).mpr hc
  nlinarith only [mul_le_mul_of_nonneg_left hc2 (abs_nonneg d), hd]

theorem solution (m a e L : ℝ) :
    ∃ R C : ℝ, max 0 L < R ∧ ∀ y ∈ exteriorRegion R,
      0 < ksRadius a y ∧
      (∀ i j, |kerrNewmanMetric m a e y i j - minkowski i j| ≤ C / spatialRadius y) ∧
      (∀ i j k, |coordPartial (fun z => kerrNewmanMetric m a e z i j) k y| ≤ C / spatialRadius y ^ 2) ∧
      (∀ i j, |kerrNewmanField a e y i j| ≤ C / spatialRadius y ^ 2) := by
  obtain ⟨C, hC, hb⟩ := coefficient_bound m a e
  let R := max (max 0 L) (2*(|a|+1)) + 1
  have hL : max 0 L < R := by dsimp [R]; linarith [le_max_left (max 0 L) (2*(|a|+1))]
  refine ⟨R, 4*C, hL, fun y hy => ?_⟩
  change R < spatialRadius y at hy
  have hρ : 0 < spatialRadius y := ((le_max_left 0 L).trans_lt hL).trans hy
  have hlarge : 2*(|a|+1) < spatialRadius y := by
    dsimp [R] at hy
    linarith [le_max_right (max 0 L) (2*(|a|+1))]
  obtain ⟨h1, hc⟩ := radius_comparison a y hlarge
  have hr := lt_of_lt_of_le zero_lt_one h1
  obtain ⟨hM, hD, hF⟩ := hb _ (atoms_in_cube a y h1)
  obtain ⟨hSM, hSD, hSF⟩ := scaled_identities m a e (ksRadius a y) (ksNull a y 1)
    (ksNull a y 2) (ksNull a y 3) (Wf a y) hr.ne'
  obtain ⟨hmetric, hfield⟩ := component_formulas m a e y hr
  refine ⟨hr, ?_, ?_, ?_⟩
  · intro i j
    apply decay_one hρ hr.le hc hC
    rw [hmetric, ← hSM]
    exact hM i j
  · intro i j k
    apply decay_two hρ hr.le hc
    rw [cp_metric m a e y hr, ← hSD]
    exact hD i j k
  · intro i j
    apply decay_two hρ hr.le hc
    rw [hfield, ← hSF]
    exact hF i j
