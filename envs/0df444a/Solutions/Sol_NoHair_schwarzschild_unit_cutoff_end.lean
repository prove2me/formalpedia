-- Prove2me | solution 1 for NoHair.schwarzschild_unit_cutoff_end
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:45:49.368796+00:00
-- url     : https://prove2.me/submissions/9f2bda9b-e04a-4f03-bf30-0d7459e12a5b

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

private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2) = Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero, Real.sqrt_sq hp]
  congr 1
  ring

private theorem bounds (m : ℝ) : ∃ C : ℝ, ∀ y ∈ exteriorRegion 1,
      0 < ksRadius 0 y ∧
      (∀ i j, |kerrNewmanMetric m 0 0 y i j - minkowski i j| ≤ C / spatialRadius y) ∧
      (∀ i j k, |coordPartial (fun z => kerrNewmanMetric m 0 0 z i j) k y| ≤ C / spatialRadius y ^ 2) ∧
      (∀ i j, |kerrNewmanField 0 0 y i j| ≤ C / spatialRadius y ^ 2) := by
  obtain ⟨C, hC, hb⟩ := coefficient_bound m 0 0
  refine ⟨4*C, fun y hy => ?_⟩
  change 1 < spatialRadius y at hy
  have hρ : 0 < spatialRadius y := by linarith
  have h1 : 1 ≤ ksRadius 0 y := by rw [radius_eq]; exact hy.le
  have hc : spatialRadius y ≤ 2 * ksRadius 0 y := by rw [radius_eq]; linarith
  have hr := lt_of_lt_of_le zero_lt_one h1
  obtain ⟨hM, hD, hF⟩ := hb _ (atoms_in_cube 0 y h1)
  obtain ⟨hSM, hSD, hSF⟩ := scaled_identities m 0 0 (ksRadius 0 y) (ksNull 0 y 1)
    (ksNull 0 y 2) (ksNull 0 y 3) (Wf 0 y) hr.ne'
  obtain ⟨hmetric, hfield⟩ := component_formulas m 0 0 y hr
  refine ⟨hr, ?_, ?_, ?_⟩
  · intro i j
    apply decay_one hρ hr.le hc hC
    rw [hmetric, ← hSM]
    exact hM i j
  · intro i j k
    apply decay_two hρ hr.le hc
    rw [cp_metric m 0 0 y hr, ← hSD]
    exact hD i j k
  · intro i j
    apply decay_two hρ hr.le hc
    rw [hfield, ← hSF]
    exact hF i j

open scoped ContDiff Manifold Topology

private abbrev I4 := 𝓘(ℝ, E4)

private theorem inclusion_deriv (U : TopologicalSpace.Opens E4) (x : U) :
    (mfderiv I4 I4 (Subtype.val : U → E4) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
  mfderiv_extChartAt_self (I := I4) (x := x)

private theorem inclusion_diff (U : TopologicalSpace.Opens E4) (x : U) :
    MDifferentiableAt I4 I4 (Subtype.val : U → E4) x :=
  (contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp)

private theorem translate_the_fields (m a e s : ℝ) (y : E4) :
    kerrNewmanMetric m a e (y + s • coordBasis 0) = kerrNewmanMetric m a e y ∧
    kerrNewmanField a e (y + s • coordBasis 0) = kerrNewmanField a e y := by
  have h3 (x : E4) : (x + s • coordBasis 0) 3 = x 3 := NoHair.KNE.time_shift x s 3 (by decide)
  have hA (j : Fin 4) : (fun x : E4 => kerrNewmanPotential a e (x + s • coordBasis 0) j) =
      (fun x : E4 => kerrNewmanPotential a e x j) := by
    funext x
    simp only [kerrNewmanPotential, NoHair.KNE.ksRadius_time, NoHair.KNE.ksNull_time, h3]
  have hd (j : Fin 4) : fderiv ℝ (fun x => kerrNewmanPotential a e x j) (y + s • coordBasis 0) =
      fderiv ℝ (fun x => kerrNewmanPotential a e x j) y := by
    rw [← fderiv_comp_add_right (f := fun x => kerrNewmanPotential a e x j), hA]
  constructor
  · funext i j
    simp only [kerrNewmanMetric, ksProfile, NoHair.KNE.ksRadius_time, NoHair.KNE.ksNull_time, h3]
  · funext i j
    simp only [kerrNewmanField, coordPartial, hd]

private theorem stationary_translation (m a e : ℝ) :
    ∃ φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a,
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ := by
  let U := kerrNewmanSpacetime a
  let φ (s : ℝ) (x : U) : U := ⟨x.val + s • coordBasis 0, by
    change 0 < ksRadius a (x.val + s • coordBasis 0)
    rw [NoHair.KNE.ksRadius_time]
    exact x.property⟩
  have hV : ContMDiff I4 I4 ∞ (Subtype.val : U → E4) := contMDiff_subtype_val
  have hφ (t : ℝ) : ContMDiff I4 I4 ∞ (φ t) := by
    apply (ContMDiff.subtypeVal_comp_iff U (φ t)).mp
    exact hV.add contMDiff_const
  have hD (s : ℝ) (x : U) : (mfderiv I4 I4 (φ s) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    let shift (y : E4) := y + s • coordBasis 0
    have hs : HasFDerivAt shift (ContinuousLinearMap.id ℝ E4) x.val := (hasFDerivAt_id x.val).add_const _
    calc
      _ = (mfderiv I4 I4 (Subtype.val : U → E4) (φ s x)).comp (mfderiv I4 I4 (φ s) x) := by
        rw [inclusion_deriv]
        rfl
      _ = mfderiv I4 I4 ((Subtype.val : U → E4) ∘ φ s) x :=
        (mfderiv_comp x (inclusion_diff U _) ((hφ s).mdifferentiableAt (by simp))).symm
      _ = (mfderiv I4 I4 shift x.val).comp (mfderiv I4 I4 (Subtype.val : U → E4) x) :=
        mfderiv_comp x hs.differentiableAt.mdifferentiableAt (inclusion_diff U x)
      _ = _ := by
        rw [inclusion_deriv, mfderiv_eq_fderiv, hs.fderiv]
        rfl
  refine ⟨φ, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    simp [φ]
  · intro s t x
    apply Subtype.ext
    change x.val + (s + t) • coordBasis 0 = x.val + t • coordBasis 0 + s • coordBasis 0
    rw [add_smul]
    abel
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (hV.comp contMDiff_snd).add (contMDiff_fst.smul contMDiff_const)
  · intro s x v w
    rw [hD]
    change matrixBilin (kerrNewmanMetric m a e (x.val + s • coordBasis 0)) v w = _
    rw [(translate_the_fields m a e s x.val).1]
    rfl
  · intro s x v w
    rw [hD]
    change matrixBilin (kerrNewmanField a e (x.val + s • coordBasis 0)) v w = _
    rw [(translate_the_fields m a e s x.val).2]
    rfl

private theorem basis_entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem solution :
    ∃ (φ : ℝ → kerrNewmanSpacetime 0 → kerrNewmanSpacetime 0) (E : AsymptoticallyFlatEnd (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) φ),
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) φ ∧ E.R = 1 ∧ E.region = ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) := by
  classical
  let m : ℝ := 1
  let a : ℝ := 0
  let e : ℝ := 0
  let R : ℝ := 1
  let U := kerrNewmanSpacetime a
  obtain ⟨φ, hφ, hstation⟩ := stationary_translation m a e
  obtain ⟨C, hbounds⟩ := bounds m
  have hR0 : 0 < R := zero_lt_one
  let S := exteriorRegion R
  have hS : IsOpen S := by
    apply isOpen_lt continuous_const
    unfold spatialRadius
    fun_prop
  let y₀ : E4 := WithLp.toLp 2 ![0, R+1, 0, 0]
  have hy₀ : y₀ ∈ S := by
    change R < Real.sqrt ((R+1)^2 + 0^2 + 0^2)
    simp [Real.sqrt_sq_eq_abs, abs_of_pos (show 0 < R+1 by linarith)]
  let x₀ : U := ⟨y₀, (hbounds y₀ hy₀).1⟩
  let ψ (y : E4) : U := if h : y ∈ U then ⟨y,h⟩ else x₀
  have hv' (y : E4) (hy : y ∈ U) : (ψ y).val = y := by simp [ψ, hy]
  have hv (y : E4) (hy : y ∈ S) : (ψ y).val = y := hv' y (hbounds y hy).1
  have himg : ψ '' S = (Subtype.val : U → E4) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (ψ y).val ∈ S
      rwa [hv y hy]
    · intro hx
      exact ⟨x.val, hx, Subtype.ext (hv x.val hx)⟩
  have hgerm : EqOn ((Subtype.val : U → E4) ∘ ψ) id S := hv
  have hsm : ContMDiffOn I4 I4 ∞ ψ S := by
    intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ S z).mp
    exact ((contMDiff_id (I := I4)).contMDiffOn.congr (fun w hw => hgerm hw)) z hz
  have hder (y : E4) (hy : y ∈ S) :
      (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    have hψ := ((hsm y hy).contMDiffAt (hS.mem_nhds hy)).mdifferentiableAt (by simp)
    have hc := mfderiv_comp y (inclusion_diff U (ψ y)) hψ
    rw [inclusion_deriv] at hc
    change mfderiv I4 I4 ((Subtype.val : U → E4) ∘ ψ) y = (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) at hc
    rw [← hc, mfderiv_eq_fderiv, (hgerm.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq, fderiv_id]
  have hcoeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (hy : y ∈ S) (i j : Fin 4) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) ψ y i j = A y i j := by
    unfold pullbackCoeffs
    rw [hder y hy]
    change matrixBilin (A (ψ y).val) (coordBasis i) (coordBasis j) = A y i j
    rw [hv y hy, basis_entry]
  let E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ := {
    R := R, ψ := ψ, C := C, R_pos := hR0
    diffeo := by
      refine ⟨Subtype.val, mapsTo_image _ _, ?_, hv, ?_, hsm, contMDiff_subtype_val.contMDiffOn⟩
      · rw [himg]; exact fun _ hx => hx
      · rw [himg]; exact fun x hx => Subtype.ext (hv x.val hx)
    isOpen_image := by rw [himg]; exact hS.preimage continuous_subtype_val
    equivariant := by
      intro s y hy
      have hshift : y + s • coordBasis 0 ∈ S := by
        change R < spatialRadius (y + s • coordBasis 0)
        have heq : spatialRadius (y + s • coordBasis 0) = spatialRadius y := by
          simp only [spatialRadius, NoHair.KNE.time_shift y s 1 (by decide),
            NoHair.KNE.time_shift y s 2 (by decide), NoHair.KNE.time_shift y s 3 (by decide)]
        rwa [heq]
      exact Subtype.ext (by rw [hv _ hshift, hφ, hv y hy])
    metric_decay := by
      intro y hy i j
      have hentry : pullbackCoeffs (kerrNewmanMetricField m a e) ψ y i j = _ := hcoeff (kerrNewmanMetric m a e) y hy i j
      rw [hentry]
      exact (hbounds y hy).2.1 i j
    metric_deriv_decay := by
      intro y hy i j k
      have he : EqOn (fun w => pullbackCoeffs (kerrNewmanMetricField m a e) ψ w i j)
          (fun w => kerrNewmanMetric m a e w i j) S := fun w hw => hcoeff _ w hw i j
      unfold coordPartial
      rw [(he.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq]
      exact (hbounds y hy).2.2.1 i j k
    field_decay := by
      intro y hy i j
      have hentry : pullbackCoeffs (kerrNewmanFieldField a e) ψ y i j = _ := hcoeff (kerrNewmanField a e) y hy i j
      rw [hentry]
      exact (hbounds y hy).2.2.2 i j }
  exact ⟨φ, E, hφ, hstation, rfl, himg⟩
