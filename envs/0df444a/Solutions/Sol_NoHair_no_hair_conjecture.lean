-- Prove2me | solution 1 for NoHair.no_hair_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:24:57.560849+00:00
-- url     : https://prove2.me/submissions/bd95aa3f-0398-45e0-883c-c86f05ac7102

import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_PseudoRiemannianNormalCoordinates
import Definitions.Def_NoHair_kerrNewman
import Definitions.Def_NoHair_kerrNewmanTimeDirection


/-!
# A penetrating Schwarzschild reference end contradicts the formal no-hair conjecture

The standing-hypothesis certificates for the mass-one Schwarzschild solution and
the trapped-shell argument are adapted from the verified Prove2Me submissions
d7495020-76f1-4156-9aba-96f0713e1887 and e680ffac-1f08-46ce-a597-756f81b8dfce.
The circular-orbit calculation below treats arbitrary charge in the comparison
metric. The contradiction consequently uses only the metric pullback clause.
-/
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option Elab.async true

/- Prove2Me theorem NoHair.schwarzschild_unit_cutoff_end (0c64ffc6-957d-4422-b0dc-ce9e2ded4685). -/
namespace IsraelBundle.NoHair_schwarzschild_unit_cutoff_end
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

theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
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

theorem _root_.NoHair.schwarzschild_unit_cutoff_end :
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
end
end IsraelBundle.NoHair_schwarzschild_unit_cutoff_end

/- Prove2Me theorem NoHair.kerrNewman_outerHorizon_futureTrapped (c9973130-c829-4b75-bc23-b60ddc79d7b2). -/
namespace IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped
open NoHair NoHair.KNE Set
open scoped BigOperators Manifold ContDiff

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev T (m a e : ℝ) := kerrNewmanTimeDirection m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def timeC (v : E4) := v 0

theorem dot_symm (u v : V3) : dot3 u v = dot3 v u := by simp [dot3, mul_comm]
theorem dot_add_l (u v w : V3) : dot3 (u+v) w = dot3 u w + dot3 v w := by
  simp [dot3, add_mul, Finset.sum_add_distrib]
theorem dot_add_r (u v w : V3) : dot3 u (v+w) = dot3 u v + dot3 u w := by
  simp [dot3, mul_add, Finset.sum_add_distrib]
theorem dot_scale_l (c : ℝ) (u v : V3) : dot3 (c • u) v = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_assoc]
theorem dot_scale_r (c : ℝ) (u v : V3) : dot3 u (c • v) = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
theorem dot_cauchy (u v : V3) : (dot3 u v)^2 ≤ dot3 u u * dot3 v v := by
  simpa only [dot3, sq] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) u v
theorem axis_unit (a : ℝ) (x : U a) : dot3 (axis a x.val) (axis a x.val) = 1 := by
  simpa [dot3, axis, Fin.sum_univ_three, sq] using ks_rel a x.val x.property

theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(timeC v*timeC w) + dot3 (space v) (space w) +
      ksProfile m a e x.val * (timeC v + dot3 (axis a x.val) (space v)) *
        (timeC w + dot3 (axis a x.val) (space w)) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski, dot3, space, timeC, axis, Fin.sum_univ_three] <;> ring

theorem t_coords (m a e : ℝ) (x : U a) :
    timeC (T m a e x) = 1 + ksProfile m a e x.val / 2 ∧
    space (T m a e x) = -(ksProfile m a e x.val / 2) • axis a x.val := by
  refine ⟨rfl, ?_⟩
  ext i
  fin_cases i <;> rfl

theorem metric_T (m a e : ℝ) (x : U a) (v : E4) :
    G m a e x v (T m a e x) = -timeC v + (ksProfile m a e x.val/2) *
      (timeC v + dot3 (axis a x.val) (space v)) := by
  obtain ⟨ht, hs⟩ := t_coords m a e x
  erw [metric_formula m a e x v (T m a e x), ht, hs, dot_scale_r, dot_scale_r, axis_unit, dot_symm (space v)]
  ring

theorem time_orientation (m a e : ℝ) : IsTimeOrientation (G m a e) (T m a e) := by
  constructor
  · have hc : Continuous (fun x : U a => (T m a e x : E4)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      have hr : Continuous (fun y : U a => ksRadius a y.val) := (continuous_ksRadius a).comp continuous_subtype_val
      have hk (i : Fin 4) : ContinuousAt (fun y : U a => ksNull a y.val i) x :=
        (ksNull_differentiableAt a x.val x.property i).continuousAt.comp continuous_subtype_val.continuousAt
      have hd := (ks_den_pos a x.val x.property).ne'
      have hf : ContinuousAt (fun y : U a => ksProfile m a e y.val) x := by
        unfold ksProfile
        fun_prop (disch := assumption)
      unfold T kerrNewmanTimeDirection
      apply (PiLp.continuous_toLp 2 _).continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      fin_cases i <;> simp only [Matrix.cons_val] <;> fun_prop
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_section]
    have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T m a e y⟩).2 = (T m a e y : E4) := by
      change tangentCoordChange I4 y y y (T m a e y) = _
      exact tangentCoordChange_self (mem_extChartAt_source y)
    simpa only [htr] using hc.continuousAt (x := x)
  · intro x
    obtain ⟨ht,hs⟩ := t_coords m a e x
    erw [metric_T m a e x (T m a e x), ht, hs, dot_scale_r, axis_unit]
    nlinarith

private def radialNormal (a : ℝ) (y : E4) : V3 :=
  let r := ksRadius a y
  let k := axis a y
  let W := Wf a y
  ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]

theorem normal_geometry (a : ℝ) (x : U a) :
    dot3 (radialNormal a x.val) (axis a x.val) = 1 ∧
    dot3 (radialNormal a x.val) (radialNormal a x.val) = (ksRadius a x.val^2 + a^2)*Wf a x.val := by
  let r := ksRadius a x.val
  let k := axis a x.val
  let W := Wf a x.val
  have hrel : k 0^2+k 1^2+k 2^2=1 := ks_rel a x.val x.property
  have hW : W*(r^2+a^2*k 2^2)=1 := ks_W a x.val x.property
  let n : V3 := ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]
  change dot3 n k = 1 ∧ dot3 n n = (r^2+a^2)*W
  constructor
  · calc
      dot3 n k = W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2) := by simp [dot3, n, Fin.sum_univ_three]; ring
      _ = 1 := by rw [hrel, mul_one, hW]
  · calc
      dot3 n n = (r^2+a^2)*W*(W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2)) := by
        simp [dot3, n, Fin.sum_univ_three]; ring
      _ = (r^2+a^2)*W := by rw [hrel, mul_one, hW, mul_one]

theorem radial_derivative (a : ℝ) (x : U a) (v : E4) :
    fderiv ℝ (ksRadius a) x.val v = dot3 (radialNormal a x.val) (space v) := by
  have hv : ∑ i, v i • coordBasis i = v := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four, coordBasis]
  have cp (i : Fin 4) := (hasCP_R a x.val x.property).eq i
  change ∀ (i : Fin 4), fderiv ℝ (ksRadius a) x.val (coordBasis i) = _ at cp
  calc
    _ = fderiv ℝ (ksRadius a) x.val (∑ i, v i • coordBasis i) := congrArg _ hv.symm
    _ = _ := by
      simp only [Fin.sum_univ_four, map_add, map_smul, smul_eq_mul]
      erw [cp 0, cp 1, cp 2, cp 3]
      simp [dot3, radialNormal, space, axis, dRt, Fin.sum_univ_three] <;> ring

private theorem horizon_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : ksRadius a x.val = kerrNewmanOuterRadius m a e) :
    ksProfile m a e x.val = (ksRadius a x.val ^ 2 + a^2) * Wf a x.val ∧ 0 < ksProfile m a e x.val := by
  obtain ⟨hm,he⟩ := hp
  have hs := Real.sq_sqrt (show 0 ≤ m^2-a^2-e^2 by linarith)
  have hc : 2*m*ksRadius a x.val-e^2 = ksRadius a x.val^2+a^2 := by
    rw [hx]
    unfold kerrNewmanOuterRadius
    nlinarith only [hs]
  have heq : ksProfile m a e x.val = (ksRadius a x.val^2+a^2)*Wf a x.val := by
    rw [profile_eq m a e x.val x.property]
    unfold fA
    rw [hc]
  have hr : 0 < ksRadius a x.val := x.property
  refine ⟨heq, ?_⟩
  rw [heq]
  unfold Wf
  positivity

private theorem inward (k n s : V3) (f t : ℝ) (hk : dot3 k k = 1)
    (hnk : dot3 n k = 1) (hn : dot3 n n = f) (hf : 0 < f)
    (htime : -t*t + dot3 s s + f*(t+dot3 k s)*(t+dot3 k s) < 0)
    (hfuture : -t+(f/2)*(t+dot3 k s) < 0) : dot3 n s < 0 := by
  let c := f/2
  let l := t+dot3 k s
  let τ := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hc : 0 < c := by dsimp [c]; linarith
  have hτ : 0 < τ := by dsimp [τ,c,l]; linarith only [hfuture]
  have ff : f=2*c := by dsimp [c]; ring
  have hu : dot3 u u < τ^2 := by
    have h : dot3 u u-τ^2 = -t*t+dot3 s s+f*l*l := by
      simp only [u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, dot_symm s k]
      rw [ff]
      ring
    change -t*t + dot3 s s + f*l*l < 0 at htime
    linarith only [h,htime]
  have hb : dot3 b b = c^2 := by
    simp only [b, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, hnk, dot_symm k n, hn]
    rw [ff]
    ring
  have he : dot3 n s = dot3 b u - c*τ := by
    simp only [b, u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hnk, hk]
    ring
  have hcs := dot_cauchy b u
  rw [hb] at hcs
  have habs : |dot3 b u| < |c*τ| := sq_lt_sq.mp (by
    rw [mul_pow]
    exact hcs.trans_lt (mul_lt_mul_of_pos_left hu (sq_pos_of_pos hc)))
  rw [abs_of_pos (mul_pos hc hτ)] at habs
  rw [he]
  linarith [le_abs_self (dot3 b u)]

private theorem horizon_velocity (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : ksRadius a x.val = kerrNewmanOuterRadius m a e) (v : E4)
    (hv : IsFutureTimelike (G m a e) (T m a e) x v) : fderiv ℝ (ksRadius a) x.val v < 0 := by
  obtain ⟨h1,h2⟩ := hv
  rw [metric_formula] at h1
  rw [metric_T] at h2
  obtain ⟨hnk,hn⟩ := normal_geometry a x
  obtain ⟨hf,hp'⟩ := horizon_profile m a e hp x hx
  rw [radial_derivative]
  apply inward (axis a x.val) (radialNormal a x.val) (space v) (ksProfile m a e x.val) (timeC v)
    (axis_unit a x) hnk (hn.trans hf.symm) hp' _ h2
  simpa only [neg_mul] using h1

theorem _root_.NoHair.kerrNewman_outerHorizon_futureTrapped (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    let T := kerrNewmanTimeDirection m a e
    let g := kerrNewmanMetricField m a e
    let b := kerrNewmanOuterRadius m a e
    IsTimeOrientation g T ∧ ∀ γ : ℝ → kerrNewmanSpacetime a,
      IsFutureTimelikeCurveIn g T univ γ → ksRadius a (γ 0).val ≤ b → ksRadius a (γ 1).val ≤ b := by
  refine ⟨time_orientation m a e, ?_⟩
  intro γ hγ h0
  let z : ℝ → E4 := Subtype.val ∘ γ
  let h (s : ℝ) := ksRadius a (z s)
  let d (s : ℝ) := fderiv ℝ (ksRadius a) (z s) (velocity γ s)
  let b := kerrNewmanOuterRadius m a e
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hz : ContDiff ℝ 1 z := (hval.comp hγ.1).contDiff
  have deriv (s : ℝ) : HasDerivAt h (d s) s := by
    have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
    rw [hinc] at hcomp
    have hh : fderiv ℝ z s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
      rw [← mfderiv_eq_fderiv]
      exact hcomp
    have hv := ((hz.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hh] at hv
    exact (ksRadius_differentiableAt a (z s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have fence := image_le_of_deriv_right_lt_deriv_boundary (f := h) (f' := d)
    (B := fun _ => b) (B' := fun _ => 0) (a := (0:ℝ)) (b := 1)
    ((continuous_ksRadius a).comp hz.continuous).continuousOn (fun s _ => (deriv s).hasDerivWithinAt) h0
    (fun s => hasDerivAt_const s b)
    (fun s hs he => horizon_velocity m a e hp (γ s) he (velocity γ s) (hγ.2 s (Ico_subset_Icc_self hs)).2)
  exact fence (right_mem_Icc.mpr zero_le_one)
end
end IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped

/- Prove2Me theorem NoHair.kerrNewman_exterior_radialVelocityBound (744f6859-6d54-4439-a20b-6e34fb1538d7). -/
namespace IsraelBundle.NoHair_kerrNewman_exterior_radialVelocityBound
open NoHair NoHair.KNE Set
open scoped BigOperators Manifold ContDiff

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def timeC (v : E4) := v 0

private theorem dot_symm (u v : V3) : dot3 u v = dot3 v u :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_symm u v

private theorem dot_add_l (u v w : V3) : dot3 (u+v) w = dot3 u w + dot3 v w :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_add_l u v w

private theorem dot_add_r (u v w : V3) : dot3 u (v+w) = dot3 u v + dot3 u w :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_add_r u v w

private theorem dot_scale_l (c : ℝ) (u v : V3) : dot3 (c • u) v = c*dot3 u v :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_scale_l c u v

private theorem dot_scale_r (c : ℝ) (u v : V3) : dot3 u (c • v) = c*dot3 u v :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_scale_r c u v

private theorem dot_cauchy (u v : V3) : (dot3 u v)^2 ≤ dot3 u u * dot3 v v :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_cauchy u v

private theorem axis_unit (a : ℝ) (x : U a) : dot3 (axis a x.val) (axis a x.val) = 1 :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.axis_unit a x

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(timeC v*timeC w) + dot3 (space v) (space w) +
      ksProfile m a e x.val * (timeC v + dot3 (axis a x.val) (space v)) *
        (timeC w + dot3 (axis a x.val) (space w)) :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.metric_formula m a e x v w

private def radialNormal (a : ℝ) (y : E4) : V3 :=
  let r := ksRadius a y
  let k := axis a y
  let W := Wf a y
  ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]

private theorem normal_geometry (a : ℝ) (x : U a) :
    dot3 (radialNormal a x.val) (axis a x.val) = 1 ∧
    dot3 (radialNormal a x.val) (radialNormal a x.val) = (ksRadius a x.val^2 + a^2)*Wf a x.val :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.normal_geometry a x

private theorem radial_derivative (a : ℝ) (x : U a) (v : E4) :
    fderiv ℝ (ksRadius a) x.val v = dot3 (radialNormal a x.val) (space v) :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.radial_derivative a x v

private theorem radial_cone_bound (k n s : V3) (f t q : ℝ) (hk : dot3 k k = 1)
    (hnk : dot3 n k = 1) (hn : dot3 n n ≤ f+f*q) (hf : 0 ≤ f) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hv : -t*t + dot3 s s + f*(t+dot3 k s)*(t+dot3 k s) ≤ 0) : dot3 n s ≤ q*t := by
  let c := f/2
  let l := t+dot3 k s
  let τ := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have ff : f=2*c := by dsimp [c]; ring
  have hks := dot_cauchy k s
  rw [hk,one_mul] at hks
  have hspeed : dot3 s s ≤ t^2 := by
    nlinarith only [hv, mul_nonneg hf (sq_nonneg (t+dot3 k s))]
  have habs : |dot3 k s| ≤ t := by
    apply (sq_le_sq₀ (abs_nonneg _) ht).mp
    rw [sq_abs]; exact hks.trans hspeed
  have hl : 0 ≤ l := by dsimp [l]; linarith [neg_abs_le (dot3 k s)]
  have hτ : 0 ≤ τ := by
    by_cases he : l=0
    · simpa [τ,he] using ht
    · have h1 : f*l*l ≤ (t-dot3 k s)*l := by
        dsimp [l]; nlinarith only [hv,hks]
      have h2 := le_of_mul_le_mul_right h1 (lt_of_le_of_ne hl (Ne.symm he))
      dsimp [τ,c,l] at h2 ⊢
      dsimp [l] at hl
      linarith
  have hτt : τ ≤ t := by dsimp only [τ]; linarith only [mul_nonneg hc hl]
  have hu : dot3 u u ≤ τ^2 := by
    have hh : dot3 u u-τ^2 = -t*t+dot3 s s+f*l*l := by
      simp only [u,τ,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hk,dot_symm s k]
      rw [ff]; ring
    change -t*t+dot3 s s+f*l*l ≤ 0 at hv
    linarith only [hh,hv]
  have hb : dot3 b b ≤ (c+q)^2 := by
    simp only [b,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hk,hnk,dot_symm k n]
    rw [ff] at hn
    nlinarith only [hn,sq_nonneg q]
  have he : dot3 n s = dot3 b u - c*τ := by
    simp only [b,u,τ,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hnk,hk]
    ring
  have hnorm : 0 ≤ dot3 u u := Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  have hcq : 0 ≤ c+q := add_nonneg hc hq
  have hbound : |dot3 b u| ≤ (c+q)*τ := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hcq hτ)).mp
    rw [sq_abs,mul_pow]
    exact (dot_cauchy b u).trans (mul_le_mul hb hu hnorm (sq_nonneg _))
  rw [he]
  nlinarith only [le_abs_self (dot3 b u),hbound,mul_le_mul_of_nonneg_left hτt hq]

theorem _root_.NoHair.kerrNewman_exterior_radialVelocityBound (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (x : kerrNewmanSpacetime a)
    (hx : kerrNewmanOuterRadius m a e < ksRadius a x.val) (v : E4)
    (ht : 0 ≤ v 0) (hv : kerrNewmanMetricField m a e x v v ≤ 0) :
    m * fderiv ℝ (ksRadius a) x.val v ≤ (ksRadius a x.val - kerrNewmanOuterRadius m a e) * v 0 := by
  let r := ksRadius a x.val
  let b := kerrNewmanOuterRadius m a e
  let d := Real.sqrt (m^2-a^2-e^2)
  let q := (r-b)/m
  let H := 2*m*r-e^2
  let W := Wf a x.val
  have hm := hp.1
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hx.le) hm.le
  have hq_eq : m*q = r-b := by dsimp [q]; field_simp
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2 = m^2-a^2-e^2 := Real.sq_sqrt (by linarith [hp.2])
  have hbm : 0 ≤ m-d := by
    have hle : d ≤ m := (sq_le_sq₀ hd hm.le).mp (by nlinarith only [hd2,sq_nonneg a,sq_nonneg e])
    linarith
  have hb : b=m+d := rfl
  have hmr : m ≤ r := by change b<r at hx; linarith
  have he2 : e^2 ≤ m^2 := by linarith [hp.2,sq_nonneg a]
  have hH : 0 ≤ H := by dsimp [H]; nlinarith only [mul_le_mul_of_nonneg_left hmr hm.le,he2,sq_nonneg m]
  have hΔ : r^2+a^2-H=(r-b)*(r-(m-d)) := by dsimp [H]; rw [hb]; nlinarith only [hd2]
  have hlin : m*(r-(m-d)) ≤ H := by
    dsimp [H]; nlinarith only [mul_le_mul_of_nonneg_left hmr hm.le,mul_nonneg hm.le hbm,he2]
  have hpoly : r^2+a^2 ≤ H+H*q := by
    have hgap : 0 ≤ r-b := sub_nonneg.mpr hx.le
    have hmul := mul_le_mul_of_nonneg_left hlin hgap
    have fact : m*(r^2+a^2-H) ≤ m*(H*q) := by
      calc
        _ = (r-b)*(m*(r-(m-d))) := by rw [hΔ]; ring
        _ ≤ (r-b)*H := hmul
        _ = m*(H*q) := by rw [← hq_eq]; ring
    linarith only [le_of_mul_le_mul_left fact hm]
  have hW : 0 ≤ W := by dsimp [W,Wf]; positivity
  have hf : ksProfile m a e x.val = H*W := profile_eq m a e x.val x.property
  obtain ⟨hnk,hn⟩ := normal_geometry a x
  have hnn : dot3 (radialNormal a x.val) (radialNormal a x.val) ≤
      ksProfile m a e x.val + ksProfile m a e x.val*q := by
    rw [hn,hf]
    change (r^2+a^2)*W ≤ H*W+H*W*q
    nlinarith only [mul_le_mul_of_nonneg_right hpoly hW]
  erw [metric_formula m a e x v v] at hv
  have h := radial_cone_bound (axis a x.val) (radialNormal a x.val) (space v) (ksProfile m a e x.val)
    (v 0) q (axis_unit a x) hnk hnn (hf ▸ mul_nonneg hH hW) ht hq (by simpa [timeC,neg_mul] using hv)
  rw [radial_derivative]
  calc
    _ ≤ m*(q*v 0) := mul_le_mul_of_nonneg_left h hm.le
    _ = (r-b)*v 0 := by rw [← mul_assoc,hq_eq]
end
end IsraelBundle.NoHair_kerrNewman_exterior_radialVelocityBound

/- Prove2Me theorem NoHair.kerrNewman_regularTensors (68f76ba9-21a0-4e2d-b77e-ee28df7c13f3). -/
namespace IsraelBundle.NoHair_kerrNewman_regularTensors
open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

theorem entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private noncomputable def shear (K : E4 →ₗ[ℝ] ℝ) (n : E4) (c : ℝ) (hn : K n = 0) : E4 ≃ₗ[ℝ] E4 where
  toLinearMap := LinearMap.id - K.smulRight (c • n)
  invFun w := w + K w • (c • n)
  left_inv w := by
    change w - K w • (c • n) + K (w - K w • (c • n)) • (c • n) = w
    simp [hn]
  right_inv w := by
    change w + K w • (c • n) - K (w + K w • (c • n)) • (c • n) = w
    simp [hn]

private theorem ks_basis (f : ℝ) (k : Fin 4 → ℝ)
    (hnull : -(k 0)^2 + (k 1)^2 + (k 2)^2 + (k 3)^2 = 0) :
    ∃ B : Module.Basis (Fin 4) ℝ E4, ∀ i j,
      matrixBilin (fun p q => minkowski p q + f * k p * k q) (B i) (B j) = minkowski i j := by
  let K : E4 →ₗ[ℝ] ℝ := k 0 • EuclideanSpace.projₗ 0 + k 1 • EuclideanSpace.projₗ 1 +
    k 2 • EuclideanSpace.projₗ 2 + k 3 • EuclideanSpace.projₗ 3
  let n : E4 := WithLp.toLp 2 ![-k 0, k 1, k 2, k 3]
  have kv (v : E4) : K v = k 0 * v 0 + k 1 * v 1 + k 2 * v 2 + k 3 * v 3 := rfl
  have hn : K n = 0 := by
    rw [kv]
    change k 0 * (-k 0) + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0
    nlinarith only [hnull]
  have hleft (w : E4) : matrixBilin minkowski n w = K w := by
    rw [matrix_eval, kv]
    simp [Fin.sum_univ_four, minkowski, n] <;> ring
  have hright (v : E4) : matrixBilin minkowski v n = K v := by
    rw [matrix_eval, kv]
    simp [Fin.sum_univ_four, minkowski, n] <;> ring
  have metric (v w : E4) : matrixBilin (fun p q => minkowski p q + f * k p * k q) v w =
      matrixBilin minkowski v w + f * K v * K w := by
    rw [matrix_eval (fun p q => minkowski p q + f * k p * k q) v w, matrix_eval minkowski v w]
    simp only [kv, Fin.sum_univ_four]
    ring
  let P := shear K n (f / 2) hn
  have iso (v w : E4) : matrixBilin (fun p q => minkowski p q + f * k p * k q) (P v) (P w) =
      matrixBilin minkowski v w := by
    rw [metric]
    change matrixBilin minkowski (v - K v • ((f / 2) • n)) (w - K w • ((f / 2) • n)) +
      f * K (v - K v • ((f / 2) • n)) * K (w - K w • ((f / 2) • n)) = matrixBilin minkowski v w
    simp [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      hleft, hright, hn, smul_eq_mul] <;> ring
  let B := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
  refine ⟨B.map P, ?_⟩
  intro i j
  change matrixBilin _ (P (B i)) (P (B j)) = _
  rw [iso]
  have hb (l : Fin 4) : B l = coordBasis l := EuclideanSpace.basisFun_apply (Fin 4) ℝ l
  rw [hb, hb]
  exact entry minkowski i j

private theorem smooth_restrict (U : TopologicalSpace.Opens E4) (A : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ∞ (fun z => A z i j) y) :
    IsSmoothBilinField (M := U) (fun x => matrixBilin (A x.val)) := by
  intro c hc i j y hy
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : U) : c = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ c.target) : (c.symm z).val = z := by
    have eqval (x : U) : c x = x.val := by rw [hchart x] <;> rfl
    exact (eqval (c.symm z)).symm.trans (c.right_inv hz)
  have derivAt (x : U) :
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) c.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    rw [hchart x]
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E4)) (x := x)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
    exact hd
  have coeff (z : E4) (hz : z ∈ c.target) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm z i j = A z i j := by
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz, entry]
  have hs : ContDiffOn ℝ ∞ (fun z => A z i j) c.target := by
    intro z hz
    have hzU : z ∈ U := (hval z hz) ▸ (c.symm z).property
    exact (h z hzU i j).contDiffWithinAt
  exact (hs.congr coeff) y hy

theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z := by
  have hr := radius_smooth a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

theorem _root_.NoHair.kerrNewman_regularTensors (m a e : ℝ) :
    IsLorentzian (kerrNewmanMetricField m a e) ∧
    IsSmoothBilinField (kerrNewmanMetricField m a e) ∧
    IsSmoothBilinField (kerrNewmanFieldField a e) := by
  refine ⟨?_, smooth_restrict (kerrNewmanSpacetime a) (kerrNewmanMetric m a e) ?_,
    smooth_restrict (kerrNewmanSpacetime a) (kerrNewmanField a e) ?_⟩
  · intro x
    exact ks_basis (ksProfile m a e x.val) (ksNull a x.val) (ks_null a x.val x.property)
  · intro y hy i j
    have hpos : 0 < ksRadius a y := hy
    have hr := radius_smooth a y hpos
    have hi := null_smooth a y hpos i
    have hj := null_smooth a y hpos j
    have hd := (ks_den_pos a y hpos).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  · intro y hy i j
    have hpos : 0 < ksRadius a y := hy
    have hr := radius_smooth a y hpos
    have hd := (ks_den_pos a y hpos).ne'
    have hpot (l : Fin 4) : ContDiffAt ℝ ∞ (fun w => kerrNewmanPotential a e w l) y := by
      have hk := null_smooth a y hpos l
      unfold kerrNewmanPotential
      fun_prop (disch := assumption)
    have hpart (k l : Fin 4) : ContDiffAt ℝ ∞ (coordPartial (fun w => kerrNewmanPotential a e w l) k) y :=
      ((hpot l).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    exact (hpart i j).sub (hpart j i)
end IsraelBundle.NoHair_kerrNewman_regularTensors

/- Prove2Me theorem NoHair.kerrNewman_mass_shell_compact_limit (902bc027-c150-42e7-a09b-a7ef36af5cd7). -/
section
open NoHair Set

abbrev massShell (m a _e : ℝ) : Set E4 := {z | m < ksRadius a z}


open NoHair NoHair.KNE Set Filter
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000

/-! Regular parametrized arcs and rounding of causal corners. Matching first derivatives
give a regular join. For a strict corner the quadratic middle arc matches both endpoint jets. -/
namespace NoHair.MassShellJoining
noncomputable section

abbrev U (a : ℝ) := kerrNewmanSpacetime a
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' massShell m a e
private abbrev I4 := 𝓘(ℝ, E4)
abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := hx.le
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
  have hb (i : Fin 4) : |v i| ≤ |v 0| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    fin_cases i <;> simp <;> nlinarith only [hs, sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    exact abs_nonpos_iff.mp (by simpa only [h, abs_zero] using hb i)
  refine ⟨hb, ?_⟩
  by_contra! hprod
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

private theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) :=
  @IsraelBundle.NoHair_kerrNewman_regularTensors.matrix_eval A v w

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z :=
  @IsraelBundle.NoHair_kerrNewman_regularTensors.radius_smooth a z hz

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z :=
  @IsraelBundle.NoHair_kerrNewman_regularTensors.null_smooth a z hz i

theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
  rw [hinc] at hcomp
  have h : fderiv ℝ (fun t => (γ t).val) s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) h).symm.trans hd.deriv

abbrev J := Icc (0:ℝ) 1
abbrev F (m a e : ℝ) (z : E4) := matrixBilin (kerrNewmanMetric m a e z)
noncomputable def W (a : ℝ) (T : VecField (U a)) (z : E4) : E4 := by
  classical
  exact if h : z ∈ U a then (T ⟨z,h⟩ : E4) else 0

theorem W_on (a : ℝ) (T : VecField (U a)) (x : U a) :
    W a T x.val = (T x : E4) := by
  classical
  unfold W
  rw [dif_pos x.property]

theorem W_cont (m a e : ℝ) (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T)
    (x : U a) : ContinuousAt (W a T) x.val := by
  apply (U a).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
  have h := hT.1.continuousAt (x := x)
  rw [FiberBundle.continuousAt_section] at h
  have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T y⟩).2 = (T y : E4) := by
    change tangentCoordChange I4 y y y (T y) = _
    exact tangentCoordChange_self (mem_extChartAt_source y)
  change ContinuousAt (fun y : U a => W a T y.val) x
  rw [show (fun y : U a => W a T y.val) = (fun y : U a => (T y : E4)) from funext (W_on a T)]
  simpa only [htr] using h

theorem eval_smooth (m a e : ℝ) (z v w : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ 1 (fun k : E4 × E4 × E4 => F m a e k.1 k.2.1 k.2.2) (z,v,w) := by
  have hc (i j : Fin 4) : ContDiffAt ℝ ∞ (fun y => kerrNewmanMetric m a e y i j) z := by
    have hr := radius_smooth a z hz
    have hi := null_smooth a z hz i
    have hj := null_smooth a z hz j
    have hd := (ks_den_pos a z hz).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  simp_rw [F, matrix_eval]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hk : ContDiffAt ℝ 1 (fun y : E4 => kerrNewmanMetric m a e y i j) z :=
    (hc i j).of_le (show (1:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hk' := hk.comp (f:=fun k : E4×E4×E4 => k.1) (z,v,w) contDiffAt_fst
  exact (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp _ (contDiffAt_fst.comp _ contDiffAt_snd))).mul
    ((((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp _ (contDiffAt_snd.comp _ contDiffAt_snd))).mul hk')

def Good (m a e : ℝ) (T : VecField (U a)) (z v : E4) : Prop :=
  z ∈ massShell m a e ∧ F m a e z v v ≤ 0 ∧ F m a e z v (W a T z) < 0

private theorem good_scale (m a e : ℝ) (T : VecField (U a)) {z v : E4} (h : Good m a e T z v)
    {c : ℝ} (hc : 0<c) : Good m a e T z (c • v) := by
  obtain ⟨hz,hv,hw⟩ := h
  refine ⟨hz, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (mul_nonpos_of_nonneg_of_nonpos hc.le hv)
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc hw

theorem directions (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (T : VecField (U a))
    (hT : IsTimeOrientation (G m a e) T) (x : U a) (v w : E4)
    (hv : Good m a e T x.val v) (hw : Good m a e T x.val w) :
    (∃ c : ℝ, 0<c ∧ v=c • w) ∨ F m a e x.val v w < 0 := by
  have hf := exterior_profile m a e hp x hv.1
  have vn (h : E4) (hh : Good m a e T x.val h) : h ≠ 0 := by
    intro he
    have hh' := hh.2.2
    simp [he] at hh'
  have ht (h : E4) (hh : Good m a e T x.val h) : 0 < h 0 * timeComponent (T x) := by
    apply (cone_estimates m a e x hf h (T x) (vn h hh) hh.2.1 _ (hT.2 x)).2
    exact (show F m a e x.val h (T x : E4)<0 by simpa only [W_on] using hh.2.2)
  have hprod : 0 < v 0*w 0 := by
    rcases mul_pos_iff.mp (ht v hv) with h₁|h₁ <;> rcases mul_pos_iff.mp (ht w hw) with h₂|h₂
    · exact mul_pos h₁.1 h₂.1
    · linarith [h₁.2,h₂.2]
    · linarith [h₁.2,h₂.2]
    · exact mul_pos_of_neg_of_neg h₁.1 h₂.1
  let u : E4 := (w 0) • v - (v 0) • w
  by_cases h : u=0
  · left
    have hw0 := (mul_ne_zero_iff.mp hprod.ne').2
    refine ⟨v 0/w 0, (div_pos_iff.mpr (mul_pos_iff.mp hprod)), ?_⟩
    have hh : (w 0) • v = (v 0) • w := sub_eq_zero.mp h
    ext i
    have ee := congrArg (fun k : E4 => k i) hh
    change w 0*v i = v 0*w i at ee
    change v i = v 0/w 0*w i
    field_simp [hw0]
    linarith
  · right
    have hu0 : u 0 = 0 := by simp [u, smul_eq_mul, mul_comm]
    have hpos : 0 < F m a e x.val u u := by
      by_contra! hle
      have hsq := spatial_squares m a e x hf u hle
      rw [hu0] at hsq
      apply h
      ext i
      fin_cases i
      · exact hu0
      · change u 1=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 2=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 3=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
    let A := F m a e x.val
    have hsym : A w v = A v w := by
      change G m a e x w v = G m a e x v w
      rw [metric_formula, metric_formula]; ring
    change 0 < A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hpos
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hsym] at hpos
    by_contra! hn
    change 0 ≤ A v w at hn
    nlinarith only [hpos, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hv.2.1,
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (v 0)) hw.2.1, mul_nonneg hprod.le hn]

structure Arc where
  pos : ℝ → E4
  vel : ℝ → E4
  hasDeriv : ∀ s, HasDerivAt pos (vel s) s
  continuous_vel : Continuous vel

theorem Arc.smooth (P : Arc) : ContDiff ℝ 1 P.pos := by
  have he : deriv P.pos = P.vel := funext fun s => (P.hasDeriv s).deriv
  exact contDiff_one_iff_deriv.mpr ⟨fun s => (P.hasDeriv s).differentiableAt,he ▸ P.continuous_vel⟩

private def Arc.reparam (P : Arc) (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (hc : Continuous d) : Arc where
  pos := fun t => P.pos (f t)
  vel := fun t => d t • P.vel (f t)
  hasDeriv s := (P.hasDeriv (f s)).scomp s (hd s)
  continuous_vel := hc.smul (P.continuous_vel.comp (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt))

private def Arc.affine (P : Arc) (c b : ℝ) : Arc :=
  P.reparam (fun s => c*(s-b)) (fun _ => c) (fun s => by
    simpa using (((hasDerivAt_id s).sub_const b).const_mul c)) continuous_const

def join (c : ℝ) (P Q : Arc) (hp : P.pos c=Q.pos c) (hv : P.vel c=Q.vel c) : Arc where
  pos := fun s => if s ≤ c then P.pos s else Q.pos s
  vel := fun s => if s ≤ c then P.vel s else Q.vel s
  continuous_vel := continuous_if_le continuous_id continuous_const P.continuous_vel.continuousOn
    Q.continuous_vel.continuousOn (fun _ he => he ▸ hv)
  hasDeriv s := by
    rcases lt_trichotomy s c with h|rfl|h
    · rw [if_pos h.le]
      apply (P.hasDeriv s).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds h] with t ht using if_pos ht.le
    · rw [if_pos le_rfl]
      apply hasDerivWithinAt_univ.mp
      rw [← Iic_union_Ici (a := s)]
      apply HasDerivWithinAt.union
      · exact (P.hasDeriv s).hasDerivWithinAt.congr_of_mem (fun t ht => if_pos ht) (Set.mem_Iic.mpr (le_refl s))
      · rw [hv]
        apply (Q.hasDeriv s).hasDerivWithinAt.congr_of_mem _ (Set.mem_Ici.mpr (le_refl s))
        intro t ht
        by_cases hs : t ≤ s
        · have he : t=s := le_antisymm hs ht
          simpa [he] using hp
        · exact if_neg hs
    · rw [if_neg h.not_ge]
      apply (Q.hasDeriv s).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds h] with t ht using if_neg ht.not_ge

def fromCurve {a : ℝ} (γ : ℝ → U a) (hc : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) : Arc :=
  let hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  let h : ContDiff ℝ 1 (Subtype.val ∘ γ) := (hval.comp hc).contDiff
  ⟨Subtype.val ∘ γ,deriv (Subtype.val ∘ γ),fun s => (h.differentiable (by simp) s).hasDerivAt,
    h.continuous_deriv le_rfl⟩

theorem fromCurve_good (m a e : ℝ) (T : VecField (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    Good m a e T ((fromCurve γ hγ.1).pos s) ((fromCurve γ hγ.1).vel s) := by
  let P := fromCurve γ hγ.1
  have he := ambient_velocity a γ hγ.1 s (P.vel s) (P.hasDeriv s)
  change Good m a e T (γ s).val (P.vel s)
  rw [← he]
  obtain ⟨hx,_,hv,ht⟩ := hγ.2 s hs
  change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4)<0 at ht
  exact ⟨hx,hv,by rw [W_on]; exact ht⟩

private theorem realize (m a e : ℝ) (T : VecField (U a)) (P : Arc) (L : ℝ) (hL : 0<L)
    (p q : U a) (h0 : P.pos 0=p.val) (h1 : P.pos L=q.val) (hU : ∀ s, P.pos s∈U a)
    (hg : ∀ s ∈ Icc (0:ℝ) L, Good m a e T (P.pos s) (P.vel s)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
  let γ (s : ℝ) : U a := ⟨P.pos (L*s),hU _⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := P.smooth.comp (contDiff_const.mul contDiff_id)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := by
    intro s
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext (by simpa [γ] using h0),Subtype.ext (by simpa [γ] using h1)⟩
  intro s hs
  have hls : L*s∈Icc (0:ℝ) L := ⟨mul_nonneg hL.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 hL.le⟩
  have h := good_scale m a e T (hg _ hls) hL
  have hd : HasDerivAt (fun t => (γ t).val) (L • P.vel (L*s)) s :=
    (P.hasDeriv (L*s)).scomp s (by simpa using (hasDerivAt_id s).const_mul L)
  have he := ambient_velocity a γ hγ s _ hd
  have htg : G m a e (γ s) (velocity γ s) (T (γ s)) < 0 := by
    change F m a e (γ s).val (velocity γ s : E4) (T (γ s) : E4) < 0
    rw [he, ← W_on a T (γ s)]
    exact h.2.2
  refine ⟨h.1,?_,?_,htg⟩
  · intro hh
    simp [hh] at htg
  · change F m a e (γ s).val (velocity γ s : E4) (velocity γ s : E4) ≤ 0
    rw [he]
    exact h.2.1

def middleTime (d s : ℝ) := (s-(1-d))/(2*d)
def middle (d : ℝ) (hd : 0<d) (P Q : Arc) (y : E4) : Arc where
  pos s := let u := middleTime d s; P.pos (1-d*(1-u)^2)+Q.pos (d*u^2)-y
  vel s := let u := middleTime d s; (1-u) • P.vel (1-d*(1-u)^2) + u • Q.vel (d*u^2)
  continuous_vel := by
    have h := P.continuous_vel
    have h' := Q.continuous_vel
    unfold middleTime
    fun_prop
  hasDeriv s := by
    let u := middleTime d
    have hu : HasDerivAt u (1/(2*d)) s := by
      change HasDerivAt (fun t : ℝ => (t-(1-d))/(2*d)) (1/(2*d)) s
      exact ((hasDerivAt_id s).sub_const (1-d)).div_const (2*d)
    have hα : HasDerivAt (fun t => 1-d*(1-u t)^2) (1-u s) s := by
      have h := (((hu.const_sub 1).pow 2).const_mul d).const_sub 1
      apply h.congr_deriv
      field_simp [hd.ne'] <;> ring
    have hβ : HasDerivAt (fun t => d*(u t)^2) (u s) s := by
      have h := (hu.pow 2).const_mul d
      apply h.congr_deriv
      field_simp [hd.ne'] <;> ring
    exact (((P.hasDeriv _).scomp s hα).add ((Q.hasDeriv _).scomp s hβ)).sub_const y

private theorem use_join (c : ℝ) (P Q : Arc) (h : P.pos c=Q.pos c) (h' : P.vel c=Q.vel c)
    (s : ℝ) (R : E4→E4→Prop) (hL : s ≤ c → R (P.pos s) (P.vel s))
    (hR : c ≤ s → R (Q.pos s) (Q.vel s)) :
    R ((join c P Q h h').pos s) ((join c P Q h h').vel s) := by
  by_cases hs : s ≤ c
  · simpa [join,hs] using hL hs
  · simpa [join,hs] using hR (le_of_not_ge hs)

theorem combine_parallel (m a e : ℝ) (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (c : ℝ) (hc : 0<c) (he : P.vel 1=c • Q.vel 0) : q∈causalFuture (G m a e) T (D m a e) p := by
  let B := Q.affine c 1
  have hj : P.pos 1=B.pos 1 := by simpa [B,Arc.affine,Arc.reparam,g0] using h1
  have hv : P.vel 1=B.vel 1 := by simpa [B,Arc.affine,Arc.reparam] using he
  let A := join 1 P B hj hv
  let L := 1+1/c
  have hL : 1<L := by dsimp [L]; linarith [one_div_pos.mpr hc]
  have hlast : c*(L-1)=1 := by dsimp [L]; field_simp [hc.ne'] <;> ring
  apply realize m a e T A L (by linarith) p q
  · simpa [A,join] using h0
  · simpa [A,join,hL.not_ge,B,Arc.affine,Arc.reparam,hlast] using g1
  · intro s
    apply use_join 1 P B hj hv s (fun z _ => z∈U a) (fun _ => pU s) (fun _ => qU _)
  · intro s hs
    apply use_join 1 P B hj hv s (Good m a e T) (fun ht => pG s ⟨hs.1,ht⟩)
    intro ht
    apply good_scale m a e T _ hc
    apply qG _ ⟨mul_nonneg hc.le (sub_nonneg.mpr ht),?_⟩
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 1) hc.le).trans_eq hlast

theorem combine_round (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (d : ℝ) (hd : 0<d) (hd1 : d<1)
    (hmid : ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Good m a e T (P.pos s+Q.pos t-x.val) ((1-u) • P.vel s + u • Q.vel t)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
  let M := middle d hd P Q x.val
  let B := Q.affine 1 1
  have hleft : middleTime d (1-d)=0 := by simp [middleTime]
  have hright : middleTime d (1+d)=1 := by unfold middleTime; field_simp [hd.ne']; ring
  have hj : P.pos (1-d)=M.pos (1-d) := by
    change P.pos (1-d) = P.pos (1-d*(1-middleTime d (1-d))^2)+Q.pos (d*middleTime d (1-d)^2)-x.val
    rw [hleft]
    simp [g0]
  have hv : P.vel (1-d)=M.vel (1-d) := by simp [M,middle,hleft]
  let A := join (1-d) P M hj hv
  have hlt : 1-d < 1+d := by linarith
  have hj' : A.pos (1+d)=B.pos (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,h1,B,Arc.affine,Arc.reparam]
  have hv' : A.vel (1+d)=B.vel (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,B,Arc.affine,Arc.reparam]
  let path := join (1+d) A B hj' hv'
  have hmg (s : ℝ) (hl : 1-d ≤ s) (hr : s ≤ 1+d) : Good m a e T (M.pos s) (M.vel s) := by
    apply hmid (middleTime d s)
    constructor
    · exact div_nonneg (sub_nonneg.mpr hl) (by positivity)
    · apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
      linarith
  have hdu {z : E4} (h : z∈massShell m a e) : z∈U a := by
    change m < ksRadius a z at h
    change 0<ksRadius a z
    linarith only [h,hp.1,Real.sqrt_nonneg (m^2-a^2-e^2)]
  apply realize m a e T path 2 (by norm_num) p q
  · simpa [path,A,join,show (0:ℝ) ≤ 1+d by linarith,show (0:ℝ) ≤ 1-d by linarith] using h0
  · simpa [path,join,show ¬ (2:ℝ) ≤ 1+d by linarith,B,Arc.affine,Arc.reparam,show (2:ℝ)-1=1 by norm_num] using g1
  · intro s
    apply use_join _ A B hj' hv' s (fun z _ => z∈U a) _ (fun _ => qU _)
    intro hr
    exact use_join _ P M hj hv s (fun z _ => z∈U a) (fun _ => pU _) (fun hl => hdu (hmg s hl hr).1)
  · intro s hs
    apply use_join _ A B hj' hv' s (Good m a e T)
    · intro hr
      apply use_join _ P M hj hv s (Good m a e T) _ (fun hl => hmg s hl hr)
      intro hl
      exact pG s ⟨hs.1,by linarith⟩
    · intro hl
      have hJ : s-1∈J := ⟨by linarith,by linarith [hs.2]⟩
      simpa [B,Arc.affine,Arc.reparam] using qG (s-1) hJ


end
end NoHair.MassShellJoining

open NoHair NoHair.KNE Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 270000

/-! The time and signed-energy tests for regular normal geodesics in the Kerr–Newman exterior. -/
namespace NoHair.MassShellGeodesics
noncomputable section

abbrev U (a : ℝ) := kerrNewmanSpacetime a
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' massShell m a e
abbrev I4 := 𝓘(ℝ, E4)
abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w :=
  @NoHair.MassShellJoining.metric_formula m a e x v w

theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val :=
  @NoHair.MassShellJoining.exterior_profile m a e hp x hx

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 :=
  @NoHair.MassShellJoining.spatial_squares m a e x hf v hv

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v :=
  @NoHair.MassShellJoining.spatial_kernel m a e x hf v h0

theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) :=
  @NoHair.MassShellJoining.cone_estimates m a e x hf v w hv hvv hvw hww

private theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) :=
  @IsraelBundle.NoHair_kerrNewman_regularTensors.matrix_eval A v w

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z :=
  @IsraelBundle.NoHair_kerrNewman_regularTensors.radius_smooth a z hz

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z :=
  @IsraelBundle.NoHair_kerrNewman_regularTensors.null_smooth a z hz i

theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v :=
  @NoHair.MassShellJoining.ambient_velocity a γ hγ s v hd

abbrev J := Icc (0:ℝ) 1
abbrev F (m a e : ℝ) (z : E4) := matrixBilin (kerrNewmanMetric m a e z)
noncomputable def W (a : ℝ) (T : VecField (U a)) (z : E4) : E4 := by
  classical
  exact if h : z ∈ U a then (T ⟨z,h⟩ : E4) else 0

theorem W_on (a : ℝ) (T : VecField (U a)) (x : U a) :
    W a T x.val = (T x : E4) :=
  @NoHair.MassShellJoining.W_on a T x

theorem W_cont (m a e : ℝ) (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T)
    (x : U a) : ContinuousAt (W a T) x.val :=
  @NoHair.MassShellJoining.W_cont m a e T hT x

abbrev S (m a e : ℝ) := massShell m a e
theorem openS (m a e : ℝ) : IsOpen (S m a e) := isOpen_lt continuous_const (continuous_ksRadius a)
theorem inU (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (h : z∈S m a e) : z∈U a := by
  change m < ksRadius a z at h
  change 0 < ksRadius a z
  linarith only [hp.1,h,Real.sqrt_nonneg (m^2-a^2-e^2)]

private theorem smooth_scalar_multiple {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (v : Y) :
    ContDiffAt ℝ ∞ (fun z => f z • v) x := hf.smul_const v

set_option backward.defeqAttrib.useBackward true in
theorem field_smooth (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ContDiffOn ℝ ∞ (F m a e) (S m a e) := by
  let P (i : Fin 4) := EuclideanSpace.proj (𝕜:=ℝ) i
  have heP (i : Fin 4) (v : E4) : P i v = v i := rfl
  let B (i j : Fin 4) := (P i).smulRight (P j)
  have he (y : E4) : F m a e y = ∑ i, ∑ j, (kerrNewmanMetric m a e y i j) • B i j := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [F,matrix_eval,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,B,ContinuousLinearMap.smulRight_apply,heP]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  intro y hy
  have hy' : 0 < ksRadius a y := inU m a e hp hy
  apply ContDiffAt.contDiffWithinAt
  rw [show F m a e = fun z => ∑ i, ∑ j, (kerrNewmanMetric m a e z i j) • B i j from funext he]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hcoeff : ContDiffAt ℝ ∞ (fun z : E4 => kerrNewmanMetric m a e z i j) y := by
    have hR := radius_smooth a y hy'
    have hi := null_smooth a y hy' i
    have hj := null_smooth a y hy' j
    have hd := (ks_den_pos a y hy').ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  first
  | exact smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j)
  | convert! smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j) using 1
  | let L : ℝ →L[ℝ] MetricTensor E4 := ContinuousLinearMap.toSpanSingleton ℝ (B i j)
    have hL := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=ℝ) (F:=MetricTensor E4) (n:=∞) L
    exact hL.contDiffAt.comp (f:=fun z : E4 => kerrNewmanMetric m a e z i j) y hcoeff

theorem field_sym (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) (v w : E4) : F m a e z v w=F m a e z w v := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  change G m a e x v w=G m a e x w v
  rw [metric_formula,metric_formula]; ring

theorem field_inv (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) : (F m a e z).IsInvertible := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  obtain ⟨b,hb⟩ := (kerrNewman_regularTensors m a e).1 x
  let M := F m a e z
  change ∀ i j, M (b i) (b j) = minkowski i j at hb
  have hi : Function.Injective M := by
    apply (injective_iff_map_eq_zero M).mpr
    intro v hv
    have hs : (∑ i, b.repr v i • b i) = v := b.sum_repr v
    have hw (j : Fin 4) : (∑ i, b.repr v i * minkowski i j)=0 := by
      have eq := congrArg (fun L : E4 →L[ℝ] ℝ => L (b j)) hv
      change M v (b j)=0 at eq
      rw [←hs] at eq
      simpa only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hb] using eq
    have h0 (i : Fin 4) : b.repr v i = 0 := by
      have h := hw i
      fin_cases i <;> simpa [minkowski,Fin.sum_univ_four] using h
    rw [←hs]
    simp [h0]
  have hdim : Module.finrank ℝ E4=Module.finrank ℝ (E4→L[ℝ]ℝ) := (InnerProductSpace.toDual ℝ E4).toLinearEquiv.finrank_eq
  have hs : Function.Surjective M := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective M (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

theorem nonzero_time (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z v : E4}
    (hz : z∈S m a e) (hn : v≠0) (h : F m a e z v v ≤ 0) : v 0≠0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hs := spatial_squares m a e x (exterior_profile m a e hp x hz) v h
  intro h0
  rw [h0] at hs
  apply hn
  ext i
  fin_cases i
  · exact h0
  · change v 1=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 2=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 3=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]

theorem cone_pair_negative (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {z v w : E4} (hz : z∈S m a e) (hvv : F m a e z v v ≤ 0) (hww : F m a e z w w < 0)
    (hvw : 0 < v 0*w 0) : F m a e z v w < 0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hk := spatial_kernel m a e x (exterior_profile m a e hp x hz) ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul,mul_comm])
  let A := F m a e z
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hk
  have he : A w v = A v w := field_sym m a e hp hz w v
  simp only [map_sub,map_smul,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,he] at hk
  by_contra! h
  change 0 ≤ A v w at h
  have hn := (mul_ne_zero_iff.mp hvw.ne').1
  nlinarith only [hk,mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hn) hww, mul_nonneg hvw.le h]

theorem sign_prop {L : ℝ} {f : ℝ→ℝ} (hc : ContinuousOn f (Icc 0 L))
    (hne : ∀ s∈Icc 0 L, f s≠0) {u : ℝ} (hu : u∈Icc 0 L) (hpos : 0 < f u) :
    ∀ t∈Icc 0 L, 0 < f t := by
  intro t ht
  by_contra! h
  obtain ⟨r,hr,he⟩ := isPreconnected_Icc.intermediate_value ht hu hc (show (0:ℝ)∈Icc (f t) (f u) from ⟨h,hpos.le⟩)
  exact hne _ hr he

theorem time_deriv {c : ℝ→E4} {v : E4} {t : ℝ} (h : HasDerivAt c v t) :
    HasDerivAt (fun s => c s 0) (v 0) t := by
  let P : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hh : HasDerivAt (P ∘ c) (P v) t := P.hasFDerivAt.comp_hasDerivAt t h
  exact hh

theorem clock_positive {L o : ℝ} (hL : 0 < L) (c v : ℝ→E4)
    (hc : ∀ t∈Icc 0 L, HasDerivAt c (v t) t) (hv : ContinuousOn v (Icc 0 L))
    (hne : ∀ t∈Icc 0 L, v t 0≠0) (hdisp : 0 < o*(c L 0-c 0 0)) :
    ∀ t∈Icc 0 L, 0 < o*v t 0 := by
  let d (t : ℝ) := o*(c t 0)
  have hd (t : ℝ) (ht : t∈Icc 0 L) : HasDerivAt d (o*v t 0) t :=
    (time_deriv (hc t ht)).const_mul o
  have hco : ContinuousOn d (Icc 0 L) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope d (fun s => o*v s 0) hL hco (fun s hs => hd s (Ioo_subset_Icc_self hs))
  have htd : 0 < o*v t 0 := by
    rw [he]
    exact div_pos (by dsimp [d]; linarith only [hdisp]) (sub_pos.mpr hL)
  have ho := (mul_ne_zero_iff.mp hdisp.ne').1
  exact sign_prop (continuousOn_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp_continuousOn hv))
    (fun s hs => mul_ne_zero ho (hne s hs)) (Ioo_subset_Icc_self ht) htd

theorem common_sign {o u v : ℝ} (h1 : 0 < o*u) (h2 : 0 < o*v) : 0 < u*v := by
  rcases mul_pos_iff.mp h1 with h|h <;> rcases mul_pos_iff.mp h2 with k|k
  · exact mul_pos h.2 k.2
  · linarith [h.1,k.1]
  · linarith [h.1,k.1]
  · exact mul_pos_of_neg_of_neg h.2 k.2

private theorem fit_clock {A : Set ℝ} (hA : IsOpen A) {L : ℝ} (hL : 0 < L) (hS : Icc 0 L⊆A) :
    ∃ f : ℝ→ℝ, ContDiff ℝ 1 f ∧ (∀ t, f t∈A) ∧ ∀ t∈Icc 0 L, f=ᶠ[𝓝 t] id := by
  obtain ⟨r₁,hr₁,h₁⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (left_mem_Icc.mpr hL.le)))
  obtain ⟨r₂,hr₂,h₂⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (right_mem_Icc.mpr hL.le)))
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let m := L/2
  let b : ContDiffBump m := ⟨m+r/2,m+r,by dsimp [m]; linarith,by linarith⟩
  let f (t : ℝ) := m+b t*(t-m)
  refine ⟨f,?_,?_,?_⟩
  · exact contDiff_const.add (b.contDiff.mul (contDiff_id.sub contDiff_const))
  · intro t
    have hb : |f t-m| < m+r := by
      by_cases h : b t=0
      · simp [f,h]; dsimp [m]; linarith
      · have hh : t∈Function.support b := h
        rw [b.support_eq,Metric.mem_ball,Real.dist_eq] at hh
        have he : f t-m=b t*(t-m) := by dsimp [f]; ring
        rw [he,abs_mul,abs_of_nonneg b.nonneg]
        exact (mul_le_mul_of_nonneg_right b.le_one (abs_nonneg _)).trans_lt (by simpa using hh)
    have hl := (abs_lt.mp hb).1
    have hu := (abs_lt.mp hb).2
    by_cases h0 : f t < 0
    · apply h₁
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_neg h0]
      dsimp [m] at hl; linarith only [hl,min_le_left r₁ r₂]
    · by_cases h1 : L < f t
      · apply h₂
        rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr h1)]
        dsimp [m] at hu; linarith only [hu,min_le_right r₁ r₂]
      · exact hS ⟨le_of_not_gt h0,le_of_not_gt h1⟩
  · intro t ht
    have hh : t∈Metric.ball m b.rIn := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      change -(L/2+r/2) < t-L/2 ∧ t-L/2 < L/2+r/2
      constructor <;> linarith [ht.1,ht.2]
    filter_upwards [b.eventuallyEq_one_of_mem_ball hh] with z hz
    change b z=1 at hz
    simp [f,hz]

abbrev NF (m a e : ℝ) (x₀ : E4) := NormalFlow (F m a e) (S m a e) x₀
abbrev span {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) := Icc (0:ℝ) N.time
abbrev Z {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).1
abbrev Velo {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).2

theorem radial_data {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) {p v : E4}
    (hv : (p,v)∈N.normal.source) :
    (∀ t∈span N, Z N p v t∈S m a e ∧ HasDerivAt (Z N p v) (Velo N p v t) t) ∧
    ContinuousOn (Velo N p v) (span N) ∧ Z N p v 0=p ∧ Velo N p v 0=v := by
  have h0 := N.initial (p,v) (N.source_stays (p,v) hv 0 ⟨le_rfl,N.time_pos.le⟩)
  refine ⟨fun t ht => ⟨(N.ode _ (N.source_stays _ hv t ht)).1,?_⟩,?_,congrArg Prod.fst h0,congrArg Prod.snd h0⟩
  · exact (N.ode _ (N.source_stays _ hv t ht)).2.fst
  · exact (N.flow_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (N.source_stays (p,v) hv)).snd

private theorem radial_nonzero {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p v : E4} (hv : (p,v)∈N.normal.source) (hn : v≠0) {t : ℝ} (ht : t∈span N) :
    Velo N p v t≠0 := by
  intro hbad
  let f := geodesicSpray (F m a e)
  let u (s : ℝ) := N.flow (t-s,(p,v))
  let y := N.flow (t,(p,v))
  have htime {s : ℝ} (hs : s∈Icc 0 t) : t-s∈span N := ⟨sub_nonneg.mpr hs.2,by linarith [ht.2,hs.1]⟩
  have hdu (s : ℝ) (hs : s∈Icc 0 t) : HasDerivAt u (-f (u s)) s := by
    simpa [u,f,Function.comp_def] using ((N.ode _ (N.source_stays (p,v) hv _ (htime hs))).2.scomp s ((hasDerivAt_id s).const_sub t))
  have hy : f y=0 := by
    change (y.2,-OAI.WeakMTWGlobalSupport.CoordinateGeometry.christoffel (F m a e) y.1 y.2 y.2) = 0
    change y.2=0 at hbad
    simp [hbad]
  have hsmooth := contDiffOn_geodesicSpray_of_invertible (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz)
  have hz : EqOn u (fun _=>y) (Icc 0 t) := by
    apply FlowLinearization.unique_Icc (f:=fun z => -f z) (fun s hs => (hdu s hs).continuousAt.continuousWithinAt) continuousOn_const
    · intro z hz
      have hz' : z∈(S m a e) ×ˢ (univ : Set E4) := by
        rcases hz with ⟨s,hs,rfl⟩|⟨_,_,rfl⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv _ (htime hs))).1,mem_univ _⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv t ht)).1,mem_univ _⟩
      exact (((hsmooth z hz').contDiffAt (((openS m a e).prod isOpen_univ).mem_nhds hz')).of_le (by simp)).neg
    · exact fun s hs => (hdu s hs).hasDerivWithinAt
    · intro s _
      simpa only [hy,neg_zero] using hasDerivWithinAt_const s (Icc (0:ℝ) t) y
    · simp [u,y]
  have h := congrArg Prod.snd (hz (right_mem_Icc.mpr ht.1))
  have h0 := (radial_data N hv).2.2.2
  apply hn
  calc
    v = Velo N p v 0 := h0.symm
    _ = Velo N p v t := by simpa only [u,y,sub_self] using h
    _ = 0 := hbad

theorem radial_future (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (p q : U a) (htarget : (p.val,q.val)∈N.normal.target)
    (hE : initialEnergy N p.val q.val ≤ 0)
    (ho : 0 ≤ (q.val 0-p.val 0)*timeComponent (T p)) : q∈causalFuture (G m a e) T (D m a e) p := by
  by_cases hdiag : q=p
  · exact Or.inl (mem_singleton_iff.mpr hdiag)
  let v := logVec N p.val q.val
  let R := Z N p.val v
  let d := Velo N p.val v
  let o := timeComponent (T p)
  have hv : (p.val,v)∈N.normal.source := (N.normalAt p.val).map_target htarget
  have hlast : R N.time = q.val := by
    simpa only [N.normalAt_apply,R,Z,v,logVec] using (N.normalAt p.val).right_inv htarget
  have hvne : v≠0 := by
    intro hv0
    have hh : (p.val,(0:E4))∈N.normal.source := hv0 ▸ hv
    have he := normalAt_zero_of_invertible N (openS m a e) (field_smooth m a e hp)
      (fun z hz => field_inv m a e hp hz) hh
    apply hdiag
    apply Subtype.ext
    calc
      q.val = N.normalAt p.val v := ((N.normalAt p.val).right_inv htarget).symm
      _ = p.val := hv0 ▸ he
  obtain ⟨hR,hdc,hfirst,_⟩ := radial_data N hv
  have henergy (t : ℝ) (ht : t∈span N) : F m a e (R t) (d t) (d t) ≤ 0 :=
    (flow_energy N (openS m a e) (field_smooth m a e hp) (fun _ hz => field_sym m a e hp hz)
      (fun _ hz => field_inv m a e hp hz) hv ht).trans_le hE
  have hdn (t : ℝ) (ht : t∈span N) := radial_nonzero hp N hv hvne ht
  have hdt (t : ℝ) (ht : t∈span N) : d t 0≠0 := nonzero_time m a e hp (hR _ ht).1 (hdn t ht) (henergy t ht)
  have h₀ : (0:ℝ)∈span N := ⟨le_rfl,N.time_pos.le⟩
  have hpS := N.base_mem hv
  have hor : o≠0 := by
    apply nonzero_time m a e hp hpS _ (hT.2 p).le
    intro h
    have hh := hT.2 p
    change (T p : E4)=0 at h
    change F m a e p.val (T p : E4) (T p : E4) < 0 at hh
    simp [h] at hh
  have hdiff (s : ℝ) (hs : s∈span N) : HasDerivAt (fun t => R t 0) (d s 0) s :=
    time_deriv (hR s hs).2
  have hstrict : 0 < o*(R N.time 0-R 0 0) := by
    have h0' : R 0=p.val := hfirst
    have hs := exists_hasDerivAt_eq_slope (fun t => R t 0) (fun t => d t 0) N.time_pos
      (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt) (fun t ht => hdiff t (Ioo_subset_Icc_self ht))
    obtain ⟨t,ht,he⟩ := hs
    have hdne : R N.time 0 - R 0 0 ≠ 0 := fun hh => hdt t (Ioo_subset_Icc_self ht) (by simpa [hh] using he)
    apply lt_of_le_of_ne _ ((mul_ne_zero hor hdne).symm)
    rw [hlast,h0',mul_comm]
    exact ho
  have hsign := clock_positive N.time_pos R d (fun s hs => (hR s hs).2) hdc hdt hstrict
  have horient (s : ℝ) (hs : s∈span N) : 0 < o*(W a T (R s)) 0 := by
    have hc : ContinuousOn (fun t => o*(W a T (R t)) 0) (span N) := by
      intro t ht
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hz : ContinuousAt (W a T) (R t) := W_cont m a e T hT z
      have hr : ContinuousAt R t := (hR t ht).2.continuousAt
      have ht' : ContinuousAt (fun s => W a T (R s)) t := hz.comp (f:=R) hr
      let proj : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
      have hh : ContinuousAt (fun s => proj (W a T (R s))) t :=
        proj.continuous.continuousAt.comp (f:=fun s => W a T (R s)) ht'
      exact (continuousAt_const.mul hh).continuousWithinAt
    have hn (t : ℝ) (ht : t∈span N) : o*(W a T (R t)) 0≠0 := by
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hg := hT.2 z
      change F m a e (R t) (T z : E4) (T z : E4) < 0 at hg
      have he : W a T (R t)=(T z:E4) := W_on a T z
      rw [he]
      exact mul_ne_zero hor (nonzero_time m a e hp (hR t ht).1 (fun hh => by simp [hh] at hg) hg.le)
    apply sign_prop hc hn h₀ _ s hs
    change 0 < o*(W a T (R 0)) 0
    rw [show R 0=p.val from hfirst,W_on]
    exact mul_self_pos.mpr hor
  let A : Set ℝ := {s | (s,(p.val,v))∈N.domain}
  have hA : IsOpen A := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨f,hf,hfA,hfe⟩ := fit_clock hA N.time_pos (N.source_stays (p.val,v) hv)
  let γ (t : ℝ) : U a := ⟨R (f (N.time*t)),inU m a e hp (N.ode _ (hfA _)).1⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    let param (u : ℝ) : ℝ×(E4×E4) := (f (N.time*u),(p.val,v))
    have hparam : ContDiff ℝ 1 param := (hf.comp (contDiff_const.mul contDiff_id)).prodMk contDiff_const
    have hh : ContDiffAt ℝ 1 N.flow (param t) :=
      ((N.flow_smooth _ (hfA (N.time*t))).contDiffAt (N.domain_open.mem_nhds (hfA (N.time*t)))).of_le
        (show (1:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hh' : ContDiffAt ℝ 1 (N.flow ∘ param) t := hh.comp (f:=param) t hparam.contDiffAt
    exact hh'.fst
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := fun s =>
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  have eqF (s : ℝ) (hs : s∈span N) : f s=s := (hfe s hs).eq_of_nhds
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext ?_,Subtype.ext ?_⟩
  · intro s hs
    have hts : N.time*s∈span N := ⟨mul_nonneg N.time_pos.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 N.time_pos.le⟩
    let t := N.time*s
    have hz : (γ s).val=R t := by change R (f t)=R t; rw [eqF t hts]
    have hb : HasDerivAt (fun u => f (N.time*u)) N.time s := by
      have hclock : HasDerivAt (fun u : ℝ => N.time*u) N.time s := by
        simpa only [id_eq,mul_one] using (hasDerivAt_id s).const_mul N.time
      have hequal : (fun u : ℝ => f (N.time*u)) =ᶠ[𝓝 s] (fun u : ℝ => N.time*u) :=
        (hfe t hts).comp_tendsto hclock.continuousAt.tendsto
      exact hclock.congr_of_eventuallyEq hequal
    have hr : HasDerivAt R (d t) (f t) := by rw [eqF t hts]; exact (hR t hts).2
    have hder : HasDerivAt (fun u => (γ u).val) (N.time • d t) s := by
      change HasDerivAt (R ∘ fun u => f (N.time*u)) (N.time • d t) s
      exact hr.scomp s hb
    have hv' := ambient_velocity a γ hγ s _ hder
    have htim := hT.2 (γ s)
    have heW : W a T (R t)=(T (γ s):E4) := hz ▸ W_on a T (γ s)
    have hpair := cone_pair_negative m a e hp (hR t hts).1 (henergy t hts)
      (w:=W a T (R t)) (by
        change F m a e (R t) (W a T (R t)) (W a T (R t)) < 0
        rw [heW,←hz]
        exact htim) (common_sign (hsign t hts) (horient t hts))
    refine ⟨show (γ s).val∈S m a e by rw [hz]; exact (hR t hts).1,?_,?_,?_⟩
    · change (velocity γ s:E4)≠0
      rw [hv']
      exact smul_ne_zero N.time_pos.ne' (hdn t hts)
    · change F m a e (γ s).val (velocity γ s:E4) (velocity γ s:E4) ≤ 0
      rw [hv',hz]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (henergy t hts))
    · change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4) < 0
      rw [hv',hz,←heW]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_neg_of_pos_of_neg N.time_pos hpair
  · simpa only [γ,mul_zero,eqF 0 h₀] using hfirst
  · simpa only [γ,mul_one,eqF _ (right_mem_Icc.mpr N.time_pos.le)] using hlast

theorem energy_cont {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p q : E4} (hpS : p∈S m a e) (ht : (p,q)∈N.normal.target) :
    ContinuousAt (fun k : E4×E4 => initialEnergy N k.1 k.2) (p,q) := by
  have hF := ((field_smooth m a e hp p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)).comp
    (continuous_fst.continuousAt (x:=(p,q)))
  exact (hF.clm_apply (logVec_continuousAt N ht)).clm_apply (logVec_continuousAt N ht)


end
end NoHair.MassShellGeodesics
namespace NoHair.MassShellTrans

open NoHair NoHair.MassShellJoining Set Filter
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option maxHeartbeats 270000

private def patch (P Q : Arc) (y : E4) (k : ℝ×ℝ) : E4 := P.pos k.1 + Q.pos k.2-y
private abbrev corner := ((1:ℝ),(0:ℝ))

private abbrev CornerBilin := E4 → E4 →L[ℝ] E4 →L[ℝ] ℝ
private def Okay (S : Set E4) (g : CornerBilin) (O : E4→E4) (z v : E4) :=
  z∈S ∧ g z v v ≤ 0 ∧ g z v (O z) < 0
private def SmoothAt (g : CornerBilin) (y : E4) := ∀ v w : E4,
  ContDiffAt ℝ 1 (fun k : E4×E4×E4 => g k.1 k.2.1 k.2.2) (y,v,w)

private def OrientedNear (S : Set E4) (g : CornerBilin) (O : E4→E4) (P Q : Arc) (y : E4) (c : ℝ) (k : ℝ×ℝ) :=
  let z := patch P Q y k
  z∈S ∧
    g z (P.vel k.1) (O z) < 0 ∧ g z (Q.vel k.2) (O z) < 0 ∧
    g z (P.vel k.1) (Q.vel k.2) ≤ -c

private def MetricError (g : CornerBilin) (P Q : Arc) (y : E4) (C : ℝ) (k : ℝ×ℝ) :=
  let z := patch P Q y k
  let v := P.vel k.1
  let w := Q.vel k.2
  g z v v - g (P.pos k.1) v v ≤ C*|k.2| ∧
    g z w w - g (Q.pos k.2) w w ≤ C*|k.1-1|

private theorem orientation_near (S : Set E4) (g : CornerBilin) (O : E4→E4) (y : E4) (hdoc : IsOpen S) (hg : SmoothAt g y) (hw : ContinuousAt O y) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y)
    (hP : ∀ s∈J, Okay S g O (P.pos s) (P.vel s)) (hQ : ∀ s∈J, Okay S g O (Q.pos s) (Q.vel s))
    (hcross : g y (P.vel 1) (Q.vel 0) < 0) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ k in 𝓝 corner, OrientedNear S g O P Q y c k := by
  let A := P.vel 1
  let B := Q.vel 0
  let c := -(g y A B)/2
  have hc : 0<c := by dsimp [c,A,B]; linarith only [hcross]
  have ha := hP 1 (right_mem_Icc.mpr zero_le_one)
  have hb := hQ 0 (left_mem_Icc.mpr zero_le_one)
  rw [hp] at ha
  rw [hq] at hb
  let l : Filter (ℝ×ℝ) := 𝓝 ((1:ℝ),(0:ℝ))
  let Z := patch P Q y
  let v (k : ℝ×ℝ) := P.vel k.1
  let w (k : ℝ×ℝ) := Q.vel k.2
  have pL : Tendsto (fun k : ℝ×ℝ => P.pos k.1) l (𝓝 y) := by
    simpa only [l,←hp,Function.comp_apply,Function.comp_def] using (P.smooth.continuous.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have qL : Tendsto (fun k : ℝ×ℝ => Q.pos k.2) l (𝓝 y) := by
    simpa only [l,←hq,Function.comp_apply,Function.comp_def] using (Q.smooth.continuous.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have zL : Tendsto Z l (𝓝 y) := by
    have hz : Z = (fun k : ℝ×ℝ => P.pos k.1 + Q.pos k.2 - y) := funext (fun _ => rfl)
    rw [hz]
    simpa only [add_sub_cancel_right,add_sub_cancel_left] using (pL.add qL).sub (tendsto_const_nhds (x:=y) (f:=l))
  have vL : Tendsto v l (𝓝 A) := (P.continuous_vel.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have wL : Tendsto w l (𝓝 B) := (Q.continuous_vel.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have tL : Tendsto (fun k => O (Z k)) l (𝓝 (O y)) := hw.tendsto.comp zL
  have ev {V V' : (ℝ×ℝ)→E4} {b b' : E4} (h : Tendsto V l (𝓝 b)) (h' : Tendsto V' l (𝓝 b')) :
      Tendsto (fun k => g (Z k) (V k) (V' k)) l (𝓝 (g y b b')) :=
    (hg b b').continuousAt.tendsto.comp (zL.prodMk_nhds (h.prodMk_nhds h'))
  have hcx : g y A B < -c := by dsimp [c,A,B]; linarith only [hcross]
  have hd : ∀ᶠ k in l, Z k∈S := zL (hdoc.mem_nhds ha.1)
  have h1 : ∀ᶠ k in l, g (Z k) (v k) (O (Z k))<0 := (ev vL tL).eventually_lt_const ha.2.2
  have h2 : ∀ᶠ k in l, g (Z k) (w k) (O (Z k))<0 := (ev wL tL).eventually_lt_const hb.2.2
  have h3 : ∀ᶠ k in l, g (Z k) (v k) (w k) < -c := (ev vL wL).eventually_lt_const hcx
  refine ⟨c,hc,?_⟩
  filter_upwards [hd,h1,h2,h3] with k hk h1 h2 h3 using ⟨hk,h1,h2,h3.le⟩

private theorem metric_error_near (g : CornerBilin) (y : E4) (hg : SmoothAt g y) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in 𝓝 corner, MetricError g P Q y C k := by
  let A := P.vel 1
  let B := Q.vel 0
  let l : Filter (ℝ×ℝ) := 𝓝 ((1:ℝ),(0:ℝ))
  let Z := patch P Q y
  let v (k : ℝ×ℝ) := P.vel k.1
  let w (k : ℝ×ℝ) := Q.vel k.2
  have pL : Tendsto (fun k : ℝ×ℝ => P.pos k.1) l (𝓝 y) := by
    simpa only [l,←hp,Function.comp_apply,Function.comp_def] using (P.smooth.continuous.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have qL : Tendsto (fun k : ℝ×ℝ => Q.pos k.2) l (𝓝 y) := by
    simpa only [l,←hq,Function.comp_apply,Function.comp_def] using (Q.smooth.continuous.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have zL : Tendsto Z l (𝓝 y) := by
    have hz : Z = (fun k : ℝ×ℝ => P.pos k.1 + Q.pos k.2 - y) := funext (fun _ => rfl)
    rw [hz]
    simpa only [add_sub_cancel_right,add_sub_cancel_left] using (pL.add qL).sub (tendsto_const_nhds (x:=y) (f:=l))
  have vL : Tendsto v l (𝓝 A) := (P.continuous_vel.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have wL : Tendsto w l (𝓝 B) := (Q.continuous_vel.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  let H (p : E4×E4) := g p.1 p.2 p.2
  have qsm (b : E4) : ContDiffAt ℝ 1 H (y,b) :=
    (hg b b).comp (f:=fun k : E4×E4 => (k.1,k.2,k.2)) (y,b) (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_snd))
  obtain ⟨K₁,S₁,hS₁,hK₁⟩ := (qsm A).exists_lipschitzOnWith
  obtain ⟨K₂,S₂,hS₂,hK₂⟩ := (qsm B).exists_lipschitzOnWith
  obtain ⟨L₁,V₁,hV₁,hL₁⟩ := (P.smooth.contDiffAt (x:=1)).exists_lipschitzOnWith
  obtain ⟨L₂,V₂,hV₂,hL₂⟩ := (Q.smooth.contDiffAt (x:=0)).exists_lipschitzOnWith
  let C : ℝ := max ((K₁:ℝ)*L₂) ((K₂:ℝ)*L₁)
  have hC : 0 ≤ C := (mul_nonneg K₁.2 L₂.2).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  filter_upwards [(zL.prodMk_nhds vL) hS₁,(pL.prodMk_nhds vL) hS₁,(zL.prodMk_nhds wL) hS₂,
    (qL.prodMk_nhds wL) hS₂,(continuous_fst.tendsto corner) hV₁,
    (continuous_snd.tendsto corner) hV₂] with k h1 h2 h3 h4 h5 h6
  constructor
  · have hx := hK₁.dist_le_mul _ h1 _ h2
    have hh := hL₂.dist_le_mul _ h6 0 (mem_of_mem_nhds hV₂)
    rw [dist_prod_same_right, Real.dist_eq] at hx
    rw [Real.dist_eq,sub_zero,hq] at hh
    have he : dist (Z k) (P.pos k.1) = dist (Q.pos k.2) y := by
      simp only [Z,patch,dist_eq_norm]
      congr 1
      abel
    rw [he] at hx
    calc
      _ ≤ |H (Z k,v k)-H (P.pos k.1,v k)| := le_abs_self _
      _ ≤ _ := hx
      _ ≤ (K₁:ℝ)*((L₂:ℝ)*|k.2|) := mul_le_mul_of_nonneg_left hh K₁.2
      _ ≤ C*|k.2| := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  · have hx := hK₂.dist_le_mul _ h3 _ h4
    have hh := hL₁.dist_le_mul _ h5 1 (mem_of_mem_nhds hV₁)
    rw [dist_prod_same_right, Real.dist_eq] at hx
    rw [Real.dist_eq,hp] at hh
    have he : dist (Z k) (Q.pos k.2) = dist (P.pos k.1) y := by
      simp only [Z,patch,dist_eq_norm]
      congr 1
      abel
    rw [he] at hx
    calc
      _ ≤ |H (Z k,w k)-H (Q.pos k.2,w k)| := le_abs_self _
      _ ≤ _ := hx
      _ ≤ (K₂:ℝ)*((L₁:ℝ)*|k.1-1|) := mul_le_mul_of_nonneg_left hh K₂.2
      _ ≤ C*|k.1-1| := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

private theorem round_window (S : Set E4) (g : CornerBilin) (O : E4→E4) (y : E4) (hdoc : IsOpen S) (hg : SmoothAt g y) (hw : ContinuousAt O y)
    (symm : ∀ z v w, g z v w = g z w v) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y)
    (hP : ∀ s∈J, Okay S g O (P.pos s) (P.vel s)) (hQ : ∀ s∈J, Okay S g O (Q.pos s) (Q.vel s))
    (hcross : g y (P.vel 1) (Q.vel 0) < 0) :
    ∃ d : ℝ, 0 < d ∧ d<1 ∧ ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Okay S g O (P.pos s+Q.pos t-y) ((1-u) • P.vel s + u • Q.vel t) := by
  let Z := patch P Q y
  obtain ⟨c,hc,ho⟩ := orientation_near S g O y hdoc hg hw P Q hp hq hP hQ hcross
  obtain ⟨C,hC,he⟩ := metric_error_near g y hg P Q hp hq
  have near : ∀ᶠ k in 𝓝 corner, OrientedNear S g O P Q y c k ∧ MetricError g P Q y C k := ho.and he
  obtain ⟨r,hr,hrset⟩ := Metric.mem_nhds_iff.mp near
  have hCp : 0<C+1 := by linarith
  obtain ⟨d,hd,hdmax⟩ := exists_between (lt_min (lt_min hr zero_lt_one) (div_pos hc hCp))
  obtain ⟨hdr,hd1⟩ := lt_min_iff.mp (lt_min_iff.mp hdmax).1
  have hCd : C*d ≤ c := by
    have h := (lt_div_iff₀ hCp).mp (lt_min_iff.mp hdmax).2
    nlinarith only [h,hd]
  refine ⟨d,hd,hd1,?_⟩
  intro u hu
  let b := 1-u
  let s := 1-d*b^2
  let t := d*u^2
  have hb0 : 0 ≤ b := sub_nonneg.mpr hu.2
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hu.1]
  have hu2 : u^2 ≤ 1 := by nlinarith only [mul_nonneg hu.1 (sub_nonneg.mpr hu.2), hu.2]
  have hb2 : b^2 ≤ 1 := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb1), hb1]
  have hs : s∈J := by
    constructor <;> dsimp [s]
    · linarith only [mul_le_mul_of_nonneg_left hb2 hd.le,hd1]
    · linarith only [mul_nonneg hd.le (sq_nonneg b)]
  have ht : t∈J := ⟨mul_nonneg hd.le (sq_nonneg u),by dsimp [t]; linarith only [mul_le_mul_of_nonneg_left hu2 hd.le,hd1]⟩
  have hm : (s,t)∈Metric.ball ((1:ℝ),(0:ℝ)) r := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,Real.dist_eq,sub_zero,
      abs_of_nonpos (sub_nonpos.mpr hs.2),abs_of_nonneg ht.1]
    constructor
    · dsimp [s]; linarith only [mul_le_mul_of_nonneg_left hb2 hd.le,hdr]
    · dsimp [t]; linarith only [mul_le_mul_of_nonneg_left hu2 hd.le,hdr]
  obtain ⟨hOr,hEr⟩ := hrset hm
  obtain ⟨hD,horA,horB,hmix⟩ := hOr
  obtain ⟨heA,heB⟩ := hEr
  let z := Z (s,t)
  let M := g z
  let V := P.vel s
  let V' := Q.vel t
  change M V (O z)<0 at horA
  change M V' (O z)<0 at horB
  change M V V' ≤ -c at hmix
  change M V V - g (P.pos s) V V ≤ C*|t| at heA
  change M V' V' - g (Q.pos t) V' V' ≤ C*|s-1| at heB
  rw [abs_of_nonneg ht.1] at heA
  rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at heB
  have hA : M V V ≤ C*d*u^2 := by dsimp [t] at heA; nlinarith only [heA,(hP s hs).2.1]
  have hB : M V' V' ≤ C*d*b^2 := by dsimp [s] at heB; nlinarith only [heB,(hQ t ht).2.1]
  have hsym : M V' V = M V V' := symm z V' V
  change Okay S g O z (b • V + u • V')
  refine ⟨hD,?_,?_⟩
  · change M (b • V + u • V') (b • V + u • V') ≤ 0
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hsym]
    have hbu := mul_nonneg hb0 hu.1
    have hbu1 : b*u ≤ 1 := (mul_le_mul_of_nonneg_left hu.2 hb0).trans (by simpa using hb1)
    have hsmall : C*d*(b*u) ≤ c := (mul_le_mul_of_nonneg_left hbu1 (mul_nonneg hC hd.le)).trans (by simpa using hCd)
    nlinarith only [mul_le_mul_of_nonneg_left hA (sq_nonneg b),mul_le_mul_of_nonneg_left hB (sq_nonneg u),
      mul_le_mul_of_nonneg_left hmix hbu, mul_nonpos_of_nonneg_of_nonpos hbu (sub_nonpos.mpr hsmall)]
  · change M (b • V + u • V') (O z)<0
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    by_cases h : u=0
    · simpa [b,h] using horA
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hb0 horA.le)
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne hu.1 (Ne.symm h)) horB)

private theorem cartesian_formula (m a e : ℝ) (y : E4) (v w : E4) :
    F m a e y v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e y * kEval a y v * kEval a y w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e y) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

theorem result (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' massShell m a e
    let g := kerrNewmanMetricField m a e
    ∀ p ∈ D, ∀ x ∈ D, ∀ q ∈ D,
      x ∈ causalFuture g T D p → q ∈ causalFuture g T D x → q ∈ causalFuture g T D p := by
  dsimp only
  intro p _ x _ q _ h1 h2
  rcases h1 with hid|⟨α,ha,ha0,ha1⟩
  · rcases mem_singleton_iff.mp hid with rfl
    exact h2
  rcases h2 with hid|⟨β,hb,hb0,hb1⟩
  · rcases mem_singleton_iff.mp hid with rfl
    exact Or.inr ⟨α,ha,ha0,ha1⟩
  let P := fromCurve α ha.1
  let Q := fromCurve β hb.1
  have p0 : P.pos 0=p.val := congrArg Subtype.val ha0
  have p1 : P.pos 1=x.val := congrArg Subtype.val ha1
  have q0 : Q.pos 0=x.val := congrArg Subtype.val hb0
  have q1 : Q.pos 1=q.val := congrArg Subtype.val hb1
  have pG := fromCurve_good m a e T α ha
  have qG := fromCurve_good m a e T β hb
  have ha' : Good m a e T x.val (P.vel 1) := p1 ▸ pG 1 (right_mem_Icc.mpr zero_le_one)
  have hb' : Good m a e T x.val (Q.vel 0) := q0 ▸ qG 0 (left_mem_Icc.mpr zero_le_one)
  rcases directions m a e hp T hT x (P.vel 1) (Q.vel 0) ha' hb' with ⟨c,hc,he⟩|hn
  · exact combine_parallel m a e T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG c hc he
  · obtain ⟨d,hd,hd1,hmid⟩ := round_window (massShell m a e) (F m a e) (W a T) x.val
      (isOpen_lt continuous_const (continuous_ksRadius a)) (fun b b' => eval_smooth m a e x.val b b' x.property)
      (W_cont m a e T hT x) (fun z v w => by rw [cartesian_formula,cartesian_formula]; ring)
      P Q p1 q0 pG qG hn
    exact combine_round m a e hp T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG d hd hd1 hmid

end
end NoHair.MassShellTrans
namespace NoHair.MassShellLocal

open NoHair NoHair.MassShellGeodesics Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 330000
noncomputable section

private theorem energy_barrier (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (base : E4) (c v : ℝ→E4) (o : ℝ)
    (hd : ∀ t, HasDerivAt c (v t) t) (hmemS : ∀ t∈J, c t∈S m a e)
    (htarget : ∀ t∈J, (base,c t)∈N.normal.target)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < o*v t 0) (htime : ∀ t∈J, 0 < o*(c t 0-base 0))
    (hseed : initialEnergy N base (c 0) < 0) : initialEnergy N base (c 1) ≤ initialEnergy N base (c 0) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have symG (z : E4) (hz : z∈S m a e) := field_sym m a e hp hz
  let d (t : ℝ) := (2/N.time)*F m a e (c t) (terminalVelocity N base (c t)) (v t)
  have HE (t : ℝ) (ht : t∈J) : HasDerivAt (fun t => initialEnergy N base (c t)) (d t) t :=
    initialEnergy_deriv N (openS m a e) sG symG invG (htarget t ht) (hd t)
  have H := image_le_of_deriv_right_lt_deriv_boundary (f:=fun t => initialEnergy N base (c t))
    (f':=d) (B:=fun _ => initialEnergy N base (c 0)) (B':=fun _ => 0) (a:=(0:ℝ)) (b:=1)
    (fun t ht => (HE t ht).continuousAt.continuousWithinAt) (fun t ht => (HE t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    le_rfl (fun t => hasDerivAt_const t _) (by
      intro t hti ha
      have ht := Ico_subset_Icc_self hti
      let u := logVec N base (c t)
      have htar' := htarget t ht
      have hu : (base,u)∈N.normal.source := (N.normalAt base).map_target htar'
      obtain ⟨hR,hC,hfirst,_⟩ := radial_data N hu
      have hlast : Z N base u N.time=c t := by simpa only [N.normalAt_apply,Z,u,logVec] using (N.normalAt base).right_inv htar'
      have htim (r : ℝ) (hr : r∈span N) :
          F m a e (Z N base u r) (Velo N base u r) (Velo N base u r) < 0 :=
        (flow_energy N (openS m a e) sG symG invG hu hr).trans_lt (ha.trans_lt hseed)
      have hdt (r : ℝ) (hr : r∈span N) : Velo N base u r 0≠0 := by
        have hh := htim r hr
        exact nonzero_time m a e hp (hR r hr).1 (fun h => by simp [h] at hh) hh.le
      have hforward : 0 < o*(Z N base u N.time 0-Z N base u 0 0) := by
        rw [hlast,hfirst]
        exact htime t ht
      have hfin : N.time∈span N := right_mem_Icc.mpr N.time_pos.le
      have hsg := clock_positive N.time_pos (Z N base u) (Velo N base u) (fun r hr => (hR r hr).2) hC hdt hforward N.time hfin
      have hh := htim N.time hfin
      rw [hlast] at hh
      have hm := cone_pair_negative m a e hp (hmemS t ht) (hcone t ht) hh (common_sign (hsign t ht) hsg)
      dsimp only [d]
      apply mul_neg_of_pos_of_neg (div_pos (by norm_num) N.time_pos)
      rw [symG (c t) (hmemS t ht)]
      exact hm)
  exact H (right_mem_Icc.mpr zero_le_one)

private theorem past_shift_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p w : E) :
    Tendsto (fun t : ℝ => p-t • w) (𝓝[>] (0:ℝ)) (𝓝 p) := by
  have h : Continuous (fun t : ℝ => p-t • w) := continuous_const.sub (continuous_id.smul continuous_const)
  have hh := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  simpa only [zero_smul,sub_zero] using hh

private theorem derivative_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (v : E) (hf : HasDerivAt f v 0) (h0 : f 0=0) :
    Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] (0:ℝ)) (𝓝 v) := by
  have h := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have he : slope f 0 = (fun s : ℝ => s⁻¹ • f s) := by
    funext s
    rw [slope_def_module,h0,sub_zero,sub_zero]
  rwa [he] at h

private theorem scaled_norm_negative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (f : ℝ→E) (v : E)
    (hg : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 g₀)) (hf : Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] 0) (𝓝 v))
    (hneg : g₀ v v < 0) : ∀ᶠ s in 𝓝[>] (0:ℝ), g s (f s) (f s) < 0 := by
  have he : Continuous (fun k : (E →L[ℝ] E →L[ℝ] ℝ) × (E×E) => k.1 k.2.1 k.2.2) :=
    (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply (continuous_snd.comp continuous_snd)
  have hlim : Tendsto (fun s : ℝ => g s (s⁻¹ • f s) (s⁻¹ • f s)) (𝓝[>] 0) (𝓝 (g₀ v v)) :=
    (he.tendsto (g₀,v,v)).comp (hg.prodMk_nhds (hf.prodMk_nhds hf))
  have hspos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  filter_upwards [hlim.eventually_lt_const hneg,hspos] with s hs hp
  change g s (s⁻¹ • f s) (s⁻¹ • f s) < 0 at hs
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at hs
  exact neg_of_mul_neg_right (neg_of_mul_neg_right hs (inv_pos.mpr hp).le) (inv_pos.mpr hp).le

private theorem scale_timelike {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (t : ℝ) (ht : 0 < t) (hv : G v v < 0) :
    G (t⁻¹ • v) (t⁻¹ • v) < 0 := by
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr ht) (mul_neg_of_pos_of_neg (inv_pos.mpr ht) hv)

private theorem past_seed (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4} (N : NF m a e x₀)
    {p : E4} (hpS : p∈S m a e) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (w : E4) (hw : F m a e p w w < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (p-s • w) p < 0 := by
  let f (s : ℝ) := logVec N (p-s • w) p
  let g (s : ℝ) := F m a e (p-s • w)
  have sm := field_smooth m a e hp
  have hG : ContinuousAt (F m a e) p := (sm p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)
  have gL : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (F m a e p)) := hG.tendsto.comp (past_shift_limit p w)
  have hd : HasDerivAt f (N.time⁻¹ • w) 0 := logVec_base_deriv N (openS m a e) sm
    (fun z hz => field_inv m a e hp hz) hsrc w
  have f0 : f 0 = 0 := by simpa only [f,zero_smul,sub_zero] using hlog
  exact scaled_norm_negative g (F m a e p) f (N.time⁻¹ • w) gL
    (derivative_quotient f _ hd f0) (scale_timelike _ w N.time N.time_pos hw)

private theorem positive_shift {a p o s : ℝ} (h : 0 ≤ o*(a-p)) (ho : o≠0) (hs : 0<s) :
    0 < o*(a-(p-s*o)) := by
  nlinarith only [h,mul_pos hs (sq_pos_iff.mpr ho)]

private theorem past_energy_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : E×E→ℝ) (p q w : E) (hc : ContinuousAt k (p,q))
    (hh : ∀ᶠ s in 𝓝[>] (0:ℝ), k (p-s • w,q) ≤ 0) : k (p,q) ≤ 0 := by
  have hpair : Tendsto (fun s : ℝ => (p-s • w,q)) (𝓝[>] 0) (𝓝 (p,q)) :=
    (past_shift_limit p w).prodMk_nhds tendsto_const_nhds
  exact le_of_tendsto (hc.tendsto.comp hpair) hh

private theorem clock_along (c v : ℝ→E4) (o : ℝ) (hd : ∀ t, HasDerivAt c (v t) t)
    (hc : Continuous v) (hn : ∀ t∈J, v t 0≠0) (hstart : 0 < o*v 0 0) :
    (∀ t∈J, 0 < o*v t 0) ∧ ∀ t∈J, 0 ≤ o*(c t 0-c 0 0) := by
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone := (mul_ne_zero_iff.mp hstart.ne').1
  have hsign : ∀ t∈J, 0 < o*v t 0 := sign_prop
    (continuous_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp hc)).continuousOn
    (fun t ht => mul_ne_zero hone (hn t ht)) h₀ hstart
  have hclock (t : ℝ) : HasDerivAt (fun s => o*c s 0) (o*v t 0) t :=
    (time_deriv (hd t)).const_mul o
  have hdiff : Differentiable ℝ (fun s => o*c s 0) := fun t => (hclock t).differentiableAt
  have hmono : MonotoneOn (fun s => o*c s 0) J := monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn (fun t ht => (hclock t).deriv.symm ▸ (hsign t (interior_subset ht)).le)
  refine ⟨hsign,?_⟩
  intro t ht
  rw [mul_sub]
  exact sub_nonneg.mpr (hmono h₀ ht ht.1)

private theorem energy_of_arc (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target) (p q w : E4)
    (hpV : p∈V) (hqV : q∈V) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (hw : F m a e p w w < 0)
    (c v : ℝ→E4) (hd : ∀ t, HasDerivAt c (v t) t)
    (hmem : ∀ t∈J, c t∈V) (he0 : c 0=p) (he1 : c 1=q)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < w 0*v t 0) (hdisp : ∀ t∈J, 0 ≤ w 0*(c t 0-p 0)) :
    initialEnergy N p q ≤ 0 := by
  let o := w 0
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone : o≠0 := (mul_ne_zero_iff.mp (hsign 0 h₀).ne').1
  let b (s : ℝ) := p-s • w
  have bL : Tendsto b (𝓝[>] (0:ℝ)) (𝓝 p) := past_shift_limit p w
  have bV : ∀ᶠ s in 𝓝[>] (0:ℝ), b s∈V := bL (hV.mem_nhds hpV)
  have spos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  have hbase : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) p < 0 :=
    past_seed m a e hp N (hVS hpV) hsrc hlog w hw
  have hbound : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) q ≤ 0 := by
    filter_upwards [hbase,bV,spos] with s hseed hsV hspos
    have htime (t : ℝ) (ht : t∈J) : 0 < o*(c t 0-b s 0) := by
      change 0 < o*(c t 0-(p 0-s*o))
      exact positive_shift (hdisp t ht) hone hspos
    have h := energy_barrier m a e hp N (b s) c v o hd (fun t ht => hVS (hmem t ht))
      (fun t ht => htar _ hsV _ (hmem t ht)) hcone hsign htime (by rwa [he0])
    rw [he0,he1] at h
    exact h.trans hseed.le
  exact past_energy_limit (fun k : E4×E4 => initialEnergy N k.1 k.2) p q w
    (energy_cont hp N (hVS hpV) (htar _ hpV _ hqV)) hbound


private theorem curve_necessary (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e) (hsrc : ∀ x∈V, (x,(0:E4))∈N.normal.source)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target)
    (p q : U a) (hpV : p.val∈V) (hqV : q.val∈V)
    (hJ : q∈causalFuture (G m a e) T ((Subtype.val : U a → E4) ⁻¹' V) p) :
    initialEnergy N p.val q.val ≤ 0 ∧ 0 ≤ (q.val 0-p.val 0)*timeComponent (T p) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have hxsrc := hsrc p.val hpV
  have hlog0 : logVec N p.val p.val = 0 := by
    have he := normalAt_zero_of_invertible N (openS m a e) sG invG hxsrc
    simpa only [logVec,he] using (N.normalAt p.val).left_inv hxsrc
  rcases hJ with he|⟨γ,hγ,h0,h1⟩
  · have heq : q = p := mem_singleton_iff.mp he
    subst q
    constructor
    · change F m a e p.val (logVec N p.val p.val) (logVec N p.val p.val) ≤ 0
      simp only [hlog0,map_zero,ContinuousLinearMap.zero_apply,le_refl]
    · simp only [sub_self,zero_mul,le_refl]
  let c (t : ℝ) := (γ t).val
  let v := deriv c
  let w : E4 := T p
  let o := w 0
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a→E4) := contMDiff_subtype_val
  have hc : ContDiff ℝ 1 c := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : HasDerivAt c (v t) t := (hc.differentiable (by simp) t).hasDerivAt
  have hvel (t : ℝ) := ambient_velocity a γ hγ.1 t (v t) (hd t)
  have hmem (t : ℝ) (ht : t∈J) : c t∈V := (hγ.2 t ht).1
  have he0 : c 0=p.val := congrArg Subtype.val h0
  have he1 : c 1=q.val := congrArg Subtype.val h1
  have hcone (t : ℝ) (ht : t∈J) : v t≠0 ∧ F m a e (c t) (v t) (v t) ≤ 0 ∧ 0 < (v t 0)*timeComponent (T (γ t)) := by
    obtain ⟨hx,hn,hv,hf⟩ := hγ.2 t ht
    have hh := (cone_estimates m a e (γ t) (exterior_profile m a e hp _ (hVS hx)) _ _ hn hv hf (hT.2 _)).2
    change 0 < timeComponent (velocity γ t) * timeComponent (T (γ t)) at hh
    rw [hvel] at hh
    change (velocity γ t:E4)≠0 at hn
    change F m a e (c t) (velocity γ t:E4) (velocity γ t:E4) ≤ 0 at hv
    rw [hvel] at hn hv
    exact ⟨hn,hv,hh⟩
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
  have hstart : 0 < o*v 0 0 := by
    have h := (hcone 0 h₀).2.2
    rw [h0,mul_comm] at h
    exact h
  have hn (t : ℝ) (ht : t∈J) : v t 0≠0 :=
    nonzero_time m a e hp (hVS (hmem t ht)) (hcone t ht).1 (hcone t ht).2.1
  obtain ⟨hsign,hdisp₀⟩ := clock_along c v o hd (hc.continuous_deriv le_rfl) hn hstart
  have hdisp (t : ℝ) (ht : t∈J) : 0 ≤ o*(c t 0-p.val 0) := by
    simpa only [he0] using hdisp₀ t ht
  refine ⟨energy_of_arc m a e hp N V hV hVS htar p.val q.val w hpV hqV hxsrc hlog0
    (hT.2 p) c v hd hmem he0 he1 (fun t ht => (hcone t ht).2.1) hsign hdisp,?_⟩
  rw [← he1,mul_comm]
  exact hdisp 1 h₁

theorem result (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' massShell m a e
    let g := kerrNewmanMetricField m a e
    ∀ x ∈ D, ∃ V : Set U, IsOpen V ∧ x ∈ V ∧ V ⊆ D ∧
      ∀ z : U × U, z.1 ∈ V → z.2 ∈ V →
        z ∈ closure {y : U × U | y.1 ∈ V ∧ y.2 ∈ V ∧ y.2 ∈ causalFuture g T V y.1} →
          z.2 ∈ causalFuture g T D z.1 := by
  classical
  dsimp only
  intro x hx
  obtain ⟨N⟩ := exists_normalFlow_of_invertible (openS m a e) (field_smooth m a e hp)
    (fun z hz => field_inv m a e hp hz) (x₀:=x.val) hx
  have hdiag := normal_center N (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz) N.center_mem
  have htar : (x.val,x.val)∈N.normal.target := hdiag ▸ N.normal.map_source N.center_mem
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (N.normal.open_target.mem_nhds htar)
  let V := Metric.ball x.val r ∩ (S m a e ∩ {p | (p,(0:E4))∈N.normal.source})
  have hV : IsOpen V := Metric.isOpen_ball.inter ((openS m a e).inter
    (N.normal.open_source.preimage (continuous_id.prodMk continuous_const)))
  have hVS {z : E4} (hz : z∈V) := hz.2.1
  have htr (p : E4) (hp : p∈V) (q : E4) (hq : q∈V) : (p,q)∈N.normal.target := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hp.1) (Metric.mem_ball.mp hq.1)
  refine ⟨(Subtype.val : U a→E4) ⁻¹' V,hV.preimage continuous_subtype_val,
    ⟨Metric.mem_ball_self hr,hx,N.center_mem⟩,fun _ hz => hVS hz,?_⟩
  intro z hpV hqV hcl
  obtain ⟨seq,hseq,hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hnec (n : ℕ) := curve_necessary m a e hp T hT N V hV (fun _ hz => hVS hz)
    (fun _ hz => hz.2.2) htr (seq n).1 (seq n).2 (hseq n).1 (hseq n).2.1 (hseq n).2.2
  have hP : Tendsto (fun n => (seq n).1.val) atTop (𝓝 z.1.val) :=
    (continuous_subtype_val.tendsto z.1).comp ((continuous_fst.tendsto z).comp hlim)
  have hQ : Tendsto (fun n => (seq n).2.val) atTop (𝓝 z.2.val) :=
    (continuous_subtype_val.tendsto z.2).comp ((continuous_snd.tendsto z).comp hlim)
  apply radial_future m a e hp T hT N z.1 z.2 (htr _ hpV _ hqV)
  · exact le_of_tendsto ((energy_cont hp N (hVS hpV) (htr _ hpV _ hqV)).tendsto.comp
      (hP.prodMk_nhds hQ)) (Eventually.of_forall fun n => (hnec n).1)
  · have hTlim : Tendsto (fun n => W a T (seq n).1.val) atTop (𝓝 (W a T z.1.val)) :=
      (W_cont m a e T hT z.1).tendsto.comp hP
    have hproj : Continuous timeComponent := (EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 4)).continuous
    have hQ0 : Tendsto (fun n => timeComponent (seq n).2.val) atTop (𝓝 (timeComponent z.2.val)) :=
      (hproj.tendsto _).comp hQ
    have hP0 : Tendsto (fun n => timeComponent (seq n).1.val) atTop (𝓝 (timeComponent z.1.val)) :=
      (hproj.tendsto _).comp hP
    have ht0 : Tendsto (fun n => timeComponent (W a T (seq n).1.val)) atTop (𝓝 (timeComponent (W a T z.1.val))) :=
      (hproj.tendsto _).comp hTlim
    have hT0 : Tendsto (fun n => timeComponent (T (seq n).1)) atTop (𝓝 (timeComponent (T z.1))) := by
      simpa only [W_on] using ht0
    exact ge_of_tendsto ((hQ0.sub hP0).mul hT0) (Eventually.of_forall fun n => (hnec n).2)

end
end NoHair.MassShellLocal
namespace NoHair.MassShellCompact

open NoHair Set
open scoped ContDiff Manifold BigOperators

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' massShell m a e
private abbrev I4 := 𝓘(ℝ, E4)
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w :=
  @NoHair.MassShellJoining.metric_formula m a e x v w

private theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val :=
  @NoHair.MassShellJoining.exterior_profile m a e hp x hx

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 :=
  @NoHair.MassShellJoining.spatial_squares m a e x hf v hv

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v :=
  @NoHair.MassShellJoining.spatial_kernel m a e x hf v h0

private theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) :=
  @NoHair.MassShellJoining.cone_estimates m a e x hf v w hv hvv hvw hww

theorem sign_on_interval (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < f u ↔ 0 < f v := by
  have imp (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hp : 0 < f s) :
      0 < f t := by
    by_contra! h
    obtain ⟨z, hz, he⟩ := isPreconnected_Icc.intermediate_value ht hs hf.continuousOn
      (show (0:ℝ) ∈ Icc (f t) (f s) from ⟨h,hp.le⟩)
    exact hn z hz he
  exact ⟨imp u v hu hv, imp v u hv hu⟩


private abbrev J := Icc (0:ℝ) 1
theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J := by
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hf.continuous.continuousOn hf.differentiableOn
    (fun s hs => (hd s).deriv.symm ▸ h s (interior_subset hs))


private theorem arc_displacement (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    dist (γ s) (γ 0) ≤ 2*|(γ 1).val 0-(γ 0).val 0| := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  let o : ℝ := if 0 < v 0 0 then 1 else -1
  have ho : o=1 ∨ o= -1 := by unfold o; split <;> simp
  have h₀ : (0:ℝ) ∈ J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ) ∈ J := right_mem_Icc.mpr zero_le_one
  have hsign (s : ℝ) (hs : s ∈ J) : 0 < o*v s 0 := by
    have he := sign_on_interval (fun t => v t 0) hcont hne 0 s h₀ hs
    unfold o
    split_ifs with h
    · simpa using he.mp h
    · have hh : v s 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun h' => h (he.mpr h'))) (hne s hs)
      simpa using hh
  have hmag (s : ℝ) (hs : s ∈ J) : |v s 0| = o*v s 0 := by
    have hh := abs_of_pos (hsign s hs)
    rw [abs_mul] at hh
    rcases ho with h|h <;> simpa [h] using hh
  have htmono : MonotoneOn (fun s => o*f s 0) J :=
    monotone_from_deriv _ _ (fun s => (hder 0 s).const_mul o) (fun s hs => (hsign s hs).le)
  have ht01 := htmono h₀ h₁ zero_le_one
  change o*f 0 0 ≤ o*f 1 0 at ht01
  have hclock : o*(f 1 0-f 0 0) = |f 1 0-f 0 0| := by
    rcases ho with h|h <;> rw [h] at ht01 ⊢
    · rw [abs_of_nonneg (by linarith : 0 ≤ f 1 0-f 0 0)]; ring
    · rw [abs_of_nonpos (by linarith : f 1 0-f 0 0 ≤ 0)]; ring
  have hcoords (i : Fin 4) : |f s i-f 0 i| ≤ |f 1 0-f 0 0| := by
    have hplus : MonotoneOn (fun s => o*f s 0+f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).add (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [neg_abs_le (v s i)])
    have hminus : MonotoneOn (fun s => o*f s 0-f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).sub (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [le_abs_self (v s i)])
    have ha := hplus h₀ hs hs.1
    have hb := hminus h₀ hs hs.1
    have hc := htmono hs h₁ hs.2
    beta_reduce at ha hb hc
    change |f s i-f 0 i| ≤ |f 1 0-f 0 0|
    rw [← hclock]
    exact abs_le.mpr ⟨by nlinarith only [ha,hc],by nlinarith only [hb,hc]⟩
  let B := |f 1 0-f 0 0|
  have hb : 0 ≤ B := abs_nonneg _
  have hsq (i : Fin 4) : (f s i-f 0 i)^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hcoords i)
  change ‖f s-f 0‖ ≤ 2*B
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  change (f s 0-f 0 0)^2+(f s 1-f 0 1)^2+(f s 2-f 0 2)^2+(f s 3-f 0 3)^2 ≤ _
  nlinarith only [hsq 0,hsq 1,hsq 2,hsq 3]

private theorem restrict_arc (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T K γ) (l h : ℝ) (hl : 0≤l) (hh : 0<h) (hlh : l+h≤1) :
    IsFutureCausalCurveIn (G m a e) T K (fun s => γ (l+h*s)) := by
  let φ (s : ℝ) := l+h*s
  have hφ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) 1 φ := contMDiff_iff_contDiff.mpr (by dsimp [φ]; fun_prop)
  refine ⟨hγ.1.comp hφ,?_⟩
  intro s hs
  have hi : φ s ∈ J := ⟨by dsimp [φ]; linarith [mul_nonneg hh.le hs.1],by dsimp [φ]; nlinarith only [hlh,mul_le_mul_of_nonneg_left hs.2 hh.le]⟩
  obtain ⟨hK,hn,hvv,hvT⟩ := hγ.2 (φ s) hi
  have dφ : HasDerivAt φ h s := by simpa [φ] using (((hasDerivAt_id s).const_mul h).const_add l)
  have hvel : (velocity (γ ∘ φ) s : E4) = h • (velocity γ (φ s) : E4) := by
    unfold velocity
    rw [mfderiv_comp s (hγ.1.mdifferentiableAt (by simp)) (hφ.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s) (fderiv ℝ φ s 1) = _
    rw [show fderiv ℝ φ s 1 = h from dφ.deriv]
    let L : ℝ →L[ℝ] E4 := mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s)
    change L h = h • L 1
    simpa only [smul_eq_mul,mul_one] using L.map_smul h (1:ℝ)
  let A := matrixBilin (kerrNewmanMetric m a e (γ (φ s)).val)
  let v : E4 := velocity γ (φ s)
  let w : E4 := T (γ (φ s))
  change v ≠ 0 at hn
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvT
  refine ⟨hK,?_⟩
  change (velocity (γ ∘ φ) s : E4) ≠ 0 ∧ A (velocity (γ ∘ φ) s) (velocity (γ ∘ φ) s) ≤ 0 ∧
    A (velocity (γ ∘ φ) s) w<0
  rw [hvel]
  change (h • v : E4) ≠ 0 ∧ A (h • v) (h • v) ≤ 0 ∧ A (h • v) w < 0
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact ⟨smul_ne_zero hh.ne' hn,mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hvv),
    mul_neg_of_pos_of_neg hh hvT⟩

private def composeRel {X : Type*} (A : Set (X × X)) : Set (X × X) := {z | ∃ x, (z.1,x)∈A ∧ (x,z.2)∈A}

private theorem compact_composition {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set (X × X)}
    (hA : IsCompact A) : IsCompact (composeRel A) := by
  let S : Set ((X×X)×(X×X)) := {z | z.1.2=z.2.1}
  have hs : IsClosed S := isClosed_eq (continuous_snd.comp continuous_fst) (continuous_fst.comp continuous_snd)
  let F (z : (X×X)×(X×X)) := (z.1.1,z.2.2)
  have e : composeRel A = F '' ((A ×ˢ A) ∩ S) := by
    ext z
    constructor
    · rintro ⟨x,h1,h2⟩
      exact ⟨((z.1,x),(x,z.2)),⟨⟨h1,h2⟩,rfl⟩,rfl⟩
    · rintro ⟨⟨⟨p,x⟩,⟨y,q⟩⟩,⟨⟨hx,hy⟩,h⟩,rfl⟩
      change x=y at h
      subst y
      exact ⟨x,hx,hy⟩
  rw [e]
  exact ((hA.prod hA).inter_right hs).image ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))

private def shortRel (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) : Set (U a × U a) :=
  {z | z.1∈K ∧ z.2∈K ∧ z.2∈causalFuture (G m a e) T K z.1 ∧ |z.2.val 0-z.1.val 0|≤d}

private theorem bisect (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) (hd : 0≤d) :
    shortRel m a e T K (2*d) ⊆ composeRel (shortRel m a e T K d) := by
  rintro ⟨p,q⟩ ⟨hp,hq,hj,hlen⟩
  by_cases hshort : |q.val 0-p.val 0|≤d
  · exact ⟨p,⟨hp,hp,Or.inl rfl,by simpa⟩,⟨hp,hq,hj,hshort⟩⟩
  rcases hj with he|⟨γ,hγ,h0,h1⟩
  · have hqp : q = p := Set.mem_singleton_iff.mp he
    exact (hshort (by simpa [hqp] using hd)).elim
  let t (s : ℝ) := (γ s).val 0
  have hc : Continuous t := (PiLp.continuous_apply 2 _ 0).comp (continuous_subtype_val.comp hγ.1.continuous)
  have hne : t 0 ≠ t 1 := by
    intro h
    change (γ 0).val 0 = (γ 1).val 0 at h
    rw [h0,h1] at h
    change p.val 0 = q.val 0 at h
    exact hshort (by rw [h,sub_self,abs_zero]; exact hd)
  let mid := (t 0+t 1)/2
  have hmid : mid ∈ t '' J := by
    rcases le_total (t 0) (t 1) with h|h
    · apply intermediate_value_Icc zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
    · apply intermediate_value_Icc' zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
  obtain ⟨s,hs,he⟩ := hmid
  have hs0 : 0<s := lt_of_le_of_ne hs.1 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hs1 : s<1 := lt_of_le_of_ne hs.2 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hsK := (hγ.2 s hs).1
  have hγa := restrict_arc m a e T K γ hγ 0 s le_rfl hs0 (by linarith)
  have hγb := restrict_arc m a e T K γ hγ s (1-s) hs.1 (by linarith) (by linarith)
  have hpq : |t 1-t 0| ≤ 2*d := by simpa only [t,h0,h1] using hlen
  have hhalf : |(t 1-t 0)/2| ≤ d := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have ha : t s-t 0=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  have hb : t 1-t s=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  refine ⟨γ s,⟨hp,hsK,Or.inr ⟨_,hγa,by simpa using h0,by simp⟩,?_⟩,
    ⟨hsK,hq,Or.inr ⟨_,hγb,by simp,by convert h1 using 2 <;> ring⟩,?_⟩⟩
  · rw [← h0]; change |t s-t 0|≤d; rwa [ha]
  · rw [← h1]; change |t 1-t s|≤d; rwa [hb]

theorem result (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' massShell m a e
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := by
  dsimp only
  intro K hK hKD
  let R := shortRel m a e T K
  let JD : Set (U a × U a) := {z | z.2 ∈ causalFuture (G m a e) T (D m a e) z.1}
  have hloc (x : K) := NoHair.MassShellLocal.result m a e hp T hT x.val (hKD x.property)
  choose V hOpen hContain hDom hLocal using hloc
  have hc : K ⊆ ⋃ x : K, V x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hContain ⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric hK hOpen hc
  let d := δ/8
  have hd : 0<d := by dsimp [d]; linarith
  have hcompact (b : ℝ) : IsCompact (closure (R b)) := (hK.prod hK).of_isClosed_subset isClosed_closure
    (closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed))
  have hinside (b : ℝ) : closure (R b) ⊆ K ×ˢ K := closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed)
  have hbase : closure (R d) ⊆ JD := by
    intro z hz
    obtain ⟨x,hx⟩ := hLeb z.1 (hinside d hz).1
    have hdist : ∀ y∈R d, dist y.2 y.1 ≤ 2*d := by
      rintro y ⟨_,_,hJ,ht⟩
      rcases hJ with he|⟨γ,hγ,h0,h1⟩
      · rw [Set.mem_singleton_iff.mp he,dist_self]; linarith
      · have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
          ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
        have h := arc_displacement m a e hp T hT γ hg 1 (right_mem_Icc.mpr zero_le_one)
        rw [h0,h1] at h; linarith
    have hs : dist z.2 z.1 ≤ 2*d := (closure_minimal (show R d ⊆ {y | dist y.2 y.1 ≤ 2*d} from hdist)
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const)) hz
    have hpx : z.1∈V x := hx (Metric.mem_ball_self hδ)
    have hqx : z.2∈V x := hx (show dist z.2 z.1<δ by dsimp [d] at hs; linarith)
    apply hLocal x z hpx hqx
    let N : Set (U a × U a) := {y | dist y.1 z.1 < d}
    have ho : IsOpen N := (Metric.isOpen_ball.preimage continuous_fst)
    have hzn : z ∈ N := by change dist z.1 z.1<d; simpa
    apply closure_mono _ (ho.inter_closure ⟨hzn,hz⟩)
    rintro y ⟨hy,hyR⟩
    change dist y.1 z.1<d at hy
    have near (v : U a) (hv : dist v y.1 ≤ 2*d) : v∈V x := hx (by
      change dist v z.1<δ
      have := dist_triangle v y.1 z.1
      dsimp [d] at hv hy
      linarith)
    refine ⟨near y.1 (by rw [dist_self]; linarith),near y.2 (hdist y hyR),?_⟩
    rcases hyR.2.2.1 with he|⟨γ,hγ,h0,h1⟩
    · exact Or.inl he
    · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
      intro t ht
      have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
        ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
      have hh := arc_displacement m a e hp T hT γ hg t ht
      rw [h0,h1] at hh
      exact ⟨near _ (by linarith [hyR.2.2.2]),(hγ.2 t ht).2⟩
  have hdyadic (n : ℕ) : closure (R ((2:ℝ)^n*d)) ⊆ JD := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      let b := (2:ℝ)^n*d
      have hsup : closure (R (2*b)) ⊆ composeRel (closure (R b)) := by
        apply closure_minimal _ (compact_composition (hcompact b)).isClosed
        intro z hz
        obtain ⟨x,hx,hy⟩ := bisect m a e T K b (by dsimp [b]; positivity) hz
        exact ⟨x,subset_closure hx,subset_closure hy⟩
      intro z hz
      have he : (2:ℝ)^(n+1)*d=2*b := by dsimp [b]; ring
      rw [he] at hz
      obtain ⟨x,hx,hy⟩ := hsup hz
      exact NoHair.MassShellTrans.result m a e hp T hT z.1 (hKD (hinside b hx).1)
        x (hKD (hinside b hx).2) z.2 (hKD (hinside b hy).2) (ih hx) (ih hy)
  have hct : Continuous (fun z : U a => |z.val 0|) := by fun_prop
  obtain ⟨M,hM⟩ := hK.bddAbove_image hct.abs.continuousOn
  have bound (x : U a) (hx : x∈K) : |x.val 0|≤M := by
    simpa using hM (show |(|x.val 0|)| ∈ (fun z : U a => |(|z.val 0|)|) '' K from ⟨x,hx,rfl⟩)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2*M/d) (by norm_num : (1:ℝ)<2)
  apply (closure_mono ?_).trans (hdyadic n)
  rintro z ⟨h1,h2,hj⟩
  refine ⟨h1,h2,hj,?_⟩
  have ht := (div_lt_iff₀ hd).mp hn
  linarith [abs_sub (z.2.val 0) (z.1.val 0),bound z.1 h1,bound z.2 h2]

end
end NoHair.MassShellCompact

open NoHair Set

theorem _root_.NoHair.kerrNewman_mass_shell_compact_limit (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' {z | m < ksRadius a z}
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := NoHair.MassShellCompact.result m a e hp T hT
end

/- Prove2Me theorem NoHair.schwarzschild_unit_cutoff_causality (ddc642bf-c57b-4b4d-b191-d17c8ed3de9c). -/
namespace IsraelBundle.NoHair_schwarzschild_unit_cutoff_causality
open Filter Topology
set_option backward.isDefEq.respectTransparency false

open NoHair NoHair.KNE Set
open scoped BigOperators Manifold ContDiff

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev T (m a e : ℝ) := kerrNewmanTimeDirection m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def timeC (v : E4) := v 0

private theorem dot_symm (u v : V3) : dot3 u v = dot3 v u :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_symm u v

private theorem dot_add_l (u v w : V3) : dot3 (u+v) w = dot3 u w + dot3 v w :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_add_l u v w

private theorem dot_add_r (u v w : V3) : dot3 u (v+w) = dot3 u v + dot3 u w :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_add_r u v w

private theorem dot_scale_l (c : ℝ) (u v : V3) : dot3 (c • u) v = c*dot3 u v :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_scale_l c u v

private theorem dot_scale_r (c : ℝ) (u v : V3) : dot3 u (c • v) = c*dot3 u v :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_scale_r c u v

private theorem dot_cauchy (u v : V3) : (dot3 u v)^2 ≤ dot3 u u * dot3 v v :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.dot_cauchy u v

private theorem axis_unit (a : ℝ) (x : U a) : dot3 (axis a x.val) (axis a x.val) = 1 :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.axis_unit a x

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(timeC v*timeC w) + dot3 (space v) (space w) +
      ksProfile m a e x.val * (timeC v + dot3 (axis a x.val) (space v)) *
        (timeC w + dot3 (axis a x.val) (space w)) :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.metric_formula m a e x v w

private theorem t_coords (m a e : ℝ) (x : U a) :
    timeC (T m a e x) = 1 + ksProfile m a e x.val / 2 ∧
    space (T m a e x) = -(ksProfile m a e x.val / 2) • axis a x.val :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.t_coords m a e x

private theorem metric_T (m a e : ℝ) (x : U a) (v : E4) :
    G m a e x v (T m a e x) = -timeC v + (ksProfile m a e x.val/2) *
      (timeC v + dot3 (axis a x.val) (space v)) :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.metric_T m a e x v

private theorem time_orientation (m a e : ℝ) : IsTimeOrientation (G m a e) (T m a e) :=
  @IsraelBundle.NoHair_kerrNewman_outerHorizon_futureTrapped.time_orientation m a e

private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x :=
  @IsraelBundle.NoHair_schwarzschild_unit_cutoff_end.radius_eq x

private theorem timelike_scale (m a e : ℝ) (x : U a) (v : E4) (N : ℝ) (hN : 0<N)
    (hv : IsFutureTimelike (G m a e) (T m a e) x v) :
    IsFutureTimelike (G m a e) (T m a e) x (N • v) := by
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  let w : E4 := T m a e x
  change A v v < 0 ∧ A v w < 0 at hv
  change A (N • v) (N • v)<0 ∧ A (N • v) w<0
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact ⟨mul_neg_of_pos_of_neg hN (mul_neg_of_pos_of_neg hN hv.1),mul_neg_of_pos_of_neg hN hv.2⟩


private abbrev Space := kerrNewmanSpacetime 0
private abbrev A : Set Space := (Subtype.val : Space → E4) ⁻¹' exteriorRegion 1
private abbrev big := G 1 0 0
private abbrev small := G (1/2) 0 0
private abbrev Tbig := T 1 0 0
private abbrev Tsmall := T (1/2) 0 0
private lemma halfParams : IsKerrNewmanBlackHoleParams (1/2) 0 0 := by norm_num [IsKerrNewmanBlackHoleParams]
private lemma oneParams : IsKerrNewmanBlackHoleParams 1 0 0 := by norm_num [IsKerrNewmanBlackHoleParams]
private lemma halfOuter : kerrNewmanOuterRadius (1/2) 0 0 = 1 := by
  norm_num [kerrNewmanOuterRadius]
  all_goals rw [show Real.sqrt 4 = 2 by convert Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2) using 2 <;> norm_num] <;> norm_num
private lemma small_domain : ((Subtype.val : Space → E4) ⁻¹' kerrNewmanDOC (1/2) 0 0) = A := by
  ext x
  change (kerrNewmanOuterRadius (1/2) 0 0 < ksRadius 0 x.val) ↔ 1 < spatialRadius x.val
  rw [halfOuter,radius_eq]
private lemma massDomain : ((Subtype.val : Space → E4) ⁻¹' {z | (1:ℝ) < ksRadius 0 z}) = A := by
  ext x; change (1 < ksRadius 0 x.val) ↔ 1 < spatialRadius x.val; rw [radius_eq]
private lemma profileS (m : ℝ) (x : Space) : ksProfile m 0 0 x.val = 2*m/ksRadius 0 x.val := by
  have h : 0 < ksRadius 0 x.val := x.property
  unfold ksProfile
  field_simp [h.ne'] <;> ring

private lemma wider (x : Space) (v : E4) (hne : v ≠ 0) (hg : big x v v ≤ 0) (ht : big x v (Tbig x) < 0) :
    small x v v ≤ big x v v ∧ small x v (Tsmall x) ≤ big x v (Tbig x) := by
  let f := ksProfile 1 0 0 x.val
  let l := timeC v + dot3 (axis 0 x.val) (space v)
  have fpos : 0 < f := by dsimp only [f]; rw [profileS]; exact div_pos (by norm_num) x.property
  have half : ksProfile (1/2) 0 0 x.val = f/2 := by dsimp only [f]; rw [profileS,profileS]; ring
  have tc := (NoHair.MassShellGeodesics.cone_estimates 1 0 0 x fpos.le v (Tbig x) hne hg ht
    ((time_orientation 1 0 0).2 x)).2
  change 0 < timeC v * timeC (Tbig x) at tc
  rw [(t_coords 1 0 0 x).1] at tc
  have tv : 0 < timeC v := pos_of_mul_pos_left tc (by linarith [fpos] : 0 ≤ 1+f/2)
  have hh := hg
  rw [metric_formula] at hh
  have bound : dot3 (space v) (space v) ≤ (timeC v)^2 := by
    change -(timeC v * timeC v) + dot3 (space v) (space v) + f*l*l ≤ 0 at hh
    nlinarith only [hh, mul_nonneg fpos.le (sq_nonneg l)]
  have cs := dot_cauchy (axis 0 x.val) (space v)
  rw [axis_unit,one_mul] at cs
  have hl : 0 ≤ l := by
    have cmp := (sq_le_sq.mp (cs.trans bound)).trans_eq (abs_of_pos tv)
    dsimp only [l]; linarith [neg_abs_le (dot3 (axis 0 x.val) (space v))]
  constructor
  · rw [metric_formula,metric_formula,half]
    change -(timeC v*timeC v) + dot3 (space v) (space v) + (f/2)*l*l ≤ -(timeC v*timeC v) + dot3 (space v) (space v) + f*l*l
    nlinarith only [mul_nonneg fpos.le (sq_nonneg l)]
  · rw [metric_T, metric_T,half]
    change -timeC v+(f/2/2)*l ≤ -timeC v+(f/2)*l
    nlinarith only [mul_nonneg fpos.le hl]

private lemma widen_arc (S : Set Space) (γ : ℝ → Space) (hg : IsFutureCausalCurveIn big Tbig S γ) :
    IsFutureCausalCurveIn small Tsmall S γ := by
  refine ⟨hg.1, fun t ht => ?_⟩
  obtain ⟨hx,hn,hv,hw⟩ := hg.2 t ht
  obtain ⟨he,he'⟩ := wider _ _ hn hv hw
  exact ⟨hx,hn,he.trans hv,he'.trans_lt hw⟩

private lemma widen_timelike (γ : ℝ → Space) (hg : IsFutureTimelikeCurveIn big Tbig univ γ) :
    IsFutureTimelikeCurveIn small Tsmall univ γ := by
  refine ⟨hg.1,fun t ht => ?_⟩
  obtain ⟨hx,hv,hw⟩ := hg.2 t ht
  have hn : (velocity γ t : E4) ≠ 0 := by intro hn; change (big (γ t)) (velocity γ t) (velocity γ t) < 0 at hv; simp [hn] at hv
  obtain ⟨he,he'⟩ := wider _ _ hn hv.le hw
  exact ⟨hx,he.trans_lt hv,he'.trans_lt hw⟩

private def fourV (a b c d : ℝ) : E4 := WithLp.toLp 2 ![a,b,c,d]
private lemma vecDer {t x y z : ℝ → ℝ} {dt dx dy dz s : ℝ}
    (ht : HasDerivAt t dt s) (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) (hz : HasDerivAt z dz s) :
    HasDerivAt (fun s => fourV (t s) (x s) (y s) (z s)) (fourV dt dx dy dz) s := by
  have h : HasDerivAt (fun s => (![t s,x s,y s,z s] : Fin 4 → ℝ)) ![dt,dx,dy,dz] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    exacts [ht,hx,hy,hz]
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s h

private def dir (x : Space) := fourV 2 (-ksNull 0 x.val 1) (-ksNull 0 x.val 2) (-ksNull 0 x.val 3)
private lemma dir_future (x : Space) (hr : 1 < ksRadius 0 x.val) : IsFutureTimelike big Tbig x (dir x) := by
  have tb : timeC (dir x)=2 := rfl
  have sp : space (dir x)=(-1:ℝ) • axis 0 x.val := by
    rw [neg_one_smul]
    ext i
    fin_cases i <;> rfl
  have hl : ksProfile 1 0 0 x.val < 2 := by rw [profileS]; exact (div_lt_iff₀ x.property).mpr (by linarith)
  constructor
  · rw [metric_formula,tb,sp,dot_scale_l,dot_scale_r,axis_unit]
    linarith
  · rw [metric_T,tb,sp,dot_scale_r,axis_unit]
    linarith

private def scaleR (a b t : ℝ) := Real.exp (-a*(t-b))
private def pathY (p : Space) (a b t : ℝ) : E4 :=
  let f := scaleR a b t
  let r := ksRadius 0 p.val
  fourV (p.val 0+2*r*(1-f)) (f*p.val 1) (f*p.val 2) (f*p.val 3)
private lemma path_radius (p : Space) (a b t : ℝ) : ksRadius 0 (pathY p a b t) =
    scaleR a b t * ksRadius 0 p.val := by
  let f := scaleR a b t
  have hf : 0<f := Real.exp_pos _
  let r := ksRadius 0 p.val
  have hr : 0 < r := p.property
  have hsq : r^2=p.val 1^2+p.val 2^2+p.val 3^2 := by dsimp only [r]; rw [radius_eq,spatialRadius,Real.sq_sqrt (by positivity)]
  rw [radius_eq]
  change Real.sqrt ((f*p.val 1)^2+(f*p.val 2)^2+(f*p.val 3)^2)=f*r
  have e : (f*p.val 1)^2+(f*p.val 2)^2+(f*p.val 3)^2=(f*r)^2 := by rw [show (f*r)^2=f^2*r^2 by ring,hsq]; ring
  rw [e,Real.sqrt_sq (mul_pos hf hr).le]

private def pathS (p : Space) (a b t : ℝ) : Space :=
  ⟨pathY p a b t,by change 0<ksRadius 0 (pathY p a b t); rw [path_radius]; exact mul_pos (Real.exp_pos _) p.property⟩

private lemma path_smooth (p:Space) (a b:ℝ) : ContMDiff 𝓘(ℝ,ℝ) I4 1 (pathS p a b) := by
  apply ContMDiff.of_le (n := ∞) _ (by simp)
  apply (ContMDiff.subtypeVal_comp_iff (U 0) (pathS p a b)).mp
  apply contMDiff_iff_contDiff.mpr
  change ContDiff ℝ ∞ (pathY p a b)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [pathY,fourV,scaleR,Matrix.cons_val] <;> fun_prop

private lemma path_velocity (p : Space) (a b t : ℝ) :
    (velocity (pathS p a b) t : E4) = (a*ksRadius 0 (pathS p a b t).val) • dir (pathS p a b t) := by
  let x := pathS p a b t
  let f := scaleR a b t
  let r := ksRadius 0 p.val
  have hh : HasDerivAt (scaleR a b) (-a*f) t := by
    apply ((((hasDerivAt_id' t).sub_const b).const_mul (-a)).exp).congr_deriv
    change Real.exp (-a*(t-b)) * (-a*1) = -a*f
    dsimp only [f,scaleR]; ring
  have hd := vecDer (((hasDerivAt_const t (1:ℝ)).fun_sub hh).const_mul (2*r) |>.const_add (p.val 0))
    (hh.mul_const (p.val 1)) (hh.mul_const (p.val 2)) (hh.mul_const (p.val 3))
  have vel := NoHair.MassShellGeodesics.ambient_velocity 0 (pathS p a b) (path_smooth p a b) t _ hd
  rw [vel]
  have hR : ksRadius 0 x.val = f*r := path_radius p a b t
  have h1 : f*p.val 1 = ksRadius 0 x.val * ksNull 0 x.val 1 := by
    change x.val 1 = _
    simpa only [zero_mul,sub_zero] using ks_x1 0 x.val x.property
  have h2 : f*p.val 2 = ksRadius 0 x.val * ksNull 0 x.val 2 := by
    change x.val 2 = _
    simpa only [zero_mul,zero_add] using ks_x2 0 x.val x.property
  have h3 : f*p.val 3 = ksRadius 0 x.val * ksNull 0 x.val 3 := ks_x3 0 x.val x.property
  apply (show ∀ v w : E4, (∀ i : Fin 4, v i=w i) → v=w from fun v w h => by ext i; exact h i) _ _
  intro i
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by fin_cases i <;> decide) with rfl|rfl|rfl|rfl
  · change 2*r*(0- -a*f)=a*ksRadius 0 x.val*2; rw [hR]; ring
  · change -a*f*p.val 1=a*ksRadius 0 x.val*(-ksNull 0 x.val 1); linear_combination (-a)*h1
  · change -a*f*p.val 2=a*ksRadius 0 x.val*(-ksNull 0 x.val 2); linear_combination (-a)*h2
  · change -a*f*p.val 3=a*ksRadius 0 x.val*(-ksNull 0 x.val 3); linear_combination (-a)*h3

private lemma neighbors (p : Space) (hp : p ∈ A) (b : ℝ) (hb : b ∈ Icc (0:ℝ) 1) :
    ∃ γ : ℝ → Space, IsFutureTimelikeCurveIn big Tbig univ γ ∧
      (∀ s ∈ Icc (0:ℝ) 1, γ s ∈ A) ∧ γ b=p := by
  let r := ksRadius 0 p.val
  have hr : 1<r := by change 1<ksRadius 0 p.val; rw [radius_eq]; exact hp
  have hr0 : 0<r := p.property
  let a := Real.log r/2
  have logpos := Real.log_pos hr
  have ha : 0<a := by dsimp only [a]; positivity
  have within (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 1 < ksRadius 0 (pathS p a b s).val := by
    rw [show ksRadius 0 (pathS p a b s).val=scaleR a b s*r from path_radius p a b s]
    change 1<Real.exp (-a*(s-b))*r
    rw [← Real.exp_log hr0,← Real.exp_add]
    apply Real.one_lt_exp_iff.mpr
    have cmp := mul_le_mul_of_nonneg_left (show s-b ≤ 1 by linarith only [hs.2,hb.1]) ha.le
    have e : Real.log r=2*a := by dsimp only [a]; ring
    linarith
  refine ⟨pathS p a b,⟨path_smooth p a b,?_⟩,?_,?_⟩
  · intro s hs
    refine ⟨mem_univ _,?_⟩
    rw [path_velocity]
    exact timelike_scale 1 0 0 _ _ _ (mul_pos ha (pathS p a b s).property) (dir_future _ (within s hs))
  · intro s hs
    change 1<spatialRadius (pathS p a b s).val
    rw [← radius_eq]; exact within s hs
  · apply Subtype.ext
    change pathY p a b b=p.val
    have hf : scaleR a b b=1 := by simp [scaleR]
    unfold pathY
    rw [hf]
    ext i
    rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by fin_cases i <;> decide) with rfl|rfl|rfl|rfl
    · change p.val 0+2*ksRadius 0 p.val*(1-1)=p.val 0; ring
    · change 1*p.val 1=p.val 1; ring
    · change 1*p.val 2=p.val 2; ring
    · change 1*p.val 3=p.val 3; ring

private lemma pastA : chronoPastSet big Tbig A = A := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨x,hx'⟩ := mem_iUnion.mp hp
    obtain ⟨hx,γ,hγ,hp',hx'⟩ := mem_iUnion.mp hx'
    by_contra h
    have hlow : ksRadius 0 (γ 0).val ≤ kerrNewmanOuterRadius (1/2) 0 0 := by
      rw [hp',halfOuter,radius_eq]; exact le_of_not_gt h
    have hr := (kerrNewman_outerHorizon_futureTrapped (1/2) 0 0 halfParams).2 γ (widen_timelike γ hγ) hlow
    rw [hx',halfOuter,radius_eq] at hr
    exact (not_lt.mpr hr) hx
  · intro p hp
    obtain ⟨γ,hγ,hmem,h0⟩ := neighbors p hp 0 (left_mem_Icc.mpr zero_le_one)
    exact mem_iUnion.mpr ⟨γ 1,mem_iUnion.mpr ⟨hmem _ (right_mem_Icc.mpr zero_le_one),γ,hγ,h0,rfl⟩⟩

private lemma futureA : A ⊆ chronoFutureSet big Tbig A := by
  intro p hp
  obtain ⟨γ,hγ,hmem,h1⟩ := neighbors p hp 1 (right_mem_Icc.mpr zero_le_one)
  exact mem_iUnion.mpr ⟨γ 0,mem_iUnion.mpr ⟨hmem _ (left_mem_Icc.mpr zero_le_one),γ,hγ,rfl,h1⟩⟩

namespace SchwarzschildConfinement
open NoHair Set
open scoped ContDiff Manifold BigOperators

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' kerrNewmanDOC m a e
private abbrev I4 := 𝓘(ℝ, E4)
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w :=
  @NoHair.MassShellJoining.metric_formula m a e x v w

private theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m + Real.sqrt (m^2 - a^2 - e^2) < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := by linarith [Real.sqrt_nonneg (m^2-a^2-e^2)]
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 :=
  @NoHair.MassShellJoining.spatial_squares m a e x hf v hv

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v :=
  @NoHair.MassShellJoining.spatial_kernel m a e x hf v h0

private theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) :=
  @NoHair.MassShellJoining.cone_estimates m a e x hf v w hv hvv hvw hww

private theorem sign_on_interval (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < f u ↔ 0 < f v :=
  @NoHair.MassShellCompact.sign_on_interval f hf hn u v hu hv

private abbrev J := Icc (0:ℝ) 1
private def weight (m a e : ℝ) (z : E4) :=
  (ksRadius a z-kerrNewmanOuterRadius m a e)*Real.exp (-(z 0)/m)

private theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J :=
  @NoHair.MassShellCompact.monotone_from_deriv f d hd h

private theorem curve_envelope (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    let w (s : ℝ) := weight m a e (γ s).val
    (∀ s ∈ J, ∀ i : Fin 4, |(γ s).val i-(γ 0).val i| ≤ |(γ 1).val 0-(γ 0).val 0|) ∧
    (∀ s ∈ J, min (w 0) (w 1) ≤ w s) ∧
    ∀ s ∈ J, 0 ≤ ((γ 1).val 0-(γ 0).val 0)*timeComponent (T (γ s)) ∧
      (w 1-w 0)*timeComponent (T (γ s)) ≤ 0 := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  let o : ℝ := if 0 < v 0 0 then 1 else -1
  have ho : o=1 ∨ o= -1 := by unfold o; split <;> simp
  have h₀ : (0:ℝ) ∈ J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ) ∈ J := right_mem_Icc.mpr zero_le_one
  have hsign (s : ℝ) (hs : s ∈ J) : 0 < o*v s 0 := by
    have he := sign_on_interval (fun t => v t 0) hcont hne 0 s h₀ hs
    unfold o
    split_ifs with h
    · simpa using he.mp h
    · have hh : v s 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun h' => h (he.mpr h'))) (hne s hs)
      simpa using hh
  have hTsign (s : ℝ) (hs : s ∈ J) : 0 < o*timeComponent (T (γ s)) := by
    have h1 := hsign s hs
    have h2 := (hcone s hs).2
    rcases ho with h|h <;> rw [h] at h1 ⊢
    · simpa using pos_of_mul_pos_right h2 (by linarith : 0 ≤ v s 0)
    · have ht : timeComponent (T (γ s)) < 0 := by
        by_contra! ht
        exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (show v s 0 ≤ 0 by linarith) ht)) h2
      simpa using ht
  have hmag (s : ℝ) (hs : s ∈ J) : |v s 0| = o*v s 0 := by
    have hh := abs_of_pos (hsign s hs)
    rw [abs_mul] at hh
    rcases ho with h|h <;> simpa [h] using hh
  let b := kerrNewmanOuterRadius m a e
  let w (s : ℝ) := weight m a e (f s)
  let dv (s : ℝ) := fderiv ℝ (ksRadius a) (f s) (v s)
  let dw (s : ℝ) := Real.exp (-(f s 0)/m)*(dv s-(ksRadius a (f s)-b)*(v s 0)/m)
  have hdr (s : ℝ) : HasDerivAt (fun t => ksRadius a (f t)) (dv s) s := by
    have hv := ((hf.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hd] at hv
    exact (ksRadius_differentiableAt a (f s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have hdw (s : ℝ) : HasDerivAt w (dw s) s := by
    apply (((hdr s).sub_const b).mul (((hder 0 s).neg.div_const m).exp)).congr_deriv
    dsimp [dw]; ring
  have hwd (s : ℝ) (hs : s ∈ J) : o*dw s ≤ 0 := by
    have hvv := (hγ.2 s hs).2.2.1
    let A := matrixBilin (kerrNewmanMetric m a e (γ s).val)
    change A (v s) (v s) ≤ 0 at hvv
    have hvs : G m a e (γ s) (o • v s) (o • v s) ≤ 0 := by
      change A (o • v s) (o • v s) ≤ 0
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg o) hvv]
    have ht : 0 ≤ (o • v s) 0 := (hsign s hs).le
    have h := kerrNewman_exterior_radialVelocityBound m a e hp (γ s) (hγ.2 s hs).1 (o • v s) ht hvs
    rw [map_smul] at h
    change m*(o*dv s) ≤ (ksRadius a (f s)-b)*(o*v s 0) at h
    have hh : o*(dv s-(ksRadius a (f s)-b)*(v s 0)/m) ≤ 0 := by
      apply le_of_mul_le_mul_left (a := m) _ hp.1
      rw [mul_zero]
      field_simp [hp.1.ne']
      nlinarith only [mul_le_mul_of_nonneg_left h hp.1.le, h]
    calc
      o*dw s = Real.exp (-(f s 0)/m)*(o*(dv s-(ksRadius a (f s)-b)*(v s 0)/m)) := by dsimp [dw]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hh
  have hwmono : MonotoneOn (fun s => -(o*w s)) J :=
    monotone_from_deriv _ _ (fun s => ((hdw s).const_mul o).neg) (fun s hs => neg_nonneg.mpr (hwd s hs))
  have htmono : MonotoneOn (fun s => o*f s 0) J :=
    monotone_from_deriv _ _ (fun s => (hder 0 s).const_mul o) (fun s hs => (hsign s hs).le)
  have ht01 := htmono h₀ h₁ zero_le_one
  have hw01 := hwmono h₀ h₁ zero_le_one
  change o*f 0 0 ≤ o*f 1 0 at ht01
  change -(o*w 0) ≤ -(o*w 1) at hw01
  have hclock : o*(f 1 0-f 0 0) = |f 1 0-f 0 0| := by
    rcases ho with h|h <;> rw [h] at ht01 ⊢
    · rw [abs_of_nonneg (by linarith : 0 ≤ f 1 0-f 0 0)]; ring
    · rw [abs_of_nonpos (by linarith : f 1 0-f 0 0 ≤ 0)]; ring
  refine ⟨?_,?_,?_⟩
  · intro s hs i
    have hplus : MonotoneOn (fun s => o*f s 0+f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).add (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [neg_abs_le (v s i)])
    have hminus : MonotoneOn (fun s => o*f s 0-f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).sub (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [le_abs_self (v s i)])
    have ha := hplus h₀ hs hs.1
    have hb := hminus h₀ hs hs.1
    have hc := htmono hs h₁ hs.2
    beta_reduce at ha hb hc
    change |f s i-f 0 i| ≤ |f 1 0-f 0 0|
    rw [← hclock]
    exact abs_le.mpr ⟨by nlinarith only [ha,hc],by nlinarith only [hb,hc]⟩
  · intro s hs
    have ha := hwmono h₀ hs hs.1
    have hb := hwmono hs h₁ hs.2
    beta_reduce at ha hb
    change min (w 0) (w 1) ≤ w s
    rcases ho with h|h <;> rw [h] at ha hb
    · exact (min_le_right _ _).trans (by linarith)
    · exact (min_le_left _ _).trans (by linarith)
  · intro s hs
    have hO := hTsign s hs
    change 0 ≤ (f 1 0-f 0 0)*timeComponent (T (γ s)) ∧ (w 1-w 0)*timeComponent (T (γ s)) ≤ 0
    rcases ho with h|h <;> rw [h] at hO ht01 hw01
    · exact ⟨mul_nonneg (by linarith) (by linarith),mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)⟩
    · exact ⟨mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith),
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)⟩

theorem curve_estimates (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    (∀ i : Fin 4, |(γ 1).val i - (γ 0).val i| ≤ |(γ 1).val 0 - (γ 0).val 0|) ∧
    ∀ t ∈ Icc (0:ℝ) 1, 0 < ((γ 1).val 0 - (γ 0).val 0) * timeComponent (T (γ t)) := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  constructor
  · intro i
    obtain ⟨c, hc', he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      (fun t => f t 0) (fun t => v t 0) zero_lt_one (hc 0).continuous.continuousOn (fun t _ => hder 0 t)
      (fun t => f t i) (fun t => v t i) (hc i).continuous.continuousOn (fun t _ => hder i t)
    have hci := Ioo_subset_Icc_self hc'
    have h := congrArg abs he
    simp only [abs_mul] at h
    apply le_of_mul_le_mul_right (a := |v c 0|) _ (abs_pos.mpr (hne c hci))
    exact h.trans_le (mul_le_mul_of_nonneg_left ((hcone c hci).1 i) (abs_nonneg _))
  · intro t ht
    obtain ⟨c,hc',he⟩ := exists_hasDerivAt_eq_slope (fun s => f s 0) (fun s => v s 0) zero_lt_one
      (hc 0).continuous.continuousOn (fun s _ => hder 0 s)
    simp only [sub_zero, div_one] at he
    change 0 < (f 1 0 - f 0 0) * _
    rw [← he]
    have hci := Ioo_subset_Icc_self hc'
    have hsign := sign_on_interval (fun s => v s 0) hcont hne c t hci ht
    rcases (mul_pos_iff.mp (hcone t ht).2) with h|h
    · exact mul_pos (hsign.mpr h.1) h.2
    · have hneg : v c 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun hh => h.1.not_gt (hsign.mp hh))) (hne c hci)
      exact mul_pos_of_neg_of_neg hneg h.2

private theorem future_envelope (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) 
    (g' : BilinField (U a)) (T' : VecField (U a))
    (widen : ∀ γ, IsFutureCausalCurveIn g' T' (D m a e) γ →
      IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (p q : U a) (hpD : p ∈ D m a e)
    (hq : q ∈ causalFuture g' T' (D m a e) p) :
    let w (x : U a) := weight m a e x.val
    let dt := q.val 0-p.val 0
    q ∈ D m a e ∧ (∀ i : Fin 4, |q.val i-p.val i| ≤ |dt|) ∧
      (0 ≤ dt*timeComponent (T p) ∧ (w q-w p)*timeComponent (T p) ≤ 0) ∧
      (0 ≤ dt*timeComponent (T q) ∧ (w q-w p)*timeComponent (T q) ≤ 0) ∧
      ∀ K : Set (U a), (∀ y : U a, min (w p) (w q) ≤ w y →
        (∀ i : Fin 4, |y.val i-p.val i| ≤ |dt|) → y∈K) →
          q ∈ causalFuture g' T' K p := by
  rcases hq with he|⟨γ,hγ,hp',hq'⟩
  · rcases Set.mem_singleton_iff.mp he with rfl
    refine ⟨hpD, by simp, by simp, by simp, fun K _ => Or.inl rfl⟩
  · subst p
    subst q
    obtain ⟨hc,hw,ht⟩ := curve_envelope m a e hp T hT γ (widen γ hγ)
    have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
    have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
    refine ⟨(hγ.2 1 h₁).1, hc 1 h₁, ht 0 h₀, ht 1 h₁, ?_⟩
    intro K hK
    refine Or.inr ⟨γ,⟨hγ.1,?_⟩,rfl,rfl⟩
    intro s hs
    exact ⟨hK _ (hw s hs) (hc s hs),(hγ.2 s hs).2⟩

private theorem interval_length (u v w s : ℝ) (hs : s ≠ 0)
    (h1 : 0 ≤ (v-u)*s) (h2 : 0 ≤ (w-v)*s) : |v-u| ≤ |w-u| := by
  rcases lt_or_gt_of_ne hs with hn|hp
  · have hv : v-u ≤ 0 := by by_contra! h; exact (not_lt_of_ge h1) (mul_neg_of_pos_of_neg h hn)
    have hw : w-v ≤ 0 := by by_contra! h; exact (not_lt_of_ge h2) (mul_neg_of_pos_of_neg h hn)
    rw [abs_of_nonpos hv, abs_of_nonpos (by linarith : w-u ≤ 0)]
    linarith
  · have hv : 0 ≤ v-u := by by_contra! h; exact (not_lt_of_ge h1) (mul_neg_of_neg_of_pos h hp)
    have hw : 0 ≤ w-v := by by_contra! h; exact (not_lt_of_ge h2) (mul_neg_of_neg_of_pos h hp)
    rw [abs_of_nonneg hv, abs_of_nonneg (by linarith : 0 ≤ w-u)]
    linarith

theorem compact_enclosure (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T)
    (g' : BilinField (U a)) (T' : VecField (U a))
    (widen : ∀ γ, IsFutureCausalCurveIn g' T' (D m a e) γ →
      IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    let U := kerrNewmanSpacetime a
    let g := g'
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ p ∈ D, ∀ q ∈ D, ∃ K : Set U, IsCompact K ∧ K ⊆ D ∧ p ∈ K ∧ q ∈ K ∧
      ∀ x ∈ causalFuture g T' D p ∩ causalPast g T' D q,
        x ∈ K ∧ x ∈ causalFuture g T' K p ∧ q ∈ causalFuture g T' K x := by
  dsimp only
  intro p hpD q hqD
  let w := weight m a e
  let l := min (w p.val) (w q.val)
  let B := |q.val 0-p.val 0|
  let C (i : Fin 4) := |q.val i-p.val i|+2*B+1
  let box : Set (Fin 4 → ℝ) := Icc (fun i => p.val i-C i) (fun i => p.val i+C i)
  let H : Set E4 := (WithLp.toLp 2 '' box) ∩ {z | l ≤ w z}
  let K := (Subtype.val : U a → E4) ⁻¹' H
  have hB : 0 ≤ B := abs_nonneg _
  have hC (i : Fin 4) : 2*B ≤ C i := by dsimp [C]; linarith [abs_nonneg (q.val i-p.val i)]
  have hW : Continuous w := by
    unfold w weight
    exact ((continuous_ksRadius a).sub continuous_const).mul (by fun_prop)
  have hH : IsCompact H := ((show IsCompact box from isCompact_Icc).image (PiLp.continuous_toLp 2 _)).inter_right
    (isClosed_le continuous_const hW)
  have hweight (z : U a) (hz : z∈D m a e) : 0 < w z.val :=
    mul_pos (sub_pos.mpr hz) (Real.exp_pos _)
  have hl : 0<l := lt_min (hweight p hpD) (hweight q hqD)
  have hreg (z : E4) (hz : z ∈ H) : kerrNewmanOuterRadius m a e < ksRadius a z := by
    have hw := hl.trans_le hz.2
    change 0 < (ksRadius a z-kerrNewmanOuterRadius m a e)*Real.exp (-(z 0)/m) at hw
    by_contra! h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (Real.exp_pos _).le)) hw
  have hb : 0<kerrNewmanOuterRadius m a e := hp.1.trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hcompact : IsCompact K := by
    apply Subtype.isCompact_iff.mpr
    have himg : (Subtype.val : U a → E4) '' K = H := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hx
      · intro hz
        exact ⟨⟨z,hb.trans (hreg z hz)⟩,hz,rfl⟩
    rwa [himg]
  have put (x : U a) (hw : l ≤ w x.val) (h : ∀ i : Fin 4, |x.val i-p.val i| ≤ C i) : x∈K := by
    refine ⟨⟨WithLp.ofLp x.val,⟨?_,?_⟩,rfl⟩,hw⟩
    · intro i; have ha := (abs_le.mp (h i)).1; change p.val i-C i ≤ x.val i; linarith
    · intro i; have ha := (abs_le.mp (h i)).2; change x.val i ≤ p.val i+C i; linarith
  have hpK := put p (min_le_left _ _) (fun i => by simp only [sub_self,abs_zero]; linarith [hC i])
  have hqK := put q (min_le_right _ _) (fun i => by dsimp [C]; linarith)
  refine ⟨K,hcompact,fun x hx => hreg x.val hx,hpK,hqK,?_⟩
  intro x hx
  obtain ⟨hxD,hxp,_,h1,hleg1⟩ := future_envelope m a e hp T hT g' T' widen p x hpD hx.1
  obtain ⟨_,_,h2,_,hleg2⟩ := future_envelope m a e hp T hT g' T' widen x q hxD hx.2
  let s := timeComponent (T x)
  have hs : s ≠ 0 := fun h =>
    (not_lt_of_ge (spatial_kernel m a e x (exterior_profile m a e hp x hxD) (T x) h)) (hT.2 x)
  have hxpT : |x.val 0-p.val 0| ≤ B := interval_length _ _ _ s hs h1.1 h2.1
  have hxqT : |q.val 0-x.val 0| ≤ B := by
    rw [abs_sub_comm,show B = |p.val 0-q.val 0| from abs_sub_comm _ _]
    apply interval_length _ _ _ (-s) (neg_ne_zero.mpr hs)
    · nlinarith only [h2.1]
    · nlinarith only [h1.1]
  have hxw : l ≤ w x.val := by
    have hA : (w x.val-w p.val)*s ≤ 0 := h1.2
    have hB' : (w q.val-w x.val)*s ≤ 0 := h2.2
    rcases lt_or_gt_of_ne hs with hn|hpos
    · apply (min_le_left _ _).trans
      by_contra! he
      exact (not_lt_of_ge hA) (mul_pos_of_neg_of_neg (sub_neg.mpr he) hn)
    · apply (min_le_right _ _).trans
      by_contra! he
      exact (not_lt_of_ge hB') (mul_pos (sub_pos.mpr he) hpos)
  have hxi (i : Fin 4) : |x.val i-p.val i| ≤ B := (hxp i).trans hxpT
  refine ⟨put x hxw (fun i => (hxi i).trans (by linarith [hC i])),hleg1 K ?_,hleg2 K ?_⟩
  · intro y hwy hy
    apply put y ((le_min (min_le_left _ _) hxw).trans hwy)
    exact fun i => (hy i).trans (hxpT.trans (by linarith [hC i]))
  · intro y hwy hy
    apply put y ((le_min hxw (min_le_right _ _)).trans hwy)
    intro i
    have htri : |y.val i-p.val i| ≤ |y.val i-x.val i|+|x.val i-p.val i| := by
      simpa only [Real.dist_eq] using dist_triangle (y.val i) (x.val i) (p.val i)
    linarith only [htri,(hy i).trans hxqT,hxi i,hC i]

end
end SchwarzschildConfinement

private lemma shellGH : IsGloballyHyperbolicOn big Tbig A := by
  have orientation := time_orientation (1/2) 0 0
  constructor
  · rintro p hp ⟨γ,hγ,h0,h1⟩
    have hc := widen_arc A γ hγ
    rw [← small_domain] at hc
    have hs := (SchwarzschildConfinement.curve_estimates (1/2) 0 0 halfParams Tsmall orientation γ hc).2 0
      (left_mem_Icc.mpr zero_le_one)
    simp [h0,h1] at hs
  intro p hp q hq
  have encl := SchwarzschildConfinement.compact_enclosure (1/2) 0 0 halfParams Tsmall orientation big Tbig
    (fun γ h => widen_arc _ γ h)
  dsimp only at encl
  rw [small_domain] at encl
  obtain ⟨K,hK,hKA,hpK,hqK,conf⟩ := encl p hp q hq
  let E := causalFuture big Tbig A p ∩ causalPast big Tbig A q
  change IsCompact E
  let Rel : Set (Space × Space) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture big Tbig K z.1}
  let B : Set Space := (fun x => (p,x)) ⁻¹' closure Rel ∩ (fun x => (x,q)) ⁻¹' closure Rel
  have hB : IsClosed B := (isClosed_closure.preimage (continuous_const.prodMk continuous_id)).inter
    (isClosed_closure.preimage (continuous_id.prodMk continuous_const))
  have lim := kerrNewman_mass_shell_compact_limit 1 0 0 oneParams Tbig (time_orientation 1 0 0)
  dsimp only at lim
  rw [massDomain] at lim
  have eq : E = K ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨xK,px,xq⟩ := conf x hx
      exact ⟨xK,subset_closure (show (p,x) ∈ Rel from ⟨hpK,xK,px⟩),
        subset_closure (show (x,q) ∈ Rel from ⟨xK,hqK,xq⟩)⟩
    · rintro ⟨_,h1,h2⟩
      exact ⟨lim K hK hKA (show (p,x) ∈ closure Rel from h1),lim K hK hKA (show (x,q) ∈ closure Rel from h2)⟩
  rw [eq]
  exact hK.inter_right hB

theorem _root_.NoHair.schwarzschild_unit_cutoff_causality :
    ∃ T : VecField (kerrNewmanSpacetime 0), IsTimeOrientation (kerrNewmanMetricField 1 0 0) T ∧
      chronoPastSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) = ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ⊆ chronoFutureSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      IsGloballyHyperbolicOn (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) := ⟨Tbig,time_orientation 1 0 0,pastA,futureA,shellGH⟩
end
end IsraelBundle.NoHair_schwarzschild_unit_cutoff_causality

/- Prove2Me theorem NoHair.schwarzschild_unit_cartesian_ricci_zero (300a3522-f0bd-4483-abc9-c71400d21b85). -/
namespace IsraelBundle.NoHair_schwarzschild_unit_cartesian_ricci_zero
open NoHair NoHair.KNE Set
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
private abbrev rv := ksRadius 0
private def u (z : E4) : ℝ := (rv z)⁻¹
private def tvec : Fin 4 → ℝ := ![1,0,0,0]
private def pmat : Mat := !![0,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1]
private def eta : Mat := !![-1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1]
private def pos (z:E4) : Fin 4 → ℝ := ![0,z 1,z 2,z 3]
private def n (z : E4) (i : Fin 4) : ℝ := pos z i * u z
private lemma four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 :=
  by fin_cases i <;> decide

private lemma v0 {α : Type*} (a b c d : α) : ![a,b,c,d] (0 : Fin 4) = a := rfl
private lemma v1 {α : Type*} (a b c d : α) : ![a,b,c,d] (1 : Fin 4) = b := rfl
private lemma v2 {α : Type*} (a b c d : α) : ![a,b,c,d] (2 : Fin 4) = c := rfl
private lemma v3 {α : Type*} (a b c d : α) : ![a,b,c,d] (3 : Fin 4) = d := rfl

private lemma flat (i j : Fin 4) : minkowski i j = eta i j := by
  rcases four i with rfl | rfl | rfl | rfl <;> rcases four j with rfl | rfl | rfl | rfl <;> rfl
private lemma basis (i j : Fin 4) : coordBasis i j =
    (!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1] : Mat) i j := by
  rcases four i with rfl | rfl | rfl | rfl <;> rcases four j with rfl | rfl | rfl | rfl <;> rfl

private lemma radius_eq (x : E4) : rv x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2)=Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,add_zero,sub_zero,Real.sqrt_sq hp]
  congr 1; ring

private lemma radiusCP (p : E4) (hp : 0 < rv p) : HasCP rv p (n p) := by
  have rsq : rv p ^ 2 = p 1^2+p 2^2+p 3^2 := by rw [radius_eq, spatialRadius, Real.sq_sqrt (by positivity)]
  have qual : DifferentiableAt ℝ rv p := by
    have hpos : 0 < p 1^2+p 2^2+p 3^2 := by rw [← rsq]; positivity
    rw [show rv=spatialRadius from funext radius_eq]
    unfold spatialRadius
    fun_prop (disch := exact hpos.ne')
  refine ⟨qual,fun k => ?_⟩
  apply (hasDerivAt_ksRadius_line 0 p (coordBasis k) hp).congr_deriv
  rcases four k with rfl|rfl|rfl|rfl <;>
    simp only [basis,Matrix.of_apply,v0,v1,v2,v3,n,pos,u,rv,zero_pow (by decide : 2 ≠ 0),
      mul_zero,zero_mul,add_zero,sub_zero,mul_one,zero_add] <;> field_simp [hp.ne'] <;> ring

private structure Atom where
  val : E4 → ℝ
  d : E4 → Fin 4 → ℝ
  cp : ∀ z, 0 < rv z → HasCP val z (d z)

private def ac (c : ℝ) : Atom := ⟨fun _ => c, fun _ _ => 0, fun z _ => HasCP.cst c z⟩
private instance : Add Atom where
  add f g := ⟨fun z => f.val z+g.val z,fun z k => f.d z k+g.d z k,fun z h => (f.cp z h).add (g.cp z h)⟩
private instance : Sub Atom where
  sub f g := ⟨fun z => f.val z-g.val z,fun z k => f.d z k-g.d z k,fun z h => (f.cp z h).sub (g.cp z h)⟩
private instance : Mul Atom where
  mul f g := ⟨fun z => f.val z*g.val z,fun z k => f.d z k*g.val z+f.val z*g.d z k,
    fun z h => (f.cp z h).mul (g.cp z h)⟩

private def inverseRadius : Atom := ⟨u, fun z i => -(u z)^2*n z i, by
  intro z h
  have hu := (HasCP.cst 1 z).div (radiusCP z h) h.ne'
  have hu' : HasCP u z (fun k => (0*rv z-1*n z k)/(rv z)^2) := by
    have eq : u = fun w => 1/rv w := by funext w; simp [u, one_div]
    rw [eq]
    exact hu
  apply hu'.congr_d
  intro k; dsimp only [u]; field_simp [h.ne'] <;> ring⟩

private lemma cpPos (z:E4) (i : Fin 4) : HasCP (fun p => pos p i) z (fun j => pmat i j) := by
  rcases four i with rfl|rfl|rfl|rfl
  · apply (HasCP.cst 0 z).congr_d
    intro j; rcases four j with rfl|rfl|rfl|rfl <;> rfl
  all_goals
    apply (hasCP_coord z _).congr_d
    intro j
    rcases four j with rfl|rfl|rfl|rfl <;> rfl

private def normal (i : Fin 4) : Atom := ⟨fun z => n z i,
  fun z j => u z*(pmat i j-n z i*n z j),by
  intro z h
  apply ((cpPos z i).mul (inverseRadius.cp z h)).congr_d
  intro j
  change pmat i j*u z + pos z i*(-(u z)^2*n z j) = u z*(pmat i j-pos z i*u z*n z j)
  ring⟩

private lemma kronecker_null (p : E4) (h : 0 < rv p) (i : Fin 4) :
    ksNull 0 p i = tvec i+n p i := by
  rcases four i with rfl|rfl|rfl|rfl <;>
    simp only [ksNull_zero,ksNull_one,ksNull_two,ksNull_three,tvec,n,pos,u,rv,v0,v1,v2,v3,
      zero_mul,add_zero,zero_add,mul_zero,sub_zero,zero_pow (by decide : 2 ≠ 0)] <;>
    field_simp [h.ne'] <;> ring

private lemma normal_unit (p : E4) (h : 0 < rv p) : n p 1^2+n p 2^2+n p 3^2=1 := by
  have hh := ks_rel 0 p h
  simpa only [kronecker_null p h,tvec,v1,v2,v3,zero_add] using hh

private lemma prof (p:E4) (h:0<rv p) : ksProfile 1 0 0 p=2*u p := by
  unfold ksProfile u
  change rv p^2*(2*1*rv p-0^2)/(rv p^4+0^2*p 3^2)=_
  field_simp [h.ne'] <;> ring

private def metricF {α : Type*} [Add α] [Mul α] (two U η : α) (N T : Fin 4 → α) (i j : Fin 4) :=
  η+two*U*(T i+N i)*(T j+N j)
private def metricAtom (i j:Fin 4) := metricF (ac 2) inverseRadius (ac (eta i j)) normal (fun i=>ac (tvec i)) i j
private def inverseF (U:ℝ) (N:Fin 4→ℝ) (i j:Fin 4) :=
  eta i j-2*U*(N i-tvec i)*(N j-tvec j)

private lemma metricEq (p:E4) (h:0<rv p) (i j:Fin 4) :
    kerrNewmanMetric 1 0 0 p i j = (metricAtom i j).val p := by
  change minkowski i j+ksProfile 1 0 0 p*ksNull 0 p i*ksNull 0 p j =
    eta i j+2*u p*(tvec i+n p i)*(tvec j+n p j)
  rw [flat,prof p h,kronecker_null p h,kronecker_null p h]

private lemma inverseEq (p:E4) (h:0<rv p) (i j:Fin 4) :
    invMetric (kerrNewmanMetric 1 0 0) p i j = inverseF (u p) (n p) i j := by
  have hn := ks_null 0 p h
  have hg : kerrNewmanMetric 1 0 0 p = Matrix.of (fun i j => minkowski i j+ksProfile 1 0 0 p*ksNull 0 p i*ksNull 0 p j) := rfl
  unfold invMetric
  rw [hg, Matrix.inv_eq_right_inv (mul_inv_KS _ _ hn)]
  have raised (l : Fin 4) : ![-ksNull 0 p 0,ksNull 0 p 1,ksNull 0 p 2,ksNull 0 p 3] l =
      n p l-tvec l := by
    rcases four l with rfl|rfl|rfl|rfl <;>
      simp only [v0,v1,v2,v3,kronecker_null p h,tvec,n,pos] <;> ring
  simp only [Matrix.of_apply,inverseF,flat,prof p h,raised]

private def gammaF {α : Type*} [Add α] [Sub α] [Mul α] (two U : α) (N T : Fin 4 → α) (P : Fin 4 → Fin 4 → α)
    (i j k:Fin 4) : α :=
  let L := N i-T i
  let B := two*P j k-two*N j*N k-N j*(T k+N k)-N k*(T j+N j)
  U*U*(L*B+(N i-two*U*L)*(T j+N j)*(T k+N k))
private def gammaAtom (i j k:Fin 4) := gammaF (ac 2) inverseRadius normal (fun i=>ac (tvec i))
  (fun i j=>ac (pmat i j)) i j k
private abbrev gam (U:ℝ) (N:Fin 4→ℝ) := gammaF 2 U N tvec pmat

private structure Jt where
  val : ℝ
  d : ℝ
private instance : Add Jt where add f g := ⟨f.val+g.val,f.d+g.d⟩
private instance : Sub Jt where sub f g := ⟨f.val-g.val,f.d-g.d⟩
private instance : Mul Jt where mul f g := ⟨f.val*g.val,f.d*g.val+f.val*g.d⟩
private def cj (c:ℝ) : Jt := ⟨c,0⟩
private def uj (U:ℝ) (N:Fin 4→ℝ) (h:Fin 4) : Jt := ⟨U,-U^2*N h⟩
private def nj (U:ℝ) (N:Fin 4→ℝ) (h i:Fin 4) : Jt := ⟨N i,U*(pmat i h-N i*N h)⟩
private def dg (U:ℝ) (N:Fin 4→ℝ) (i j h:Fin 4) :=
  (metricF (cj 2) (uj U N h) (cj (eta i j)) (nj U N h) (fun i=>cj (tvec i)) i j).d
private def dgam (U:ℝ) (N:Fin 4→ℝ) (i j k h:Fin 4) :=
  (gammaF (cj 2) (uj U N h) (nj U N h) (fun i=>cj (tvec i)) (fun i j=>cj (pmat i j)) i j k).d
private def rawConnection (U:ℝ) (N:Fin 4→ℝ) (i j k:Fin 4) :=
  (1/2:ℝ)*∑ l, inverseF U N i l*(dg U N l k j+dg U N l j k-dg U N j k l)
private def rawRicci (U:ℝ) (N:Fin 4→ℝ) (s v:Fin 4) :=
  ∑ h, (dgam U N h v s h-dgam U N h h s v+
    ∑ l, (gam U N h h l*gam U N l v s-gam U N h v l*gam U N l h s))
private lemma jaV (a b:Jt) : (a+b).val = a.val+b.val := rfl
private lemma jaD (a b:Jt) : (a+b).d = a.d+b.d := rfl
private lemma jsV (a b:Jt) : (a-b).val = a.val-b.val := rfl
private lemma jsD (a b:Jt) : (a-b).d = a.d-b.d := rfl
private lemma jmV (a b:Jt) : (a*b).val = a.val*b.val := rfl
private lemma jmD (a b:Jt) : (a*b).d = a.d*b.val+a.val*b.d := rfl

private lemma perm_basics (σ : Equiv.Perm (Fin 4)) (hσ : σ 0=0) :
    (∀ i, tvec (σ i)=tvec i) ∧ (∀ i j, pmat (σ i) (σ j)=pmat i j) ∧
      (∀ i j, eta (σ i) (σ j)=eta i j) := by
  have t0 (i:Fin 4) : tvec i=if i=0 then 1 else 0 := by fin_cases i <;> rfl
  have p0 (i j:Fin 4) : pmat i j=if i=0 then 0 else if i=j then 1 else 0 := by fin_cases i <;> fin_cases j <;> rfl
  have e0 (i j:Fin 4) : eta i j=if i=j then (if i=0 then -1 else 1) else 0 := by fin_cases i <;> fin_cases j <;> rfl
  have z (i:Fin 4) : σ i=0 ↔ i=0 := by
    calc
      (σ i=0) ↔ σ i=σ 0 := by rw [hσ]
      _ ↔ i=0 := σ.injective.eq_iff
  exact ⟨fun i => by simp only [t0,z],fun i j => by simp only [p0,z,σ.injective.eq_iff],
    fun i j => by simp only [e0,z,σ.injective.eq_iff]⟩

private lemma perm_formula (σ : Equiv.Perm (Fin 4)) (hσ : σ 0=0) (U:ℝ) (N:Fin 4→ℝ) :
    (∀ i j k, gam U (N ∘ σ) i j k=gam U N (σ i) (σ j) (σ k)) ∧
    (∀ i j k, rawConnection U (N ∘ σ) i j k=rawConnection U N (σ i) (σ j) (σ k)) ∧
    (∀ i j, rawRicci U (N ∘ σ) i j=rawRicci U N (σ i) (σ j)) := by
  obtain ⟨ht,hp,he⟩ := perm_basics σ hσ
  have iv (i j : Fin 4) : inverseF U (N ∘ σ) i j=inverseF U N (σ i) (σ j) := by
    simp only [inverseF,Function.comp_apply,ht,he]
  have d (i j k:Fin 4) : dg U (N ∘ σ) i j k=dg U N (σ i) (σ j) (σ k) := by
    simp only [dg,metricF,uj,nj,Function.comp_apply,hp,he,ht]
  have g (i j k:Fin 4) : gam U (N ∘ σ) i j k=gam U N (σ i) (σ j) (σ k) := by
    simp only [gam,gammaF,Function.comp_apply,hp,ht]
  have dg' (i j k l:Fin 4) : dgam U (N ∘ σ) i j k l=dgam U N (σ i) (σ j) (σ k) (σ l) := by
    simp only [dgam,gammaF,uj,nj,Function.comp_apply,hp,he,ht]
  refine ⟨g,?_,?_⟩
  · intro i j k
    simp only [rawConnection,iv,d]
    congr 1
    exact Equiv.sum_comp σ (fun l => inverseF U N (σ i) l * (dg U N l (σ k) (σ j)+dg U N l (σ j) (σ k)-dg U N (σ j) (σ k) l))
  · intro i j
    simp only [rawRicci,dg',g]
    have inner (h:Fin 4) := Equiv.sum_comp σ
      (fun l => gam U N h h l * gam U N l (σ j) (σ i) - gam U N h (σ j) l * gam U N l h (σ i))
    simp only [inner]
    exact Equiv.sum_comp σ (fun h => dgam U N h (σ j) (σ i) h - dgam U N h h (σ i) (σ j) +
      ∑ l, (gam U N h h l*gam U N l (σ j) (σ i)-gam U N h (σ j) l*gam U N l h (σ i)))

private def sp132 : Equiv.Perm (Fin 4) where
  toFun := ![0,1,3,2]
  invFun := ![0,1,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp132_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp132)=![0,X,Z,Y] := by
  funext i
  fin_cases i <;> rfl
private def sp213 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp213_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp213)=![0,Y,X,Z] := by
  funext i
  fin_cases i <;> rfl
private def sp231 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp231_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp231)=![0,Y,Z,X] := by
  funext i
  fin_cases i <;> rfl
private def sp312 : Equiv.Perm (Fin 4) where
  toFun := ![0,3,1,2]
  invFun := ![0,2,3,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp312_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp312)=![0,Z,X,Y] := by
  funext i
  fin_cases i <;> rfl
private def sp321 : Equiv.Perm (Fin 4) where
  toFun := ![0,3,2,1]
  invFun := ![0,3,2,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp321_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp321)=![0,Z,Y,X] := by
  funext i
  fin_cases i <;> rfl
private lemma conn_sym (U:ℝ) (N:Fin 4 → ℝ) (i j k:Fin 4) : rawConnection U N i j k=rawConnection U N i k j := by
  have d (k j l: Fin 4) : dg U N j k l = dg U N k j l := by
    simp only [dg,metricF,jmV,jmD,jaV,jaD,cj,nj,uj]; ring
  dsimp only [rawConnection]
  congr 1
  apply Finset.sum_congr rfl; intro l _
  rw [d j k l, add_comm (dg U N l k j)]
private lemma gam_sym (U:ℝ) (N:Fin 4 → ℝ) (i j k:Fin 4) : gam U N i j k = gam U N i k j := by
  have e : pmat j k=pmat k j := by rcases four j with rfl|rfl|rfl|rfl <;> rcases four k with rfl|rfl|rfl|rfl <;> rfl
  dsimp only [gam,gammaF]; rw [e]; ring

set_option maxHeartbeats 1400000 in
private lemma conn_000 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 0 0=gam U ![0,X,Y,Z] 0 0 0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^3)*h

set_option maxHeartbeats 1400000 in
private lemma conn_001 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 0 1=gam U ![0,X,Y,Z] 0 0 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (0)*h

set_option maxHeartbeats 1400000 in
private lemma conn_011 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 1 1=gam U ![0,X,Y,Z] 0 1 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-2*U^3*(3*X^2 - 2))*h

set_option maxHeartbeats 1400000 in
private lemma conn_012 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 1 2=gam U ![0,X,Y,Z] 0 1 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-6*U^3*X*Y)*h

set_option maxHeartbeats 1400000 in
private lemma conn_100 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 0 0=gam U ![0,X,Y,Z] 1 0 0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-2*U^3*X)*h

set_option maxHeartbeats 1400000 in
private lemma conn_101 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 0 1=gam U ![0,X,Y,Z] 1 0 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (0)*h

set_option maxHeartbeats 1400000 in
private lemma conn_102 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 0 2=gam U ![0,X,Y,Z] 1 0 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (0)*h

set_option maxHeartbeats 1400000 in
private lemma conn_111 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 1 1=gam U ![0,X,Y,Z] 1 1 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^3*X*(3*X^2 - 2))*h

set_option maxHeartbeats 1400000 in
private lemma conn_112 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 1 2=gam U ![0,X,Y,Z] 1 1 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (6*U^3*X^2*Y)*h

set_option maxHeartbeats 1400000 in
private lemma conn_122 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 2 2=gam U ![0,X,Y,Z] 1 2 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^3*X*(3*Y^2 - 2))*h

set_option maxHeartbeats 1400000 in
private lemma conn_123 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 2 3=gam U ![0,X,Y,Z] 1 2 3 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (6*U^3*X*Y*Z)*h

private lemma conn_cert (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) (i j k:Fin 4) :
    rawConnection U ![0,X,Y,Z] i j k=gam U ![0,X,Y,Z] i j k := by
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> rcases four k with rfl|rfl|rfl|rfl
  · exact conn_000 U X Y Z h
  · exact conn_001 U X Y Z h
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_001 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_001 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    exact conn_001 U X Y Z h
  · exact conn_011 U X Y Z h
  · exact conn_012 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_012 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_001 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_012 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_011 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 1 1).symm.trans (z.trans (H.1 0 1 1))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_012 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_001 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_012 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_012 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_011 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 1 1).symm.trans (z.trans (H.1 0 1 1))
  · exact conn_100 U X Y Z h
  · exact conn_101 U X Y Z h
  · exact conn_102 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_102 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    exact conn_101 U X Y Z h
  · exact conn_111 U X Y Z h
  · exact conn_112 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_112 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    exact conn_102 U X Y Z h
  · rw [conn_sym _ _ _ 2 1,gam_sym _ _ _ 2 1]
    exact conn_112 U X Y Z h
  · exact conn_122 U X Y Z h
  · exact conn_123 U X Y Z h
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_102 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · rw [conn_sym _ _ _ 3 1,gam_sym _ _ _ 3 1]
    have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_112 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_123 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_122 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_100 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 0).symm.trans (z.trans (H.1 1 0 0))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_101 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_122 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · rw [conn_sym _ _ _ 1 2,gam_sym _ _ _ 1 2]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_123 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_101 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_111 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 1 1).symm.trans (z.trans (H.1 1 1 1))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_123 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · rw [conn_sym _ _ _ 3 2,gam_sym _ _ _ 3 2]
    have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_122 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_100 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 0).symm.trans (z.trans (H.1 1 0 0))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_101 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_122 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_123 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · rw [conn_sym _ _ _ 1 3,gam_sym _ _ _ 1 3]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_123 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_122 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · rw [conn_sym _ _ _ 2 3,gam_sym _ _ _ 2 3]
    have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_101 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_111 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 1 1).symm.trans (z.trans (H.1 1 1 1))
set_option maxHeartbeats 1400000 in
private lemma ric_00 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 0 0=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (U^3*(4*U^2*X^2 + 4*U^2*Y^2 + 4*U^2*Z^2 - 3*U*X^2 - 3*U*Y^2 - 3*U*Z^2 + 6*U - 3))*h

set_option maxHeartbeats 1400000 in
private lemma ric_01 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 0 1=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (4*U^4*X*(U - 1))*h

set_option maxHeartbeats 1400000 in
private lemma ric_10 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 1 0=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^4*X*(2*U + 3))*h

set_option maxHeartbeats 1400000 in
private lemma ric_11 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 1 1=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-U^3*(4*U^2*Y^2 + 4*U^2*Z^2 - 4*U^2 + 3*U*X^2 + 6*U*Y^2 + 6*U*Z^2 - 2*U + 3))*h

set_option maxHeartbeats 1400000 in
private lemma ric_12 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 1 2=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (U^4*X*Y*(4*U + 3))*h

private lemma ric_cert (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) (i j:Fin 4) :
    rawRicci U ![0,X,Y,Z] i j=0 := by
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl
  · exact ric_00 U X Y Z h
  · exact ric_01 U X Y Z h
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_01 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 0 1).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_01 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 0 1).symm.trans z
  · exact ric_10 U X Y Z h
  · exact ric_11 U X Y Z h
  · exact ric_12 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := ric_12 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_10 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 1 0).symm.trans z
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_12 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_11 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 1 1).symm.trans z
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := ric_12 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_10 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 1 0).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_12 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := ric_12 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_11 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 1 1).symm.trans z

private lemma norm_vec (p : E4) : n p = ![0,n p 1,n p 2,n p 3] := by
  funext i
  rcases four i with rfl|rfl|rfl|rfl
  · change 0*u p=0; ring
  all_goals rfl

private lemma metricPartial (p : E4) (hp : 0 < rv p) (i j k : Fin 4) :
    coordPartial (fun z => kerrNewmanMetric 1 0 0 z i j) k p = dg (u p) (n p) i j k := by
  have ev : ∀ᶠ z in 𝓝 p, 0 < rv z :=
    (isOpen_lt continuous_const (continuous_ksRadius 0)).mem_nhds hp
  have hg : (fun z => kerrNewmanMetric 1 0 0 z i j) =ᶠ[𝓝 p] (metricAtom i j).val :=
    ev.mono (fun z hz => metricEq z hz i j)
  unfold coordPartial
  rw [hg.fderiv_eq]
  exact ((metricAtom i j).cp p hp).eq k

private lemma connection (p : E4) (hp : 0 < rv p) (i j k:Fin 4) :
    christoffel (kerrNewmanMetric 1 0 0) p i j k = gam (u p) (n p) i j k := by
  calc
    _ = rawConnection (u p) (n p) i j k := by
      simp only [christoffel,rawConnection,inverseEq p hp,metricPartial p hp,Finset.mul_sum,mul_assoc]
    _ = _ := by
      have C := conn_cert (u p) _ _ _ (normal_unit p hp) i j k
      simpa only [← norm_vec p] using C

private lemma connPartial (p : E4) (hp : 0 < rv p) (i j k l : Fin 4) :
    coordPartial (fun z => christoffel (kerrNewmanMetric 1 0 0) z i j k) l p = dgam (u p) (n p) i j k l := by
  have ev : ∀ᶠ z in 𝓝 p, 0 < rv z :=
    (isOpen_lt continuous_const (continuous_ksRadius 0)).mem_nhds hp
  have hg : (fun z => christoffel (kerrNewmanMetric 1 0 0) z i j k) =ᶠ[𝓝 p] (gammaAtom i j k).val :=
    ev.mono (fun z hz => connection z hz i j k)
  unfold coordPartial
  rw [hg.fderiv_eq]
  exact ((gammaAtom i j k).cp p hp).eq l

theorem _root_.NoHair.schwarzschild_unit_cartesian_ricci_zero (p : E4) (hp : 0 < ksRadius 0 p) (i j : Fin 4) :
    ricci (kerrNewmanMetric 1 0 0) p i j=0 := by
  calc
    _ = rawRicci (u p) (n p) i j := by simp only [ricci,riemann,connPartial p hp,connection p hp,rawRicci]
    _ = _ := by
      have C := ric_cert (u p) _ _ _ (normal_unit p hp) i j
      simpa only [← norm_vec p] using C
end
end IsraelBundle.NoHair_schwarzschild_unit_cartesian_ricci_zero

/- Prove2Me theorem NoHair.isElectrovac_of_coordinate_equations (89c7e4da-033b-40c9-93e9-ecf4428a5a45). -/
namespace IsraelBundle.NoHair_isElectrovac_of_coordinate_equations
open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

private theorem partial_eq_on_open {s : Set E4} (hs : IsOpen s) {f g : E4 → ℝ}
    (h : EqOn f g s) (k : Fin 4) {z : E4} (hz : z ∈ s) :
    coordPartial f k z = coordPartial g k z :=
  congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis k))
    (h.eventuallyEq_of_mem (hs.mem_nhds hz)).fderiv_eq

private theorem einsteinMaxwell_of_eqOn {s : Set E4} (hs : IsOpen s)
    {G' G F' F : E4 → Matrix (Fin 4) (Fin 4) ℝ}
    (hG : EqOn G' G s) (hF : EqOn F' F s) {y : E4} (hy : y ∈ s)
    (hem : EinsteinMaxwellAt G F y) : EinsteinMaxwellAt G' F' y := by
  have dG (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => G' w i j) k z = coordPartial (fun w => G w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hG hw)) k hz
  have dF (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => F' w i j) k z = coordPartial (fun w => F w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hF hw)) k hz
  have chr (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      christoffel G' z i j k = christoffel G z i j k := by
    simp only [christoffel, invMetric, hG hz, dG z hz]
  have dChr (z : E4) (hz : z ∈ s) (i j k l : Fin 4) :
      coordPartial (fun w => christoffel G' w i j k) l z =
      coordPartial (fun w => christoffel G w i j k) l z :=
    partial_eq_on_open hs (fun w hw => chr w hw i j k) l hz
  have ric (i j : Fin 4) : ricci G' y i j = ricci G y i j := by
    simp only [ricci, riemann, dChr y hy, chr y hy]
  have flux (i j : Fin 4) :
      coordPartial (fun z => Real.sqrt |(G' z).det| * raiseBoth G' F' z i j) i y =
      coordPartial (fun z => Real.sqrt |(G z).det| * raiseBoth G F z i j) i y := by
    apply partial_eq_on_open hs _ i hy
    intro z hz
    simp only [raiseBoth, invMetric, hG hz, hF hz]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simpa only [einsteinTensor, scalarCurvature, maxwellSource, raiseBoth, invMetric,
      hG hy, hF hy, ric] using hem.1 i j
  · intro j
    simpa only [flux] using hem.2.1 j
  · intro i j k
    simpa only [dF y hy] using hem.2.2 i j k

theorem _root_.NoHair.isElectrovac_of_coordinate_equations (U : TopologicalSpace.Opens E4) (G F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, EinsteinMaxwellAt G F y) :
    IsElectrovac (M := U) (fun x => matrixBilin (G x.val)) (fun x => matrixBilin (F x.val)) := by
  intro c hc y hy
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : U) : c = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ c.target) : (c.symm z).val = z := by
    have eqval (x : U) : c x = x.val := by rw [hchart x] <;> rfl
    exact (eqval (c.symm z)).symm.trans (c.right_inv hz)
  have derivAt (x : U) :
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) c.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    rw [hchart x]
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E4)) (x := x)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
    exact hd
  have coeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) :
      EqOn (pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm) A c.target := by
    intro z hz
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    funext i j
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz]
    change Matrix.toLinearMap₂' ℝ (A z) (WithLp.ofLp (coordBasis i))
      (WithLp.ofLp (coordBasis j)) = A z i j
    simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
    rw [Matrix.toLinearMap₂'_apply]
    simp_rw [← Finset.smul_sum]
    simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  apply einsteinMaxwell_of_eqOn c.open_target (coeff G) (coeff F) hy
  apply h
  rw [← hval y hy]
  exact (c.symm y).property
end IsraelBundle.NoHair_isElectrovac_of_coordinate_equations

/- Prove2Me theorem NoHair.ksRadius_superlevel_frontier (31c42fe2-1d74-4c32-8e59-050876e4749c). -/
namespace IsraelBundle.NoHair_ksRadius_superlevel_frontier
open NoHair Set Metric
open scoped Topology

private abbrev Space3 := EuclideanSpace ℝ (Fin 3)

private noncomputable def ellipsoidChart (d b : ℝ) (hd : d ≠ 0) (hb : b ≠ 0) : E4 ≃ₜ ℝ × Space3 where
  toFun x := (x 0, WithLp.toLp 2 ![x 1 / d, x 2 / d, x 3 / b])
  invFun q := WithLp.toLp 2 ![q.1, q.2 0 * d, q.2 1 * d, q.2 2 * b]
  left_inv x := by
    ext i
    fin_cases i <;> simp [PiLp.toLp_apply, hd, hb]
  right_inv q := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> simp [PiLp.toLp_apply, hd, hb]
  continuous_toFun := by
    apply Continuous.prodMk
    · fun_prop
    · apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

private theorem ellipsoid_compare (a b : ℝ) (hb : 0 < b) (x : E4)
    (d : ℝ) (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 + a ^ 2) :
    let w := (ellipsoidChart d b hd.ne' hb.ne' x).2
    (b < ksRadius a x ↔ 1 < ‖w‖) ∧ (ksRadius a x = b ↔ ‖w‖ = 1) := by
  let w := (ellipsoidChart d b hd.ne' hb.ne' x).2
  let c := x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 - a ^ 2
  let s := Real.sqrt (c ^ 2 + 4 * a ^ 2 * x 3 ^ 2)
  have hs2 : s ^ 2 = c ^ 2 + 4 * a ^ 2 * x 3 ^ 2 := Real.sq_sqrt (by positivity)
  have habs : |c| ≤ s := calc
    |c| = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ ≤ s := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (a * x 3)])
  have hp : 0 ≤ (c + s) / 2 := by linarith [neg_abs_le c]
  have hr2 : ksRadius a x ^ 2 = (c + s) / 2 := Real.sq_sqrt hp
  have hneg : (c - s) / 2 ≤ 0 := by linarith [le_abs_self c]
  have hr : 0 ≤ ksRadius a x := Real.sqrt_nonneg _
  have hn : ‖w‖ ^ 2 = (x 1 / d) ^ 2 + (x 2 / d) ^ 2 + (x 3 / b) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rfl
  have hid : (‖w‖ ^ 2 - 1) * (b ^ 2 * d ^ 2) =
      (ksRadius a x ^ 2 - b ^ 2) * (b ^ 2 - (c - s) / 2) := calc
    _ = (x 1 ^ 2 + x 2 ^ 2) * b ^ 2 + x 3 ^ 2 * d ^ 2 - b ^ 2 * d ^ 2 := by
      rw [hn]
      field_simp [hd.ne', hb.ne'] <;> ring
    _ = _ := by
      rw [hr2, hd2]
      dsimp only [c] at hs2 ⊢
      nlinarith only [hs2]
  have hsign : (‖w‖ - 1) * ((‖w‖ + 1) * (b ^ 2 * d ^ 2)) =
      (ksRadius a x - b) * ((ksRadius a x + b) * (b ^ 2 - (c - s) / 2)) := by
    linear_combination hid
  have hleft : 0 < (‖w‖ + 1) * (b ^ 2 * d ^ 2) := by positivity
  have hgap : 0 < b ^ 2 - (c - s) / 2 := sub_pos.mpr (hneg.trans_lt (sq_pos_of_pos hb))
  have hright : 0 < (ksRadius a x + b) * (b ^ 2 - (c - s) / 2) :=
    mul_pos (add_pos_of_nonneg_of_pos hr hb) hgap
  change (b < ksRadius a x ↔ 1 < ‖w‖) ∧ (ksRadius a x = b ↔ ‖w‖ = 1)
  constructor
  · have h := congrArg (fun v : ℝ => 0 < v) hsign
    simpa only [mul_pos_iff_of_pos_right hleft, mul_pos_iff_of_pos_right hright, sub_pos] using
      (Iff.of_eq h).symm
  · have h := congrArg (fun v : ℝ => v = 0) hsign
    simpa only [mul_eq_zero, hleft.ne', hright.ne', or_false, sub_eq_zero] using (Iff.of_eq h).symm

theorem _root_.NoHair.ksRadius_superlevel_frontier (a b : ℝ) (hb : 0 < b) :
    frontier {x : kerrNewmanSpacetime a | b < ksRadius a x.val} =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = b} ∧
      IsConnected {x : kerrNewmanSpacetime a | ksRadius a x.val = b} := by
  let d := Real.sqrt (b ^ 2 + a ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = b ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  let H := ellipsoidChart d b hd.ne' hb.ne'
  let P : E4 → Space3 := fun x => (H x).2
  let V : Set E4 := {y | b < ksRadius a y}
  let L : Set E4 := {y | ksRadius a y = b}
  have hout : V = P ⁻¹' (closedBall (0 : Space3) 1)ᶜ := by
    ext y
    simpa [V, P, H, Metric.mem_closedBall, dist_zero_right] using (ellipsoid_compare a b hb y d hd hd2).1
  have hlevel : L = P ⁻¹' sphere (0 : Space3) 1 := by
    ext y
    simpa [L, P, H, Metric.mem_sphere, dist_zero_right] using (ellipsoid_compare a b hb y d hd hd2).2
  have op : IsOpenMap P := isOpenMap_snd.comp H.isOpenMap
  have co : Continuous P := continuous_snd.comp H.continuous
  have hfront : frontier V = L := by
    rw [hout, ← op.preimage_frontier_eq_frontier_preimage co, frontier_compl,
      frontier_closedBall (0 : Space3) one_ne_zero, hlevel]
  have hsph : IsConnected (sphere (0 : Space3) 1) := by
    apply isConnected_sphere _ _ zero_le_one
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [finrank_euclideanSpace_fin]
    decide
  have hconn : IsConnected L := by
    have hp : IsConnected ((univ : Set ℝ) ×ˢ sphere (0 : Space3) 1) := isConnected_univ.prod hsph
    have he : P ⁻¹' sphere (0 : Space3) 1 = H ⁻¹' ((univ : Set ℝ) ×ˢ sphere (0 : Space3) 1) := by
      ext x
      simp [P]
    rw [hlevel, he]
    exact H.isConnected_preimage.mpr hp
  let U := kerrNewmanSpacetime a
  have hop : IsOpenMap (Subtype.val : U → E4) := U.isOpen.isOpenMap_subtype_val
  change frontier ((Subtype.val : U → E4) ⁻¹' V) = Subtype.val ⁻¹' L ∧ IsConnected ((Subtype.val : U → E4) ⁻¹' L)
  constructor
  · rw [← hop.preimage_frontier_eq_frontier_preimage continuous_subtype_val, hfront]
  · have him : (Subtype.val : U → E4) '' (Subtype.val ⁻¹' L) = L := by
      apply image_preimage_eq_of_subset
      intro y hy
      exact ⟨⟨y, show 0 < ksRadius a y from (show ksRadius a y = b from hy) ▸ hb⟩, rfl⟩
    have hc : IsConnected ((Subtype.val : U → E4) '' (Subtype.val ⁻¹' L)) := him.symm ▸ hconn
    exact ⟨hc.nonempty.of_image, Topology.IsInducing.subtypeVal.isPreconnected_image.mp hc.isPreconnected⟩
end IsraelBundle.NoHair_ksRadius_superlevel_frontier

namespace CircularOrbit
open NoHair NoHair.KNE Set
open scoped ContDiff Manifold BigOperators

noncomputable section

private def four (t x y z : ℝ) : E4 := WithLp.toLp 2 ![t,x,y,z]
private def oblate (a r t X Y Z : ℝ) := four t (r*X-a*Y) (a*X+r*Y) (r*Z)

private theorem oblate_data (a r t X Y Z : ℝ) (hr : 0 < r) (hk : X^2+Y^2+Z^2=1) :
    let y := oblate a r t X Y Z
    ksRadius a y = r ∧ ksNull a y = ![1,X,Y,Z] ∧ r  ≤  spatialRadius y := by
  let ρ2 := (r*X-a*Y)^2+(a*X+r*Y)^2+(r*Z)^2
  have hρ : ρ2 = r^2+a^2*(1-Z^2) := by
    dsimp [ρ2]; linear_combination (r^2+a^2)*hk
  have hs : 0  ≤  r^2+a^2*Z^2 := by positivity
  have hc : ρ2-a^2 = r^2-a^2*Z^2 := by rw [hρ]; ring
  have hD : (ρ2-a^2)^2+4*a^2*(r*Z)^2 = (r^2+a^2*Z^2)^2 := by rw [hc]; ring
  have hrad : ksRadius a (oblate a r t X Y Z) = r := by
    change Real.sqrt ((ρ2-a^2+Real.sqrt ((ρ2-a^2)^2+4*a^2*(r*Z)^2))/2)=r
    rw [hD, Real.sqrt_sq hs, hc]
    convert Real.sqrt_sq hr.le using 2 <;> ring
  refine ⟨hrad, ?_, ?_⟩
  · unfold ksNull
    rw [hrad]
    have hden : r^2+a^2  ≠  0 := by positivity
    funext i
    fin_cases i <;> simp [four,oblate, hden, hr.ne'] <;> field_simp [hden,hr.ne'] <;> ring
  · change r  ≤  Real.sqrt ρ2
    have hxy : 0  ≤  1-Z^2 := by nlinarith only [hk,sq_nonneg X,sq_nonneg Y]
    apply Real.le_sqrt_of_sq_le
    rw [hρ]; linarith [mul_nonneg (sq_nonneg a) hxy]

private theorem four_deriv {t x y z : ℝ → ℝ} {dt dx dy dz s : ℝ}
    (ht : HasDerivAt t dt s) (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) (hz : HasDerivAt z dz s) :
    HasDerivAt (fun s => four (t s) (x s) (y s) (z s)) (four dt dx dy dz) s := by
  have h : HasDerivAt (fun s => (![t s,x s,y s,z s] : Fin 4 → ℝ)) ![dt,dx,dy,dz] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ht
    · exact hx
    · exact hy
    · exact hz
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s h

private theorem orbit_energy (m a e R c X Y τ : ℝ) (hR : 0 < R) (hu : X^2+Y^2+c^2=1) :
    let z:=oblate a R τ X Y c
    let b:=R^2+a^2
    let Q:=R^2+a^2*c^2
    let v:=four b (-a*(a*X+R*Y)) (a*(R*X-a*Y)) 0
    matrixBilin (kerrNewmanMetric m a e z) v v = -(Q*(b-2*m*R+e^2)) := by
  let z:=oblate a R τ X Y c
  let b:=R^2+a^2
  let Q:=R^2+a^2*c^2
  let v:=four b (-a*(a*X+R*Y)) (a*(R*X-a*Y)) 0
  obtain ⟨hr,hk,_⟩:=oblate_data a R τ X Y c hR hu
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hF : ksProfile m a e z * Q = 2*m*R-e^2 := by
    unfold ksProfile
    change (ksRadius a z)^2*(2*m*ksRadius a z-e^2)/((ksRadius a z)^4+a^2*(R*c)^2)*Q=_
    change ksRadius a z = R at hr
    rw [hr, show R^4+a^2*(R*c)^2=R^2*Q by dsimp [Q]; ring]
    field_simp [hR.ne',hQ.ne'] <;> ring
  have hk' : v 0+X*v 1+Y*v 2+c*v 3=Q := by
    change (R^2+a^2)+X*(-a*(a*X+R*Y))+Y*(a*(R*X-a*Y))+c*0=R^2+a^2*c^2
    linear_combination -a^2*hu
  have hflat : -(v 0*v 0)+v 1*v 1+v 2*v 2+v 3*v 3 = -b*Q := by
    change -((R^2+a^2)*(R^2+a^2))+(-a*(a*X+R*Y))*(-a*(a*X+R*Y))+
      (a*(R*X-a*Y))*(a*(R*X-a*Y))+0*0= -(R^2+a^2)*(R^2+a^2*c^2)
    linear_combination (a^2*(R^2+a^2))*hu
  have matrix_form : matrixBilin (kerrNewmanMetric m a e z) v v =
      -(v 0*v 0)+v 1*v 1+v 2*v 2+v 3*v 3+
      ksProfile m a e z*(v 0+X*v 1+Y*v 2+c*v 3)*(v 0+X*v 1+Y*v 2+c*v 3) := by
    change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e z) (WithLp.ofLp v) (WithLp.ofLp v)=_
    change ksNull a z = ![1,X,Y,c] at hk
    simp only [Matrix.toLinearMap₂'_apply,smul_eq_mul,kerrNewmanMetric,hk,Fin.sum_univ_four]
    simp [minkowski] <;> ring
  change matrixBilin (kerrNewmanMetric m a e z) v v = -(Q*(b-2*m*R+e^2))
  rw [matrix_form,hflat,hk',hF]
  ring

theorem orbit_exists (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (y : E4)
    (hy : y∈kerrNewmanDOC m a e) :
    ∃ (c : ℝ) (γ v : ℝ → E4), 0 < c ∧ γ 0 = y ∧
      ∀ s : ℝ, γ s ∈ kerrNewmanDOC m a e ∧ HasDerivAt γ (v s) s ∧
        matrixBilin (kerrNewmanMetric m a e (γ s)) (v s) (v s) = -c := by
  let R:=ksRadius a y
  let X₀:=ksNull a y 1
  let Y₀:=ksNull a y 2
  let c:=ksNull a y 3
  let b:=R^2+a^2
  let Q:=R^2+a^2*c^2
  have hlarge : m+Real.sqrt (m^2-a^2-e^2) < R := by simpa [kerrNewmanDOC,kerrNewmanOuterRadius,R] using hy
  have hR : 0 < R := by linarith [hp.1,Real.sqrt_nonneg (m^2-a^2-e^2)]
  have hδ : 0 < b-2*m*R+e^2 := by
    have hs := Real.sq_sqrt (show 0 ≤ m^2-a^2-e^2 by nlinarith only [hp.2])
    have hprod := mul_pos (show 0 < R-m-Real.sqrt (m^2-a^2-e^2) by linarith)
      (show 0 < R-m+Real.sqrt (m^2-a^2-e^2) by linarith [Real.sqrt_nonneg (m^2-a^2-e^2)])
    dsimp [b]; nlinarith only [hs,hprod]
  let X := fun s : ℝ => X₀*Real.cos (a*s)-Y₀*Real.sin (a*s)
  let Y := fun s : ℝ => X₀*Real.sin (a*s)+Y₀*Real.cos (a*s)
  let t := fun s : ℝ => y 0+b*s
  let γ := fun s => oblate a R (t s) (X s) (Y s) c
  let v := fun s => four b (-a*(a*X s+R*Y s)) (a*(R*X s-a*Y s)) 0
  have hf (s : ℝ) : (X s)^2+(Y s)^2+c^2=1 := by
    have h:=ks_rel a y hR
    change X₀^2+Y₀^2+c^2=1 at h
    dsimp [X,Y]
    linear_combination (X₀^2+Y₀^2)*Real.sin_sq_add_cos_sq (a*s)+h
  refine ⟨Q*(b-2*m*R+e^2),γ,v,mul_pos (by dsimp [Q]; positivity) hδ,?_,?_⟩
  · have hz : γ 0=oblate a R (y 0) X₀ Y₀ c := by simp [γ,X,Y,t]
    rw [hz]
    ext i
    fin_cases i
    · rfl
    · exact (ks_x1 a y hR).symm
    · exact (ks_x2 a y hR).symm
    · exact (ks_x3 a y hR).symm
  · intro s
    have ha : HasDerivAt (fun q : ℝ => a*q) a s := by simpa using (hasDerivAt_id' s).const_mul a
    have ht : HasDerivAt t b s := by simpa [t] using ((hasDerivAt_id' s).const_mul b).const_add (y 0)
    have hx : HasDerivAt X (-a*Y s) s := by
      apply ((ha.cos.const_mul X₀).fun_sub (ha.sin.const_mul Y₀)).congr_deriv
      dsimp [Y]; ring
    have hY : HasDerivAt Y (a*X s) s := by
      apply ((ha.sin.const_mul X₀).fun_add (ha.cos.const_mul Y₀)).congr_deriv
      dsimp [X]; ring
    refine ⟨?_,?_,orbit_energy m a e R c (X s) (Y s) (t s) hR (hf s)⟩
    · change kerrNewmanOuterRadius m a e < ksRadius a (γ s)
      rw [(oblate_data a R (t s) (X s) (Y s) c hR (hf s)).1]
      exact hy
    · apply (four_deriv ht ((hx.const_mul R).fun_sub (hY.const_mul a))
        ((hx.const_mul a).fun_add (hY.const_mul R)) (hasDerivAt_const s (R*c))).congr_deriv
      change four b (R*(-a*Y s)-a*(a*X s)) (a*(-a*Y s)+R*(a*X s)) 0=_
      unfold v
      congr 1 <;> ring

end
end CircularOrbit
namespace TrappedShell

open NoHair Set Filter Topology
open scoped ContDiff Manifold BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2) = Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero, Real.sqrt_sq hp]
  congr 1
  ring

private abbrev r := ksRadius 0
private abbrev I4 := 𝓘(ℝ,E4)
private def dotS (x v : E4) := x 1*v 1+x 2*v 2+x 3*v 3
private def rd (x v : E4) := dotS x v / r x

private lemma rsq (x : E4) : r x ^ 2 = x 1^2+x 2^2+x 3^2 := by
  rw [r, radius_eq, spatialRadius, Real.sq_sqrt (by positivity)]

private lemma norm_bound (x v : E4) (hr : 0 < r x) : rd x v ^ 2 ≤ dotS v v := by
  have iden : (r x)^2 * dotS v v - dotS x v ^ 2 =
      (x 1*v 2-x 2*v 1)^2+(x 1*v 3-x 3*v 1)^2+(x 2*v 3-x 3*v 2)^2 := by
    rw [rsq]; unfold dotS; ring
  dsimp only [rd]
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith only [iden, sq_nonneg (x 1*v 2-x 2*v 1), sq_nonneg (x 1*v 3-x 3*v 1),
    sq_nonneg (x 2*v 3-x 3*v 2)]

private lemma radius_diff (x : E4) (hp : 0 < r x) : DifferentiableAt ℝ r x := by
  have q : 0 < x 1^2+x 2^2+x 3^2 := by rw [← rsq]; positivity
  change DifferentiableAt ℝ (ksRadius 0) x
  rw [show ksRadius 0 = spatialRadius from funext radius_eq]
  unfold spatialRadius
  fun_prop (disch := exact q.ne')

private lemma radius_der (x v : E4) (hp : 0 < r x) : fderiv ℝ r x v = rd x v := by
  have d := hasDerivAt_ksRadius_line 0 x v hp
  apply fderiv_eq_of_line (radius_diff x hp)
  apply d.congr_deriv
  change r x * (r x ^ 2 * (x 1 * v 1 + x 2 * v 2) + (r x ^ 2 + 0 ^ 2) * x 3 * v 3) /
    (r x ^ 4 + 0 ^ 2 * x 3 ^ 2) = rd x v
  dsimp only [rd,dotS]
  field_simp [hp.ne'] <;> ring

private lemma profile (m : ℝ) (x : E4) (hp : 0 < r x) : ksProfile m 0 0 x = 2*m/r x := by
  unfold ksProfile
  change r x^2*(2*m*r x-0^2)/(r x^4+0^2*x 3^2) = _
  field_simp [hp.ne'] <;> ring

private lemma matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

private lemma quadratic (x v : E4) (hp : 0 < r x) :
    matrixBilin (kerrNewmanMetric 1 0 0 x) v v =
      -(v 0)^2+dotS v v+(2/r x)*(v 0+rd x v)^2 := by
  have hx1 : ksNull 0 x 1 = x 1/r x := by rw [ksNull_one]; change (r x*x 1+0*x 2)/(r x^2+0^2)=_; field_simp [hp.ne'] <;> ring
  have hx2 : ksNull 0 x 2 = x 2/r x := by rw [ksNull_two]; change (r x*x 2-0*x 1)/(r x^2+0^2)=_; field_simp [hp.ne'] <;> ring
  have hx3 : ksNull 0 x 3 = x 3/r x := ksNull_three 0 x
  have flat : matrixBilin minkowski v v = -(v 0)^2+dotS v v := by
    rw [matrix_eval]
    simp [minkowski, Fin.sum_univ_four, dotS] <;> ring
  rw [← flat, matrix_eval, matrix_eval]
  simp only [kerrNewmanMetric, profile 1 x hp, mul_one, ksNull_zero, hx1, hx2, hx3, Fin.sum_univ_four,
    dotS,rd]
  ring

private lemma trapped (x v : E4) (hp : 0 < r x) (hr : r x ≤ 3/2) {c : ℝ} (hc : 0 < c)
    (hv : matrixBilin (kerrNewmanMetric 1 0 0 x) v v = -c) : c/3 ≤ rd x v ^ 2 := by
  let B := 2/r x-1
  have hB : 1/3 ≤ B := by
    change 1/3 ≤ 2/r x-1
    have hl : 4/3 ≤ 2/r x := (le_div_iff₀ hp).mpr (by linarith)
    linarith
  rw [quadratic x v hp] at hv
  have hcompl : B*(-c)+rd x v^2 =
      B*(dotS v v-rd x v^2)+(B*v 0+(B+1)*rd x v)^2 := by
    rw [← hv]; dsimp only [B]; ring
  nlinarith only [hcompl, mul_nonneg (show 0 ≤ B by linarith) (sub_nonneg.mpr (norm_bound x v hp)),
    sq_nonneg (B*v 0+(B+1)*rd x v), mul_le_mul_of_nonneg_right hB hc.le]

private lemma bounded_radius {f d : ℝ → ℝ} (c : ℝ) (hc : 0 < c)
    (h : ∀ t, 1 < f t) (h0 : f 0 = 3/2) (hd : ∀ t, HasDerivAt f (d t) t)
    (htr : ∀ t, f t ≤ 3/2 → c/3 ≤ d t^2) : False := by
  let e := c/12
  have he : 0 < e := by dsimp only [e]; positivity
  let P := fun t : ℝ => f t+e*t^2
  have diff (t : ℝ) : HasDerivAt P (d t+2*e*t) t := by
    apply ((hd t).add (((hasDerivAt_id' t).fun_pow 2).const_mul e)).congr_deriv
    ring
  let L := 1+1/e
  have hL : 0 < L := by dsimp only [L]; positivity
  have hel : 1 ≤ e*L^2 := by
    have hi : e*(1/e)=1 := by field_simp
    have hh : e*(1/e)^2 ≥ 0 := by positivity
    dsimp only [L]
    nlinarith only [hi, he, hh]
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (-L) L).Nonempty from ⟨0, by constructor <;> linarith⟩)
      (show Continuous P from continuous_iff_continuousAt.mpr (fun t => (diff t).continuousAt)).continuousOn
  have hP : f t+e*t^2 ≤ 3/2 := by
    have hm := hmin (show (0:ℝ) ∈ Icc (-L) L by constructor <;> linarith)
    change f t+e*t^2 ≤ f 0+e*0^2 at hm
    simpa only [P, h0, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hm
  have hlt₁ : -L < t := ht.1.lt_of_ne (by
    intro eq; rw [← eq] at hP; nlinarith only [hP, h (-L),hel])
  have hlt₂ : t < L := ht.2.lt_of_ne (by
    intro eq; rw [eq] at hP; linarith only [hP, h L,hel])
  have hz := (hmin.isLocalMin (Icc_mem_nhds hlt₁ hlt₂)).hasDerivAt_eq_zero (diff t)
  have htR : f t ≤ 3/2 := by linarith only [hP,mul_nonneg he.le (sq_nonneg t)]
  have hsmall : e*t^2 ≤ 1/2 := by linarith only [h t,hP]
  have ds : d t = -(2*e*t) := by linarith only [hz]
  have hard := htr t htR
  rw [ds] at hard
  have hmul := mul_le_mul_of_nonneg_left hsmall he.le
  change c/3 ≤ (-(2*e*t))^2 at hard
  have hc' : c = 12*e := by dsimp only [e]; ring
  rw [hc'] at hard
  nlinarith only [hard, hmul, he]

private lemma expand_coord (w : E4) : ∑ i, w i • coordBasis i = w := by
  apply WithLp.ofLp_injective 2
  funext j
  change (∑ i, w i • coordBasis i) j = w j
  simp [coordBasis, Pi.single_apply, mul_ite]

private lemma pullback_quadratic {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    (B : BilinField M) (ψ : E4 → M) (x w : E4) :
    matrixBilin (pullbackCoeffs B ψ x) w w =
      B (ψ x) (mfderiv I4 I4 ψ x w) (mfderiv I4 I4 ψ x w) := by
  let L : E4 →L[ℝ] E4 := mfderiv I4 I4 ψ x
  let G : E4 →L[ℝ] E4 →L[ℝ] ℝ := B (ψ x)
  rw [matrix_eval]
  change (∑ i, ∑ j, w i*(w j*(G (L (coordBasis i)) (L (coordBasis j)))))=G (L w) (L w)
  have he : L w=∑ i, w i • L (coordBasis i) := calc
    L w=L (∑ i, w i • coordBasis i) := congrArg L (expand_coord w).symm
    _ = _ := by simp
  rw [he]
  simp only [map_add,map_sum,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    Finset.mul_sum,Fin.sum_univ_four]
  ring

theorem no_kerrNewman (m a e : ℝ) (hm : IsKerrNewmanBlackHoleParams m a e) :
    ¬ IsKerrNewmanDOC (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0)
      ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) m a e := by
  rintro ⟨_,ψ,⟨χ,hmap,hinv,_,hrinv,hs,_⟩,hcoeff⟩
  let U := kerrNewmanSpacetime 0
  let z : E4 := WithLp.toLp 2 ![0,3/2,0,0]
  have rz : r z = 3/2 := by
    rw [r,radius_eq]; change Real.sqrt ((3/2)^2+0^2+0^2) = _
    rw [show (3/2:ℝ)^2+0^2+0^2=(3/2)^2 by ring,Real.sqrt_sq (by norm_num)]
  let p : U := ⟨z, by change 0 < r z; rw [rz]; norm_num⟩
  have hp : p ∈ (Subtype.val : U → E4) ⁻¹' exteriorRegion 1 := by
    change 1 < spatialRadius z; rw [← radius_eq, ← show r z = ksRadius 0 z from rfl, rz]; norm_num
  let y := χ p
  have hy := hinv hp
  have hψy : ψ y = p := hrinv hp
  obtain ⟨c,ℓ,v,hc,h0,horb⟩ := CircularOrbit.orbit_exists m a e hm y hy
  have line (t : ℝ) := (horb t).2.1
  have linemem (t : ℝ) := (horb t).1
  have hopen : IsOpen (kerrNewmanDOC m a e) := isOpen_lt continuous_const (continuous_ksRadius a)
  let X := fun t : ℝ => (ψ (ℓ t)).val
  let V := fun t : ℝ => (show E4 from mfderiv I4 I4 ψ (ℓ t) (v t))
  have dX (t : ℝ) : HasDerivAt X (V t) t := by
    let P := (Subtype.val : U → E4) ∘ ψ
    have dψ := ((hs (ℓ t) (linemem t)).contMDiffAt (hopen.mem_nhds (linemem t))).mdifferentiableAt (by simp)
    have dv : MDifferentiableAt I4 I4 (Subtype.val : U → E4) (ψ (ℓ t)) :=
      (contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp)
    have dP : DifferentiableAt ℝ P (ℓ t) := mdifferentiableAt_iff_differentiableAt.mp (dv.comp (ℓ t) dψ)
    have dvId : (mfderiv I4 I4 (Subtype.val : U → E4) (ψ (ℓ t)) : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
      mfderiv_extChartAt_self (I := I4) (x := ψ (ℓ t))
    have jP : fderiv ℝ P (ℓ t) = (mfderiv I4 I4 ψ (ℓ t) : E4 →L[ℝ] E4) := by
      have hh := mfderiv_comp (I' := I4) (ℓ t) dv dψ
      rw [dvId, mfderiv_eq_fderiv] at hh
      exact hh
    exact (dP.hasFDerivAt.comp_hasDerivAt t (line t)).congr_deriv (by rw [jP]; rfl)
  have rangeX (t : ℝ) : 1 < r (X t) := by
    rw [r,radius_eq]; exact hmap (linemem t)
  have smoothr (t : ℝ) : HasDerivAt (fun s => r (X s)) (rd (X t) (V t)) t := by
    have pos : 0 < r (X t) := by linarith only [rangeX t]
    exact ((radius_diff (X t) pos).hasFDerivAt.comp_hasDerivAt t (dX t)).congr_deriv (radius_der _ _ pos)
  apply bounded_radius c hc rangeX _ smoothr
  · intro t ht
    apply trapped _ _ (by linarith only [rangeX t]) ht hc
    have h := pullback_quadratic (kerrNewmanMetricField 1 0 0) ψ (ℓ t) (v t)
    change _=matrixBilin (kerrNewmanMetric 1 0 0 (X t)) (V t) (V t) at h
    rw [←h,(hcoeff (ℓ t) (linemem t)).1]
    exact (horb t).2.2
  · change r ((ψ (ℓ 0)).val) = _
    rw [h0,hψy]
    exact rz

end
end TrappedShell

open NoHair Set
open scoped ContDiff Manifold

private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2) = Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero, Real.sqrt_sq hp]
  congr 1
  ring

theorem solution : ¬ (∀ {M : Type} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E),
    ∃ m a e : ℝ, IsKerrNewmanBlackHoleParams m a e ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a e) := by
  intro claimed
  let U := kerrNewmanSpacetime 0
  let A := (Subtype.val : U → E4) ⁻¹' exteriorRegion 1
  let g := kerrNewmanMetricField 1 0 0
  let F := kerrNewmanFieldField 0 0
  obtain ⟨φ, E, hφ, hsym, _, hE⟩ := schwarzschild_unit_cutoff_end
  obtain ⟨T, hT, hp, hf, hgh⟩ := schwarzschild_unit_cutoff_causality
  have past : chronoPastSet g T E.region = A := hE ▸ hp
  have doc : domainOfOuterCommunications g T E.region = A := by
    unfold domainOfOuterCommunications
    rw [past, hE]
    exact inter_eq_right.mpr hf
  have hz : ∀ x, F x = 0 := by
    intro x
    ext v w
    change Matrix.toLinearMap₂' ℝ (kerrNewmanField 0 0 x.val) (WithLp.ofLp v) (WithLp.ofLp w) = 0
    simp [Matrix.toLinearMap₂'_apply, kerrNewmanField, kerrNewmanPotential, coordPartial]
  obtain ⟨hl, hsg, hsF⟩ := kerrNewman_regularTensors 1 0 0
  have hem : IsElectrovac g F := isElectrovac_of_coordinate_equations U
      (kerrNewmanMetric 1 0 0) (kerrNewmanField 0 0)
      (fun y hy => by
        have zeroF : kerrNewmanField 0 0 = fun _ => 0 := by
          funext z i j
          simp [kerrNewmanField,kerrNewmanPotential,coordPartial]
        refine ⟨?_,?_,?_⟩
        · intro i j
          simp [einsteinTensor,scalarCurvature,schwarzschild_unit_cartesian_ricci_zero y hy,
            zeroF,maxwellSource,raiseBoth]
        · intro j
          simp [zeroF,raiseBoth,coordPartial]
        · intro i j k
          simp [zeroF,coordPartial])
  have Aeq : A = {x : U | 1 < ksRadius 0 x.val} := by ext x; simp [A, exteriorRegion, radius_eq]
  obtain ⟨hfront,hlevel⟩ := ksRadius_superlevel_frontier 0 1 zero_lt_one
  have hBH : IsStationaryBlackHole g F T φ E := {
    lorentzian := hl
    smooth_metric := hsg
    smooth_field := hsF
    twoForm := by intro x v w; simp [hz]
    timeOrientation := hT
    electrovac := hem
    stationary := hsym
    globallyHyperbolic := doc ▸ hgh
    blackHole_nonempty := by
      obtain ⟨x,hx⟩ := hlevel.nonempty
      refine ⟨x, ?_⟩
      change x ∉ chronoPastSet g T E.region
      rw [past, Aeq]
      change ¬ 1 < ksRadius 0 x.val
      exact not_lt.mpr (le_of_eq hx)
    horizon_connected := by
      change IsConnected (frontier (chronoPastSet g T E.region))
      rw [past, Aeq, hfront]
      exact hlevel }
  obtain ⟨m, a, e, hparams, hiso⟩ := claimed g F T φ E hBH
  rw [doc] at hiso
  exact TrappedShell.no_kerrNewman m a e hparams hiso
