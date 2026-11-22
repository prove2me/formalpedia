-- Prove2me | solution 1 for NoHair.TwoCentre.Model.electrovac_across_horizon
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:13:55.79384+00:00
-- url     : https://prove2.me/submissions/89646235-fdbd-4ff9-aee7-6656017dd0ce

import Theorems.Thm_NoHair_TwoCentre_Advanced_regular_horizon
import Theorems.Thm_NoHair_isElectrovac_of_coordinate_equations
import Definitions.Def_NoHair_TwoCentreBlackHole

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology Filter
open scoped ContDiff Manifold RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Continuation

noncomputable section

private abbrev AM (f : E4 → ℝ) (z : E4) := ContDiffAt ℝ ω f z
private abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

private theorem partial_an {f : E4 → ℝ} {z : E4} (hf : AM f z) (i : Fin 4) :
    AM (coordPartial f i) z :=
  (hf.fderiv_right (m := ω) (by simp)).clm_apply contDiffAt_const

private theorem det_an {G : E4 → Mat4} {z : E4} (hG : ∀ i j, AM (fun x => G x i j) z) :
    AM (fun x => (G x).det) z := by
  simp only [Matrix.det_apply']
  unfold AM
  fun_prop

private theorem inv_an {G : E4 → Mat4} {z : E4} (hG : ∀ i j, AM (fun x => G x i j) z)
    (hn : (G z).det ≠ 0) (i j : Fin 4) : AM (fun x => invMetric G x i j) z := by
  have ha : AM (fun x => ((G x).adjugate) i j) z := by
    simp_rw [Matrix.adjugate_apply]
    apply det_an
    intro a b
    by_cases h : a = j
    · subst a
      simp only [Matrix.updateRow_self]
      exact contDiffAt_const
    · simpa [Matrix.updateRow_ne h] using hG a b
  simpa [invMetric, Matrix.inv_def, Ring.inverse_eq_inv] using ((det_an hG).inv hn).mul ha

private def einResidual (G F : E4 → Mat4) (i j : Fin 4) (x : E4) :=
  einsteinTensor G x i j - maxwellSource G F x i j
private def divResidual (G F : E4 → Mat4) (j : Fin 4) (x : E4) :=
  ∑ i, coordPartial (fun y => Real.sqrt |(G y).det| * raiseBoth G F y i j) i x
private def closedResidual (F : E4 → Mat4) (i j k : Fin 4) (x : E4) :=
  coordPartial (fun y => F y j k) i x + coordPartial (fun y => F y k i) j x +
    coordPartial (fun y => F y i j) k x

private theorem residual_an {G F : E4 → Mat4} {z : E4}
    (hG : ∀ i j, AM (fun x => G x i j) z) (hF : ∀ i j, AM (fun x => F x i j) z)
    (hn : (G z).det ≠ 0) :
    (∀ i j, AM (einResidual G F i j) z) ∧ (∀ j, AM (divResidual G F j) z) ∧
    ∀ i j k, AM (closedResidual F i j k) z := by
  have hi := inv_an hG hn
  have hpart i j k := partial_an (hG i j) k
  have hc (i j k : Fin 4) : AM (fun x => christoffel G x i j k) z := by
    unfold AM christoffel
    fun_prop
  have hpc (i j k l : Fin 4) := partial_an (hc i j k) l
  have hr (i j : Fin 4) : AM (fun x => ricci G x i j) z := by
    unfold AM ricci riemann
    fun_prop
  have hu (i j : Fin 4) : AM (fun x => raiseBoth G F x i j) z := by
    unfold AM raiseBoth
    fun_prop
  have hsq : AM (fun x => Real.sqrt |(G x).det|) z :=
    by simpa only [Real.norm_eq_abs] using (((det_an hG).norm ℝ hn).sqrt (norm_ne_zero_iff.mpr hn))
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold AM einResidual einsteinTensor scalarCurvature maxwellSource
    fun_prop
  · intro j
    have hd (i : Fin 4) := partial_an (hsq.mul (hu i j)) i
    unfold AM divResidual
    fun_prop
  · intro i j k
    exact ((partial_an (hF j k) i).add (partial_an (hF k i) j)).add (partial_an (hF i j) k)

private theorem spatial_an : ContDiff ℝ ω spatial :=
  contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))

private theorem coordinates_an : ContDiff ℝ ω (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  apply contDiff_euclidean.2
  intro i
  refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
  simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
  fun_prop

private theorem unit_dir (z : E4) (h : 0 < ‖spatial z‖) : ‖angularDirection z‖ = 1 := by
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_cancel₀ h.ne']

private theorem collar_data {z : E4} (hc : |‖spatial z‖ - 1| < 1/4) :
    (∀ i j, AM (fun x => metricCoeffs x i j) z) ∧
    (∀ i j, AM (fun x => faradayCoeffs x i j) z) ∧
    Matrix.det (metricCoeffs z : Mat4) ≠ 0 := by
  have hp : 0 < ‖spatial z‖ := by linarith [(abs_lt.mp hc).1]
  have hu := unit_dir z hp
  have hd : |angularDirection z 0| ≤ 1 := by
    simpa [Real.norm_eq_abs, hu] using (PiLp.norm_apply_le (angularDirection z) 0)
  have hreg := Advanced.regular_horizon.1 (parameters z) hc hd
  have hnorm := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hp)
  have hdire : ContDiffAt ℝ ω angularDirection z :=
    (hnorm.inv hp.ne').smul spatial_an.contDiffAt
  have hparams : ContDiffAt ℝ ω parameters z :=
    (hnorm.sub contDiffAt_const).prodMk ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 3))).comp z hdire)
  have hfn (f : ℝ × ℝ → ℝ) (hf : f ∈ [Advanced.gvv, Advanced.gvr, Advanced.grr, Advanced.angularScale,
        Advanced.potentialV, Advanced.potentialR]) : AM (fun x => f (parameters x)) z :=
    (hreg.2.1 f hf).contDiffAt.comp z hparams
  have hvv := hfn _ (by simp : Advanced.gvv ∈ _)
  have hvr := hfn _ (by simp : Advanced.gvr ∈ _)
  have hrr := hfn _ (by simp : Advanced.grr ∈ _)
  have ha := hfn _ (by simp : Advanced.angularScale ∈ _)
  have hv := hfn _ (by simp : Advanced.potentialV ∈ _)
  have hav := hfn _ (by simp : Advanced.potentialR ∈ _)
  have hdr (i : Fin 4) : AM (fun x => dr x i) z := by
    refine Fin.cases (by exact contDiffAt_const) (fun j => ?_) i
    exact (contDiffAt_piLp_apply (p := 2) (i := j)).comp z hdire
  have hpotential (i : Fin 4) : AM (potential i) z :=
    (hv.mul contDiffAt_const).add (hav.mul (hdr i))
  refine ⟨?_, fun i j => (partial_an (hpotential j) i).sub (partial_an (hpotential i) j), ?_⟩
  · intro i j
    exact (((hvv.mul contDiffAt_const).mul contDiffAt_const).add
      (hvr.mul ((contDiffAt_const.mul (hdr j)).add ((hdr i).mul contDiffAt_const))) |>.add
      ((hrr.mul (hdr i)).mul (hdr j))).add
      ((ha.div (hnorm.pow 2) (pow_ne_zero 2 hp.ne')).mul (contDiffAt_const.sub ((hdr i).mul (hdr j))))
  · let n := angularDirection z
    let a := Advanced.gvv (parameters z)
    let b := Advanced.gvr (parameters z)
    let d := Advanced.grr (parameters z)
    let k := Advanced.angularScale (parameters z) / ‖spatial z‖ ^ 2
    have hk : 0 < k := div_pos (sq_pos_of_pos hreg.1) (sq_pos_of_pos hp)
    have hrad : a * d - b ^ 2 = -1 := hreg.2.2.1
    have hs : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
      have h : ‖n‖ ^ 2 = 1 := by rw [show ‖n‖ = 1 from hu]; norm_num
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] using h
    let B : Mat4 := !![a, b*n 0, b*n 1, b*n 2;
      b*n 0, k+(d-k)*n 0*n 0, (d-k)*n 0*n 1, (d-k)*n 0*n 2;
      b*n 1, (d-k)*n 1*n 0, k+(d-k)*n 1*n 1, (d-k)*n 1*n 2;
      b*n 2, (d-k)*n 2*n 0, (d-k)*n 2*n 1, k+(d-k)*n 2*n 2]
    have hB : (metricCoeffs z : Mat4) = B := by
      have dr0 : dr z 0 = 0 := rfl
      have dr1 : dr z 1 = n 0 := rfl
      have dr2 : dr z 2 = n 1 := rfl
      have dr3 : dr z 3 = n 2 := rfl
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp (config := {decide := true}) [metricCoeffs, dt, dr0, dr1, dr2, dr3, spatialDelta, a, b, d, k, B] <;> ring
    have hdet : B.det = k^2 * (a*d-b^2) := by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, B, Fin.succAbove]
      linear_combination k ^ 2 * (a * (d-k)-b^2) * hs
    rw [hB, hdet, hrad]
    positivity

private theorem extend_scalar (f : E4 → ℝ)
    (han : ∀ z, |‖spatial z‖ - 1| < 1/4 → AM f z)
    (hzero : ∀ z ∈ outerRegion, f z = 0) {z : E4} (hz : z ∈ manifold) : f z = 0 := by
  change 3 / 4 < ‖spatial z‖ ∧ spatial z ≠ (3 : ℝ) • unitAxis at hz
  by_cases ho : 1 < ‖spatial z‖
  · exact hzero z ⟨ho, hz.2⟩
  let r := ‖spatial z‖ - 1
  let n := angularDirection z
  have hp : 0 < ‖spatial z‖ := by linarith [hz.1]
  have hn : ‖n‖ = 1 := unit_dir z hp
  let ray := fun s : ℝ => coordinates (z 0) ((1+s) • n)
  have hray : ContDiff ℝ ω ray :=
    coordinates_an.comp (contDiff_const.prodMk ((contDiff_const.add contDiff_id).smul contDiff_const))
  have hnray {s : ℝ} (hs : -(1/4 : ℝ) < s) : ‖spatial (ray s)‖ = 1+s := by
    change ‖spatial (coordinates _ _)‖ = _
    rw [Model.spatial_coordinates, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hn, mul_one]
  have har : AnalyticOnNhd ℝ (fun s => f (ray s)) (Ioo (-(1/4 : ℝ)) (1/4)) := by
    intro s hs
    exact ((han (ray s) (by rw [hnray hs.1]; apply abs_lt.mpr; constructor <;> linarith [hs.1, hs.2])).comp
      s hray.contDiffAt).analyticAt
  have hpos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1/4)) : ray s ∈ outerRegion := by
    have hn' := hnray (s := s) (by linarith [hs.1])
    refine ⟨by linarith [hs.1], ?_⟩
    intro heq
    have h3 : ‖spatial (ray s)‖ = 3 := by rw [heq, norm_smul]; norm_num [unitAxis]
    linarith [hs.2]
  have hev : (fun s => f (ray s)) =ᶠ[𝓝 (1/8 : ℝ)] 0 := by
    filter_upwards [Ioo_mem_nhds (a := (0 : ℝ)) (b := 1/4) (by norm_num : 0 < (1/8 : ℝ)) (by norm_num)] with s hs
    exact hzero _ (hpos hs)
  have hall := har.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    (show (1/8 : ℝ) ∈ Ioo (- (1/4 : ℝ)) (1/4) by constructor <;> norm_num) hev
  have hr : r ∈ Ioo (-(1/4 : ℝ)) (1/4) := by dsimp [r]; constructor <;> linarith [hz.1]
  have hid : ray r = z := by
    change coordinates (z 0) ((1 + (‖spatial z‖ - 1)) • (‖spatial z‖⁻¹ • spatial z)) = z
    rw [show 1 + (‖spatial z‖ - 1) = ‖spatial z‖ by ring, smul_smul,
      mul_inv_cancel₀ hp.ne', one_smul]
    ext i
    exact Fin.cases rfl (fun j => by rfl) i
  simpa only [hid, Pi.zero_apply] using hall hr

theorem across (he : ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z) :
    IsElectrovac metric faraday := by
  apply isElectrovac_of_coordinate_equations manifold metricCoeffs faradayCoeffs
  intro z hz
  have ha (x : E4) (hx : |‖spatial x‖ - 1| < 1/4) := by
    obtain ⟨hG, hF, hd⟩ := collar_data hx
    exact residual_an (G := metricCoeffs) (F := faradayCoeffs) hG hF hd
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply sub_eq_zero.mp
    exact extend_scalar (einResidual metricCoeffs faradayCoeffs i j)
      (fun x hx => (ha x hx).1 i j) (fun x hx => sub_eq_zero.mpr ((he x hx).1 i j)) hz
  · intro j
    exact extend_scalar (divResidual metricCoeffs faradayCoeffs j)
      (fun x hx => (ha x hx).2.1 j) (fun x hx => (he x hx).2.1 j) hz
  · intro i j k
    exact extend_scalar (closedResidual faradayCoeffs i j k)
      (fun x hx => (ha x hx).2.2 i j k) (fun x hx => (he x hx).2.2 i j k) hz

end
end NoHair.TwoCentre.Model.Continuation

open NoHair.TwoCentre.Model.Continuation

theorem solution (he : ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z) :
    IsElectrovac metric faraday := across he
