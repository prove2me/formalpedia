-- Prove2me | solution 1 for NoHair.TwoCentre.Model.advanced_exterior_equations
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:02:11.490984+00:00
-- url     : https://prove2.me/submissions/298c26f8-c8c6-4a89-830c-9dfab91c17e9

import Theorems.Thm_ExactVacuumAtlas_Variation_einsteinMaxwell_transform
import Theorems.Thm_ExactVacuumAtlas_Variation_maxwellDiv_transform
import Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_eq_det_mul_trace_readable
import Definitions.Def_NoHair_coordinates
import Definitions.Def_NoHair_TwoCentreIsotropic
import Definitions.Def_NoHair_TwoCentreBlackHole
import Theorems.Thm_NoHair_TwoCentre_Advanced_regular_horizon
import Theorems.Thm_NoHair_TwoCentre_Model_stationary_geometry
import Theorems.Thm_ExactVacuumAtlas_Variation_faradayCyclic_transform
import Theorems.Thm_NoHair_TwoCentre_Cartesian_exterior_and_frontier

open NoHair Set Filter Topology
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

namespace NoHair.AtlasBridge
noncomputable section
abbrev Pt := ExactVacuumAtlas.Pt 4
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev SC (f : E4 → ℝ) (y : E4) := ContDiffAt ℝ ∞ f y
abbrev EMetric := E4 → M4
abbrev enc (G : EMetric) : ExactVacuumAtlas.Metric 4 := fun i j x => G (WithLp.toLp 2 x) i j
abbrev encodeSet (S : Set E4) := (WithLp.toLp 2 : Pt → E4) ⁻¹' S

def pack : Pt →L[ℝ] E4 := LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ Pt).symm.toLinearMap
def unpack : E4 →L[ℝ] Pt := LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ Pt).toLinearMap

theorem coord_slice (p : Pt) (i : Fin 4) :
    HasDerivAt (fun s : ℝ => WithLp.toLp 2 (Function.update p i s) : ℝ → E4) (coordBasis i) (p i) := by
  have eq : (fun s : ℝ => WithLp.toLp 2 (Function.update p i s) : ℝ → E4) =
      (fun s : ℝ => WithLp.toLp 2 p + (s-p i) • coordBasis i) := by
    funext s; ext j
    by_cases hj : j=i
    · subst j;simp [coordBasis,PiLp.add_apply,PiLp.smul_apply]
    · simp [coordBasis,Function.update_of_ne hj,PiLp.add_apply,PiLp.smul_apply,Pi.single_apply,hj,Ne.symm hj]
  rw [eq]
  simpa using (((hasDerivAt_id (p i)).sub_const (p i)).smul_const (coordBasis i)).const_add (WithLp.toLp 2 p)

theorem pd_eq {f : E4 → ℝ} {p : Pt} (hf : DifferentiableAt ℝ f (WithLp.toLp 2 p)) (i : Fin 4) :
    ExactVacuumAtlas.pd i (fun x : Pt => f (WithLp.toLp 2 x)) p = coordPartial f i (WithLp.toLp 2 p) := by
  have hd : HasFDerivAt f (fderiv ℝ f (WithLp.toLp 2 p)) (WithLp.toLp 2 (Function.update p i (p i))) := by simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt (p i) (coord_slice p i)).deriv

theorem partial_smooth {f : E4 → ℝ} {z : E4} (hf : SC f z) (i : Fin 4) : SC (coordPartial f i) z :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem det_smooth {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y) :
    SC (fun x => (G x).det) y := by simp only [Matrix.det_apply'];unfold SC;fun_prop

theorem inv_smooth {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hn : (G y).det ≠ 0) (i j : Fin 4) : SC (fun x => invMetric G x i j) y := by
  have ha : SC (fun x => ((G x).adjugate) i j) y := by
    simp_rw [Matrix.adjugate_apply]
    apply det_smooth
    intro a b
    by_cases h : a = j
    · subst a;simp only [Matrix.updateRow_self];exact contDiffAt_const
    · simpa [Matrix.updateRow_ne h] using hG a b
  simpa [invMetric, Matrix.inv_def, Ring.inverse_eq_inv] using ((det_smooth hG).inv hn).mul ha

theorem chr_smooth {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hn : (G y).det ≠ 0) (i j k : Fin 4) : SC (fun x => christoffel G x i j k) y := by
  have hi := inv_smooth hG hn
  have hpart (a b c : Fin 4) := partial_smooth (hG a b) c
  unfold SC christoffel;fun_prop

theorem upper_smooth {G F : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hF : ∀ i j, SC (fun x => F x i j) y) (hn : (G y).det ≠ 0) (i j : Fin 4) :
    SC (fun x => raiseBoth G F x i j) y := by
  have hi := inv_smooth hG hn
  unfold SC raiseBoth;fun_prop

theorem chr_bridge {G : EMetric} {p : Pt}
    (hG : ∀ i j, SC (fun x => G x i j) (WithLp.toLp 2 p)) (a b c : Fin 4) :
    ExactVacuumAtlas.christoffel (enc G) (enc (invMetric G)) a b c p =
      christoffel G (WithLp.toLp 2 p) a b c := by
  have hd (i j k : Fin 4) := pd_eq ((hG i j).differentiableAt (by simp)) k
  simp only [ExactVacuumAtlas.christoffel,enc,hd,christoffel,Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _;ring

theorem chr_symm {G : EMetric} {S : Set E4} (hS : IsOpen S)
    (hG : ∀ x ∈ S, (G x).transpose=G x) {y : E4} (hy : y ∈ S) (a b c : Fin 4) :
    christoffel G y a b c = christoffel G y a c b := by
  have ev : (fun x => G x b c) =ᶠ[𝓝 y] (fun x => G x c b) :=
    Filter.mem_of_superset (hS.mem_nhds hy) (fun x hx => congrFun (congrFun (hG x hx) c) b)
  have hder (k : Fin 4) : coordPartial (fun x => G x b c) k y = coordPartial (fun x => G x c b) k y :=
    DFunLike.congr_fun ev.fderiv_eq _
  unfold christoffel
  simp only [hder]
  apply Finset.sum_congr rfl;intro k _;ring

theorem ricci_bridge {G : EMetric} {S : Set E4} (hS : IsOpen S)
    (hsm : ∀ x ∈ S, ∀ i j, SC (fun w => G w i j) x)
    (hsym : ∀ x ∈ S, (G x).transpose=G x) {p : Pt} (hp : WithLp.toLp 2 p ∈ S)
    (hn : (G (WithLp.toLp 2 p)).det ≠ 0) (i j : Fin 4) :
    ExactVacuumAtlas.ricciOf (enc G) (enc (invMetric G)) i j p = ricci G (WithLp.toLp 2 p) i j := by
  let y := WithLp.toLp 2 p
  have hder (a b c k : Fin 4) : ExactVacuumAtlas.pd k (ExactVacuumAtlas.christoffel (enc G) (enc (invMetric G)) a b c) p =
      coordPartial (fun x => christoffel G x a c b) k y := by
    let f := fun x => christoffel G x a c b
    have hd : HasDerivAt (fun t : ℝ => WithLp.toLp 2 (Function.update p k t) : ℝ → E4) (coordBasis k) (p k) := coord_slice p k
    have h0 : WithLp.toLp 2 (Function.update p k (p k)) ∈ S := by simpa using hp
    have he : (fun t => ExactVacuumAtlas.christoffel (enc G) (enc (invMetric G)) a b c (Function.update p k t)) =ᶠ[𝓝 (p k)]
        (fun t => f (WithLp.toLp 2 (Function.update p k t))) := by
      filter_upwards [hd.continuousAt (hS.mem_nhds h0)] with t ht
      exact (chr_bridge (hsm _ ht) a b c).trans (chr_symm hS hsym ht _ _ _)
    exact he.deriv_eq.trans (pd_eq ((chr_smooth (hsm _ hp) hn a c b).differentiableAt (by simp)) k)
  have hchr := chr_bridge (hsm _ hp)
  unfold ExactVacuumAtlas.ricciOf ExactVacuumAtlas.ricci ricci riemann
  simp only [hder,hchr]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  apply Finset.sum_congr rfl;intro l _
  rw [chr_symm hS hsym hp l i j,chr_symm hS hsym hp l i k]

theorem ein_bridge {G F : EMetric} {S : Set E4} (hS : IsOpen S)
    (hsm : ∀ x ∈ S, ∀ i j, SC (fun w => G w i j) x) (hsym : ∀ x ∈ S, (G x).transpose=G x)
    {p : Pt} (hp : WithLp.toLp 2 p ∈ S) (hn : (G (WithLp.toLp 2 p)).det ≠ 0) (i j : Fin 4) :
    ExactVacuumAtlas.EinsteinMaxwell.einsteinMaxwell (enc G) (enc (invMetric G)) (enc F) i j p =
      einsteinTensor G (WithLp.toLp 2 p) i j - maxwellSource G F (WithLp.toLp 2 p) i j := by
  have hr := ricci_bridge hS hsm hsym hp hn
  unfold ExactVacuumAtlas.EinsteinMaxwell.einsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ricciScalar
    ExactVacuumAtlas.EinsteinMaxwell.emStress ExactVacuumAtlas.EinsteinMaxwell.fieldSq
    ExactVacuumAtlas.EinsteinMaxwell.raise2 einsteinTensor scalarCurvature maxwellSource raiseBoth
  simp only [hr,enc]
  ring

def derivMatrix (G : EMetric) (k : Fin 4) (y : E4) : M4 := fun a b => coordPartial (fun x => G x a b) k y

theorem det_partial {G : EMetric} {y : E4} (hG : ∀ a b, SC (fun w => G w a b) y)
    (hn : (G y).det≠0) (k : Fin 4) :
    coordPartial (fun x => (G x).det) k y = (G y).det * Matrix.trace ((G y)⁻¹ * derivMatrix G k y) := by
  have hmat : DifferentiableAt ℝ G y := by
    apply differentiableAt_pi.mpr;intro i
    apply differentiableAt_pi.mpr;intro j
    exact (hG i j).differentiableAt (by simp)
  have hdet : DifferentiableAt ℝ (Matrix.det : M4 → ℝ) (G y) := by
    exact ((FunctionalInequalities.Analysis.detML (ι := Fin 4)).hasFDerivAt (G y)).differentiableAt
  have hd : fderiv ℝ G y (coordBasis k) = derivMatrix G k y := by
    ext i j
    let P₁ : M4 →L[ℝ] (Fin 4 → ℝ) := (ContinuousLinearMap.proj (φ := fun _ : Fin 4 => Fin 4 → ℝ) i)
    let P₂ : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (φ := fun _ : Fin 4 => ℝ) j
    let P := P₂.comp P₁
    exact (DFunLike.congr_fun (P.hasFDerivAt.comp y hmat.hasFDerivAt).fderiv (coordBasis k)).symm
  have h := DFunLike.congr_fun (hdet.hasFDerivAt.comp y hmat.hasFDerivAt).fderiv (coordBasis k)
  exact h.trans ((FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_readable
    (G y) (fderiv ℝ G y (coordBasis k)) (isUnit_iff_ne_zero.mpr hn)).trans (by rw [hd]))

theorem trace_christoffel {G : EMetric} {y : E4} (hsym : (G y).transpose=G y) (k : Fin 4) :
    ∑ a, christoffel G y a a k = Matrix.trace ((G y)⁻¹ * derivMatrix G k y) / 2 := by
  have hisym : (invMetric G y).transpose=invMetric G y := by
    unfold invMetric;rw [Matrix.transpose_nonsing_inv,hsym]
  have hi (a b : Fin 4) : invMetric G y a b = invMetric G y b a := congrFun (congrFun hisym b) a
  have cancel : (∑ a, ∑ l, invMetric G y a l * coordPartial (fun x => G x l k) a y) =
      ∑ a, ∑ l, invMetric G y a l * coordPartial (fun x => G x a k) l y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro a _;apply Finset.sum_congr rfl;intro l _;rw [hi l a]
  unfold christoffel Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, derivMatrix]
  have e (a l : Fin 4) : 1/2 * invMetric G y a l *
      (coordPartial (fun x => G x l k) a y+coordPartial (fun x => G x l a) k y-coordPartial (fun x => G x a k) l y) =
      (invMetric G y a l * coordPartial (fun x => G x l k) a y + invMetric G y a l * coordPartial (fun x => G x l a) k y -
       invMetric G y a l * coordPartial (fun x => G x a k) l y)/2 := by ring
  change (∑ a : Fin 4, ∑ l : Fin 4, (1/2:ℝ) * invMetric G y a l * _) = _
  simp_rw [e]
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,cancel]
  dsimp [invMetric]
  ring

def volume (G : EMetric) (y : E4) := Real.sqrt |(G y).det|

theorem volume_partial {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hn : (G y).det≠0) (hsym : (G y).transpose=G y) (k : Fin 4) :
    coordPartial (volume G) k y = volume G y * ∑ a, christoffel G y a a k := by
  have hd := (det_smooth hG).differentiableAt (by simp)
  have hpos : 0<volume G y := Real.sqrt_pos.mpr (abs_pos.mpr hn)
  have hsq : volume G y ^ 2 = |(G y).det| := Real.sq_sqrt (abs_nonneg _)
  rw [trace_christoffel hsym]
  rcases lt_or_gt_of_ne hn with hN | hP
  · have ev : volume G =ᶠ[𝓝 y] (fun x => Real.sqrt (-(G x).det)) := by
      filter_upwards [hd.continuousAt.eventually_lt_const hN] with x hx
      simp [volume,abs_of_neg hx]
    have hf := (hd.hasFDerivAt.neg).sqrt (neg_ne_zero.mpr hn)
    have e := DFunLike.congr_fun (ev.fderiv_eq.trans hf.fderiv) (coordBasis k)
    change fderiv ℝ (volume G) y (coordBasis k) = _
    rw [e]
    rw [abs_of_neg hN] at hsq
    change (1 / (2 * Real.sqrt (-(G y).det))) * -(coordPartial (fun x => (G x).det) k y) = _
    have hv : Real.sqrt (-(G y).det) = volume G y := by simp [volume,abs_of_neg hN]
    rw [hv,det_partial hG hn]
    field_simp [hpos.ne']
    <;> nlinarith [congrArg (· * Matrix.trace ((G y)⁻¹ * derivMatrix G k y)) hsq]
  · have ev : volume G =ᶠ[𝓝 y] (fun x => Real.sqrt (G x).det) := by
      filter_upwards [hd.continuousAt.eventually_const_lt hP] with x hx
      simp [volume,abs_of_pos hx]
    have hf := hd.hasFDerivAt.sqrt hn
    have e := DFunLike.congr_fun (ev.fderiv_eq.trans hf.fderiv) (coordBasis k)
    change fderiv ℝ (volume G) y (coordBasis k) = _
    rw [e]
    rw [abs_of_pos hP] at hsq
    change (1 / (2 * Real.sqrt (G y).det)) * coordPartial (fun x => (G x).det) k y = _
    have hv : Real.sqrt (G y).det = volume G y := by simp [volume,abs_of_pos hP]
    rw [hv,det_partial hG hn]
    field_simp [hpos.ne']
    <;> nlinarith [congrArg (· * Matrix.trace ((G y)⁻¹ * derivMatrix G k y)) hsq]

theorem raised_anti {G F : EMetric} {y : E4} (hF : ∀ i j, F y i j = - F y j i) (i j : Fin 4) :
    raiseBoth G F y i j = -raiseBoth G F y j i := by
  unfold raiseBoth
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl;intro l _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl;intro k _
  rw [hF k l]
  ring

def divDensity (G F : EMetric) (j : Fin 4) (y : E4) :=
  ∑ i, coordPartial (fun x => volume G x * raiseBoth G F x i j) i y

theorem div_bridge {G F : EMetric} {S : Set E4} (hS : IsOpen S)
    (hsym : ∀ x ∈ S, (G x).transpose=G x) {p : Pt} (hp : WithLp.toLp 2 p ∈ S)
    (hG : ∀ i j, SC (fun x => G x i j) (WithLp.toLp 2 p)) (hF : ∀ i j, SC (fun x => F x i j) (WithLp.toLp 2 p))
    (hn : (G (WithLp.toLp 2 p)).det ≠ 0) (ha : ∀ i j, F (WithLp.toLp 2 p) i j = -F (WithLp.toLp 2 p) j i) (b : Fin 4) :
    divDensity G F b (WithLp.toLp 2 p) = volume G (WithLp.toLp 2 p) *
      ExactVacuumAtlas.EinsteinMaxwell.maxwellDiv (enc G) (enc (invMetric G)) (enc F) b p := by
  let y : E4 := WithLp.toLp 2 p
  let A (i j : Fin 4) := raiseBoth G F y i j
  let C (i j k : Fin 4) := christoffel G y i j k
  have hpd (i : Fin 4) :
      ExactVacuumAtlas.pd i (ExactVacuumAtlas.EinsteinMaxwell.raise2 (enc (invMetric G)) (enc F) i b) p =
      coordPartial (fun x => raiseBoth G F x i b) i y :=
    pd_eq ((upper_smooth hG hF hn i b).differentiableAt (by simp)) i
  have hv : SC (volume G) y := ((det_smooth hG).norm ℝ hn).sqrt (norm_ne_zero_iff.mpr hn)
  have hdiff (i : Fin 4) : coordPartial (fun x => volume G x * raiseBoth G F x i b) i y =
      volume G y * ((∑ a, C a a i)*A i b + coordPartial (fun x => raiseBoth G F x i b) i y) := by
    have hp := (hv.differentiableAt (by simp)).hasFDerivAt.mul ((upper_smooth hG hF hn i b).differentiableAt (by simp)).hasFDerivAt
    calc
      _ = volume G y * coordPartial (fun x => raiseBoth G F x i b) i y + A i b * coordPartial (volume G) i y := by
        simpa only [coordPartial,A,y,Pi.mul_def,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
          using DFunLike.congr_fun hp.fderiv (coordBasis i)
      _ = _ := by rw [volume_partial hG hn (hsym _ ‹_ ∈ S›)];dsimp [C];ring
  have vanish : (∑ i, ∑ k, C b i k * A i k) = 0 := by
    have h : (∑ i, ∑ k, C b i k * A i k) = -(∑ i, ∑ k, C b i k * A i k) := by
      calc
        _ = ∑ k, ∑ i, C b i k * A i k := Finset.sum_comm
        _ = _ := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl;intro k _;rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl;intro i _
          change christoffel G y b i k * raiseBoth G F y i k = -(christoffel G y b k i * raiseBoth G F y k i)
          calc
            _ = christoffel G y b k i * (-raiseBoth G F y k i) := congrArg₂ (· * ·) (chr_symm hS hsym hp b i k) (raised_anti ha i k)
            _ = _ := by ring
    linarith
  have reorder : (∑ i, (∑ a, C a a i)*A i b) = ∑ a, ∑ i, C a a i*A i b := by
    simp only [Finset.sum_mul];rw [Finset.sum_comm]
  change (∑ i, coordPartial (fun x => volume G x * raiseBoth G F x i b) i y) = _
  simp only [hdiff,← Finset.mul_sum,ExactVacuumAtlas.EinsteinMaxwell.maxwellDiv,hpd,chr_bridge hG]
  change volume G y * (∑ i, ((∑ a, C a a i)*A i b + coordPartial (fun x => raiseBoth G F x i b) i y)) =
    volume G y * (∑ a, (coordPartial (fun x => raiseBoth G F x a b) a y +
      ∑ k, (C a a k * A k b + C b a k * A a k)))
  simp only [Finset.sum_add_distrib,vanish,add_zero,zero_add,reorder,add_comm]

theorem cyclic_bridge {F : EMetric} {p : Pt} (hs : ∀ i j, SC (fun y => F y i j) (WithLp.toLp 2 p)) (a b c : Fin 4) :
    ExactVacuumAtlas.EinsteinMaxwell.faradayCyclic (enc F) a b c p =
      coordPartial (fun y => F y b c) a (WithLp.toLp 2 p) + coordPartial (fun y => F y c a) b (WithLp.toLp 2 p) +
        coordPartial (fun y => F y a b) c (WithLp.toLp 2 p) := by
  unfold ExactVacuumAtlas.EinsteinMaxwell.faradayCyclic enc
  rw [pd_eq ((hs b c).differentiableAt (by simp)), pd_eq ((hs c a).differentiableAt (by simp)), pd_eq ((hs a b).differentiableAt (by simp))]
end
end NoHair.AtlasBridge

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves

noncomputable section

def radialSpeed (z : E4) (w : E4) : ℝ := ⟪angularDirection z, spatial w⟫

theorem spatial_inner (w v : E4) :
    ⟪spatial w, spatial v⟫ = w 1 * v 1 + w 2 * v 2 + w 3 * v 3 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, spatial]
  ring

private theorem radialSpeed_coords (z w : E4) :
    radialSpeed z w = dr z 1 * w 1 + dr z 2 * w 2 + dr z 3 * w 3 := by
  unfold radialSpeed
  rw [← Model.spatial_coordinates 0 (angularDirection z), spatial_inner]
  rfl

theorem metric_eval (z : manifold) (v w : E4) :
    metric z v w =
    Advanced.gvv (parameters z) * v 0 * w 0
    + Advanced.gvr (parameters z) * (v 0 * radialSpeed z w + radialSpeed z v * w 0)
    + Advanced.grr (parameters z) * radialSpeed z v * radialSpeed z w
    + Advanced.angularScale (parameters z) / ‖spatial z‖ ^ 2 *
      (⟪spatial v, spatial w⟫ - radialSpeed z v * radialSpeed z w) := by
  change Matrix.toLinearMap₂' ℝ (metricCoeffs z) (WithLp.ofLp v) (WithLp.ofLp w) = _
  rw [Matrix.toLinearMap₂'_apply (R := ℝ) (metricCoeffs z : Matrix (Fin 4) (Fin 4) ℝ) (WithLp.ofLp v) (WithLp.ofLp w), spatial_inner]
  simp only [radialSpeed_coords, Fin.sum_univ_four, smul_eq_mul, metricCoeffs]
  have hd : dr z 0 = 0 := rfl
  simp (config := {decide := true}) [dt, spatialDelta, hd]
  ring

theorem angular_unit (z : manifold) : ‖angularDirection z‖ = 1 := by
  have hz : (3 : ℝ) / 4 < ‖spatial z‖ := z.property.1
  have hpos : 0 < ‖spatial z‖ := by linarith
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']


end
end NoHair.TwoCentre.Model.Curves

namespace NoHair.TwoCentre.Advanced
noncomputable section
theorem gap_factor {p : ℝ × ℝ} (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) :
    H p - H₀ p = p.1 ^ 2 * gapCoeff p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd2 : distanceToOther p ^ 2 = 4 + p.1 ^ 2 - 4 * p.1 * p.2 :=
    Real.sq_sqrt harg.le
  unfold H H₀ gapCoeff
  field_simp [hd.ne', show 2 + distanceToOther p ≠ 0 by linarith]
  linear_combination -p.1 * hd2

theorem coefficient_analytic {p : ℝ × ℝ}
    (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) (hH : 0 < H p) :
    ∀ f ∈ [gvv, gvr, grr, angularScale, potentialV, potentialR], AnalyticAt ℝ f p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd' : 0 < 2 + distanceToOther p := by linarith
  have ds : ContDiffAt ℝ ω distanceToOther p := by
    unfold distanceToOther
    exact (show ContDiffAt ℝ ω (fun q : ℝ × ℝ => 4 + q.1 ^ 2 - 4 * q.1 * q.2) p
      by fun_prop).sqrt harg.ne'
  have hs : ContDiffAt ℝ ω H p := by unfold H; fun_prop (disch := positivity)
  have h0s : ContDiffAt ℝ ω H₀ p := by unfold H₀; fun_prop
  have cs : ContDiffAt ℝ ω gapCoeff p := by unfold gapCoeff; fun_prop (disch := positivity)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> apply ContDiffAt.analyticAt <;>
    first | unfold gvv | unfold gvr | unfold grr | unfold angularScale | unfold potentialV |
      unfold potentialR
  all_goals fun_prop (disch := positivity)

theorem determinant {p : ℝ × ℝ} (hH : H p ≠ 0)
    (hgap : H p - H₀ p = p.1 ^ 2 * gapCoeff p) :
    gvv p * grr p - gvr p ^ 2 = -1 := by
  unfold gvv grr gvr
  field_simp [hH]
  linear_combination (H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) * hgap

theorem match_exterior {p : ℝ × ℝ} (hr : p.1 ≠ 0) (hH : H p ≠ 0)
    (hgap : H p - H₀ p = p.1 ^ 2 * gapCoeff p) :
    grr p = (H p ^ 4 - H₀ p ^ 4) / (p.1 ^ 2 * H p ^ 2) ∧
      potentialR p = -(H₀ p ^ 2 / (p.1 * H p)) + H₀ p / p.1 := by
  constructor
  · unfold grr
    field_simp [hr, hH]
    linear_combination -(H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) * hgap
  · unfold potentialR
    field_simp [hr, hH]
    linear_combination -H₀ p * hgap


end
end NoHair.TwoCentre.Advanced

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev AM (f : E4 → ℝ) (z : E4) := ContDiffAt ℝ ω f z
theorem spatial_an : ContDiff ℝ ω spatial :=
  contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
theorem coordinate_an : ContDiff ℝ ω (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  apply contDiff_euclidean.2
  intro i
  refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
  simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
  fun_prop

theorem coords_self (z : E4) : coordinates (z 0) (spatial z) = z := by
  ext i; exact Fin.cases rfl (fun _ => rfl) i

theorem partial_an {f : E4 → ℝ} {z : E4} (hf : AM f z) (i : Fin 4) : AM (coordPartial f i) z :=
  (hf.fderiv_right (m := ω) (by simp)).clm_apply contDiffAt_const

theorem unit_inner (x : E3) : ⟪x,unitAxis⟫ = x 0 := by
  simp [unitAxis,PiLp.inner_apply]

theorem param_norm {z : E4} (hp : 0 < ‖spatial z‖) :
    ‖angularDirection z‖ = 1 := by
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

theorem radius_data (z : manifold) :
    0 < ‖spatial z‖ ∧
    0 < 4 + (parameters z).1^2 - 4*(parameters z).1*(parameters z).2 ∧
    0 < Advanced.H (parameters z) ∧ 0 < Advanced.H₀ (parameters z) := by
  let p := parameters z
  let n := angularDirection z
  let r := p.1
  have hsize : (3 : ℝ)/4 < ‖spatial z‖ := z.property.1
  have hp : 0 < ‖spatial z‖ := by linarith
  have hn : ‖n‖ = 1 := param_norm hp
  have hc : |p.2| ≤ 1 := by
    change |n 0| ≤ 1
    simpa only [Real.norm_eq_abs, hn] using PiLp.norm_apply_le n 0
  have hela : (4 + p.1^2 - 4*p.1*p.2) = ‖r • n - (2:ℝ) • unitAxis‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, unit_inner,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hn]
    have he : n 0 = p.2 := rfl
    rw [he]
    simp [unitAxis,sq_abs,r]
    ring
  have har : 0 < 4 + p.1 ^ 2 - 4*p.1*p.2 := by
    rw [hela,sq_pos_iff,norm_ne_zero_iff,sub_ne_zero]
    intro h
    have hs := congrArg norm h
    simp [norm_smul,Real.norm_eq_abs,hn,unitAxis] at hs
    have hr : r=2 := by
      have hrg : -(1/4:ℝ) < r := by dsimp [r,p,parameters];linarith
      rcases le_or_gt 0 r with hpos | hneg
      · rwa [abs_of_nonneg hpos] at hs
      · rw [abs_of_neg hneg] at hs; linarith
    rw [hr] at h
    have hdir : n = unitAxis := (smul_right_injective (M := E3) (by norm_num : (2:ℝ) ≠ 0)) h
    have hre : ‖spatial z‖ = 3 := by change ‖spatial z‖ - 1 = 2 at hr; linarith
    apply z.property.2
    calc spatial z = ‖spatial z‖ • n := by simp [n,angularDirection,smul_smul,hp.ne']
         _ = (3:ℝ) • unitAxis := by rw [hre,hdir]
  have hH : 0 < Advanced.H p := by
    by_cases hnon : 0 < p.1
    · unfold Advanced.H
      have hd : 0 < Advanced.distanceToOther p := Real.sqrt_pos.2 har
      positivity
    · have hr : |p.1| < 1/4 := by apply abs_lt.mpr; change - (1/4:ℝ) < ‖spatial z‖ - 1 ∧ _; constructor <;> linarith
      exact (Advanced.regular_horizon.1 p hr hc).1
  exact ⟨hp,har,hH,by unfold Advanced.H₀; change 0 < 1 + 3/2 * (‖spatial z‖ - 1);linarith⟩

theorem reg_data (z : manifold) :
    (∀ i j, AM (fun x => metricCoeffs x i j) z) ∧ (∀ i, AM (potential i) z) ∧
    (∀ i j, AM (fun x => faradayCoeffs x i j) z) ∧
    (ContDiffAt ℝ ω (fun x : E4 => coordinates 1
      (-(Advanced.gvr (parameters x) / (1+Advanced.grr (parameters x)^2)) • angularDirection x)) (z:E4)) := by
  obtain ⟨hp,harg,hH,_⟩ := radius_data z
  have hnorm := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hp)
  have hdire : ContDiffAt ℝ ω angularDirection (z:E4) :=
    (hnorm.inv hp.ne').smul spatial_an.contDiffAt
  have hparams : ContDiffAt ℝ ω parameters (z:E4) :=
    (hnorm.sub contDiffAt_const).prodMk ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 3))).comp (z:E4) hdire)
  have hfn (f : ℝ × ℝ → ℝ) (hf : f ∈ [Advanced.gvv, Advanced.gvr, Advanced.grr, Advanced.angularScale,
        Advanced.potentialV, Advanced.potentialR]) : AM (fun x => f (parameters x)) z :=
    ((Advanced.coefficient_analytic harg hH f hf).contDiffAt).comp (z:E4) hparams
  have hvv := hfn _ (by simp : Advanced.gvv ∈ _)
  have hvr := hfn _ (by simp : Advanced.gvr ∈ _)
  have hrr := hfn _ (by simp : Advanced.grr ∈ _)
  have ha := hfn _ (by simp : Advanced.angularScale ∈ _)
  have hv := hfn _ (by simp : Advanced.potentialV ∈ _)
  have hav := hfn _ (by simp : Advanced.potentialR ∈ _)
  have hdr (i : Fin 4) : AM (fun x => dr x i) z := by
    refine Fin.cases (by exact contDiffAt_const) (fun j => ?_) i
    exact (contDiffAt_piLp_apply (p := 2) (i := j)).comp (z:E4) hdire
  have hpot (i : Fin 4) : AM (potential i) z :=
    (hv.mul contDiffAt_const).add (hav.mul (hdr i))
  refine ⟨?_, hpot, fun i j => (partial_an (hpot j) i).sub (partial_an (hpot i) j), ?_⟩
  · intro i j
    exact (((hvv.mul contDiffAt_const).mul contDiffAt_const).add
      (hvr.mul ((contDiffAt_const.mul (hdr j)).add ((hdr i).mul contDiffAt_const))) |>.add
      ((hrr.mul (hdr i)).mul (hdr j))).add
      ((ha.div (hnorm.pow 2) (pow_ne_zero 2 hp.ne')).mul (contDiffAt_const.sub ((hdr i).mul (hdr j))))
  · have hspace := ((hvr.div ((contDiffAt_const (c := (1:ℝ))).add (hrr.pow 2)) (by positivity)).neg.smul hdire)
    exact coordinate_an.contDiffAt.comp (z:E4) ((contDiffAt_const (c := (1:ℝ))).prodMk hspace)

end
end NoHair.TwoCentre.Model.Geo
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
noncomputable section

theorem val_diff (z : manifold) : HasMFDerivAt 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z
    (ContinuousLinearMap.id ℝ E4) := by
  have hd : MDifferentiableAt 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z :=
    contMDiff_subtype_val.mdifferentiableAt (n := (1:ℕ∞ω)) one_ne_zero
  have he : mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ,E4)) (x := z)
  exact he ▸ hd.hasMFDerivAt

theorem outer_open : IsOpen outerRegion := (isOpen_lt continuous_const spatial_an.continuous.norm).inter
  (isOpen_ne_fun spatial_an.continuous continuous_const)
theorem exterior_open : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance;fun_prop
  exact (isOpen_lt continuous_const (h (-1))).inter (isOpen_lt continuous_const (h 1))

theorem adv_mem {y : E4} (hy : y ∈ exterior) : toAdvanced y ∈ manifold := by
  obtain ⟨_,hm,_⟩ := Cartesian.exterior_and_frontier.2.1
  obtain ⟨hr,hn⟩ := hm hy
  exact ⟨lt_trans (by norm_num) hr,hn⟩

theorem chart_coe {y : E4} (hy : y ∈ exterior) : (Model.chart y:E4) = toAdvanced y := by
  have : toAdvanced y ∈ spacetime := adv_mem hy
  simp [Model.chart,this]

set_option backward.isDefEq.respectTransparency false in
theorem chart_der {y : E4} (hy : y ∈ exterior) :
    (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) Model.chart y : E4 →L[ℝ] E4) = fderiv ℝ toAdvanced y := by
  have he : (Subtype.val ∘ Model.chart : E4 → E4) =ᶠ[𝓝 y] toAdvanced :=
    Filter.mem_of_superset (exterior_open.mem_nhds hy) (fun _ h => chart_coe h)
  have cont := (ContMDiffAt.subtypeVal_comp_iff manifold Model.chart y).mp
    (((Cartesian.exterior_and_frontier.2.1.choose_spec.2.2.2.2.1 y hy).contMDiffAt (exterior_open.mem_nhds hy)).congr_of_eventuallyEq he)
  have hd := (val_diff (Model.chart y)).comp y (cont.mdifferentiableAt (by simp)).hasMFDerivAt
  have hh := (hasMFDerivAt_iff_hasFDerivAt.mp hd).fderiv
  exact hh.symm.trans he.fderiv_eq


end
end NoHair.TwoCentre.Model.Geo

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model NoHair.TwoCentre.Cartesian NoHair.AtlasBridge
open Set Filter Topology
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace NoHair.TwoCentre.Model.Transport
noncomputable section

def mg (z : E4) : M4 := Matrix.of (metricCoeffs z)
def ff (z : E4) : M4 := Matrix.of (faradayCoeffs z)

def basis := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
def jac (L : E4 →L[ℝ] E4) := LinearMap.toMatrix basis basis L.toLinearMap

theorem jac_apply (L : E4 →L[ℝ] E4) (a i : Fin 4) : jac L a i = L (coordBasis i) a := by
  simp [jac,LinearMap.toMatrix_apply,basis,coordBasis]

theorem jac_pair (L : E4 →L[ℝ] E4) (A : M4) (i j : Fin 4) :
    matrixBilin A (L (coordBasis i)) (L (coordBasis j)) = ((jac L).transpose * A * jac L) i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (L (coordBasis i))) (WithLp.ofLp (L (coordBasis j))) = _
  rw [Matrix.toLinearMap₂'_apply]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,jac_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro a _;apply Finset.sum_congr rfl;intro b _;ring

theorem jac_comp {f g : E4 → E4} {x : E4} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) (he : f ∘ g =ᶠ[𝓝 x] id) :
    jac (fderiv ℝ f (g x)) * jac (fderiv ℝ g x) = 1 := by
  have hd := (hf.hasFDerivAt.comp x hg.hasFDerivAt).congr_of_eventuallyEq he.symm
  have hl : (fderiv ℝ f (g x)).comp (fderiv ℝ g x) = ContinuousLinearMap.id ℝ E4 :=
    hd.unique (hasFDerivAt_id x)
  change LinearMap.toMatrix basis basis _ * LinearMap.toMatrix basis basis _ = _
  rw [← LinearMap.toMatrix_comp]
  change LinearMap.toMatrix basis basis ((fderiv ℝ f (g x)).comp (fderiv ℝ g x)).toLinearMap = _
  rw [hl]; exact LinearMap.toMatrix_id basis

theorem pair_chart {y : E4} (hy : y ∈ exterior) :
    let K := jac (fderiv ℝ toAdvanced y)
    isotropicMetric y = K.transpose * (mg (toAdvanced y)) * K ∧
    TwoCentre.field y = K.transpose * (ff (toAdvanced y)) * K := by
  obtain ⟨hg,hF⟩ := stationary_geometry.2.2.2.2.2.2.2 y hy
  constructor
  · rw [← hg]; ext i j;unfold pullbackCoeffs
    rw [Geo.chart_der hy]
    change matrixBilin (metricCoeffs (Model.chart y)) _ _ = _
    rw [Geo.chart_coe hy];exact jac_pair _ _ _ _
  · rw [← hF]; ext i j;unfold pullbackCoeffs
    rw [Geo.chart_der hy]
    change matrixBilin (faradayCoeffs (Model.chart y)) _ _ = _
    rw [Geo.chart_coe hy];exact jac_pair _ _ _ _

theorem congr_reverse {J K A B : M4} (h : B = K.transpose * A * K) (hk : K * J = 1) :
    A = J.transpose * B * J := by
  have ht := congrArg Matrix.transpose hk
  simp only [Matrix.transpose_mul,Matrix.transpose_one] at ht
  rw [h];symm
  calc
    _ = (J.transpose*K.transpose) * A * (K*J) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [ht,hk,Matrix.one_mul,Matrix.mul_one]

theorem iso_regular {y : E4} (hy : y ∈ exterior) :
    (∀ i j, SC (fun z => isotropicMetric z i j) y) ∧
    (∀ i j, SC (fun z => TwoCentre.field z i j) y) ∧
    (isotropicMetric y).det ≠ 0 := by
  have hc (b:ℝ) : SC (squaredDistance b) y := by unfold SC squaredDistance;fun_prop
  have hi (b:ℝ) (h : 0<squaredDistance b y) : SC (inverseDistance b) y :=
    (contDiffAt_const (c := (1:ℝ))).div ((hc b).sqrt h.ne') (Real.sqrt_pos.mpr h).ne'
  have hu : 0<harmonicPotential y := by unfold harmonicPotential inverseDistance;positivity
  have hs : SC harmonicPotential y := ((contDiffAt_const (c := (1:ℝ))).add (hi (-1) hy.1)).add (hi 1 hy.2)
  have he : SC electricPotential y := (contDiffAt_const (c := (1:ℝ))).div hs hu.ne'
  refine ⟨?_,?_,?_⟩
  · intro i j
    by_cases hij : i=j
    · subst j;simp only [isotropicMetric,Matrix.diagonal_apply_eq]
      by_cases hz : i=0
      · simp only [hz,if_true];exact ((contDiffAt_const (c := (1:ℝ))).div (hs.pow 2) (pow_ne_zero _ hu.ne')).neg
      · simp only [hz,if_false];exact hs.pow 2
    · simp only [isotropicMetric,Matrix.diagonal_apply_ne _ hij];exact contDiffAt_const
  · intro i j
    have hd (a : Fin 4) := partial_smooth he a
    unfold TwoCentre.field;by_cases hz : i=0 <;> by_cases hw : j=0 <;> simp only [hz,hw,if_true,if_false] <;> unfold SC <;> fun_prop
  · rw [isotropicMetric,Matrix.det_diagonal,Finset.prod_ne_zero_iff]
    intro i _;split
    · exact neg_ne_zero.mpr (div_ne_zero one_ne_zero (pow_ne_zero 2 hu.ne'))
    · exact pow_ne_zero 2 hu.ne'

theorem iso_sym (y : E4) : (isotropicMetric y).transpose = isotropicMetric y := Matrix.diagonal_transpose _
theorem iso_anti (y : E4) (a b : Fin 4) : TwoCentre.field y a b = -TwoCentre.field y b a := by unfold TwoCentre.field;ring
theorem adv_sym (z : E4) : (mg z).transpose = metricCoeffs z := by
  ext i j;change metricCoeffs z j i = metricCoeffs z i j
  have he : spatialDelta j i = spatialDelta i j := by
    unfold spatialDelta;by_cases hij : i=j <;> simp [hij,Ne.symm]
  unfold metricCoeffs;rw [he];ring

theorem adv_anti (z : E4) (a b : Fin 4) : faradayCoeffs z a b = -faradayCoeffs z b a := by unfold faradayCoeffs;ring

theorem encoded_smooth {S : Set E4} {f : E4 → ℝ} (h : ∀ x ∈ S, SC f x) :
    ContDiffOn ℝ ∞ (fun p : Pt => f (WithLp.toLp 2 p)) (encodeSet S) := by
  intro p hp;exact ((h _ hp).comp p (pack.contDiff.contDiffAt)).contDiffWithinAt

theorem encoded_open {S : Set E4} (h : IsOpen S) : IsOpen (encodeSet S) := h.preimage pack.continuous


open ExactVacuumAtlas.EinsteinMaxwell in
theorem equations (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z := by
  change ∀ z ∈ outerRegion, EinsteinMaxwellAt mg ff z
  obtain ⟨χ,hf,hb,hl,hr,hfs,hbs⟩ := Cartesian.exterior_and_frontier.2.1
  let U := encodeSet outerRegion
  let V := encodeSet exterior
  let Φ (p : Pt) := (χ (WithLp.toLp 2 p)).ofLp
  let J (p : Pt) := jac (fderiv ℝ χ (WithLp.toLp 2 p))
  let K (p : Pt) := jac (fderiv ℝ toAdvanced (χ (WithLp.toLp 2 p)))
  have hχ (z : E4) (hz : z ∈ outerRegion) : ContDiffAt ℝ ∞ χ z :=
    ((hbs z hz).contMDiffAt (Geo.outer_open.mem_nhds hz)).contDiffAt
  have hadv (x : E4) (hx : x ∈ exterior) : ContDiffAt ℝ ∞ toAdvanced x :=
    ((hfs x hx).contMDiffAt (Geo.exterior_open.mem_nhds hx)).contDiffAt
  have hback (p : Pt) (hp : p ∈ U) : J p * K p = 1 := by
    let z := WithLp.toLp 2 p
    have hx := hb hp
    have hd : DifferentiableAt ℝ χ (toAdvanced (χ z)) := by rw [hr hp];exact (hχ z hp).differentiableAt (by simp)
    have eq : χ ∘ toAdvanced =ᶠ[𝓝 (χ z)] id := Filter.mem_of_superset (Geo.exterior_open.mem_nhds hx) (fun x hx => hl hx)
    have e := jac_comp hd ((hadv _ hx).differentiableAt (by simp)) eq
    rw [hr hp] at e;exact e
  have hfor (p : Pt) (hp : p ∈ U) : K p * J p = 1 :=
    mul_eq_one_comm.mp (hback p hp)
  have hc : ExactVacuumAtlas.CoordChange U V Φ J K := by
    refine ⟨encoded_open Geo.outer_open, encoded_open Geo.exterior_open,?_, ?_, ?_, hback⟩
    · intro p hp
      exact (unpack.contDiff.contDiffAt.comp p ((hχ _ hp).comp p pack.contDiff.contDiffAt)).contDiffWithinAt
    · intro p hp;exact hb hp
    · intro p hp k i
      let L : E4 →L[ℝ] ℝ := EuclideanSpace.proj k
      have hh : HasFDerivAt (L ∘ χ) (L.comp (fderiv ℝ χ (WithLp.toLp 2 p))) (WithLp.toLp 2 (Function.update p i (p i))) := by
        simpa using (L.hasFDerivAt.comp _ ((hχ _ hp).differentiableAt (by simp)).hasFDerivAt)
      rw [show J p k i = fderiv ℝ χ (WithLp.toLp 2 p) (coordBasis i) k from jac_apply _ _ _]
      exact hh.comp_hasDerivAt (p i) (coord_slice p i)
  have hm : ExactVacuumAtlas.MetricData (enc isotropicMetric) (enc (invMetric isotropicMetric)) V := by
    refine ⟨encoded_open Geo.exterior_open,?_,?_,?_,?_⟩
    · intro p _ i j;exact congrFun (congrFun (iso_sym _) j) i
    · intro p hp;exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (iso_regular hp).2.2)
    · intro i j; exact encoded_smooth (fun y hy => (iso_regular hy).1 i j)
    · intro i j; exact encoded_smooth (fun y hy => inv_smooth (iso_regular hy).1 (iso_regular hy).2.2 i j)
  have hFs (i j : Fin 4) : ContDiffOn ℝ ∞ (enc TwoCentre.field i j) V :=
    encoded_smooth (fun y hy => (iso_regular hy).2.1 i j)
  have pair (p : Pt) (hp : p ∈ U) :
      (mg (WithLp.toLp 2 p)) = (J p).transpose * isotropicMetric (χ (WithLp.toLp 2 p)) * J p ∧
      (ff (WithLp.toLp 2 p)) = (J p).transpose * TwoCentre.field (χ (WithLp.toLp 2 p)) * J p := by
    have hh := pair_chart (hb hp)
    rw [hr hp] at hh
    exact ⟨congr_reverse hh.1 (hfor p hp),congr_reverse hh.2 (hfor p hp)⟩
  have hg (p : Pt) (hp : p ∈ U) :
      ExactVacuumAtlas.metricMatrix (enc mg) p = (J p).transpose * ExactVacuumAtlas.metricMatrix (enc isotropicMetric) (Φ p) * J p :=
    (pair p hp).1
  have hF (p : Pt) (hp : p ∈ U) :
      ExactVacuumAtlas.metricMatrix (enc ff) p = (J p).transpose * ExactVacuumAtlas.metricMatrix (enc TwoCentre.field) (Φ p) * J p :=
    (pair p hp).2
  have hgi (p : Pt) (hp : p ∈ U) :
      ExactVacuumAtlas.metricMatrix (enc (invMetric mg)) p =
      K p * ExactVacuumAtlas.metricMatrix (enc (invMetric isotropicMetric)) (Φ p) * (K p).transpose := by
    change (mg (WithLp.toLp 2 p))⁻¹ = K p * (isotropicMetric (χ (WithLp.toLp 2 p)))⁻¹ * (K p).transpose
    rw [(pair p hp).1,Matrix.mul_inv_rev,Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,Matrix.inv_eq_right_inv (hback p hp),Matrix.mul_assoc]
  have reg (z : E4) (hz : z ∈ outerRegion) := Geo.reg_data (⟨z,⟨lt_trans (by norm_num : (3:ℝ)/4<1) hz.1,hz.2⟩⟩ : manifold)
  have gs (z : E4) (hz : z ∈ outerRegion) (i j : Fin 4) : SC (fun x => mg x i j) z := ((reg z hz).1 i j).of_le (by simp)
  have fs (z : E4) (hz : z ∈ outerRegion) (i j : Fin 4) : SC (fun x => ff x i j) z := ((reg z hz).2.2.1 i j).of_le (by simp)
  intro z hz
  let p : Pt := z.ofLp
  have hp : p ∈ U := hz
  have hx : WithLp.toLp 2 (Φ p) ∈ exterior := hb hp
  have src := h _ hx
  have rs := iso_regular hx
  have hn : (mg z).det ≠ 0 := by
    have e := congrArg Matrix.det (pair p hp).1
    simp only [Matrix.det_mul,Matrix.det_transpose] at e
    change (mg (WithLp.toLp 2 p)).det ≠ 0
    rw [e]
    exact mul_ne_zero (mul_ne_zero (Matrix.det_ne_zero_of_right_inverse (hback p hp)) rs.2.2) (Matrix.det_ne_zero_of_right_inverse (hback p hp))
  have E (i j : Fin 4) : einsteinMaxwell (enc isotropicMetric) (enc (invMetric isotropicMetric)) (enc TwoCentre.field) i j (Φ p) = 0 := by
    rw [ein_bridge Geo.exterior_open (fun y hy => (iso_regular hy).1) (fun y _ => iso_sym y) hx rs.2.2,src.1 i j,sub_self]
  have D (i : Fin 4) : maxwellDiv (enc isotropicMetric) (enc (invMetric isotropicMetric)) (enc TwoCentre.field) i (Φ p)=0 := by
    have e := div_bridge Geo.exterior_open (fun y _ => iso_sym y) hx rs.1 rs.2.1 rs.2.2 (iso_anti _) i
    have hd : divDensity isotropicMetric TwoCentre.field i (WithLp.toLp 2 (Φ p))=0 := src.2.1 i
    have hv : volume isotropicMetric (WithLp.toLp 2 (Φ p)) ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr rs.2.2)).ne'
    exact (mul_eq_zero.mp (e.symm.trans hd)).resolve_left hv
  have B (i j k : Fin 4) : faradayCyclic (enc TwoCentre.field) i j k (Φ p)=0 := (cyclic_bridge rs.2.1 i j k).trans (src.2.2 i j k)
  refine ⟨?_,?_,?_⟩
  · intro i j
    have e := ExactVacuumAtlas.Variation.einsteinMaxwell_transform hc hm hg hgi hF hp
    have zz : Matrix.of (fun a b => einsteinMaxwell (enc isotropicMetric) (enc (invMetric isotropicMetric)) (enc TwoCentre.field) a b (Φ p)) = (0:M4) := by ext a b;exact E a b
    rw [zz,Matrix.mul_zero,Matrix.zero_mul] at e
    have em := congrFun (congrFun e i) j
    change einsteinMaxwell (enc mg) (enc (invMetric mg)) (enc ff) i j p=0 at em
    exact sub_eq_zero.mp ((ein_bridge (G:=mg) (F:=ff) (p:=p) Geo.outer_open gs (fun y _ => adv_sym y) hp hn i j).symm.trans em)
  · intro j
    change divDensity mg ff j (WithLp.toLp 2 p) = 0
    rw [div_bridge (G:=mg) (F:=ff) (p:=p) Geo.outer_open (fun y _ => adv_sym y) hp (gs z hz) (fs z hz) hn (adv_anti _) j,
      ExactVacuumAtlas.Variation.maxwellDiv_transform hc hm hFs hg hgi hF hp]
    simp [D]
  · intro a b c
    have e := ExactVacuumAtlas.Variation.faradayCyclic_transform hc hFs (fun x _ => iso_anti _) hF hp a b c
    simp only [B,mul_zero,Finset.sum_const_zero] at e
    exact (cyclic_bridge (p:=p) (fs z hz) a b c).symm.trans e

end
end NoHair.TwoCentre.Model.Transport
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model

theorem solution (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z := Transport.equations h
