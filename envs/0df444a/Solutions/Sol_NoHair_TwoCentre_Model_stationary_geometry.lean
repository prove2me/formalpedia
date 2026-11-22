-- Prove2me | solution 1 for NoHair.TwoCentre.Model.stationary_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:47:44.067052+00:00
-- url     : https://prove2.me/submissions/7b024e1a-ef6a-4087-8350-691468eb74eb

import Definitions.Def_NoHair_TwoCentreIsotropic
import Definitions.Def_NoHair_TwoCentreBlackHole
import Theorems.Thm_NoHair_TwoCentre_Advanced_regular_horizon
import Theorems.Thm_NoHair_TwoCentre_Cartesian_exterior_and_frontier

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

theorem matrix_basis (A : Mat4) (i j : Fin 4) : matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = A i j
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, Finset.sum_ite_eq']

theorem atlas_id {c : OpenPartialHomeomorph manifold E4} (hc : c ∈ atlas E4 manifold) {y : E4}
    (hy : y ∈ c.target) :
    (c.symm y : E4) = y ∧ (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) c.symm y : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
  obtain ⟨p,hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : manifold) : c = chartAt E4 x := hp.trans (by rfl)
  have hval : (c.symm y : E4) = y := by
    have eqval (x : manifold) : c x = x.val := by rw [hchart x]; rfl
    exact (eqval (c.symm y)).symm.trans (c.right_inv hy)
  refine ⟨hval,?_⟩
  have d := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ,E4)) (x := c.symm y)
  simp only [modelWithCornersSelf_coe,range_id,mfderivWithin_univ] at d
  rw [hchart (c.symm y), ← hval]
  exact d

theorem smooth_of_components (A : E4 → Mat4) (hA : ∀ z : manifold, ∀ i j, AM (fun y => A y i j) z) :
    IsSmoothBilinField (fun z : manifold => matrixBilin (A z)) := by
  intro c hc i j y hy
  have hh : EqOn (fun w => pullbackCoeffs (M := manifold) (fun z => matrixBilin (A z)) c.symm w i j)
      (fun w => A w i j) c.target := by
    intro w hw
    obtain ⟨hv,hder⟩ := atlas_id hc hw
    change pullbackCoeffs (M := manifold) (fun z => matrixBilin (A z)) c.symm w i j = A w i j
    unfold pullbackCoeffs
    rw [hder]
    change matrixBilin (A (c.symm w : E4)) (coordBasis i) (coordBasis j) = A w i j
    rw [hv,matrix_basis]
  have hf := (hA (c.symm y) i j).of_le (show (∞ : ℕ∞ω) ≤ ω by simp)
  rw [(atlas_id hc hy).1] at hf
  exact hf.contDiffWithinAt.congr_of_eventuallyEq (hh.eventuallyEq_of_mem (c.open_target.mem_nhds hy) |>.filter_mono nhdsWithin_le_nhds) (hh hy)

theorem antisymmetric : IsTwoForm faraday := by
  intro z v w
  let A : Mat4 := faradayCoeffs z
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (v : E4)) (WithLp.ofLp (w : E4)) =
    -Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (w : E4)) (WithLp.ofLp (v : E4))
  rw [Matrix.toLinearMap₂'_apply (R := ℝ) A (WithLp.ofLp (v : E4)) (WithLp.ofLp (w : E4)),
    Matrix.toLinearMap₂'_apply (R := ℝ) A (WithLp.ofLp (w : E4)) (WithLp.ofLp (v : E4))]
  simp only [Fin.sum_univ_four, smul_eq_mul, A, faradayCoeffs]
  ring

end
end NoHair.TwoCentre.Model.Geo

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Geo
noncomputable section

theorem frame_metric (z : manifold) :
    ∃ liftV : E4 → E4, ∀ v w, metric z (liftV v) (liftV w) = -(v 0*w 0) + ⟪spatial v,spatial w⟫ := by
  obtain ⟨hρ,harg,hH,hH0⟩ := radius_data z
  let p := parameters z
  let a := Advanced.gvv p
  let b := Advanced.gvr p
  let d := Advanced.grr p
  let n := angularDirection z
  let k := ‖spatial z‖ / Advanced.H p
  let ℓ := d / (b+1)
  have hb : 0 < b := div_pos (sq_pos_of_pos hH0) (sq_pos_of_pos hH)
  have hdet : a*d - b^2 = -1 := Advanced.determinant hH.ne' (Advanced.gap_factor harg)
  have hℓ₁ : a*ℓ = b-1 := by dsimp [ℓ];field_simp [show b+1≠0 by linarith];nlinarith
  have hℓ₂ : (b+1)*ℓ=d := by dsimp [ℓ]; field_simp [show b+1≠0 by linarith]
  have hnn : ⟪n,n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, show ‖n‖=1 from param_norm hρ];norm_num
  let R := fun v : E4 => ⟪n,spatial v⟫
  let P := fun v : E4 => spatial v - R v • n
  let U := fun v : E4 => v 0 + R v
  let W := fun v : E4 => (R v - v 0 - a*U v)/2
  let V := fun v : E4 => U v - ℓ*W v
  let liftV := fun v : E4 => coordinates (V v) (W v • n + k • P v)
  have hp (v : E4) : ⟪n,P v⟫ = 0 := by simp only [P,R,inner_sub_right,real_inner_smul_right,hnn,mul_one,sub_self]
  have hpp (v w : E4) : ⟪P v,P w⟫ = ⟪spatial v,spatial w⟫ - R v*R w := by
    simp only [P,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hnn,
      real_inner_comm (spatial v) n,R]
    ring
  have hspace (v : E4) : spatial (liftV v) = W v • n + k • P v := spatial_coordinates _ _
  have hr (v : E4) : Curves.radialSpeed z (liftV v) = W v := by
    change ⟪n,spatial (liftV v)⟫ = W v
    rw [hspace,inner_add_right,real_inner_smul_right,real_inner_smul_right,hnn,hp]
    ring
  have hpair (v w : E4) : ⟪spatial (liftV v),spatial (liftV w)⟫- W v*W w =
      k^2*(⟪spatial v,spatial w⟫-R v*R w) := by
    rw [hspace,hspace]
    have hpn : ⟪P v,n⟫ = 0 := (real_inner_comm _ _).trans (hp v)
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,hnn,hp,
      hpn,hpp]
    ring
  have scale : Advanced.angularScale p / ‖spatial z‖ ^ 2 * k^2 = 1 := by
    have hHp : Advanced.H p ≠ 0 := hH.ne'
    dsimp only [Advanced.angularScale,k];field_simp [hHp,hρ.ne']
  refine ⟨liftV,?_⟩
  intro v w
  rw [Curves.metric_eval,hr,hr,hpair]
  change a*V v*V w + b*(V v*W w+W v*V w)+d*W v*W w +
    (Advanced.angularScale p / ‖spatial z‖^2)*(k^2*_) = _
  rw [← mul_assoc,scale,one_mul]
  have ht : a*V v*V w+b*(V v*W w+W v*V w)+d*W v*W w =
      a*U v*U w + U v*W w + W v*U w := by
    change a*(U v-ℓ*W v)*(U w-ℓ*W w)+b*((U v-ℓ*W v)*W w+W v*(U w-ℓ*W w))+d*W v*W w = _
    linear_combination (-U v*W w-W v*U w+ℓ*W v*W w)*hℓ₁ - (W v*W w)*hℓ₂
  rw [ht]
  dsimp [U,W]
  ring

theorem lorentzian : IsLorentzian metric := by
  intro z
  obtain ⟨liftV, h⟩ := frame_metric z
  let B : E4 →L[ℝ] E4 →L[ℝ] ℝ := metric z
  let f := fun i => liftV (coordBasis i)
  have orth (i j : Fin 4) : B (f i) (f j) = minkowski i j := by
    change metric z (liftV (coordBasis i)) (liftV (coordBasis j)) = _
    rw [h,Curves.spatial_inner]
    fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [coordBasis,minkowski,Matrix.diagonal]
  have independent : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have eq := congrArg (fun x : E4 => B (f j) x) hc
    simp only [map_sum,map_smul,orth,smul_eq_mul,map_zero] at eq
    fin_cases j <;> simpa [Fin.sum_univ_four,minkowski,Matrix.diagonal] using eq
  have hc : Fintype.card (Fin 4) = Module.finrank ℝ E4 := by simp
  let basis := basisOfLinearIndependentOfCardEqFinrank independent hc
  refine ⟨basis,?_⟩
  intro i j
  change B (basis i) (basis j) = _
  simpa [basis,coe_basisOfLinearIndependentOfCardEqFinrank] using orth i j

theorem orientation_valid : IsTimeOrientation metric orientation := by
  constructor
  · apply continuous_iff_continuousAt.mpr
    intro z
    apply (FiberBundle.continuousAt_section E4 z).2
    have he (x : manifold) : (trivializationAt E4 (TangentSpace 𝓘(ℝ,E4)) z
        (⟨x,orientation x⟩ : TangentBundle 𝓘(ℝ,E4) manifold)).2 = (orientation x : E4) := by
      change tangentCoordChange 𝓘(ℝ,E4) x z x (orientation x) = orientation x
      have same : achart E4 z = achart E4 x := by rfl
      unfold tangentCoordChange
      rw [same]
      exact (tangentBundleCore 𝓘(ℝ,E4) manifold).coordChange_self (achart E4 x) x (mem_achart_source E4 x) _
    simp_rw [he]
    exact (reg_data z).2.2.2.continuousAt.comp continuous_subtype_val.continuousAt
  · intro z
    obtain ⟨hρ,_,hH,hH0⟩ := radius_data z
    let p := parameters z
    let α := Advanced.gvr p/(1+Advanced.grr p^2)
    have hb : 0 < Advanced.gvr p := div_pos (sq_pos_of_pos hH0) (sq_pos_of_pos hH)
    have hα : 0 < α := div_pos hb (by positivity)
    have ha0 : Advanced.gvv p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)
    let T : E4 := orientation z
    change metric z T T < 0
    have hT : spatial T = -α • angularDirection z := spatial_coordinates _ _
    have hr : Curves.radialSpeed z T = -α := by
      change ⟪angularDirection z, spatial T⟫ = -α
      rw [hT,real_inner_smul_right,real_inner_self_eq_norm_sq,Curves.angular_unit]
      ring
    have hss : ⟪spatial T,spatial T⟫ = α^2 := by
      rw [hT,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,Curves.angular_unit]
      ring
    rw [Curves.metric_eval,hr,hss]
    change Advanced.gvv p * 1 * 1 + Advanced.gvr p*(1 * -α + -α*1)+Advanced.grr p*(-α)*(-α) + _*(α^2-(-α)*(-α)) < 0
    have hrel : α*(1+Advanced.grr p^2) = Advanced.gvr p := by dsimp [α];field_simp
    have hle : Advanced.grr p ≤ 1+Advanced.grr p^2 := by nlinarith [sq_nonneg (Advanced.grr p-1/2)]
    nlinarith [mul_le_mul_of_nonneg_left hle (sq_nonneg α),mul_pos hα hb,congrArg (α * ·) hrel]

end
end NoHair.TwoCentre.Model.Geo

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
noncomputable section

theorem spatial_shift (s : ℝ) (z : E4) : spatial (z+s • coordBasis 0) = spatial z := by
  ext i; simp [spatial,coordBasis]

theorem flow_val (s : ℝ) (z : manifold) : (flow s z : E4) = (z:E4) + s • coordBasis 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [flow,coordBasis,coordinates,spatial]

theorem val_diff (z : manifold) : HasMFDerivAt 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z
    (ContinuousLinearMap.id ℝ E4) := by
  have hd : MDifferentiableAt 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z :=
    contMDiff_subtype_val.mdifferentiableAt (n := (1:ℕ∞ω)) one_ne_zero
  have he : mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ,E4)) (x := z)
  exact he ▸ hd.hasMFDerivAt

theorem flow_smooth :
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E4)) 𝓘(ℝ,E4) ∞ (fun p : ℝ × manifold => flow p.1 p.2) := by
  apply (ContMDiff.subtypeVal_comp_iff manifold _).1
  change ContMDiff _ _ _ (fun p : ℝ × manifold => (flow p.1 p.2 : E4))
  simp only [flow_val]
  exact (contMDiff_subtype_val.comp contMDiff_snd).add (contMDiff_fst.smul contMDiff_const)

set_option backward.isDefEq.respectTransparency false in
theorem flow_diff (s : ℝ) (z : manifold) : (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (flow s) z : E4 →L[ℝ] E4) =
    ContinuousLinearMap.id ℝ E4 := by
  have hs : ContMDiff 𝓘(ℝ,E4) 𝓘(ℝ,E4) ∞ (flow s) :=
    flow_smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have h := (val_diff (flow s z)).comp z (hs.mdifferentiableAt (by simp)).hasMFDerivAt
  have ht : HasFDerivAt (fun x : E4 => x+s • coordBasis 0) (ContinuousLinearMap.id ℝ E4) (z:E4) :=
    (hasFDerivAt_id _).add_const _
  have hot := (hasMFDerivAt_iff_hasFDerivAt.mpr ht).comp z (val_diff z)
  have he : (Subtype.val ∘ flow s : manifold → E4) = (fun x : E4 => x+s • coordBasis 0) ∘ Subtype.val := funext (flow_val s)
  rw [he] at h
  exact h.mfderiv.symm.trans hot.mfderiv

set_option backward.isDefEq.respectTransparency false in
theorem flow_gen (z : manifold) : (flowGenerator flow z : E4) = coordBasis 0 := by
  have hs : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E4) ∞ (fun s : ℝ => flow s z) :=
    flow_smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have h := (val_diff (flow 0 z)).comp 0 (hs.mdifferentiableAt (by simp)).hasMFDerivAt
  have ht : HasDerivAt (fun s : ℝ => (z:E4)+s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordBasis 0)).const_add (z:E4)
  have he : (Subtype.val ∘ (fun s : ℝ => flow s z) : ℝ → E4) = fun s => (z:E4)+s • coordBasis 0 :=
    funext (fun s => flow_val s z)
  rw [he] at h
  exact (hasMFDerivAt_iff_hasFDerivAt.mp h).hasDerivAt.unique ht

theorem flow_symmetry : IsSymmetryFlow metric faraday flow := by
  have pot (s : ℝ) (i : Fin 4) (z : E4) : potential i (z+s • coordBasis 0) = potential i z := by
    simp [potential,parameters,dr,angularDirection,spatial_shift]
  have dpot (s : ℝ) (i j : Fin 4) (z : E4) : coordPartial (potential i) j (z+s • coordBasis 0) =
      coordPartial (potential i) j z := by
    apply congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis j))
    rw [← fderiv_comp_add_right (f := potential i) (s • coordBasis 0), funext (pot s i)]
  refine ⟨?_,?_,flow_smooth,?_,?_⟩
  · intro z; apply Subtype.ext; simp [flow_val]
  · intro s t z; apply Subtype.ext; simp only [flow_val,add_smul]; abel
  · intro s z v w
    rw [flow_diff]
    change matrixBilin (metricCoeffs (flow s z)) v w = matrixBilin (metricCoeffs z) v w
    have he : metricCoeffs (flow s z) = metricCoeffs z := by funext i j; simp [flow_val,metricCoeffs,dr,parameters,angularDirection,spatial_shift]
    rw [he]
  · intro s z v w
    rw [flow_diff]
    change matrixBilin (faradayCoeffs (flow s z)) v w = matrixBilin (faradayCoeffs z) v w
    have he : faradayCoeffs (flow s z) = faradayCoeffs z := by funext i j; simp [flow_val,faradayCoeffs,dpot]
    rw [he]

theorem line_deriv (y v : E4) : HasDerivAt (fun t : ℝ => y+t • v) v 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y

def spatialL : E4 →L[ℝ] E3 := LinearMap.toContinuousLinearMap {
  toFun := spatial, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl }

theorem norm_der {f : ℝ → E3} {v : E3} {t : ℝ} (h : HasDerivAt f v t) (hn : 0 < ‖f t‖) :
    HasDerivAt (fun s => ‖f s‖) ⟪‖f t‖⁻¹ • f t,v⟫ t := by
  have hs := h.norm_sq.sqrt (pow_ne_zero 2 hn.ne')
  simp only [Real.sqrt_sq (norm_nonneg _)] at hs
  convert! hs using 1
  rw [real_inner_smul_left]
  field_simp
  <;> ring

theorem shift_der {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt timeShift ((1+(3/2:ℝ)*r)^2/r^2) r := by
  have h : HasDerivAt timeShift (9 * 1 / 4 + 3 * r⁻¹ - (0 * r - 1 * 1)/r^2) r := by
    unfold timeShift
    exact ((((hasDerivAt_id r).const_mul 9).div_const 4).add ((Real.hasDerivAt_log hr).const_mul 3)).sub
      ((hasDerivAt_const r (1:ℝ)).div (hasDerivAt_id r) hr)
  convert h using 1
  field_simp
  <;> ring

theorem partial_from_line {f : E4 → ℝ} {z v : E4} {k : ℝ}
    (hd : DifferentiableAt ℝ f z) (h : HasDerivAt (fun t : ℝ => f (z+t • v)) k 0) :
    fderiv ℝ f z v = k := by
  have hd' : HasFDerivAt f (fderiv ℝ f z) (z+(0:ℝ) • v) := by simpa using hd.hasFDerivAt
  exact (hd'.comp_hasDerivAt 0 (line_deriv z v)).unique h

theorem second_symm {f : E4 → ℝ} {z : E4} (hf : AM f z) (i j : Fin 4) :
    coordPartial (coordPartial f i) j z = coordPartial (coordPartial f j) i z := by
  have hd := (hf.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)
  have ev (k l : Fin 4) : coordPartial (coordPartial f k) l z =
      fderiv ℝ (fderiv ℝ f) z (coordBasis l) (coordBasis k) := by
    unfold coordPartial
    let A := ContinuousLinearMap.apply ℝ ℝ (coordBasis k)
    have h := A.hasFDerivAt.comp z hd.hasFDerivAt
    exact DFunLike.congr_fun h.fderiv (coordBasis l)
  rw [ev,ev]
  exact hf.isSymmSndFDerivAt_of_omega _ _

def staticTime (z : E4) := z 0-timeShift (‖spatial z‖-1)
theorem outer_open : IsOpen outerRegion := (isOpen_lt continuous_const spatial_an.continuous.norm).inter
  (isOpen_ne_fun spatial_an.continuous continuous_const)

theorem time_an {z : E4} (hz : z ∈ outerRegion) : AM staticTime z := by
  have hs : 0 < ‖spatial z‖ := by linarith [hz.1]
  have hnr := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hs)
  have hr : ‖spatial z‖ - 1 ≠ 0 := (sub_pos.mpr hz.1).ne'
  have hf : ContDiffAt ℝ ω timeShift (‖spatial z‖-1) := by unfold timeShift;fun_prop (disch := assumption)
  have hnr2 : ContDiffAt ℝ ω (fun x => ‖spatial x‖ - 1) z := hnr.sub contDiffAt_const
  have hh := ContDiffAt.comp (g := timeShift) (f := fun x : E4 => ‖spatial x‖-1) z hf hnr2
  exact (contDiffAt_piLp_apply (p := 2) (i := (0:Fin 4))).sub hh

theorem time_partial {z : E4} (hz : z ∈ outerRegion) (i : Fin 4) :
    coordPartial staticTime i z = dt i - (Advanced.H₀ (parameters z)^2/(‖spatial z‖-1)^2) * dr z i := by
  let v := coordBasis i
  let x := fun t : ℝ => z+t • v
  have hx := line_deriv z v
  have hx0 : x 0 = z := by simp [x]
  have hxs := spatialL.hasFDerivAt.comp_hasDerivAt 0 hx
  have hn : 0 < ‖spatial (x 0)‖ := by rw [hx0];linarith [hz.1]
  have hr := (norm_der (f := fun t => spatial (x t)) hxs hn).sub_const 1
  have hshift := (shift_der (r := ‖spatial (x 0)‖-1) (by rw [hx0];exact (sub_pos.mpr hz.1).ne')).comp 0 hr
  have ht := (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt 0 hx
  apply partial_from_line (time_an hz |>.differentiableAt (by simp))
  convert! ht.sub hshift using 1
  dsimp only [Function.comp_apply,spatialL] at *
  rw [hx0]
  have hrad : ⟪angularDirection z,spatial v⟫ = dr z i := by
    change Curves.radialSpeed z (coordBasis i) = dr z i
    have he := Curves.spatial_inner (coordinates 0 (angularDirection z)) (coordBasis i)
    rw [spatial_coordinates] at he
    change ⟪angularDirection z,spatial (coordBasis i)⟫ = _
    rw [he]
    fin_cases i <;> simp (config := {decide := true}) [coordBasis,dr,coordinates] <;> rfl
  have ht0 : v 0 = dt i := by fin_cases i <;> simp [v,dt,coordBasis]
  change _ = v 0 - ((1 + 3/2 * (‖spatial z‖-1))^2 / (‖spatial z‖-1)^2) * ⟪angularDirection z,spatial v⟫
  rw [hrad,ht0]
  rfl

theorem partial_prod {f g : E4 → ℝ} {y : E4} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (i : Fin 4) :
    coordPartial (fun z => f z * g z) i y = coordPartial f i y * g y + f y * coordPartial g i y := by
  have h := DFunLike.congr_fun (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv (coordBasis i)
  change fderiv ℝ (f * g) y (coordBasis i) = _
  rw [h]
  simp [coordPartial,smul_eq_mul]
  <;> ring

theorem staticity : IsStaticOn metric flow outer := by
  intro c hc y hy ho l i j
  let k := fun z => loweredCoeffs metric (flowGenerator flow) c.symm z
  let a := fun z : E4 => Advanced.gvv (parameters z)
  have heq {w : E4} (hw : w ∈ c.target) (houter : w ∈ outerRegion) (i : Fin 4) :
      k w i = a w * coordPartial staticTime i w := by
    obtain ⟨hv,hd⟩ := atlas_id hc hw
    change metric (c.symm w) (flowGenerator flow (c.symm w)) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) c.symm w (coordBasis i)) = _
    rw [flow_gen,hd]
    change matrixBilin (metricCoeffs (c.symm w):Mat4) (coordBasis 0) (coordBasis i) = _
    rw [hv, matrix_basis (metricCoeffs w : Mat4),time_partial houter i]
    have hH := (radius_data (c.symm w)).2.2.1
    rw [hv] at hH
    have hr : ‖spatial w‖-1 ≠ 0 := (sub_pos.mpr houter.1).ne'
    have dr0 : dr w 0 = 0 := rfl
    have del : spatialDelta 0 i = 0 := by simp [spatialDelta]
    simp only [metricCoeffs,show dt 0=1 from rfl,dr0,del,zero_mul,mul_zero,mul_one,one_mul,add_zero,sub_zero,neg_zero]
    dsimp [a,Advanced.gvv,Advanced.gvr,parameters] at *
    field_simp [hr, hH.ne']
    <;> ring
  have houter : y ∈ outerRegion := (atlas_id hc hy).1 ▸ ho
  have hw := heq hy houter
  have ha : AM a y := by
    obtain ⟨_,harg,hH,_⟩ := radius_data (c.symm y)
    rw [(atlas_id hc hy).1] at harg hH
    have hs : 0 < ‖spatial y‖ := by linarith [houter.1]
    have hn := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hs)
    have dir : ContDiffAt ℝ ω angularDirection y := (hn.inv hs.ne').smul spatial_an.contDiffAt
    have hp : ContDiffAt ℝ ω parameters y := (hn.sub contDiffAt_const).prodMk ((contDiffAt_piLp_apply (p := 2) (i := (0:Fin 3))).comp y dir)
    exact ((Advanced.coefficient_analytic harg hH _ (by simp : Advanced.gvv ∈ _)).contDiffAt).comp y hp
  have htime := time_an houter
  have d (u v : Fin 4) : coordPartial (fun z => k z u) v y =
      coordPartial a v y * coordPartial staticTime u y + a y * coordPartial (coordPartial staticTime u) v y := by
    have ev : (fun z => k z u) =ᶠ[𝓝 y] (fun z => a z*coordPartial staticTime u z) := by
      filter_upwards [c.open_target.mem_nhds hy,outer_open.mem_nhds houter] with z h1 h2
      exact heq h1 h2 u
    exact (congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis v)) ev.fderiv_eq).trans
      (partial_prod (ha.differentiableAt (by simp)) ((partial_an htime u).differentiableAt (by simp)) v)

  change k y l * (coordPartial (fun z => k z j) i y - coordPartial (fun z => k z i) j y) +
    k y i * (coordPartial (fun z => k z l) j y - coordPartial (fun z => k z j) l y) +
    k y j * (coordPartial (fun z => k z i) l y - coordPartial (fun z => k z l) i y) = 0
  simp only [d, hw]
  rw [second_symm htime j i,second_symm htime l j,second_symm htime i l]
  ring

end
end NoHair.TwoCentre.Model.Geo

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
noncomputable section

def sourceA (y : E4) := spatial y + unitAxis
def sourceR (y : E4) := ‖sourceA y‖
def sourceN (y : E4) := (sourceR y)⁻¹ • sourceA y
def sourceSpeed (y v : E4) := ⟪sourceN y,spatial v⟫

theorem dist_squared (c : ℝ) (y : E4) :
    ‖spatial y - c • unitAxis‖^2 = squaredDistance c y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spatial, unitAxis, squaredDistance, PiLp.sub_apply, PiLp.smul_apply]

theorem exterior_open : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance;fun_prop
  exact (isOpen_lt continuous_const (h (-1))).inter (isOpen_lt continuous_const (h 1))

theorem left_pos {y : E4} (hy : y ∈ exterior) : 0 < sourceR y := by
  have h : 0 < squaredDistance (-1) y := hy.1
  rw [← dist_squared, neg_one_smul, sub_neg_eq_add] at h
  exact lt_of_le_of_ne (norm_nonneg _) (fun he => by
    change 0 = ‖spatial y+unitAxis‖ at he; rw [← he] at h; norm_num at h)

theorem source_unit {y : E4} (hy : y ∈ exterior) : ‖sourceN y‖=1 := by
  have h := left_pos hy
  change ‖(sourceR y)⁻¹ • sourceA y‖=1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr h)]
  exact inv_mul_cancel₀ h.ne'

theorem adv_spatial {y : E4} (hy : y ∈ exterior) :
    spatial (toAdvanced y) = (1+sourceR y) • sourceN y := by
  change spatial (coordinates _ _) = _
  rw [spatial_coordinates]
  change (1+(sourceR y)⁻¹) • sourceA y = (1+sourceR y) • ((sourceR y)⁻¹ • sourceA y)
  rw [smul_smul]
  congr 1
  field_simp [(left_pos hy).ne']
  <;> ring

theorem adv_norm {y : E4} (hy : y ∈ exterior) : ‖spatial (toAdvanced y)‖=1+sourceR y := by
  rw [adv_spatial hy,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith [left_pos hy]),source_unit hy,mul_one]

theorem adv_direction {y : E4} (hy : y ∈ exterior) : angularDirection (toAdvanced y)=sourceN y := by
  rw [angularDirection,adv_norm hy,adv_spatial hy,smul_smul,inv_mul_cancel₀ (by linarith [left_pos hy]),one_smul]

theorem adv_params {y : E4} (hy : y ∈ exterior) : parameters (toAdvanced y)=(sourceR y,sourceN y 0) := by
  simp [parameters,adv_norm hy,adv_direction hy]

theorem source_recover {y : E4} (hy : y ∈ exterior) : sourceR y • sourceN y = sourceA y := by
  rw [sourceN,smul_smul,mul_inv_cancel₀ (left_pos hy).ne',one_smul]

theorem adv_H {y : E4} (hy : y ∈ exterior) :
    Advanced.H (parameters (toAdvanced y)) = sourceR y*harmonicPotential y := by
  let r := sourceR y
  let n := sourceN y
  have hn : ‖n‖=1 := source_unit hy
  have hd : 4 + r ^ 2 - 4*r*n 0 = squaredDistance 1 y := by
    have he : ‖r • n - (2:ℝ) • unitAxis‖^2 = 4+r^2-4*r*n 0 := by
      rw [norm_sub_sq_real,real_inner_smul_left,real_inner_smul_right,unit_inner,norm_smul,norm_smul,hn]
      simp [unitAxis,sq_abs]; ring
    rw [← he,source_recover hy,← dist_squared]
    congr 2
    simp [sourceA,two_smul]
  have hdL : Real.sqrt (squaredDistance (-1) y)=r := by
    rw [← dist_squared,Real.sqrt_sq (norm_nonneg _)]
    simp [r,sourceR,sourceA]
  have hdR : Advanced.distanceToOther (r,n 0)=Real.sqrt (squaredDistance 1 y) := congrArg Real.sqrt hd
  rw [adv_params hy]
  change 1+r*(1+1/Advanced.distanceToOther (r,n 0)) = r*(1+1/Real.sqrt (squaredDistance (-1) y)+1/Real.sqrt (squaredDistance 1 y))
  rw [hdR,hdL]
  field_simp [(left_pos hy).ne',show r ≠ 0 from (left_pos hy).ne',
    (Real.sqrt_pos.mpr (show 0<squaredDistance 1 y from hy.2)).ne']
  <;> ring

theorem adv_mem {y : E4} (hy : y ∈ exterior) : toAdvanced y ∈ manifold := by
  obtain ⟨_,hm,_⟩ := Cartesian.exterior_and_frontier.2.1
  obtain ⟨hr,hn⟩ := hm hy
  exact ⟨lt_trans (by norm_num) hr,hn⟩

theorem chart_coe {y : E4} (hy : y ∈ exterior) : (Model.chart y:E4) = toAdvanced y := by
  have : toAdvanced y ∈ spacetime := adv_mem hy
  simp [Model.chart,this]

theorem r_an {y : E4} (hy : y ∈ exterior) : AM sourceR y :=
  (spatial_an.contDiffAt.add (contDiffAt_const (c := unitAxis))).norm ℝ (norm_pos_iff.mp (left_pos hy))

theorem adv_an {y : E4} (hy : y ∈ exterior) : ContDiffAt ℝ ω toAdvanced y := by
  have ha : ContDiffAt ℝ ω sourceA y := spatial_an.contDiffAt.add contDiffAt_const
  have hr := r_an hy
  have hs : ContDiffAt ℝ ω timeShift (sourceR y) := by
    have hn := (left_pos hy).ne'
    unfold timeShift
    fun_prop (disch := assumption)
  have ht := (contDiffAt_piLp_apply (p := 2) (i := (0:Fin 4)) (𝕜 := ℝ) (n := ω) (y := y)).add (hs.comp y hr)
  have hx := ((contDiffAt_const (c := (1:ℝ))).add (hr.inv (left_pos hy).ne')).smul ha
  exact coordinate_an.contDiffAt.comp y (ht.prodMk hx)

set_option backward.isDefEq.respectTransparency false in
theorem chart_der {y : E4} (hy : y ∈ exterior) :
    (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) Model.chart y : E4 →L[ℝ] E4) = fderiv ℝ toAdvanced y := by
  have he : (Subtype.val ∘ Model.chart : E4 → E4) =ᶠ[𝓝 y] toAdvanced :=
    Filter.mem_of_superset (exterior_open.mem_nhds hy) (fun _ h => chart_coe h)
  have cont := (ContMDiffAt.subtypeVal_comp_iff manifold Model.chart y).mp
    (((adv_an hy).of_le (show (∞:ℕ∞ω) ≤ ω by simp)).contMDiffAt.congr_of_eventuallyEq he)
  have hd := (val_diff (Model.chart y)).comp y (cont.mdifferentiableAt (by simp)).hasMFDerivAt
  have hh := (hasMFDerivAt_iff_hasFDerivAt.mp hd).fderiv
  exact hh.symm.trans he.fderiv_eq

def packL : (ℝ × E3) →L[ℝ] E4 := LinearMap.toContinuousLinearMap {
  toFun := fun p => coordinates p.1 p.2
  map_add' := fun _ _ => by ext i; exact Fin.cases rfl (fun _ => rfl) i
  map_smul' := fun _ _ => by ext i; exact Fin.cases rfl (fun _ => rfl) i }

theorem r_line {y : E4} (hy : y ∈ exterior) (v:E4) :
    HasDerivAt (fun t : ℝ => sourceR (y+t • v)) (sourceSpeed y v) 0 := by
  have hx := (spatialL.hasFDerivAt.comp_hasDerivAt 0 (line_deriv y v)).add_const unitAxis
  have hh : 0 < ‖sourceA (y+(0:ℝ) • v)‖ := by rw [zero_smul,add_zero];exact left_pos hy
  have hs := norm_der (f := fun t => sourceA (y+t • v)) (v := spatial v) hx hh
  change HasDerivAt (fun t : ℝ => ‖sourceA (y+t • v)‖) ⟪‖sourceA y‖⁻¹ • sourceA y,spatial v⟫ 0
  simpa only [zero_smul,add_zero] using hs

theorem adv_der {y : E4} (hy : y ∈ exterior) (v : E4) :
    fderiv ℝ toAdvanced y v =
      coordinates (v 0 + ((1+3/2 * sourceR y)^2/sourceR y^2) * sourceSpeed y v)
        (((1+sourceR y)/sourceR y) • spatial v - (sourceSpeed y v / sourceR y) • sourceN y) := by
  let r := sourceR y
  let n := sourceN y
  let d := sourceSpeed y v
  let x := fun t : ℝ => y+t • v
  have hx := line_deriv y v
  have h0 : x 0=y := by simp [x]
  have hr := r_line hy v
  have hs := (shift_der (r := sourceR (x 0)) (by rw [h0];exact (left_pos hy).ne')).comp 0 hr
  have ht := (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt 0 hx
  have hu := (spatialL.hasFDerivAt.comp_hasDerivAt 0 hx).add_const unitAxis
  have hi := hr.inv (by change sourceR (x 0) ≠ 0;rw [h0];exact (left_pos hy).ne')
  have hd := ((hi.const_add 1).smul hu)
  have hpair := (ht.add hs).prodMk hd
  have hp := packL.hasFDerivAt.comp_hasDerivAt 0 hpair
  have hf := (adv_an hy).differentiableAt (by simp)
  have hf' : HasFDerivAt toAdvanced (fderiv ℝ toAdvanced y) (x 0) := by rw [h0];exact hf.hasFDerivAt
  have eq := (hf'.comp_hasDerivAt 0 hx).unique hp
  rw [eq]
  change coordinates (v 0 + (1+3/2*sourceR (x 0))^2/sourceR (x 0)^2*d)
    ((1+(sourceR (x 0))⁻¹) • spatial v+(-d/sourceR (x 0)^2) • sourceA (x 0)) = _
  rw [h0]
  congr 1
  rw [← source_recover hy,smul_smul]
  have hh : sourceR y ≠ 0 := (left_pos hy).ne'
  have eb : 1+(sourceR y)⁻¹=(1+sourceR y)/sourceR y := by field_simp;ring
  rw [eb,sub_eq_add_neg,← neg_smul]
  congr 2
  field_simp
  <;> ring


def J (y v : E4) := fderiv ℝ toAdvanced y v

theorem velocity_data {y : E4} (hy : y ∈ exterior) (v : E4) :
    J y v 0 = v 0 + (1+3/2 *sourceR y)^2/sourceR y^2 * sourceSpeed y v ∧
    spatial (J y v) = ((1+sourceR y)/sourceR y) • spatial v - (sourceSpeed y v/sourceR y) • sourceN y ∧
    Curves.radialSpeed (toAdvanced y) (J y v) = sourceSpeed y v := by
  have hv := adv_der hy v
  change J y v = _ at hv
  have hx := congrArg spatial hv
  rw [spatial_coordinates] at hx
  refine ⟨congrArg (fun x : E4 => x 0) hv,hx,?_⟩
  change ⟪angularDirection (toAdvanced y), spatial (J y v)⟫ = _
  rw [adv_direction hy,hx,inner_sub_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq,source_unit hy]
  change (1+sourceR y)/sourceR y * sourceSpeed y v-sourceSpeed y v/sourceR y*1^2=sourceSpeed y v
  field_simp [(left_pos hy).ne']
  <;> ring

theorem tangential_pull {y : E4} (hy : y ∈ exterior) (v w : E4) :
    ⟪spatial (J y v),spatial (J y w)⟫ - sourceSpeed y v * sourceSpeed y w =
    (((1+sourceR y)/sourceR y)^2)*(⟪spatial v,spatial w⟫-sourceSpeed y v*sourceSpeed y w) := by
  rw [(velocity_data hy v).2.1,(velocity_data hy w).2.1]
  have hnn : ⟪sourceN y,sourceN y⟫ = 1 := by rw [real_inner_self_eq_norm_sq,source_unit hy];norm_num
  have hn (u:E4) : ⟪sourceN y,spatial u⟫ = sourceSpeed y u := rfl
  have hn' (u:E4) : ⟪spatial u,sourceN y⟫ = sourceSpeed y u := real_inner_comm _ _
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hnn,hn,hn']
  field_simp [(left_pos hy).ne']
  <;> ring

theorem model_metric_pull {y : E4} (hy : y ∈ exterior) (v w : E4) :
    metric (Model.chart y) (J y v) (J y w) =
      -(v 0*w 0)/harmonicPotential y^2 + harmonicPotential y^2*⟪spatial v,spatial w⟫ := by
  let p := parameters (toAdvanced y)
  let r := sourceR y
  let U := harmonicPotential y
  let H := Advanced.H p
  let h := Advanced.H₀ p
  have hR : 0 < r := left_pos hy
  have hp : p.1 = r := congrArg Prod.fst (adv_params hy)
  have hH : H = r*U := adv_H hy
  obtain ⟨_,harg,hhpos,_⟩ := radius_data (Model.chart y)
  rw [chart_coe hy] at harg hhpos
  have hpos : 0<H := hhpos
  have hU : U ≠ 0 := fun hU => hpos.ne' (by simp [hH,hU])
  have hmatch := (Advanced.match_exterior (hp.trans_ne hR.ne') hpos.ne' (Advanced.gap_factor harg)).1
  have hh : (1+3/2*sourceR y) = h := by change _ = 1+3/2*p.1;rw [hp]
  rw [Curves.metric_eval,chart_coe hy,(velocity_data hy v).2.2,(velocity_data hy w).2.2,
    (velocity_data hy v).1,(velocity_data hy w).1,tangential_pull hy,adv_norm hy,hh]
  change Advanced.gvv p*(v 0+h^2/r^2*sourceSpeed y v)*(w 0+h^2/r^2*sourceSpeed y w) +
    Advanced.gvr p*((v 0+h^2/r^2*sourceSpeed y v)*sourceSpeed y w+
      sourceSpeed y v*(w 0+h^2/r^2*sourceSpeed y w)) +
    Advanced.grr p*sourceSpeed y v*sourceSpeed y w+
    (H^2/(1+r)^2)*(((1+r)/r)^2*(⟪spatial v,spatial w⟫-sourceSpeed y v*sourceSpeed y w)) = _
  rw [hmatch]
  change -(p.1^2)/H^2 * _ * _ + h^2/H^2 * _ + ((H^4-h^4)/(p.1^2*H^2))*_*_ + _ = -(v 0*w 0)/U^2+U^2*_
  rw [hp,hH]
  field_simp [hR.ne',hU,show 1+r≠0 by linarith]
  <;> ring

theorem metric_chart {y : E4} (hy : y ∈ exterior) :
    pullbackCoeffs metric Model.chart y = isotropicMetric y := by
  funext i j
  unfold pullbackCoeffs
  rw [chart_der hy]
  change metric (Model.chart y) (J y (coordBasis i)) (J y (coordBasis j)) = _
  rw [model_metric_pull hy,Curves.spatial_inner]
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [coordBasis,isotropicMetric,Matrix.diagonal]
  <;> ring

def gauge (y : E4) := Real.log (sourceR y) + (3/2:ℝ)*sourceR y

theorem gauge_an {y : E4} (hy : y ∈ exterior) : AM gauge y := by
  have h := r_an hy
  exact (h.log (left_pos hy).ne').add (contDiffAt_const.mul h)

theorem gauge_partial {y : E4} (hy : y ∈ exterior) (i : Fin 4) :
    coordPartial gauge i y = (1+3/2*sourceR y)/sourceR y*sourceSpeed y (coordBasis i) := by
  apply partial_from_line ((gauge_an hy).differentiableAt (by simp))
  let v := coordBasis i
  have hr := r_line hy v
  have hd := (hr.log (by simpa using (left_pos hy).ne')).add (hr.const_mul (3/2:ℝ))
  convert! hd using 1
  simp only [zero_smul,add_zero]
  field_simp [(left_pos hy).ne']
  <;> ring

theorem potential_eval (z v : E4) :
    ∑ i, potential i z*v i = Advanced.potentialV (parameters z)*v 0 + Advanced.potentialR (parameters z)*Curves.radialSpeed z v := by
  have hr := Curves.spatial_inner (coordinates 0 (angularDirection z)) v
  rw [spatial_coordinates] at hr
  unfold Curves.radialSpeed
  rw [hr]
  have hz : coordinates 0 (angularDirection z) 0 = 0 := rfl
  simp (config := {decide := true}) [Fin.sum_univ_four,potential,dt,dr,hz]
  ring

theorem potential_chart {y : E4} (hy : y ∈ exterior) (i : Fin 4) :
    ∑ k, potential k (toAdvanced y)*(J y (coordBasis i) k) =
    electricPotential y*dt i + coordPartial gauge i y := by
  let p := parameters (toAdvanced y)
  let r := sourceR y
  let U := harmonicPotential y
  let H := Advanced.H p
  let h := Advanced.H₀ p
  let v := coordBasis i
  have hR : 0<r := left_pos hy
  have hp : p.1=r := congrArg Prod.fst (adv_params hy)
  have hH : H=r*U := adv_H hy
  obtain ⟨_,harg,hpos,_⟩ := radius_data (Model.chart y)
  rw [chart_coe hy] at harg hpos
  have hHp : 0<H := hpos
  have hU : U≠0 := fun hU => hHp.ne' (by simp [hH,hU])
  have hmatch := (Advanced.match_exterior (hp.trans_ne hR.ne') hHp.ne' (Advanced.gap_factor harg)).2
  have ht : v 0 = dt i := by fin_cases i <;> simp (config := {decide := true}) [v,dt,coordBasis]
  have hh : 1+3/2*sourceR y = h := by change _=1+3/2*p.1;rw [hp]
  rw [potential_eval,(velocity_data hy v).1,(velocity_data hy v).2.2,gauge_partial hy,hh]
  change (p.1/H)*(v 0+h^2/r^2*sourceSpeed y v)+Advanced.potentialR p*sourceSpeed y v =
    1/U*dt i + h/r*sourceSpeed y v
  rw [hmatch,ht]
  change (p.1/H)*_+(-(h^2/(p.1*H))+h/p.1)*_ = _
  rw [hp,hH]
  field_simp [hR.ne',hU]
  <;> ring

end
end NoHair.TwoCentre.Model.Geo

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Calc
noncomputable section

abbrev AM := Geo.AM
def jac (f : E4 → E4) (j k : Fin 4) (z : E4) := coordPartial (fun w => f w k) j z
def pull (f : E4 → E4) (A : Fin 4 → E4 → ℝ) (j : Fin 4) (z : E4) :=
  ∑ k, A k (f z) * jac f j k z
def curl (A : Fin 4 → E4 → ℝ) (z : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => coordPartial (A j) i z - coordPartial (A i) j z

theorem basis_expand (v : E4) : ∑ k, v k • coordBasis k = v := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,coordBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v

theorem differential_expand (g : E4 → ℝ) (z v : E4) :
    fderiv ℝ g z v = ∑ k, v k * coordPartial g k z := by
  calc
    _ = fderiv ℝ g z (∑ k, v k • coordBasis k) := by rw [basis_expand]
    _ = _ := by simp [coordPartial]

theorem component_der {f : E4 → E4} {y : E4} (hf : DifferentiableAt ℝ f y) (j k : Fin 4) :
    jac f j k y = (fderiv ℝ f y (coordBasis j)) k := by
  let pr : E4 →L[ℝ] ℝ := (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) k)
  have h := pr.hasFDerivAt.comp y hf.hasFDerivAt
  exact DFunLike.congr_fun h.fderiv (coordBasis j)

theorem partial_mul {f g : E4 → ℝ} {y : E4} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) (i : Fin 4) :
    coordPartial (fun z => f z*g z) i y = coordPartial f i y*g y + f y*coordPartial g i y := by
  have h := DFunLike.congr_fun (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv (coordBasis i)
  change fderiv ℝ (f*g) y (coordBasis i) = _
  rw [h]
  simp [coordPartial,smul_eq_mul]
  <;> ring

theorem partial_sum (f : Fin 4 → E4 → ℝ) {y : E4} (hf : ∀ j, DifferentiableAt ℝ (f j) y) (i : Fin 4) :
    coordPartial (fun z => ∑ j, f j z) i y = ∑ j, coordPartial (f j) i y := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun j _ => hf j)]
  simp

theorem symmetric {g : E4 → ℝ} {y : E4} (hg : AM g y) (i j : Fin 4) :
    coordPartial (coordPartial g i) j y = coordPartial (coordPartial g j) i y := by
  have hd := (hg.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)
  have ev (k l : Fin 4) : coordPartial (coordPartial g k) l y =
      fderiv ℝ (fderiv ℝ g) y (coordBasis l) (coordBasis k) := by
    let pr := ContinuousLinearMap.apply ℝ ℝ (coordBasis k)
    exact DFunLike.congr_fun (pr.hasFDerivAt.comp y hd.hasFDerivAt).fderiv (coordBasis l)
  rw [ev,ev]
  exact hg.isSymmSndFDerivAt_of_omega _ _

theorem exterior_derivative_pull {f : E4 → E4} {A : Fin 4 → E4 → ℝ} {y : E4}
    (hf : ContDiffAt ℝ ω f y) (hA : ∀ k, AM (A k) (f y)) (i j : Fin 4) :
    curl (pull f A) y i j =
    matrixBilin (curl A (f y)) (fderiv ℝ f y (coordBasis i)) (fderiv ℝ f y (coordBasis j)) := by
  let d := fderiv ℝ f y
  have df := hf.differentiableAt (by simp)
  have hc (k : Fin 4) : AM (fun x => f x k) y := (contDiffAt_piLp_apply (p := 2) (i := k)).comp y hf
  have hj (l k : Fin 4) : AM (jac f l k) y := Geo.partial_an (hc k) l
  have ha (k : Fin 4) : AM (fun z => A k (f z)) y := (hA k).comp y hf
  have hcomp (u k : Fin 4) : coordPartial (fun z => A k (f z)) u y =
      ∑ l, d (coordBasis u) l * coordPartial (A k) l (f y) := by
    have h := ((hA k).differentiableAt (by simp)).hasFDerivAt.comp y df.hasFDerivAt
    exact (DFunLike.congr_fun h.fderiv (coordBasis u)).trans (differential_expand _ _ _)
  have hterm (u v : Fin 4) : coordPartial (pull f A v) u y =
      ∑ k, ((∑ l, d (coordBasis u) l * coordPartial (A k) l (f y)) * d (coordBasis v) k +
            A k (f y) * coordPartial (jac f v k) u y) := by
    change coordPartial (fun z => ∑ k, A k (f z)*jac f v k z) u y = _
    rw [partial_sum (fun k z => A k (f z)*jac f v k z)
      (fun k => ((ha k).differentiableAt (by simp)).mul ((hj v k).differentiableAt (by simp)))]
    apply Finset.sum_congr rfl; intro k _
    rw [partial_mul ((ha k).differentiableAt (by simp)) ((hj v k).differentiableAt (by simp)),hcomp,
      component_der df]
  have hsym (k : Fin 4) : coordPartial (jac f j k) i y = coordPartial (jac f i k) j y := symmetric (hc k) _ _
  let V := d (coordBasis i)
  let W := d (coordBasis j)
  have eval : matrixBilin (curl A (f y)) V W =
      ∑ k, ∑ l, (curl A (f y) k l * V k * W l) := by
    change Matrix.toLinearMap₂' ℝ (curl A (f y)) (WithLp.ofLp V) (WithLp.ofLp W) = _
    rw [Matrix.toLinearMap₂'_apply (R := ℝ) (curl A (f y)) (WithLp.ofLp V) (WithLp.ofLp W)]
    simp only [smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  change coordPartial (pull f A j) i y - coordPartial (pull f A i) j y = matrixBilin _ V W
  rw [hterm,hterm,eval]
  simp only [hsym,Finset.sum_add_distrib,add_sub_add_right_eq_sub]
  simp only [Finset.sum_mul, curl,sub_mul,Finset.sum_sub_distrib, V,W,d]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl;intro l _; ring
  · apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl;intro l _; ring

end
end NoHair.TwoCentre.Model.Calc
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold BigOperators
namespace NoHair.TwoCentre.Model.Geo
noncomputable section

theorem electric_an {y : E4} (hy : y ∈ exterior) : AM electricPotential y := by
  have hc (b:ℝ) : AM (squaredDistance b) y := by unfold AM squaredDistance;fun_prop
  have hi (b:ℝ) (h : 0<squaredDistance b y) : AM (inverseDistance b) y :=
    (contDiffAt_const (c := (1:ℝ))).div ((hc b).sqrt h.ne') (Real.sqrt_pos.mpr h).ne'
  have hU : 0<harmonicPotential y := by
    unfold harmonicPotential inverseDistance
    positivity
  exact (contDiffAt_const (c := (1:ℝ))).div
    (((contDiffAt_const (c := (1:ℝ))).add (hi (-1) hy.1)).add (hi 1 hy.2)) hU.ne'

theorem faraday_chart {y : E4} (hy : y ∈ exterior) :
    pullbackCoeffs faraday Model.chart y = TwoCentre.field y := by
  let f := toAdvanced
  let P := Calc.pull f potential
  have hA := reg_data (Model.chart y) |>.2.1
  rw [chart_coe hy] at hA
  have hmatch (i : Fin 4) {z : E4} (hz : z ∈ exterior) :
      P i z = electricPotential z * dt i + coordPartial gauge i z := by
    change (∑ k, potential k (toAdvanced z)*Calc.jac toAdvanced i k z)=_
    simp only [Calc.component_der ((adv_an hz).differentiableAt (by simp))]
    exact potential_chart hz i
  have hd (i j : Fin 4) : coordPartial (P i) j y =
      coordPartial electricPotential j y * dt i + coordPartial (coordPartial gauge i) j y := by
    have hh : P i =ᶠ[𝓝 y] (fun z => electricPotential z*dt i+coordPartial gauge i z) :=
      Filter.mem_of_superset (exterior_open.mem_nhds hy) (fun _ hz => hmatch i hz)
    have he := ((electric_an hy).differentiableAt (by simp)).hasFDerivAt.mul_const (dt i)
    have hg := (partial_an (gauge_an hy) i).differentiableAt (by simp) |>.hasFDerivAt
    have hs := he.add hg
    calc
      _ = fderiv ℝ (fun z => electricPotential z*dt i+coordPartial gauge i z) y (coordBasis j) :=
        DFunLike.congr_fun hh.fderiv_eq _
      _ = _ := by
        calc
          _ = (dt i • fderiv ℝ electricPotential y + fderiv ℝ (coordPartial gauge i) y) (coordBasis j) := DFunLike.congr_fun hs.fderiv _
          _ = _ := by simp [coordPartial,mul_comm]
  funext i j
  unfold pullbackCoeffs
  rw [chart_der hy]
  change matrixBilin (Calc.curl potential (Model.chart y:E4)) (fderiv ℝ f y (coordBasis i))
    (fderiv ℝ f y (coordBasis j)) = _
  rw [chart_coe hy,← Calc.exterior_derivative_pull (f := f) (adv_an hy) hA i j]
  change coordPartial (P j) i y - coordPartial (P i) j y = _
  rw [hd,hd,second_symm (gauge_an hy) j i]
  by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [TwoCentre.field,dt,hi,hj]

end
end NoHair.TwoCentre.Model.Geo

open NoHair.TwoCentre.Model.Geo

theorem solution :
    IsLorentzian metric ∧ IsSmoothBilinField metric ∧ IsSmoothBilinField faraday ∧
    IsTwoForm faraday ∧ IsTimeOrientation metric orientation ∧ IsSymmetryFlow metric faraday flow ∧
    IsStaticOn metric flow outer ∧ ∀ y ∈ exterior,
      pullbackCoeffs metric Model.chart y = isotropicMetric y ∧
      pullbackCoeffs faraday Model.chart y = TwoCentre.field y :=
  ⟨lorentzian, smooth_of_components metricCoeffs (fun z => (reg_data z).1),
    smooth_of_components faradayCoeffs (fun z => (reg_data z).2.2.1), antisymmetric,
    orientation_valid, flow_symmetry, staticity, fun _ hy => ⟨metric_chart hy,faraday_chart hy⟩⟩