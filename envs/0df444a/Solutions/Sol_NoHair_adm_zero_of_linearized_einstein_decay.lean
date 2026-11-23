-- Prove2me | solution 1 for NoHair.adm_zero_of_linearized_einstein_decay
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:54:59.623794+00:00
-- url     : https://prove2.me/submissions/1b31914c-d22d-419d-be4d-3d7868495c50

import Theorems.Thm_NoHair_linear_adm_flux_on_coordinate_sphere
open Set Metric MeasureTheory Filter NoHair
open scoped ContDiff Manifold Topology

private abbrev X := ADMPoint
private abbrev S := ADMSphere
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

private lemma partial_eq_tail {B : ℝ} {f g : X → ℝ}
    (e : ∀ y, B < ‖y‖ → f y = g y) (i : Fin 3) {x : X} (hx : B < ‖x‖) :
    spatialADMPartial i f x = spatialADMPartial i g x := by
  have h : f =ᶠ[𝓝 x] g :=
    Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hx) (fun y hy => e y hy)
  unfold spatialADMPartial
  rw [h.fderiv_eq]

private lemma unit_norm (n : S) : ‖(n:X)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using n.property

theorem solution (k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∃ B : ℝ, ∀ x : ADMPoint, B < ‖x‖ → ∀ i j, ContDiffAt ℝ ∞ (fun y => k y i j) x)
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ i j : Fin 3,
      |negativeTwiceLinearEinstein k i j x| ≤ C / ‖x‖^4) :
    Tendsto (staticADMFlux k) atTop (𝓝 0) := by
  classical
  obtain ⟨B,hB⟩ := hs
  obtain ⟨R,C,hR,hC,hD⟩ := hd
  let b := max B 0 + 1
  have bp : 0 < b := by dsimp only [b]; linarith [le_max_right B (0:ℝ)]
  have bg : B < b := by dsimp only [b]; linarith [le_max_left B (0:ℝ)]
  let cut : ContDiffBump (0:X) := ⟨b,b+1,bp,by linarith⟩
  let K : X → Mat := fun x i j => (1-cut x)*k x i j
  have smoothK (i j : Fin 3) : ContDiff ℝ ∞ (fun x => K x i j) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases outside : B < ‖x‖
    · exact (contDiffAt_const.sub cut.contDiffAt).mul (hB x outside i j)
    · have openBall : ‖x‖ < b := (le_of_not_gt outside).trans_lt bg
      apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds openBall] with y hy
      have eq : cut y = 1 := cut.one_of_mem_closedBall (Metric.mem_closedBall.mpr (by
        rw [dist_zero_right];exact (show ‖y‖ < b from hy).le))
      simp only [K,eq,sub_self,zero_mul]
  have tail (y : X) (hy : b+1 < ‖y‖) : K y = k y := by
    have z : cut y = 0 := cut.zero_of_le_dist (by rw [dist_zero_right]; exact hy.le)
    ext i j
    simp [K,z]
  have dk (i j l : Fin 3) {x : X} (hx : b+1 < ‖x‖) :
      spatialADMPartial l (fun z => K z i j) x = spatialADMPartial l (fun z => k z i j) x :=
    partial_eq_tail (fun y hy => congrFun (congrFun (tail y hy) i) j) l hx
  have av (j : Fin 3) {x : X} (hx : b+1 < ‖x‖) : admVector K j x = admVector k j x := by
    unfold admVector
    exact Finset.sum_congr rfl fun l _ => by rw [dk _ _ _ hx, dk _ _ _ hx]
  have tv (i j l : Fin 3) (x : X) (hx : b+1 < ‖x‖) : admSuperpotential K i j l x = admSuperpotential k i j l x := by
    unfold admSuperpotential
    rw [dk _ _ _ hx,dk _ _ _ hx,av _ hx,av _ hx]
  have ev (i j : Fin 3) {x : X} (hx : b+1 < ‖x‖) : negativeTwiceLinearEinstein K i j x = negativeTwiceLinearEinstein k i j x :=
    Finset.sum_congr rfl fun l _ => partial_eq_tail (tv i j l) l hx
  have size (n : S) {r : ℝ} (hr : 0 < r) : ‖r • (n:X)‖ = r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,unit_norm,mul_one]
  let I := fun (r : ℝ) (n : S) =>
    ∑ j : Fin 3, (∑ i : Fin 3, r^2*(r • (n:X)) i*negativeTwiceLinearEinstein K i j (r • (n:X))) * (n:X) j
  have limI : Tendsto (fun r => ∫ n : S, I r n ∂admSurfaceMeasure) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun r : ℝ => (9*C*admSurfaceMeasure.real univ) / r)
    · filter_upwards [eventually_gt_atTop (max (b+1) R)] with r hr
      have hrs := max_lt_iff.mp hr
      have rp := hR.trans hrs.2
      have bound (n : S) : ‖I r n‖ ≤ 9*C / r := by
        let x := r • (n:X)
        have nx : ‖x‖ = r := size n rp
        have xc (i : Fin 3) : |x i| ≤ r := by simpa only [Real.norm_eq_abs,nx] using PiLp.norm_apply_le x i
        have nc (i : Fin 3) : |(n:X) i| ≤ 1 := by simpa only [Real.norm_eq_abs,unit_norm] using PiLp.norm_apply_le (n:X) i
        have second (i j : Fin 3) : |negativeTwiceLinearEinstein K i j x| ≤ C / r^4 := by
          rw [ev i j (x:=x) (by rw [nx]; exact hrs.1)]
          simpa only [nx] using hD x (by rw [nx]; exact hrs.2) i j
        have term (i j : Fin 3) : |r^2*x i*negativeTwiceLinearEinstein K i j x| ≤ C / r := by
          rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg _)]
          calc _ ≤ (r^2*r)*(C / r^4) :=
                 mul_le_mul (mul_le_mul_of_nonneg_left (xc i) (sq_nonneg _)) (second i j) (abs_nonneg _) (by positivity)
               _ = C / r := by field_simp [rp.ne'] <;> ring
        have col (j : Fin 3) : |(∑ i : Fin 3, r^2*x i*negativeTwiceLinearEinstein K i j x)*(n:X) j| ≤ 3*(C / r) := by
          rw [abs_mul]
          have s := (Finset.abs_sum_le_sum_abs (fun i => r^2*x i*negativeTwiceLinearEinstein K i j x) Finset.univ).trans
            (Finset.sum_le_sum (fun i _ => term i j))
          simp only [Fin.sum_univ_three] at s
          apply (mul_le_mul _ (nc j) (abs_nonneg _) (by positivity : 0 ≤ 3*(C / r))).trans_eq (mul_one _)
          simp only [Fin.sum_univ_three]
          linarith only [s]
        change |∑ j : Fin 3, (∑ i : Fin 3, r^2*x i*negativeTwiceLinearEinstein K i j x)*(n:X) j| ≤ _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        exact (Finset.sum_le_sum (fun j _ => col j)).trans_eq (by simp [Fin.sum_univ_three];ring)
      exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall bound)).trans_eq (by ring)
    · exact tendsto_const_nhds.div_atTop tendsto_id
  have limDiv : Tendsto (fun r => (∫ n : S, I r n ∂admSurfaceMeasure)/(16*Real.pi)) atTop (𝓝 0) := by
    simpa only [zero_div] using limI.div_const (16*Real.pi)
  apply limDiv.congr'
  filter_upwards [eventually_gt_atTop (max (b+1) R)] with r hr
  have rp := hR.trans (max_lt_iff.mp hr).2
  change _ = staticADMFlux k r
  rw [← linear_adm_flux_on_coordinate_sphere K smoothK r rp]
  unfold staticADMFlux
  congr 1
  apply integral_congr_ae
  filter_upwards with n
  have ht : b+1 < ‖r • (n:X)‖ := by rw [size n rp]; exact (max_lt_iff.mp hr).1
  unfold staticADMDensity
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [dk _ _ _ ht,dk _ _ _ ht]
