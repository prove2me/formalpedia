-- Prove2me | solution 1 for LogLogJam.posterior_fisher_gain_identity
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:43:49.718467+00:00
-- url     : https://prove2.me/submissions/7c316591-bfbc-4929-83a2-5534746c5080

import Theorems.Thm_LogLogJam_gaussian_seed_score_centered
import Theorems.Thm_LogLogJam_gaussian_seed_mass_one
import Theorems.Thm_LogLogJam_physical_history_likelihood
import Definitions.Def_LogLogJam_postFisher
open MeasureTheory LogLogJam Filter Matrix ProbabilityTheory
open scoped ENNReal Topology ComplexOrder
set_option maxHeartbeats 1400000
private theorem gainCovPos (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    (VsqK lam θ k + Matrix.of W).PosDef := by
  have hrot : (rot θ).det = 1 := by
    simp [rot, det_fin_two, ← sq, Real.cos_sq_add_sin_sq]
  have hU : IsUnit (rot θ) := (isUnit_iff_isUnit_det _).mpr (by simp [hrot])
  have hdiag : (diagonal ![lam, lam⁻¹]).PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i <;> simp <;> positivity
  have hV : (Vsq lam θ).PosDef := by
    have h := hdiag.mul_mul_conjTranspose_same (B := rot θ)
      (vecMul_injective_of_isUnit hU)
    have heq : diagonal ![lam, lam⁻¹] = !![lam,0;0,lam⁻¹] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    simpa [Vsq, heq, conjTranspose_eq_transpose_of_trivial] using h
  apply PosDef.add_posSemidef (hV.kronecker (PosDef.one : (1 : Matrix (Fin k) (Fin k) ℝ).PosDef))
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hW.1
  · intro v
    have h := (Complex.nonneg_iff.mp (hW.2.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im, Complex.re_sum] using h

set_option maxHeartbeats 700000

private theorem gainDensityMeas {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {k : ℕ} (D : X → Matrix (Q k) (Q k) ℝ)
    (hD : Continuous D) (y : X → Q k → ℝ) (hy : Measurable y) :
    Measurable (fun x => outDens k (D x) (y x)) := by
  have hi (i j : Q k) : Measurable (fun x => (D x)⁻¹ i j) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact hD.matrix_det.measurable.inv.mul
      ((continuous_apply j).comp ((continuous_apply i).comp hD.matrix_adjugate)).measurable
  have hh (i : Q k) : Measurable (fun x => y x i) := (measurable_pi_apply i).comp hy
  simp only [outDens, dotProduct, Matrix.mulVec]
  apply Measurable.div
  · apply Real.continuous_exp.measurable.comp
    exact (Finset.measurable_fun_sum _ fun i _ => (hh i).mul
      (Finset.measurable_fun_sum _ fun j _ => (hi i j).mul (hh j))).neg
  · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hD.matrix_det.measurable)

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

private theorem pmeasDeriv {Y : Type*} [MeasurableSpace Y] (θ : ℝ) (b : ℝ → Y → ℝ)
    (hm : ∀ t, Measurable (b t)) (hd : ∀ y, DifferentiableAt ℝ (fun t => b t y) θ) :
    Measurable (fun y => deriv (fun t => b t y) θ) := by
  let d (n : ℕ) : ℝ := 1 / (n+1 : ℝ)
  have hlim : Tendsto d atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => by change 0 < 1 / (n+1 : ℝ); positivity⟩
  apply measurable_of_tendsto_metrizable (f := fun (n : ℕ) y => (d n)⁻¹ * (b (θ+d n) y - b θ y))
    (fun n => measurable_const.mul ((hm _).sub (hm _)))
  exact tendsto_pi_nhds.mpr fun y => (hd y).hasDerivAt.tendsto_slope_zero_right.comp hlim

private theorem pscore {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (p : ℝ → ℝ) (b : ℝ → Y → ℝ) (θ : ℝ)
    (hp : ∀ t, 0 < p t) (hb : ∀ t y, 0 < b t y) (hm : ∀ t, Measurable (b t))
    (hdp : DifferentiableAt ℝ p θ) (hdb : ∀ y, DifferentiableAt ℝ (fun t => b t y) θ)
    (hi : Integrable (fun y => deriv (fun t => b t y) θ) ν) (hz : ∫ y, deriv (fun t => b t y) θ ∂ν = 0)
    (hn : ∫⁻ y, ENNReal.ofReal (b θ y) ∂ν = 1) :
    (∫⁻ y, ENNReal.ofReal (p θ) * ENNReal.ofReal (b θ y) * ENNReal.ofReal ((deriv (fun t => Real.log (p t * b t y)) θ)^2) ∂ν) =
    ENNReal.ofReal (p θ) * ENNReal.ofReal ((deriv (fun t => Real.log (p t)) θ)^2) + ENNReal.ofReal (p θ) * fisherInfo ν b θ := by
  let v := deriv (fun t => Real.log (p t)) θ
  have ht y : deriv (fun t => Real.log (p t * b t y)) θ = v + deriv (fun t => b t y) θ / b θ y := by
    have eq : (fun t => Real.log (p t * b t y)) = (fun t => Real.log (p t) + Real.log (b t y)) :=
      funext fun t => Real.log_mul (hp t).ne' (hb t y).ne'
    rw [eq, deriv_fun_add (hdp.log (hp θ).ne') ((hdb y).log (hb θ y).ne')]
    rw [((hdb y).hasDerivAt.log (hb θ y).ne').deriv]
  have cen := centered_square ν (b θ) (fun y => deriv (fun t => b t y) θ) v (hb θ) (hm θ) (pmeasDeriv θ b hm hdb) hn hi hz
  simp_rw [ht, mul_assoc, ← ENNReal.ofReal_mul (hb θ _).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,cen,mul_add]
  unfold fisherInfo
  simp_rw [((hdb _).hasDerivAt.log (hb θ _).ne').deriv, ← ENNReal.ofReal_mul (hb θ _).le]
  rfl

namespace PosteriorBayes
open LogLogJam Matrix MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 1200000
private theorem density_meas {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {k : ℕ} (D : X → Matrix (Q k) (Q k) ℝ)
    (hD : Continuous D) (y : X → Q k → ℝ) (hy : Measurable y) :
    Measurable (fun x => outDens k (D x) (y x)) := by
  have hi (i j : Q k) : Measurable (fun x => (D x)⁻¹ i j) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact hD.matrix_det.measurable.inv.mul
      ((continuous_apply j).comp ((continuous_apply i).comp hD.matrix_adjugate)).measurable
  have hh (i : Q k) : Measurable (fun x => y x i) := (measurable_pi_apply i).comp hy
  simp only [outDens, dotProduct, Matrix.mulVec]
  apply Measurable.div
  · apply Real.continuous_exp.measurable.comp
    exact (Finset.measurable_fun_sum _ fun i _ => (hh i).mul
      (Finset.measurable_fun_sum _ fun j _ => (hi i j).mul (hh j))).neg
  · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hD.matrix_det.measurable)

private theorem likelihood_mass_pos {t : ℕ} (l : ℝ) (hl : 1 < l) (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) : 0 < postNorm l H := by
  obtain ⟨hpos, _, hC⟩ := physical_history_likelihood l hl H hH
  unfold postNorm
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact intervalIntegral.integral_pos Real.pi_pos hC.continuous.continuousOn
    (fun u _ => (hpos u).le) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hpos 0⟩

private def admissible (o : Obs) := IsCov o.1 (Matrix.of o.2.1)
private theorem snoc_admissible {t : ℕ} (H : Hist t) (s : Seed) (y : Q s.1 → ℝ)
    (hH : ∀ i, admissible (H i)) (hs : IsCov s.1 (Matrix.of s.2)) :
    ∀ i, admissible (Fin.snoc (α := fun _ : Fin (t+1) => Obs) H ⟨s.1,(s.2,y)⟩ i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; exact hs
  · rw [Fin.snoc_castSucc]; exact hH j

private theorem derivMeasurable {X : Type*} [MeasurableSpace X] (q : ℝ → X → ℝ)
    (hC : ∀ x, ContDiff ℝ 1 (fun t => q t x)) (hm : ∀ t, Measurable (q t)) :
    Measurable (fun z : ℝ × X => deriv (fun t => q t z.2) z.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (fun x => (hC x).continuous_deriv_one)
  intro t
  let d (n : ℕ) : ℝ := 1 / (n+1 : ℝ)
  have hlim : Tendsto d atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => by change 0 < 1 / (n+1 : ℝ); positivity⟩
  apply measurable_of_tendsto_metrizable (f := fun (n : ℕ) x => (d n)⁻¹ * (q (t+d n) x - q t x))
    (fun n => measurable_const.mul ((hm _).sub (hm _)))
  apply tendsto_pi_nhds.mpr
  intro x
  exact ((hC x).differentiable_one t).hasDerivAt.tendsto_slope_zero_right.comp hlim


private theorem gainJoint (l : ℝ) (hl : 1 < l) {t : ℕ} (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    nextCondExp l H k W (postFisher l) =
    ∫⁻ u in Set.Ico 0 Real.pi, ∫⁻ y,
      ENNReal.ofReal (post l H u) * ENNReal.ofReal (outDens k (VsqK l u k + Matrix.of W) y) *
        ENNReal.ofReal ((deriv (fun v => Real.log (post l H v *
          outDens k (VsqK l v k + Matrix.of W) y)) u)^2) := by
  let Y := Q k → ℝ
  let I := (volume : Measure ℝ).restrict (Set.Ico 0 Real.pi)
  let C (y : Y) : Hist (t+1) := Fin.snoc H ⟨k,(W,y)⟩
  let d (u : ℝ) (y : Y) := outDens k (VsqK l u k + Matrix.of W) y
  let q (u : ℝ) (y : Y) := post l H u * d u y
  let b (y : Y) := predDens l H k W y
  let score (u : ℝ) (y : Y) := ENNReal.ofReal ((deriv (fun v => Real.log (q v y)) u)^2)
  let term (u : ℝ) (y : Y) := ENNReal.ofReal (q u y) * score u y
  have hphys y : ∀ i, admissible (C y i) := snoc_admissible H ⟨k,W⟩ y hH hW
  have hfactor (u : ℝ) (y : Y) : histDens l u (C y) = histDens l u H * d u y := by
    change (∏ i, obsDens l u (C y i)) = (∏ i, obsDens l u (H i)) * _
    rw [Fin.prod_univ_castSucc]
    simp only [C, Fin.snoc_last, Fin.snoc_castSucc]
    rfl
  have hZ := likelihood_mass_pos l hl H hH
  have hZ' (y : Y) := likelihood_mass_pos l hl (C y) (hphys y)
  have hlik (y : Y) := physical_history_likelihood l hl (C y) (hphys y)
  have hq (u : ℝ) (y : Y) : q u y = histDens l u (C y) / postNorm l H := by
    unfold q post
    rw [hfactor]; ring
  have hb (y : Y) : b y = postNorm l (C y) / postNorm l H := by
    change (∫ u in Set.Ico 0 Real.pi, q u y) = _
    simp_rw [hq]
    exact integral_div _ _
  have hbpos y : 0 < b y := (hb y).symm ▸ div_pos (hZ' y) hZ
  have hpp u : 0 < post l H u := div_pos ((physical_history_likelihood l hl H hH).1 u) hZ
  have hqp (u : ℝ) (y : Y) : 0 < q u y := (hq u y).symm ▸ div_pos ((hlik y).1 u) hZ
  have hrep (u : ℝ) (y : Y) : post l (C y) u = q u y / b y := by
    unfold post
    rw [hq, hb]
    field_simp [hZ.ne', (hZ' y).ne']
  have hm (u : ℝ) : Measurable (q u) :=
    measurable_const.mul (density_meas _ continuous_const id measurable_id)
  have hc (y : Y) : ContDiff ℝ 1 (fun u => q u y) := by
    simp_rw [hq]
    exact (hlik y).2.2.div_const _
  have hqm : Measurable (Function.uncurry q) :=
    measurable_uncurry_of_continuous_of_measurable (fun y => (hc y).continuous) hm
  have hsm : Measurable (Function.uncurry score) :=
    ((derivMeasurable (fun u y => Real.log (q u y)) (fun y => (hc y).log (fun u => (hqp u y).ne'))
      (fun u => (hm u).log)).pow_const 2).ennreal_ofReal
  have ht : Measurable (Function.uncurry term) := hqm.ennreal_ofReal.mul hsm
  have hpoint (y : Y) : ENNReal.ofReal (b y) * postFisher l (C y) = ∫⁻ u, term u y ∂I := by
    change ENNReal.ofReal (b y) * (∫⁻ u, ENNReal.ofReal (post l (C y) u) *
      ENNReal.ofReal ((deriv (fun v => Real.log (post l (C y) v)) u)^2) ∂I) = _
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro u
    have he : (fun v => Real.log (post l (C y) v)) = (fun v => Real.log (q v y) - Real.log (b y)) := by
      funext v; rw [hrep, Real.log_div (hqp v y).ne' (hbpos y).ne']
    change ENNReal.ofReal (b y) * (_ * _) = ENNReal.ofReal (q u y) * score u y
    rw [he, deriv_sub_const, hrep, ENNReal.ofReal_div_of_pos (hbpos y), ← mul_assoc,
      mul_comm (ENNReal.ofReal (b y)), ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr (hbpos y)).ne' ENNReal.ofReal_ne_top]
  change (∫⁻ y, ENNReal.ofReal (b y) * postFisher l (C y)) = _
  simp_rw [hpoint]
  rw [lintegral_lintegral_swap (μ := (volume : Measure Y)) (ν := I)
    (f := fun y u => term u y) (ht.comp measurable_swap).aemeasurable]
  apply lintegral_congr
  intro u
  apply lintegral_congr
  intro y
  change ENNReal.ofReal (post l H u * d u y) * score u y = _
  rw [ENNReal.ofReal_mul (hpp u).le]

end
end PosteriorBayes

private theorem gainBayes (lam : ℝ) (hlam : 1 < lam) {t : ℕ} (H : Hist t) (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ) (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    nextCondExp lam H k W (postFisher lam) = ∫⁻ θ in Set.Ico 0 Real.pi, ∫⁻ y : Q k → ℝ, ENNReal.ofReal (post lam H θ)*ENNReal.ofReal (outDens k (VsqK lam θ k + Matrix.of W) y)*ENNReal.ofReal ((deriv (fun v => Real.log (post lam H v * outDens k (VsqK lam v k + Matrix.of W) y)) θ)^2) := 
  PosteriorBayes.gainJoint lam hlam H hH k W hW

theorem solution (lam : ℝ) (hlam : 1 < lam) {t : ℕ} (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    nextCondExp lam H k W (postFisher lam) =
        postFisher lam H +
          ∫⁻ θ in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H θ) * measFisher lam k W θ := by
  let p := post lam H
  let b := fun t y => outDens k (VsqK lam t k + Matrix.of W) y
  obtain ⟨hpos,_,hC⟩ := physical_history_likelihood lam hlam H hH
  have hZ : 0 < postNorm lam H := by
    unfold postNorm
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    apply intervalIntegral.integral_pos Real.pi_pos hC.continuous.continuousOn (fun s _ => (hpos s).le)
    exact ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hpos 0⟩
  have hp (s) : 0 < p s := div_pos (hpos s) hZ
  have hpc : ContDiff ℝ 1 p := hC.div_const _
  have hb (s) (y : Q k → ℝ) : 0 < b s y := by
    have h := (gainCovPos lam s hlam k W hW).det_pos
    dsimp only [b,outDens]; positivity
  have hmb (s) : Measurable (b s) := gainDensityMeas _ continuous_const _ measurable_id
  have eval (s) := by
    obtain ⟨hd,hi,h0⟩ := gaussian_seed_score_centered lam s hlam k W hW
    exact pscore volume p b s hp hb hmb (hpc.differentiable_one s) hd hi h0 (gaussian_seed_mass_one lam s hlam k W hW)
  rw [gainBayes lam hlam H hH k W hW]
  change (∫⁻ s in Set.Ico 0 Real.pi, ∫⁻ y, ENNReal.ofReal (p s) * ENNReal.ofReal (b s y) * ENNReal.ofReal ((deriv (fun t => Real.log (p t * b t y)) s)^2)) = _
  rw [lintegral_congr eval]
  rw [lintegral_add_left]
  · rfl
  · exact hpc.continuous.measurable.ennreal_ofReal.mul (((hpc.log (fun s => (hp s).ne')).continuous_deriv_one.measurable.pow_const 2).ennreal_ofReal)
