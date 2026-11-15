-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.smoothing_reciprocal_dual_norm
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:56:02.024324+00:00
-- url     : https://prove2.me/submissions/e7a87e54-9543-4eaa-b02e-3a85540850b2

import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark

set_option autoImplicit false

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv

noncomputable section

open scoped BigOperators

/-- A usable public version of the smoothing-threshold consequence. The
zero-dimensional case is discharged, and the positive-dimensional case
uses the recovered, proved exact characterization of smoothingParam. -/
theorem dual_mass_le_of_smoothing {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0<error) (hwidth : 0<width) (hsmoothing : smoothingParam lattice error ≤ width) :
    rhoDualNonzero (1/width) lattice ≤ error := by
  rcases Nat.eq_zero_or_pos dimension with rfl | hdimension
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {value : dual lattice // value≠0} :=
      ⟨fun value => value.property (Subsingleton.elim value.val 0)⟩
    unfold rhoDualNonzero
    simp [herror.le]
  · obtain ⟨_,hantitone,_,_,hthreshold⟩ := RegevLWE.GaussConv.smoothing_remark hdimension lattice
    obtain ⟨hpositive,hequal⟩ := hthreshold error herror
    rw [←hequal]
    exact hantitone.antitoneOn hpositive hwidth hsmoothing

/-- Increasing the positive Gaussian width increases every actual mass. -/
theorem rho_width_mono {dimension : ℕ} {first second : ℝ} (hfirst : 0<first) (hsecond : first ≤ second)
    (value : EuclideanSpace ℝ (Fin dimension)) : rho first value ≤ rho second value := by
  have hs : 0<second := hfirst.trans_le hsecond
  unfold rho
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le (sq_nonneg ‖value‖))
    (sq_pos_of_pos hfirst) ((sq_le_sq₀ hfirst.le hs.le).mpr hsecond)
  simpa only [neg_div,neg_mul] using neg_le_neg h

/-- Summability of the actual nonzero-dual Gaussian, with all premises
discharged by the proved smoothing characterization, including dim 0. -/
theorem summable_dual_of_smoothing {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0<error) (hwidth : 0<width) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (fun value : {value : dual lattice // value≠0} => rho (1/width) (value : EuclideanSpace ℝ (Fin dimension))) := by
  rcases Nat.eq_zero_or_pos dimension with rfl | hdimension
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {value : dual lattice // value≠0} :=
      ⟨fun value => value.property (Subsingleton.elim value.val 0)⟩
    have : Fintype {value : dual lattice // value≠0} := Fintype.ofIsEmpty
    exact HasSum.summable (hasSum_fintype _)
  · obtain ⟨_,_,_,_,hthreshold⟩ := RegevLWE.GaussConv.smoothing_remark hdimension lattice
    obtain ⟨hpositive,hequal⟩ := hthreshold error herror
    have hs : Summable (fun value : {value : dual lattice // value≠0} =>
        rho (1/smoothingParam lattice error) (value : EuclideanSpace ℝ (Fin dimension))) := by
      by_contra hnonsummable
      have hzero := tsum_eq_zero_of_not_summable hnonsummable
      change rhoDualNonzero (1/smoothingParam lattice error) lattice=0 at hzero
      rw [hequal] at hzero
      exact herror.ne' hzero
    apply Summable.of_nonneg_of_le (fun value => Real.exp_nonneg _) _ hs
    intro value
    apply rho_width_mono (div_pos zero_lt_one hwidth)
    exact one_div_le_one_div_of_le hpositive hsmoothing

end

end InfoLossLAR.WorstCase.GaussianProjection

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection

noncomputable section

variable {dimension : ℕ}

/-- A single genuine nonzero dual term forces reciprocal-width lattice
separation once the full smoothing error is below exp(-pi). -/
theorem smoothing_dual_separation
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi))
    (hwidth : 0 < width) (hsmoothing : smoothingParam lattice error ≤ width)
    (point : dual lattice) (hpoint : point ≠ 0) :
    1/width ≤ ‖(point : EuclideanSpace ℝ (Fin dimension))‖ := by
  have hs := summable_dual_of_smoothing lattice herror hwidth hsmoothing
  have hterm := hs.le_tsum (⟨point,hpoint⟩ : {point : dual lattice // point ≠ 0}) (fun _ _ => Real.exp_nonneg _)
  have hmass := dual_mass_le_of_smoothing lattice herror hwidth hsmoothing
  have hsingle : rho (1/width) (point : EuclideanSpace ℝ (Fin dimension)) ≤ Real.exp (-Real.pi) :=
    hterm.trans (hmass.trans hsmall)
  rw [rho,Real.exp_le_exp] at hsingle
  rw [one_div,inv_pow,div_inv_eq_mul] at hsingle
  have hnorm := norm_nonneg (point : EuclideanSpace ℝ (Fin dimension))
  have hproduct : (0 : ℝ) ≤ width*‖(point : EuclideanSpace ℝ (Fin dimension))‖ := mul_nonneg hwidth.le hnorm
  have hsquare : (1 : ℝ)^2 ≤ (width*‖(point : EuclideanSpace ℝ (Fin dimension))‖)^2 := by
    nlinarith [Real.pi_pos]
  have hlarge := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hproduct).mp hsquare
  exact (div_le_iff₀ hwidth).mpr (by nlinarith)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- Any explicit nonzero dual vector lower-bounds the actual smoothing
parameter. In particular, the final LLL dual column controls the bootstrap
iteration count without referring to the input basis encoding length. -/
theorem smoothing_reciprocal_dual_norm
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi))
    (point : dual lattice) (hpoint : point ≠ 0) :
    1/‖(point : EuclideanSpace ℝ (Fin dimension))‖ ≤ smoothingParam lattice error := by
  have hthreshold := (RegevLWE.GaussConv.smoothing_remark hdimension lattice).2.2.2.2 error herror
  have hsep := smoothing_dual_separation lattice herror hsmall hthreshold.1 le_rfl point hpoint
  have hpositive : 0 < ‖(point : EuclideanSpace ℝ (Fin dimension))‖ := by
    apply norm_pos_iff.mpr
    intro hequal
    apply hpoint
    exact Subtype.ext hequal
  apply (div_le_iff₀ hpositive).mpr
  have h := (div_le_iff₀ hthreshold.1).mp hsep
  nlinarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

theorem solution {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi))
    (point : dual lattice) (hpoint : point ≠ 0) :
    1/‖(point : EuclideanSpace ℝ (Fin dimension))‖ ≤ smoothingParam lattice error := by
  exact InfoLossLAR.WorstCase.GaussianPoissonSeries.smoothing_reciprocal_dual_norm
    lattice error hdimension herror hsmall point hpoint

