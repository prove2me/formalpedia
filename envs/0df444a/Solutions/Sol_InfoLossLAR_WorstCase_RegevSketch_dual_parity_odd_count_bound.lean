-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dual_parity_odd_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T01:19:13.234472+00:00
-- url     : https://prove2.me/submissions/85496fb0-4a03-4c56-bb24-777370dbf3e9

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Theorems.Thm_RegevLWE_GaussConv_claim_3_8
import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark

section
open scoped BigOperators Classical
namespace AFT.GaussianSource
noncomputable def finiteLaw {α : Type*} [Fintype α] (p : PMF α) : FiniteDist α where
  weight a := (p a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  sum_one := by
    rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
    have hsum : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [hsum, ENNReal.toReal_one]

end AFT.GaussianSource

namespace InfoLossLAR.WorstCase.Integration
open AFT GaussianSource
theorem finiteLaw_map_weight {α β : Type*} [Fintype β] (p : PMF α) (f : α → β) (b : β) :
    (finiteLaw (p.map f)).weight b = ∑' a, if f a = b then (p a).toReal else 0 := by
  classical
  change ((p.map f) b).toReal = _
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : f a = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro a
    split_ifs
    · exact p.apply_ne_top a
    · exact ENNReal.zero_ne_top

end InfoLossLAR.WorstCase.Integration
end


set_option linter.all false

namespace AFT
end AFT

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport
end InfoLossLAR.WorstCase.GaussianLatticeTransport

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

/- Helper module AFT.CountableNormalizedTilt. -/
section P2MDyadicModule0

namespace AFT

open scoped BigOperators

/-- Normalizing a positive approximate density costs at most
`error / (1-error)` in total variation. Both masses are genuine normalized
countable laws; no unknown normalizer is treated as one. -/
theorem normalized_tilt_total_variation {State : Type*}
    (reference actual : State → ℝ)
    (href : ∀ state, 0 ≤ reference state)
    (hreference : Summable reference) (hactual : Summable actual)
    (href_one : ∑' state, reference state = 1)
    (hactual_one : ∑' state, actual state = 1)
    (scale error : ℝ) (herror : 0 ≤ error) (herror_one : error < 1)
    (hpoint : ∀ state, |actual state - scale * reference state| ≤
      error * scale * reference state) :
    (∑' state, |actual state-reference state|) / 2 ≤ error / (1-error) := by
  have hdiff := hactual.sub (hreference.mul_left scale)
  have hnorm : |1-scale| ≤ error*scale := by
    have ht := norm_tsum_le_tsum_norm hdiff.norm
    rw [hactual.tsum_sub (hreference.mul_left scale),tsum_mul_left,hactual_one,href_one,mul_one,Real.norm_eq_abs] at ht
    have hb := hdiff.norm.tsum_le_tsum (fun state => by
      simpa only [Real.norm_eq_abs] using hpoint state) (hreference.mul_left (error*scale))
    rw [tsum_mul_left,href_one,mul_one] at hb
    exact ht.trans hb
  have hs : scale ≤ 1/(1-error) := by
    apply (le_div_iff₀ (by linarith : 0<1-error)).mpr
    have hh' := (neg_le_abs (1-scale)).trans hnorm
    nlinarith
  have hbound (state : State) : |actual state-reference state| ≤
      (2*error*scale)*reference state := by
    calc
      _ = |(actual state-scale*reference state)+(scale-1)*reference state| := by congr 1; ring
      _ ≤ |actual state-scale*reference state|+|(scale-1)*reference state| := abs_add_le _ _
      _ ≤ error*scale*reference state+(error*scale)*reference state := by
        apply add_le_add (hpoint state)
        rw [abs_mul,abs_of_nonneg (href state),abs_sub_comm]
        exact mul_le_mul_of_nonneg_right hnorm (href state)
      _ = _ := by ring
  have hsum := (hactual.sub hreference).norm.tsum_le_tsum
    (fun state => by simpa only [Real.norm_eq_abs] using hbound state)
    (hreference.mul_left (2*error*scale))
  simp only [Real.norm_eq_abs,tsum_mul_left,href_one,mul_one] at hsum
  have hmul := mul_le_mul_of_nonneg_left hs herror
  rw [mul_one_div] at hmul
  linarith

end AFT

end P2MDyadicModule0

/- Helper module Solutions.RegevBridgeGaussianLatticeTransport. -/
section P2MDyadicModule1

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

instance image_discrete (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    DiscreteTopology (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

instance image_full_rank (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    IsZLattice ℝ (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

/-- Self-adjointness transports dual membership through the forward map. -/
theorem mem_dual_image_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : Space (dimension := dimension)) :
    value ∈ dual (imageLattice lattice transform) ↔ transform value ∈ dual lattice := by
  change (∀ test ∈ imageLattice lattice transform,
    inner ℝ value test ∈ (1 : Submodule ℤ ℝ)) ↔
    ∀ test ∈ lattice, inner ℝ (transform value) test ∈ (1 : Submodule ℤ ℝ)
  constructor
  · intro membership test test_mem
    rw [selfAdjoint]
    apply membership
    simpa using test_mem
  · intro membership test test_mem
    have h := membership (transform.symm test) test_mem
    rw [selfAdjoint, transform.apply_symm_apply] at h
    exact h

/-- The dual of the image is parametrized by the inverse map on the old dual. -/
def dualEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    dual lattice ≃ dual (imageLattice lattice transform) where
  toFun value := ⟨transform.symm value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mpr (by simpa using value.property)⟩
  invFun value := ⟨transform value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mp value.property⟩
  left_inv value := by ext; simp
  right_inv value := by ext; simp

@[simp] theorem dualEquiv_eq_zero_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : dual lattice) :
    dualEquiv lattice transform selfAdjoint value = 0 ↔ value = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    have h' := congrArg (fun z : dual (imageLattice lattice transform) =>
      transform (z : Space (dimension := dimension))) h
    change transform (transform.symm (value : Space (dimension := dimension))) =
      transform (0 : Space (dimension := dimension)) at h'
    change (value : Space (dimension := dimension)) = 0
    simpa only [transform.apply_symm_apply, map_zero] using h'
  · rintro rfl
    apply Subtype.ext
    change transform.symm (0 : Space (dimension := dimension)) = 0
    exact map_zero _

def dualNonzeroEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    {value : dual lattice // value ≠ 0} ≃
      {value : dual (imageLattice lattice transform) // value ≠ 0} :=
  (dualEquiv lattice transform selfAdjoint).subtypeEquiv (by
    intro value
    exact not_congr (dualEquiv_eq_zero_iff lattice transform selfAdjoint value).symm)

/-- Exact reindexing of the entire nonzero-dual Gaussian sum. -/
theorem rhoDualNonzero_image (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (width : ℝ) :
    rhoDualNonzero width (imageLattice lattice transform) =
      ∑' value : {value : dual lattice // value ≠ 0},
        rho width (transform.symm ((value : dual lattice) : Space (dimension := dimension))) := by
  unfold rhoDualNonzero
  symm
  have reindex := (dualNonzeroEquiv lattice transform selfAdjoint).tsum_eq
    (fun value : {value : dual (imageLattice lattice transform) // value ≠ 0} =>
      rho width ((value.val : dual (imageLattice lattice transform)) : Space (dimension := dimension)))
  exact reindex

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeGaussianProjectionSmoothing. -/
section P2MDyadicModule2

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

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeGaussianLatticeScaling. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem dilation_apply (factor : ℝ) (hfactor : 0<factor) (value : ScalingSpace (dimension:=dimension)) :
    dilation factor hfactor value=factor • value := rfl

theorem dilation_symmetric (factor : ℝ) (hfactor : 0<factor) (first second : ScalingSpace (dimension:=dimension)) :
    inner ℝ (dilation factor hfactor first) second=inner ℝ first (dilation factor hfactor second) := by
  rw [dilation_apply,dilation_apply,real_inner_smul_left,real_inner_smul_right]

theorem rho_dilation_inverse (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width)
    (value : ScalingSpace (dimension:=dimension)) :
    rho width ((dilation factor hfactor).symm value)=rho (factor*width) value := by
  unfold rho
  rw [dilation_symm_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hfactor)]
  congr 1
  field_simp [hfactor.ne',hwidth.ne']

theorem rhoDualNonzero_dilation (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension)))
    (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width) :
    rhoDualNonzero width (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor))=
      rhoDualNonzero (factor*width) lattice := by
  rw [rhoDualNonzero_image lattice (dilation factor hfactor) (dilation_symmetric factor hfactor)]
  simp_rw [rho_dilation_inverse factor width hfactor hwidth]
  rfl

/-- A proved smoothing upper bound under actual lattice dilation.
Only the source smoothing condition is required. -/
theorem dilation_smoothing_le
    (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (factor width error : ℝ) (hfactor : 0<factor) (hwidth : 0<width) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ width) :
    smoothingParam (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) error ≤ factor*width := by
  have hm : rhoDualNonzero (1/(factor*width)) (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) ≤ error := by
    rw [rhoDualNonzero_dilation lattice factor (1/(factor*width)) hfactor (by positivity)]
    have he : factor*(1/(factor*width))=1/width := by field_simp
    rw [he]
    exact dual_mass_le_of_smoothing lattice herror hwidth hsmoothing
  unfold smoothingParam
  apply csInf_le
  · exact ⟨0,fun value membership => membership.1.le⟩
  · exact ⟨mul_pos hfactor hwidth,hm⟩

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeGaussianProjectionProbability. -/
section P2MDyadicModule4

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev ProbabilitySpace := EuclideanSpace ℝ (Fin dimension)

/-- Positive coset normalizer from the actual Poisson mass bound. -/
theorem rhoCoset_pos_of_smoothing
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    0<rhoCoset width lattice shift := by
  have h := (abs_le.mp (claim_3_8 lattice shift herror hwidth hsmoothing)).1
  have hp : 0<width^dimension*(ZLattice.covolume lattice)⁻¹ :=
    mul_pos (pow_pos hwidth _) (inv_pos.mpr (ZLattice.covolume_pos lattice))
  nlinarith

theorem summable_coset_of_smoothing
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (fun value : lattice => rho width ((value : ProbabilitySpace (dimension:=dimension))+shift)) := by
  by_contra hnonsummable
  have hzero := tsum_eq_zero_of_not_summable hnonsummable
  have hpos := rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing
  exact hpos.ne' hzero

/-- The genuine discrete Gaussian masses on the actual lattice coset. -/
def cosetMass (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) : ℝ :=
  discreteGaussian lattice shift width ((value : ProbabilitySpace (dimension:=dimension))+shift)

theorem cosetMass_formula (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) :
    cosetMass lattice shift width value=
      rho width ((value : ProbabilitySpace (dimension:=dimension))+shift)/rhoCoset width lattice shift := by
  unfold cosetMass discreteGaussian
  rw [Set.indicator_of_mem]
  simpa only [Set.mem_ofPred_eq,add_sub_cancel_right] using value.property

theorem cosetMass_nonneg
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (value : lattice) : 0 ≤ cosetMass lattice shift width value := by
  rw [cosetMass_formula]
  exact div_nonneg (Real.exp_nonneg _) (rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).le

theorem cosetMass_summable
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (cosetMass lattice shift width) := by
  simp_rw [funext (cosetMass_formula lattice shift width)]
  exact (summable_coset_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).div_const _

theorem cosetMass_sum
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    (∑' value : lattice,cosetMass lattice shift width value)=1 := by
  simp_rw [cosetMass_formula]
  rw [tsum_div_const]
  exact div_self (rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).ne'

/-- Literal PMF of the input lattice-Gaussian sample law. This does not
assert the existence of an efficient DGS sampler. -/
def cosetPMF
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) : PMF lattice :=
  ⟨fun value => ENNReal.ofReal (cosetMass lattice shift width value),by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [←ENNReal.ofReal_tsum_of_nonneg (cosetMass_nonneg lattice shift hwidth herror herrorOne hsmoothing)
      (cosetMass_summable lattice shift hwidth herror herrorOne hsmoothing),
      cosetMass_sum lattice shift hwidth herror herrorOne hsmoothing,ENNReal.ofReal_one]⟩

theorem cosetPMF_toReal
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (value : lattice) :
    (cosetPMF lattice shift hwidth herror herrorOne hsmoothing value).toReal=cosetMass lattice shift width value :=
  ENNReal.toReal_ofReal (cosetMass_nonneg lattice shift hwidth herror herrorOne hsmoothing value)

/-- Normalization of the real masses of any literal countable PMF. -/
theorem pmf_realMass_sum {State : Type*} (law : PMF State) :
    (∑' value : State,(law value).toReal)=1 := by
  rw [←ENNReal.tsum_toReal_eq (fun value => law.apply_ne_top value),law.tsum_coe,ENNReal.toReal_one]

theorem pmf_realMass_summable {State : Type*} (law : PMF State) :
    Summable (fun value : State => (law value).toReal) := by
  by_contra hnonsummable
  have hzero := tsum_eq_zero_of_not_summable hnonsummable
  rw [pmf_realMass_sum] at hzero
  norm_num at hzero

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeGaussianCosetGeometry. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Public coefficients and the hidden secret live in the same fixed
input basis; zero secret coordinates are allowed. -/
def publicCoordinates {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) : Index → ZMod q :=
  fun index => (basis.equivFun value index : ZMod q)

/-- Canonical input-basis representative of each public residue vector. -/
def lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) : lattice :=
  basis.equivFun.symm (fun index => ((color index).val : ℤ))

theorem publicCoordinates_lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) :
    publicCoordinates q lattice basis (lift q lattice basis color)=color := by
  funext index
  unfold publicCoordinates lift
  rw [LinearEquiv.apply_symm_apply]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem modulusLattice_le (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) :
    modulusLattice q lattice ≤ lattice := by
  intro value membership
  obtain ⟨original,horiginal,rfl⟩ := (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) value).mp membership
  have h := lattice.smul_mem (q : ℤ) horiginal
  simpa only [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h

/-- The actual point in the coset qL+u, viewed back in L. -/
def sample (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (shift : lattice) (value : modulusLattice q lattice) : lattice :=
  ⟨(value : Space (dimension:=dimension))+(shift : Space (dimension:=dimension)),
    lattice.add_mem (modulusLattice_le q lattice value.property) shift.property⟩

instance modulus_discrete (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] :
    DiscreteTopology (modulusLattice q lattice) := by unfold modulusLattice;infer_instance

instance modulus_full_rank (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice] :
    IsZLattice ℝ (modulusLattice q lattice) := by unfold modulusLattice;infer_instance

theorem publicCoordinates_add {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first+second)=publicCoordinates q lattice basis first+publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_add,Pi.add_apply,Int.cast_add]

theorem publicCoordinates_sub {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first-second)=publicCoordinates q lattice basis first-publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_sub,Pi.sub_apply,Int.cast_sub]

/-- The zero public-coefficient fiber is exactly the actual q-dilate. -/
theorem publicCoordinates_zero_iff {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) :
    publicCoordinates q lattice basis value=0 ↔ (value : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  constructor
  · intro hzero
    have hdiv (index : Index) : (q : ℤ) ∣ basis.equivFun value index :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by simpa only [publicCoordinates,Pi.zero_apply] using congrFun hzero index)
    let original := basis.equivFun.symm (fun index => basis.equivFun value index/(q : ℤ))
    have he : (q : ℤ) • original=value := by
      apply basis.equivFun.injective
      rw [map_smul]
      funext index
      simp only [original,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
      exact Int.mul_ediv_cancel' (hdiv index)
    apply (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mpr
    refine ⟨(original : Space (dimension:=dimension)),original.property,?_⟩
    have h := congrArg (fun point : lattice => (point : Space (dimension:=dimension))) he
    simpa only [Submodule.coe_smul,←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h
  · intro membership
    obtain ⟨original,horiginal,heq⟩ :=
      (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mp membership
    let originalPoint : lattice := ⟨original,horiginal⟩
    have he : value=(q : ℤ) • originalPoint := by
      apply Subtype.ext
      change (value : Space (dimension:=dimension))=(q : ℤ) • original
      rw [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast]
      exact heq.symm
    rw [he]
    funext index
    simp [publicCoordinates,Pi.smul_apply]

theorem publicCoordinates_sample {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (shift : lattice) (value : modulusLattice q lattice) :
    publicCoordinates q lattice basis (sample q lattice shift value)=publicCoordinates q lattice basis shift := by
  let original : lattice := ⟨(value : Space (dimension:=dimension)),modulusLattice_le q lattice value.property⟩
  have hz : publicCoordinates q lattice basis original=0 :=
    (publicCoordinates_zero_iff q lattice basis original).mpr value.property
  change publicCoordinates q lattice basis (original+shift)=publicCoordinates q lattice basis shift
  rw [publicCoordinates_add,hz,zero_add]

theorem publicCoordinates_fiber {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (color : Index → ZMod q) (value : lattice) :
    publicCoordinates q lattice basis value=color ↔
      ((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  rw [←publicCoordinates_zero_iff q lattice basis (value-lift q lattice basis color),
    publicCoordinates_sub,publicCoordinates_lift,sub_eq_zero]

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeFiniteProductMass. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- The full countable joint product law, not just its coordinate marginals. -/
def finiteProductMass {Index : Type*} (dimension : ℕ) (mass : Index → ℝ) (word : Fin dimension → Index) : ℝ :=
  ∏ index,mass (word index)

theorem finiteProductMass_nonnegative {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (word : Fin dimension → Index) :
    0 ≤ finiteProductMass dimension mass word := Finset.prod_nonneg (fun _ _ => hnonnegative _)

/-- A genuine full infinite product-law normalization in finitely many
coordinates, valid without finiteness of the individual coordinate space. -/
theorem finiteProductMass_hasSum {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (hsummable : Summable mass) :
    HasSum (finiteProductMass dimension mass) ((∑' value,mass value)^dimension) := by
  classical
  induction dimension with
  | zero =>
    rw [pow_zero]
    have heq : finiteProductMass 0 mass=(fun _ : Fin 0 → Index => (1 : ℝ)) := by
      funext word
      simp only [finiteProductMass,Finset.univ_eq_empty,Finset.prod_empty]
    rw [heq]
    convert hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)) using 1
    simp
  | succ dimension ih =>
    have hs := hsummable.mul_of_nonneg ih.summable hnonnegative
      (finiteProductMass_nonnegative dimension mass hnonnegative)
    have hp := hsummable.hasSum.mul ih hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass pair.1*finiteProductMass dimension mass pair.2)=
        (finiteProductMass (dimension+1) mass) ∘ (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,finiteProductMass,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [pow_succ,mul_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeGaussianCosetPartition. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators Classical

noncomputable section

variable {dimension : ℕ} {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- Exact partition of L by its actual input-basis residue vector. -/
def partitionEquiv (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) : lattice ≃ (Index → ZMod q) × modulusLattice q lattice where
  toFun value :=
    let color := publicCoordinates q lattice basis value
    (color,⟨((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)),
      (publicCoordinates_fiber q lattice basis color value).mp rfl⟩)
  invFun pair := sample q lattice (lift q lattice basis pair.1) pair.2
  left_inv value := by
    apply Subtype.ext
    change ((value : Space (dimension:=dimension))-(lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension)))+
      (lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
    abel
  right_inv pair := by
    rcases pair with ⟨color,value⟩
    have hc := (publicCoordinates_sample q lattice basis (lift q lattice basis color) value).trans
      (publicCoordinates_lift q lattice basis color)
    apply Prod.ext
    · exact hc
    · apply Subtype.ext
      change ((sample q lattice (lift q lattice basis color) value : Space (dimension:=dimension))-
        (lift q lattice basis (publicCoordinates q lattice basis (sample q lattice (lift q lattice basis color) value)) : Space (dimension:=dimension)))=
        (value : Space (dimension:=dimension))
      rw [hc]
      change ((value : Space (dimension:=dimension))+(lift q lattice basis color : Space (dimension:=dimension)))-
        (lift q lattice basis color : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
      abel

omit [DecidableEq Index] in
theorem partitionEquiv_public_symm (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) (pair : (Index → ZMod q) × modulusLattice q lattice) :
    publicCoordinates q lattice basis ((partitionEquiv q lattice basis).symm pair)=pair.1 := by
  exact congrArg Prod.fst ((partitionEquiv q lattice basis).apply_symm_apply pair)

/-- The true public coefficient law of the original lattice Gaussian. -/
def coefficientLaw (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    FiniteDist (Index → ZMod q) :=
  finiteLaw ((cosetPMF lattice 0 hwidth herror herrorOne hsmoothing).map (publicCoordinates q lattice basis))

/-- Every public point mass is the actual qL-coset Gaussian mass divided
by the original lattice normalizer. No coset probability is assumed. -/
theorem coefficientLaw_weight (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (color : Index → ZMod q) :
    (coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color=
      rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))/rhoCoset width lattice 0 := by
  classical
  let source := cosetPMF lattice 0 hwidth herror herrorOne hsmoothing
  let function : lattice → ℝ := fun value =>
    if publicCoordinates q lattice basis value=color then (source value).toReal else 0
  have hfunction : Summable function := by
    apply Summable.of_nonneg_of_le _ _ (pmf_realMass_summable source)
    · intro value;dsimp only [function];split_ifs <;> positivity
    · intro value;dsimp only [function];split_ifs <;> simp [ENNReal.toReal_nonneg]
  let equivalence := partitionEquiv q lattice basis
  have hpairs : Summable (function ∘ equivalence.symm) := equivalence.symm.summable_iff.mpr hfunction
  change Summable (fun pair => function (equivalence.symm pair)) at hpairs
  have hreindex := equivalence.symm.tsum_eq function
  rw [hpairs.tsum_prod,tsum_fintype] at hreindex
  unfold coefficientLaw
  rw [Integration.finiteLaw_map_weight]
  suffices hfinal : (∑' value : lattice,function value)=
      rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))/rhoCoset width lattice 0 by
    calc
      _ = ∑' value : lattice,function value := by
        apply tsum_congr
        intro value
        dsimp only [function,source]
        split_ifs <;> rfl
      _ = _ := hfinal
  rw [←hreindex]
  have hinner (selected : Index → ZMod q) :
      (∑' value : modulusLattice q lattice,function (equivalence.symm (selected,value)))=
      if selected=color then rhoCoset width (modulusLattice q lattice)
        (lift q lattice basis selected : Space (dimension:=dimension))/rhoCoset width lattice 0 else 0 := by
    have hpublic (value : modulusLattice q lattice) : publicCoordinates q lattice basis (equivalence.symm (selected,value))=selected :=
      partitionEquiv_public_symm q lattice basis (selected,value)
    dsimp only [function]
    simp_rw [hpublic]
    by_cases hc : selected=color
    · simp only [hc,ite_true]
      simp only [source,cosetPMF_toReal,cosetMass_formula,add_zero]
      rw [tsum_div_const]
      rfl
    · simp only [hc,ite_false,tsum_zero]
  simp_rw [hinner]
  simp

/-- The actual public residues of a wide lattice Gaussian are near uniform.
The common covolume scale is removed using both laws' true normalization,
so no determinant-index identity or unproved conditional law is needed. -/
theorem coefficientLaw_uniform (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ width)
    (hmodulus : smoothingParam (modulusLattice q lattice) error ≤ width) :
    (∑ color : Index → ZMod q, |(coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color-
      (FiniteDist.uniform (Index → ZMod q)).weight color|)/2 ≤ error/(1-error) := by
  classical
  let actual := coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing
  let reference := FiniteDist.uniform (Index → ZMod q)
  let mass := rhoCoset width lattice 0
  let main := width^dimension*(ZLattice.covolume (modulusLattice q lattice))⁻¹
  let scale := (Fintype.card (Index → ZMod q) : ℝ)*main/mass
  have hmass : 0 < mass := rhoCoset_pos_of_smoothing lattice 0 hwidth herror herrorOne hsmoothing
  have hcard : (Fintype.card (Index → ZMod q) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hscaled (color : Index → ZMod q) : scale*reference.weight color=main/mass := by
    change ((Fintype.card (Index → ZMod q) : ℝ)*main/mass)*(Fintype.card (Index → ZMod q) : ℝ)⁻¹=main/mass
    field_simp
  have hpoint (color : Index → ZMod q) : |actual.weight color-scale*reference.weight color| ≤
      error*scale*reference.weight color := by
    rw [mul_assoc error scale,hscaled]
    change |(coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color-main/mass| ≤ error*(main/mass)
    rw [coefficientLaw_weight,←sub_div,abs_div,abs_of_pos hmass]
    have h := div_le_div_of_nonneg_right
      (claim_3_8 (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension)) herror hwidth hmodulus) hmass.le
    simpa only [main,mul_div_assoc] using h
  have h := normalized_tilt_total_variation reference.weight actual.weight reference.nonneg
    (hasSum_fintype _).summable (hasSum_fintype _).summable
    (by rw [tsum_fintype];exact reference.sum_one)
    (by rw [tsum_fintype];exact actual.sum_one) scale error herror.le herrorOne hpoint
  simpa only [tsum_fintype] using h

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

/-- The coefficient vector sent to the native program represents exactly
its target-defined lattice point `latVec basis value`. -/
theorem coefficient_point (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) :
    ((integerBasis basis hdet).equivFun.symm value : Space (dimension:=dimension))=latVec basis value := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,integerBasis_apply]
  ext row
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,latVec,Matrix.mulVec,dotProduct,
    Int.cast_sum,Int.cast_mul,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

theorem publicCoordinates_coefficient_point (q : ℕ)
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (value : Fin dimension → ℤ) :
    CosetGeometry.publicCoordinates q (inputLattice basis hdet) (integerBasis basis hdet)
      ((integerBasis basis hdet).equivFun.symm value)=(fun index => (value index : ZMod q)) := by
  unfold CosetGeometry.publicCoordinates
  rw [LinearEquiv.apply_symm_apply]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule8

/- Helper module ParityPool. -/
section P2MDyadicModule9

set_option autoImplicit false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

open GaussianPoissonSeries

private theorem parity_tilt_pow (n : ℕ) (hn : 22 ≤ n) :
    (15 / 16 : ℝ) ^ ((n + 1)^3) ≤ 1 / (32 * ((n : ℝ) + 1)) := by
  let m := (n+1)^3
  have hx : (23 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (show 23 ≤ n+1 by omega)
  have hx' : 0 ≤ (n : ℝ) + 1 := by positivity
  have hs : (480 : ℝ) ≤ ((n : ℝ) + 1)^2 := by nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)+1-23 by linarith) (show 0 ≤ (n : ℝ)+1+23 by positivity)]
  have hm : 480 * ((n : ℝ) + 1) ≤ (m : ℝ) := by
    dsimp [m]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right hs hx']
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / 15 by norm_num) m
  have hb : 32 * ((n : ℝ)+1) ≤ (16/15 : ℝ)^m := by
    have haux : (1 : ℝ) + 1/15 = 16/15 := by norm_num
    rw [haux] at hbern
    linarith
  have he : (15/16 : ℝ) = 1/(16/15) := by norm_num
  rw [he, one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hb

/-- Lower tail for a countable exact product law, via a two-valued multiplicative tilt. -/
theorem exact_product_parity_failure {α : Type*} (mass : α → ℝ) (P : α → Prop)
    (hnonneg : ∀ a, 0 ≤ mass a) (hsum : HasSum mass 1)
    (hp : 7/16 ≤ ∑' a, if P a then mass a else 0)
    (n : ℕ) (hn : 22 ≤ n) :
    (∑' w : Fin ((n+1)^3) → α, (∏ j, mass (w j)) *
      (if ¬ ((n+1)^3 ≤ 4 * (Finset.univ.filter (fun j => P (w j))).card) then 1 else 0))
    ≤ 1/(32*((n:ℝ)+1)) := by
  classical
  let m := (n+1)^3
  let on : α → ℝ := fun a => if P a then mass a else 0
  let tilt : α → ℝ := fun a => if P a then 3/5 else 6/5
  let tilted : α → ℝ := fun a => mass a * tilt a
  have htilt0 (a) : 0 ≤ tilt a := by dsimp [tilt]; split <;> norm_num
  have ht0 (a) : 0 ≤ tilted a := mul_nonneg (hnonneg a) (htilt0 a)
  have ho : Summable on := by
    apply hsum.summable.of_nonneg_of_le <;> intro a <;> dsimp [on] <;> split <;> simp [hnonneg]
  have hrepr : tilted = fun a => (6/5 : ℝ) * mass a - (3/5 : ℝ) * on a := by
    funext a; by_cases h : P a <;> simp [tilted, tilt, on, h] <;> ring
  have ht : Summable tilted := by rw [hrepr]; exact (hsum.summable.mul_left _).sub (ho.mul_left _)
  have htsum : (∑' a, tilted a) ≤ 15/16 := by
    rw [hrepr, (hsum.summable.mul_left _).tsum_sub (ho.mul_left _), tsum_mul_left, tsum_mul_left, hsum.tsum_eq]
    change 7/16 ≤ ∑' a, on a at hp
    linarith
  have hgood (w : Fin m → α) : m ≤ 4 * (Finset.univ.filter (fun j => P (w j))).card ∨
      1 ≤ ∏ j, tilt (w j) := by
    let c := (Finset.univ.filter (fun j : Fin m => P (w j))).card
    let d := (Finset.univ.filter (fun j : Fin m => ¬ P (w j))).card
    by_cases h : m ≤ 4*c
    · exact Or.inl h
    right
    have hcd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun j => P (w j))
    rw [Finset.card_univ, Fintype.card_fin] at hcd
    change c+d=m at hcd
    have hdc : 3*c ≤ d := by omega
    dsimp only [tilt]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const]
    change 1 ≤ (3/5 : ℝ)^c * (6/5 : ℝ)^d
    calc
      1 ≤ ((3/5 : ℝ) * (6/5)^3)^c := one_le_pow₀ (by norm_num)
      _ = (3/5 : ℝ)^c * (6/5)^(3*c) := by rw [mul_pow,pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hdc) (by positivity)
  let bad : (Fin m → α) → ℝ := fun w => (∏ j, mass (w j)) *
      (if ¬ (m ≤ 4 * (Finset.univ.filter (fun j => P (w j))).card) then 1 else 0)
  have hp0 (w : Fin m → α) : 0 ≤ ∏ j, mass (w j) := Finset.prod_nonneg (fun _ _ => hnonneg _)
  have hbad (w) : bad w ≤ finiteProductMass m tilted w := by
    dsimp only [bad, finiteProductMass, tilted]
    rw [Finset.prod_mul_distrib]
    apply mul_le_mul_of_nonneg_left _ (hp0 w)
    rcases hgood w with h | h
    · simp only [h, not_true_eq_false, if_false]
      exact Finset.prod_nonneg (fun j _ => htilt0 (w j))
    · exact (show (if ¬ (m ≤ 4 * (Finset.univ.filter (fun j => P (w j))).card) then (1:ℝ) else 0) ≤ 1 by split <;> norm_num).trans h
  have hb0 (w) : 0 ≤ bad w := mul_nonneg (hp0 w) (by split <;> norm_num)
  have H := finiteProductMass_hasSum m tilted ht0 ht
  have hb := H.summable.of_nonneg_of_le hb0 hbad
  change (∑' w, bad w) ≤ _
  calc
    _ ≤ ∑' w, finiteProductMass m tilted w := hb.tsum_le_tsum hbad H.summable
    _ = (∑' a, tilted a)^m := H.tsum_eq
    _ ≤ (15/16 : ℝ)^m := pow_le_pow_left₀ (tsum_nonneg ht0) htsum _
    _ ≤ _ := parity_tilt_pow n hn

end InfoLossLAR.WorstCase.RegevSketch

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

private theorem inputLattice_eq_inputModule {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) :
    inputLattice D hD = inputModule D := by
  unfold inputLattice inputModule
  congr 1
  apply congrArg Set.range
  funext i
  rw [realBasis_apply]
  simp [latVec, Matrix.mulVec_single]

private theorem odd_iff_mod_two {z : ℤ} : Odd z ↔ (z : ZMod 2) = 1 := by
  rw [Int.odd_iff]
  constructor
  · intro h
    simpa [h] using (ZMod.intCast_mod z 2).symm
  · intro h
    have ha : (z % 2 : ℤ) = 0 ∨ z % 2 = 1 := by omega
    rcases ha with ha | ha
    · have hbad : (0 : ZMod 2) = 1 := by simpa [ha, h] using ZMod.intCast_mod z 2
      exact (zero_ne_one hbad).elim
    · exact ha

private theorem mod_two_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  have hn : v.val = 0 ∨ v.val = 1 := by have := ZMod.val_lt v; omega
  rw [← ZMod.natCast_zmod_val v]
  rcases hn with h | h <;> simp [h]

private theorem uniform_mod_two_coordinate {n : ℕ} (i : Fin n) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => c i = 1),
      (FiniteDist.uniform (Fin n → ZMod 2)).weight c = (1/2 : ℝ) := by
  classical
  let e : (Fin n → ZMod 2) ≃ (Fin n → ZMod 2) := Equiv.addRight (Pi.single i 1)
  let f := (FiniteDist.uniform (Fin n → ZMod 2)).weight
  have hs : ∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => c i = 1), f c =
      ∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => ¬ c i = 1), f c := by
    apply Finset.sum_equiv e
    · intro c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have he : (e c) i = c i + 1 := by simp [e, Equiv.addRight]
      rw [he]
      rcases mod_two_cases (c i) with h | h <;> simp [h]
    · intro c _
      rfl
  have hup := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → ZMod 2))
    (fun c => c i = 1) f
  rw [(FiniteDist.uniform (Fin n → ZMod 2)).sum_one, ← hs] at hup
  exact (by linarith : (∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => c i = 1), f c) = 1/2)

private theorem smoothingError_pos_small (n : ℕ) (hn : 2 ≤ n) :
    0 < smoothingError n ∧ smoothingError n ≤ 1/256 := by
  unfold smoothingError
  refine ⟨by positivity, ?_⟩
  have hsize : 2 < Nat.size (n+2) := Nat.lt_size.mpr (by omega)
  have hs : 8 ≤ (Nat.size (n+2))^2 := by
    have ha : 3 ≤ Nat.size (n+2) := hsize
    have hb := Nat.pow_le_pow_left ha 2
    exact (by decide : 8 ≤ 3^2) |>.trans hb
  calc
    1/(2 : ℝ) ^ (Nat.size (n+2))^2 ≤ 1/(2:ℝ)^8 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hs)
    _ = _ := by norm_num

/-- The literal real masses on integer coefficients have the stated sum and an odd marginal at least `7/16`. -/
theorem coefficientMass_odd_marginal {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (r : ℝ) (hr : 0 < r)
    (hs : 2 * smoothingParam (inputModule D) (smoothingError n) ≤ r) (i : Fin n) :
    (∀ z, 0 ≤ coefficientMass D r z) ∧ HasSum (coefficientMass D r) 1 ∧
      7/16 ≤ ∑' z, if Odd (z i) then coefficientMass D r z else 0 := by
  classical
  let L := inputLattice D hD
  let b := integerBasis D hD
  let e : (Fin n → ℤ) ≃ L := b.equivFun.symm.toEquiv
  let ε := smoothingError n
  obtain ⟨hε, hεsmall⟩ : 0 < ε ∧ ε ≤ 1/256 := smoothingError_pos_small n hn
  have hε1 : ε < 1 := by linarith
  have hL : smoothingParam L ε ≤ r/2 := by
    rw [← inputLattice_eq_inputModule D hD] at hs
    change 2 * smoothingParam L ε ≤ r at hs
    linarith
  have hLr : smoothingParam L ε ≤ r := by linarith
  have hr2 : 0 < r/2 := by positivity
  have hM : smoothingParam (modulusLattice 2 L) ε ≤ r := by
    simpa [modulusLattice, show 2 * (r / 2) = r by ring] using
      (dilation_smoothing_le L 2 (r/2) ε (by norm_num) hr2 hε hL)
  let source := cosetPMF L 0 hr hε hε1 hLr
  let actual := coefficientLaw 2 L b hr hε hε1 hLr
  let reference := FiniteDist.uniform (Fin n → ZMod 2)
  let t : Finset (Fin n → ZMod 2) := Finset.univ.filter (fun c => c i = 1)
  have he (z : Fin n → ℤ) : (e z : EuclideanSpace ℝ (Fin n)) = latVec D z := coefficient_point D hD z
  have hz : (∑' z : Fin n → ℤ, rho r (latVec D z)) = rhoCoset r L 0 := by
    have h := e.tsum_eq (fun x : L => rho r (x : EuclideanSpace ℝ (Fin n)))
    simpa only [rhoCoset, add_zero, he] using h
  have hm (z : Fin n → ℤ) : coefficientMass D r z = (source (e z)).toReal := by
    rw [show (source (e z)).toReal = _ from cosetPMF_toReal L 0 hr hε hε1 hLr (e z)]
    rw [cosetMass_formula, add_zero]
    change rho r (latVec D z) / (∑' y : Fin n → ℤ, rho r (latVec D y)) = _
    rw [hz, he]
  have hm0 (z) : 0 ≤ coefficientMass D r z := hm z ▸ ENNReal.toReal_nonneg
  have hms : HasSum (coefficientMass D r) 1 := by
    have hx := (pmf_realMass_summable source).hasSum
    rw [pmf_realMass_sum] at hx
    rw [show coefficientMass D r = (fun x => (source x).toReal) ∘ e from funext hm]
    exact e.hasSum_iff.mpr hx
  refine ⟨hm0, hms, ?_⟩
  have hTV : (∑ c, |actual.weight c - reference.weight c|) / 2 ≤ ε/(1-ε) :=
    coefficientLaw_uniform 2 L b hr hε hε1 hLr hM
  have hbound : ε/(1-ε) ≤ (1/32 : ℝ) := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hU : ∑ c ∈ t, reference.weight c = 1/2 := uniform_mod_two_coordinate i
  have hlow : (7/16 : ℝ) ≤ ∑ c ∈ t, actual.weight c := by
    have h1 : (∑ c ∈ t, reference.weight c) - (∑ c ∈ t, actual.weight c) ≤
        ∑ c ∈ t, |actual.weight c - reference.weight c| := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro c _
      simpa [neg_sub] using (neg_le_abs (actual.weight c - reference.weight c))
    have h2 := Finset.sum_le_univ_sum_of_nonneg (s := t) (fun c => abs_nonneg (actual.weight c - reference.weight c))
    linarith [hTV.trans hbound]
  refine hlow.trans (le_of_eq ?_)
  let fn : (Fin n → ZMod 2) → L → ℝ := fun c x =>
    if publicCoordinates 2 L b x = c then (source x).toReal else 0
  have hf (c) : Summable (fn c) := by
    apply (pmf_realMass_summable source).of_nonneg_of_le
    · intro x; dsimp [fn]; split <;> positivity
    · intro x; dsimp [fn]; split <;> simp [ENNReal.toReal_nonneg]
  have hw (c) : actual.weight c = ∑' x, fn c x := by
    change (AFT.GaussianSource.finiteLaw (source.map (publicCoordinates 2 L b))).weight c = _
    rw [Integration.finiteLaw_map_weight]
    apply tsum_congr; intro x
    by_cases h : publicCoordinates 2 L b x = c <;> simp [fn, h]
  simp_rw [hw]
  rw [← Summable.tsum_finsetSum (fun c _ => hf c)]
  rw [← e.tsum_eq (fun x : L => ∑ c ∈ t, fn c x)]
  apply tsum_congr
  intro z
  dsimp only [fn]
  have hsingle : ∑ c ∈ t, (if publicCoordinates 2 L b (e z) = c then (source (e z)).toReal else 0) =
      if publicCoordinates 2 L b (e z) ∈ t then (source (e z)).toReal else 0 := by
    rw [Finset.sum_ite_eq]
  rw [hsingle, ← hm]
  congr 1
  rw [propext odd_iff_mod_two]
  have hpc : publicCoordinates 2 L b (e z) = fun j => (z j : ZMod 2) := publicCoordinates_coefficient_point 2 D hD z
  rw [hpc]
  simp [t]

/-- Parity failure in the actual countable independent coefficient pool. -/
theorem coefficientMass_parity_pool_failure {n : ℕ} (hn : 22 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (r : ℝ) (hr : 0 < r)
    (hs : 2 * smoothingParam (inputModule D) (smoothingError n) ≤ r) (i : Fin n) :
    let m := (n+1)^3
    (∑' p : Fin m → Fin n → ℤ, (∏ j, coefficientMass D r (p j)) *
      (if ¬ (m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card) then 1 else 0))
    ≤ 1/(32*((n:ℝ)+1)) := by
  obtain ⟨h0, h1, hp⟩ := coefficientMass_odd_marginal (by omega : 2 ≤ n) D hD r hr hs i
  classical
  have hpeq : (∑' a : Fin n → ℤ, @ite ℝ (Odd (a i)) (Classical.propDecidable _) (coefficientMass D r a) 0)
      = ∑' a : Fin n → ℤ, @ite ℝ (Odd (a i)) (Int.instDecidablePredOdd (a i)) (coefficientMass D r a) 0 := by
    apply tsum_congr; intro a
    by_cases h : Odd (a i) <;> simp [h]
  have h := exact_product_parity_failure (coefficientMass D r) (fun z => Odd (z i)) h0 h1 (hpeq ▸ hp) n hn
  convert h using 1
  apply tsum_congr; intro w
  have hfilter : @Finset.filter _ (fun j => Odd (w j i)) (fun j => Int.instDecidablePredOdd (w j i)) Finset.univ =
      @Finset.filter _ (fun j => Odd (w j i)) (fun j => Classical.propDecidable _) Finset.univ := by
    ext j; simp
  simp only [hfilter]

end InfoLossLAR.WorstCase.RegevSketch

end P2MDyadicModule9

set_option autoImplicit false
open scoped BigOperators Classical
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

theorem solution :
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n → ∀ (D : Matrix (Fin n) (Fin n) ℤ), D.det ≠ 0 →
      ∀ r : ℝ, 0 < r → smoothingError n ≤ 1/8 →
      RegevLWE.GaussConv.smoothingParam (inputModule D) (smoothingError n) ≤ r/2 →
      let m := (n+1)^3
      HasSum (fun p : Fin m → Fin n → ℤ => ∏ j, coefficientMass D r (p j)) 1 ∧
      ∀ i : Fin n,
        (∑' p : Fin m → Fin n → ℤ, (∏ j, coefficientMass D r (p j)) *
          (@ite ℝ (¬ (m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card))
            (Classical.propDecidable _) 1 0)) ≤ 1/(32*((n : ℝ)+1)) := by
  refine ⟨22, ?_⟩
  intro n hn hnpos D hD r hr _ hs
  dsimp only
  have hs' : 2 * RegevLWE.GaussConv.smoothingParam (inputModule D) (smoothingError n) ≤ r := by linarith
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨hnonneg, hsum, _⟩ := coefficientMass_odd_marginal (by omega : 2 ≤ n) D hD r hr hs' i
  constructor
  · have hprod := GaussianPoissonSeries.finiteProductMass_hasSum ((n+1)^3)
      (coefficientMass D r) hnonneg hsum.summable
    rw [hsum.tsum_eq, one_pow] at hprod
    exact hprod
  · intro j
    have h := coefficientMass_parity_pool_failure hn D hD r hr hs' j
    dsimp only at h
    refine le_trans (le_of_eq ?_) h
    apply tsum_congr
    intro p
    split_ifs <;> rfl
