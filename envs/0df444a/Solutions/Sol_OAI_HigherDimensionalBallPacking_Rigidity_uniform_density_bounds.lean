-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.uniform_density_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:07:22.658997+00:00
-- url     : https://prove2.me/submissions/50a1aea0-6f8a-40c1-9357-a05f4a5c6e3b

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_affine_Holder_compactness
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_zero_mem_affineHolderModuli

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem c1Holder_contDiff (α : ℝ) (u : C1HolderSpace E α) :
    ContDiff ℝ 1 (holderValue α (c1HolderValue α u)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨holderValue α (c1HolderDeriv α u),
    (holderValue α (c1HolderDeriv α u)).continuous,c1Holder_hasFDerivAt α u⟩

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


lemma compactCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (compactCRInverseValue R u) x Complex.I -
      Complex.I • fderiv ℝ (compactCRInverseValue R u) x 1 = compactHolderValue R u x := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have hh := cauchyTransform_holder_complexCurl (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v) (compactHolderValue_bound R v) (norm_nonneg v)
    (compactHolderValue_holder R v) x
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  have hs : (2*Complex.I) • compactHolderValue R v x = -compactHolderValue R u x := by
    change (2*Complex.I) • ((Complex.I/2) • compactHolderValue R u x) = _
    rw [smul_smul,show (2*Complex.I)*(Complex.I/2)=(-1:ℂ) by ring_nf;simp,neg_one_smul]
  rw [hs] at hh
  change Complex.I • _ - _ = _ at hh
  apply neg_injective
  simpa only [neg_sub] using hh

lemma compactCRInverse_contDiff (R : ℝ) (u : CompactHolderSpace E R) :
    ContDiff ℝ 1 (compactCRInverseValue R u) := c1Holder_contDiff _ _

lemma compactCRInverse_tendsto_zero (R : ℝ) (u : CompactHolderSpace E R) :
    Tendsto (compactCRInverseValue R u) (cocompact ℂ) (𝓝 0) := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  exact cauchyTransform_tendsto_zero (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v)



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
open FramedCR

 
theorem entire_weak_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {u : ℂ → E} (hd : Differentiable ℂ u) {a : E}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a)) :
    u=fun z : ℂ => u 0+z • a := by
  have hs : Differentiable ℂ (dslope u 0) := by
    rw [←differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 (0:ℂ))).mpr hd.differentiableOn
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hl : Tendsto (dslope u 0) (cocompact ℂ) (𝓝 a) := by
    have he : Tendsto (fun z : ℂ => z⁻¹ • u z-z⁻¹ • u 0) (cocompact ℂ) (𝓝 a) := by
      simpa only [zero_smul,sub_zero] using ha.sub (hi.smul_const (u 0))
    apply he.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simp only [dslope_of_ne u hz0,slope_def_module,sub_zero,smul_sub]
  have hconst := hs.eq_const_of_tendsto_cocompact hl
  funext z
  have he := sub_smul_dslope u (0:ℂ) z
  rw [sub_zero,hconst] at he
  have he2 : u z-u 0=z • a := by simpa only [Function.const_apply] using he.symm
  exact (sub_eq_iff_eq_add.mp he2).trans (add_comm _ _)

theorem affineLine_density_representation {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (R : ℝ) (g : CompactHolderSpace (Phase n) R)
    (hg : ∀ z, compactHolderValue R g z=standardCurl u z) :
    u=densityCurve p q R g := by
  let f := compactCRInverseValue R g
  have hf : Differentiable ℝ f := (compactCRInverse_contDiff R g).differentiable (by simp)
  have hholo : Differentiable ℂ (fun z => u z-f z) := by
    intro z
    have hd := ((hu.1.differentiable (by simp) z).hasFDerivAt).sub ((hf z).hasFDerivAt)
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hd.differentiableAt,?_⟩
    change fderiv ℝ (u-(f : ℂ → Phase n)) z Complex.I =
      Complex.I • fderiv ℝ (u-(f : ℂ → Phase n)) z 1
    rw [hd.fderiv]
    simp only [sub_apply,smul_sub]
    have he := compactCRInverse_rightInverse R g z
    rw [hg] at he
    change fderiv ℝ f z Complex.I-Complex.I • fderiv ℝ f z 1 =
      fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1 at he
    exact sub_eq_sub_iff_sub_eq_sub.mp he.symm
  obtain ⟨a,ha,hal⟩ := hu.2.2.2.2
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hfl : Tendsto (fun z => z⁻¹ • f z) (cocompact ℂ) (𝓝 (0 : Phase n)) := by
    simpa only [zero_smul] using hi.smul (compactCRInverse_tendsto_zero R g)
  have hw : Tendsto (fun z => z⁻¹ • (u z-f z)) (cocompact ℂ) (𝓝 a) := by
    simpa only [smul_sub,sub_zero] using hal.sub hfl
  have hrep := entire_weak_affine hholo hw
  have ha' : a=q-p-(f 1-f 0) := by
    have h := congrFun hrep (1:ℂ)
    simp only [one_smul,hu.2.2.1,hu.2.2.2.1] at h
    calc
      a=(p-f 0+a)-(p-f 0) := by abel
      _=(q-f 1)-(p-f 0) := by rw [←h]
      _=q-p-(f 1-f 0) := by abel
  funext z
  have h := congrFun hrep z
  simp only [hu.2.2.1,ha'] at h
  change u z=p+z • (q-p)+(f z-f 0-z • (f 1-f 0))
  rw [smul_sub] at h
  linear_combination h

theorem densityCurve_leading {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) :
    Tendsto (fun z : ℂ => z⁻¹ • densityCurve p q R g z) (cocompact ℂ)
      (𝓝 (densitySlope p q R g)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have he (z : ℂ) : densityCurve p q R g z =
      (p-compactCRInverseValue R g 0)+z • densitySlope p q R g+compactCRInverseValue R g z := by
    simp only [densityCurve,markedCRInverse,densitySlope,smul_sub]
    abel
  have h := (hi.smul_const (p-compactCRInverseValue R g 0)).add
    (tendsto_const_nhds (x := densitySlope p q R g)) |>.add
    (hi.smul (compactCRInverse_tendsto_zero R g))
  simp only [zero_smul,zero_add,add_zero] at h
  apply h.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  rw [he]
  simp only [smul_add,smul_smul,inv_mul_cancel₀ hz0,one_smul]

theorem affineLine_density_slope_ne {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (R : ℝ) (g : CompactHolderSpace (Phase n) R)
    (hg : ∀ z, compactHolderValue R g z=standardCurl u z) :
    densitySlope p q R g ≠ 0 := by
  obtain ⟨a,ha,hal⟩ := hu.2.2.2.2
  rw [affineLine_density_representation hu R g hg] at hal
  have he := tendsto_nhds_unique (densityCurve_leading p q R g) hal
  exact he ▸ ha

theorem densitySlope_continuous {n : ℕ} (p q : Phase n) (R : ℝ) :
    Continuous (densitySlope p q R) := by
  have h (z : ℂ) : Continuous (fun g : CompactHolderSpace (Phase n) R =>
      compactCRInverseValue R g z) :=
    ((c1HolderEval ((1:ℝ)/3) z).comp (compactCRInverse R)).continuous
  exact continuous_const.sub ((h 1).sub (h 0))

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity FramedCR

 theorem compactCRInverseValue_eq_of_value_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R S : ℝ) (g : CompactHolderSpace E R) (h : CompactHolderSpace E S)
    (he : ∀ z, compactHolderValue R g z=compactHolderValue S h z) :
    compactCRInverseValue R g=compactCRInverseValue S h := by
  ext z
  simp only [compactCRInverseValue_apply]
  congr 1
  funext w
  rw [he w]

 theorem densityAffineSize_continuous {n : ℕ} (p : Phase n) (R : ℝ) : Continuous (densityAffineSize p R) := by
  have hc : Continuous (compactCRInverseValue (E := Phase n) R) :=
    ((holderValue ((1:ℝ)/3)).comp ((c1HolderValue ((1:ℝ)/3)).comp (compactCRInverse R))).continuous
  exact (continuous_const.sub ((BoundedContinuousFunction.evalCLM ℝ (0:ℂ)).continuous.comp hc)).norm.add hc.norm

 theorem uniform_density_bounds_oai (n : ℕ) (hn : 3≤n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p≠q) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ R : ℝ, ∀ y∈affineHolderModuli J p q R,
      m < ‖densitySlope p q R y.2‖ ∧ densityAffineSize p R y.2 < M := by
  obtain ⟨R,hR,hK,hRc⟩ := homotopy_affine_Holder_compactness n hn J hJs hJ hc hs p q hpq
  have hne : (affineHolderModuli J p q R).Nonempty := ⟨(0,0),zero_mem_affineHolderModuli J hJ p q hpq R⟩
  have ha : Continuous (fun y : ℝ × CompactHolderSpace (Phase n) R => ‖densitySlope p q R y.2‖) :=
    ((densitySlope_continuous p q R).comp continuous_snd).norm
  have hb : Continuous (fun y : ℝ × CompactHolderSpace (Phase n) R => densityAffineSize p R y.2) :=
    (densityAffineSize_continuous p R).comp continuous_snd
  obtain ⟨a,haK,haMin⟩ := hK.exists_isMinOn hne ha.continuousOn
  obtain ⟨b,hbK,hbMax⟩ := hK.exists_isMaxOn hne hb.continuousOn
  have hap : 0<‖densitySlope p q R a.2‖ := by
    obtain ⟨_,u,hu,hg⟩ := haK
    exact norm_pos_iff.mpr (affineLine_density_slope_ne hu R a.2 hg)
  have hbs : 0≤densityAffineSize p R b.2 := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨‖densitySlope p q R a.2‖/2,densityAffineSize p R b.2+1,half_pos hap,by linarith,?_⟩
  intro S y hy
  obtain ⟨ht,u,hu,hg⟩ := hy
  let g : CompactHolderSpace (Phase n) R := ⟨y.2.1,by intro z hz; change compactHolderValue S y.2 z=0; rw [hg z]; exact hRc y.1 ht u hu z hz⟩
  have hg0 : ∀ z, compactHolderValue R g z=standardCurl u z := hg
  have hgK : (y.1,g)∈affineHolderModuli J p q R := ⟨ht,u,hu,hg0⟩
  have he : compactCRInverseValue R g=compactCRInverseValue S y.2 :=
    compactCRInverseValue_eq_of_value_eq R S g y.2 (fun _ => rfl)
  have hae : densitySlope p q R g=densitySlope p q S y.2 := by simp only [densitySlope,he]
  have hbe : densityAffineSize p R g=densityAffineSize p S y.2 := by simp only [densityAffineSize,he]
  have hl := haMin hgK
  have hu' := hbMax hgK
  change ‖densitySlope p q R a.2‖ ≤ ‖densitySlope p q R g‖ at hl
  change densityAffineSize p R g ≤ densityAffineSize p R b.2 at hu'
  rw [hae] at hl
  rw [hbe] at hu'
  exact ⟨lt_of_lt_of_le (half_lt_self hap) hl,lt_of_le_of_lt hu' (lt_add_one _)⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.uniform_density_bounds_oai := @OAI.HigherDimensionalBallPacking.Rigidity.uniform_density_bounds_oai
