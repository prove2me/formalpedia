-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dual_parity_empirical_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T23:09:53.792753+00:00
-- url     : https://prove2.me/submissions/99005b32-24d1-436e-91ce-fa2d2f35f724

import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Mathlib
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

set_option linter.all false

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

/- Helper module MomentExpect. -/
section P2MDyadicModule0

set_option autoImplicit false

set_option maxHeartbeats 600000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSketch.PoolMoment

noncomputable section

section Expectation

variable {A : Type*} (P : A → ℝ)

def E (f : A → ℝ) : ℝ := ∑' z, P z * f z

def S (f : A → ℝ) : Prop := Summable (fun z => P z * f z)

theorem e_const (hnorm : HasSum P 1) (c : ℝ) : E P (fun _ => c) = c := by
  rw [E, tsum_mul_right, hnorm.tsum_eq, one_mul]

theorem s_const (hnorm : HasSum P 1) (c : ℝ) : S P (fun _ => c) := hnorm.summable.mul_right c

theorem s_mono (hP : ∀ z, 0 ≤ P z) {f g : A → ℝ} (hf : ∀ z, 0 ≤ f z)
    (hle : ∀ z, f z ≤ g z) (hg : S P g) : S P f :=
  hg.of_nonneg_of_le (fun z => mul_nonneg (hP z) (hf z)) (fun z => mul_le_mul_of_nonneg_left (hle z) (hP z))

theorem e_mono (hP : ∀ z, 0 ≤ P z) {f g : A → ℝ} (hf : S P f)
    (hle : ∀ z, f z ≤ g z) (hg : S P g) : E P f ≤ E P g :=
  hf.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left (hle z) (hP z)) hg

theorem s_add {f g : A → ℝ} (hf : S P f) (hg : S P g) : S P (fun z => f z + g z) := by
  simpa only [S, mul_add] using hf.add hg

theorem s_sub {f g : A → ℝ} (hf : S P f) (hg : S P g) : S P (fun z => f z - g z) := by
  simpa only [S, mul_sub] using hf.sub hg

theorem e_add {f g : A → ℝ} (hf : S P f) (hg : S P g) : E P (fun z => f z + g z) = E P f + E P g := by
  unfold E; simp only [mul_add]; exact hf.tsum_add hg

theorem e_sub {f g : A → ℝ} (hf : S P f) (hg : S P g) : E P (fun z => f z - g z) = E P f - E P g := by
  unfold E; simp only [mul_sub]; exact hf.tsum_sub hg

theorem s_scale (c : ℝ) {f : A → ℝ} (hf : S P f) : S P (fun z => c * f z) := by
  simpa only [S, mul_left_comm] using hf.mul_left c

theorem e_scale (c : ℝ) (f : A → ℝ) : E P (fun z => c * f z) = c * E P f := by
  unfold E; simp only [mul_left_comm (P _), tsum_mul_left]

theorem s_sum {I : Type*} {f : I → A → ℝ} {t : Finset I} (hf : ∀ i ∈ t, S P (f i)) :
    S P (fun z => ∑ i ∈ t, f i z) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [S]
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact s_add P (hf a (Finset.mem_insert_self a t)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem e_sum {I : Type*} {f : I → A → ℝ} {t : Finset I} (hf : ∀ i ∈ t, S P (f i)) :
    E P (fun z => ∑ i ∈ t, f i z) = ∑ i ∈ t, E P (f i) := by
  unfold E; simp only [Finset.mul_sum]; exact Summable.tsum_finsetSum hf

end Expectation

/-- Signed version of `dependentProductMass_hasSum`, obtained by applying its nonnegative
summability argument to absolute values. -/
theorem signed_product_hasSum {A : Type*} (m : ℕ) (f : Fin m → A → ℝ)
    (h : ∀ j, Summable (f j)) :
    HasSum (fun p : Fin m → A => ∏ j, f j (p j)) (∏ j, ∑' z, f j z) := by
  classical
  induction m with
  | zero =>
    simpa only [Finset.univ_eq_empty, Finset.prod_empty, Fintype.sum_unique] using
      (hasSum_fintype (fun _ : Fin 0 → A => (1 : ℝ)))
  | succ m ih =>
    have ht := ih (fun j => f j.succ) (fun j => h j.succ)
    let g : (Fin m → A) → ℝ := fun p => ∏ j, f j.succ (p j)
    have ht' : Summable g := ht.summable
    have hab := (h 0).norm.mul_of_nonneg ht'.norm
      (fun z => norm_nonneg (f 0 z)) (fun p => norm_nonneg (g p))
    have hmul : Summable (fun p : A × (Fin m → A) => f 0 p.1 * g p.2) :=
      Summable.of_norm (by simpa only [norm_mul] using hab)
    have hp := (h 0).hasSum.mul ht hmul
    have hcomp : (fun p : A × (Fin m → A) => f 0 p.1 * g p.2) =
        (fun p : Fin (m+1) → A => ∏ j, f j (p j)) ∘
          (Fin.consEquiv (fun _ : Fin (m+1) => A)) := by
      funext p
      simp [g, Fin.consEquiv, Fin.prod_univ_succ]
    rw [hcomp] at hp
    simpa only [Fin.prod_univ_succ] using
      (Fin.consEquiv (fun _ : Fin (m+1) => A)).hasSum_iff.mp hp

section Independent

variable {A : Type*} {m : ℕ} (P : A → ℝ)

def joint (p : Fin m → A) : ℝ := ∏ j, P (p j)

theorem joint_nonneg (hP : ∀ z, 0 ≤ P z) (p : Fin m → A) : 0 ≤ joint P p :=
  Finset.prod_nonneg (fun j _ => hP (p j))

theorem joint_mul_prod (g : Fin m → A → ℝ) (hg : ∀ j, S P (g j)) :
    S (joint P) (fun p => ∏ j, g j (p j)) ∧
      E (joint P) (fun p => ∏ j, g j (p j)) = ∏ j, E P (g j) := by
  have h := signed_product_hasSum m (fun j z => P z * g j z) hg
  have hs : HasSum (fun p => joint P p * ∏ j, g j (p j)) (∏ j, E P (g j)) := by
    simpa only [joint, Finset.prod_mul_distrib, E] using h
  exact ⟨hs.summable, hs.tsum_eq⟩

theorem joint_one (hnorm : HasSum P 1) (f : A → ℝ) (hf : S P f) (i : Fin m) :
    S (joint P) (fun p => f (p i)) ∧ E (joint P) (fun p => f (p i)) = E P f := by
  have h := joint_mul_prod P (fun j => if j = i then f else fun _ => 1) (by
    intro j; split <;> first | exact hf | exact s_const P hnorm 1)
  have hpoint (p : Fin m → A) :
      (∏ j : Fin m, (if j = i then f else fun _ => 1) (p j)) = f (p i) := by
    rw [Finset.prod_eq_single i] <;> simp_all
  have hright : (∏ j : Fin m, E P (if j = i then f else fun _ => 1)) = E P f := by
    rw [Finset.prod_eq_single i] <;> simp_all [e_const P hnorm]
  simpa only [hpoint, hright] using h

theorem joint_two (hnorm : HasSum P 1) (f g : A → ℝ) (hf : S P f) (hg : S P g)
    (i j : Fin m) (hij : i ≠ j) :
    S (joint P) (fun p => f (p i) * g (p j)) ∧
      E (joint P) (fun p => f (p i) * g (p j)) = E P f * E P g := by
  have h := joint_mul_prod P (fun k => if k = i then f else if k = j then g else fun _ => 1) (by
    intro k
    by_cases hk : k = i
    · simpa only [if_pos hk] using hf
    · by_cases hk' : k = j
      · simpa only [if_neg hk, if_pos hk'] using hg
      · simpa only [if_neg hk, if_neg hk'] using s_const P hnorm 1)
  have hpoint (p : Fin m → A) :
      (∏ k : Fin m, (if k = i then f else if k = j then g else fun _ => 1) (p k)) =
        f (p i) * g (p j) := by
    have hsplit (k : Fin m) : (if k = i then f else if k = j then g else fun _ => 1) (p k) =
        (if k = i then f (p k) else 1) * (if k = j then g (p k) else 1) := by
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
    simp only [hsplit, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hright : (∏ k : Fin m, E P (if k = i then f else if k = j then g else fun _ => 1)) = E P f * E P g := by
    have hsplit (k : Fin m) : E P (if k = i then f else if k = j then g else fun _ => 1) =
        (if k = i then E P f else 1) * (if k = j then E P g else 1) := by
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [e_const P hnorm]
    simp only [hsplit, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  simpa only [hpoint, hright] using h

end Independent

end

end InfoLossLAR.WorstCase.RegevSketch.PoolMoment

end P2MDyadicModule0

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule1

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

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeGaussianPoissonSeries. -/
section P2MDyadicModule2

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open MeasureTheory FourierTransform RegevLWE.GaussConv

open scoped FourierTransform SchwartzMap

noncomputable section

variable {dimension : ℕ}

abbrev Space := EuclideanSpace ℝ (Fin dimension)

/-- The genuine lattice periodization admits a Schwartz Gaussian with the
actual Regev pi/width convention, for every positive real width. -/
theorem exists_schwartz_rho (width : ℝ) (hwidth : 0 < width) :
    ∃ function : 𝓢(Space (dimension:=dimension),ℂ),
      ∀ point,function point=(rho width point : ℂ) := by
  obtain ⟨gaussian,hgaussian⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin dimension)
  let unit : ℝˣ := Units.mk0 width⁻¹ (inv_ne_zero hwidth.ne')
  let dilation : Space (dimension:=dimension) ≃L[ℝ] Space (dimension:=dimension) := ContinuousLinearEquiv.smulLeft unit
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ dilation gaussian,fun point => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,hgaussian,rho]
  congr 2
  have hdilation : dilation point=width⁻¹ • point := rfl
  rw [hdilation,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hwidth)]
  ring

theorem fourier_schwartz_rho (width : ℝ) (hwidth : 0 < width)
    (function : 𝓢(Space (dimension:=dimension),ℂ))
    (hfunction : ∀ point,function point=(rho width point : ℂ)) (frequency : Space (dimension:=dimension)) :
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension))) (⇑function) frequency=
      (width : ℂ)^dimension*(rho (1/width) frequency : ℂ) := by
  have hequal : (⇑function : Space (dimension:=dimension) → ℂ)=fun point => (rhoShift width 0 point : ℂ) := by
    funext point
    rw [hfunction]
    simp [rhoShift]
  have h := fourier_rhoShift hwidth (0 : Space (dimension:=dimension)) frequency
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension)))
    (fun point => (rhoShift width 0 point : ℂ)) frequency=_ at h
  rw [hequal,h]
  simp [inner_zero_left]

private theorem inner_nondegenerate : (innerₗ (Space (dimension:=dimension))).Nondegenerate :=
  ⟨fun point hzero => inner_self_eq_zero.mp (hzero point),fun point hzero => inner_self_eq_zero.mp (hzero point)⟩

private theorem inner_flip_eq : LinearMap.BilinForm.flip (innerₗ (Space (dimension:=dimension)))=
    innerₗ (Space (dimension:=dimension)) := by
  ext first second
  exact real_inner_comm first second

/-- The literal complex Gaussian amplitude periodized over an actual
lattice, before extracting real mass or normalizing a quantum vector. -/
def periodizedGaussian (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) : ℂ :=
  ∑' point : lattice,(rho width (shift+(point : Space (dimension:=dimension))) : ℂ)

/-- Exact complete dual Fourier expansion of the genuine periodized
Gaussian amplitude. Every dual Gaussian coefficient is retained. -/
theorem periodized_poisson (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width)
    (shift : Space (dimension:=dimension)) :
    periodizedGaussian lattice width shift=
      (ZLattice.covolume lattice : ℂ)⁻¹*
        ∑' frequency : dual lattice,((width : ℂ)^dimension*
          (rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
          (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have hpoisson := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral volume
    (innerₗ (Space (dimension:=dimension))) (inner_nondegenerate (dimension:=dimension)) lattice function shift
  rw [inner_flip_eq (dimension:=dimension)] at hpoisson
  simpa only [periodizedGaussian,hfunction,fourier_schwartz_rho width hwidth function hfunction,dual,innerₗ_apply_apply] using hpoisson

/-- Absolute summability of the same complete dual series, before any
finite Fourier reindexing or truncation is performed. -/
theorem summable_dual_series (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width)
    (shift : Space (dimension:=dimension)) :
    Summable (fun frequency : dual lattice =>
      (rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ)*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have h := ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule volume
    (innerₗ (Space (dimension:=dimension))) (inner_nondegenerate (dimension:=dimension)) lattice function shift
  rw [inner_flip_eq] at h
  change Summable (fun frequency : dual lattice =>
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension))) (⇑function)
      (frequency : Space (dimension:=dimension))*
      (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) at h
  simp only [fourier_schwartz_rho width hwidth function hfunction,mul_assoc] at h
  exact (summable_mul_left_iff (pow_ne_zero dimension (Complex.ofReal_ne_zero.mpr hwidth.ne'))).mp h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeLatticeGaussianMass. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped FourierTransform

noncomputable section

variable {dimension : ℕ}

/-- The complex amplitude periodization is the canonical inclusion of the
real lattice Gaussian mass, with the same shift and summation filter. -/
theorem periodized_eq_rhoCoset (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) :
    periodizedGaussian lattice width shift=(rhoCoset width lattice shift : ℂ) := by
  unfold periodizedGaussian rhoCoset
  rw [Complex.ofReal_tsum (L:=.unconditional lattice)]
  apply tsum_congr
  intro point
  rw [add_comm]

/-- Poisson summation at zero gives the exact positive real mass identity. -/
theorem rhoCoset_zero_poisson (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    rhoCoset width lattice 0=width^dimension*(ZLattice.covolume lattice)⁻¹*
      ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) := by
  have h := periodized_poisson lattice width hwidth 0
  rw [periodized_eq_rhoCoset] at h
  simp only [inner_zero_left,AddChar.map_zero_eq_one,Circle.coe_one,mul_one,tsum_mul_left] at h
  rw [←Complex.ofReal_tsum (L:=.unconditional (dual lattice))] at h
  have hequal : (rhoCoset width lattice 0 : ℂ)=
      ((width^dimension*(ZLattice.covolume lattice)⁻¹*
        ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast hequal

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeLatticeGaussianCosetMax. -/
section P2MDyadicModule4

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

variable {dimension : ℕ}

theorem rhoCoset_nonneg (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) : 0≤rhoCoset width lattice shift :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem norm_periodizedGaussian (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) :
    ‖periodizedGaussian lattice width shift‖=rhoCoset width lattice shift := by
  rw [periodized_eq_rhoCoset,Complex.norm_real,Real.norm_of_nonneg (rhoCoset_nonneg lattice width shift)]

/-- Among all translates, the genuine Gaussian mass on a lattice is
maximized at the unshifted lattice, by the full positive Poisson series. -/
theorem rhoCoset_shift_le_zero (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    rhoCoset width lattice shift≤rhoCoset width lattice 0 := by
  have hs : Summable (fun frequency : dual lattice =>
      ((width : ℂ)^dimension*(rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) := by
    simpa only [mul_assoc] using (summable_dual_series lattice width hwidth shift).mul_left ((width : ℂ)^dimension)
  have hpoint (frequency : dual lattice) :
      ‖((width : ℂ)^dimension*(rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)‖=
      width^dimension*rho (1/width) (frequency : Space (dimension:=dimension)) := by
    rw [norm_mul,norm_mul,Circle.norm_coe,mul_one,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg hwidth.le,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ rho (1/width) (frequency : Space (dimension:=dimension)) from (Real.exp_pos _).le)]
  have hbound := norm_tsum_le_tsum_norm hs.norm
  simp only [hpoint,tsum_mul_left] at hbound
  have hpoisson := congrArg norm (periodized_poisson lattice width hwidth shift)
  rw [norm_periodizedGaussian,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (ZLattice.covolume_pos lattice MeasureTheory.volume).le] at hpoisson
  rw [hpoisson,rhoCoset_zero_poisson lattice width hwidth]
  have h := mul_le_mul_of_nonneg_left hbound
    (inv_nonneg.mpr (ZLattice.covolume_pos lattice MeasureTheory.volume).le)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeLatticeGaussianSummable. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- Schwartz decay gives absolute convergence on the actual lattice;
no Gaussian normalizer or sampling algorithm is assumed. -/
theorem summable_schwartz_lattice
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (function : 𝓢(Space (dimension:=dimension),ℂ)) :
    Summable (fun point : lattice => function (point : Space (dimension:=dimension))) := by
  let exponent := Module.finrank ℤ lattice+1
  have hs := ZLattice.summable_norm_pow_inv lattice exponent (Nat.lt_succ_self _)
  apply Summable.of_norm
  apply Summable.of_norm_bounded_eventually (g:=fun point : lattice =>
    SchwartzMap.seminorm ℝ exponent 0 function*‖point‖⁻¹^exponent) (hs.mul_left _)
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_singleton (0 : lattice))
  intro point hnot
  simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff] at hnot ⊢
  by_contra hne
  apply hnot
  have hpositive : 0<‖point‖^exponent := pow_pos (norm_pos_iff.mpr hne) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ function exponent (point : Space (dimension:=dimension))
  change ‖point‖^exponent*‖function (point : Space (dimension:=dimension))‖ ≤ _ at hdecay
  rw [norm_norm,inv_pow,←div_eq_mul_inv,le_div_iff₀ hpositive,mul_comm]
  exact hdecay

/-- In particular, every positive-width genuine lattice Gaussian is
summable over the original full-rank lattice. -/
theorem summable_gaussian_lattice
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) :
    Summable (fun point : lattice => rho width (point : Space (dimension:=dimension))) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have h := (summable_schwartz_lattice lattice function).norm
  simp only [hfunction,Complex.norm_real,Real.norm_eq_abs] at h
  have habsolute (point : lattice) : |rho width (point : Space (dimension:=dimension))|=
      rho width (point : Space (dimension:=dimension)) := abs_of_pos (Real.exp_pos _)
  simpa only [habsolute] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeLatticeGaussianCosetSummable. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- Every translate has absolutely summable genuine Gaussian mass. -/
theorem summable_gaussian_coset
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => rho width ((point : Space (dimension:=dimension))+shift)) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  let translated := SchwartzMap.compSubConstCLM ℂ (-shift) function
  have h := summable_schwartz_lattice lattice translated
  have hvalue (point : lattice) : translated point=(rho width ((point : Space (dimension:=dimension))+shift) : ℂ) := by
    simp only [translated,SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add,hfunction]
  simp only [hvalue] at h
  exact Complex.summable_ofReal.mp h

theorem rhoCoset_zero_pos (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    0<rhoCoset width lattice 0 := by
  have h := (summable_gaussian_lattice lattice width hwidth).tsum_pos
    (fun _ => (Real.exp_pos _).le) (0 : lattice) (Real.exp_pos _)
  simpa only [rhoCoset,add_zero] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule6

/- Helper module MomentGaussian. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option maxHeartbeats 500000

open scoped BigOperators Classical RealInnerProductSpace

namespace InfoLossLAR.WorstCase.RegevSketch.PoolMoment

open IntegerBasis GaussianPoissonSeries RegevLWE.GaussConv

noncomputable section

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem coefficient_hasSum (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (r : ℝ) (hr : 0 < r) : (∀ z, 0 ≤ coefficientMass B r z) ∧ HasSum (coefficientMass B r) 1 := by
  let L := inputLattice B hB
  let E : (Fin n → ℤ) ≃ L := (integerBasis B hB).equivFun.symm.toEquiv
  have he (z : Fin n → ℤ) : (E z : V) = latVec B z := coefficient_point B hB z
  let w := fun z : Fin n → ℤ => rho r (latVec B z)
  let Z := ∑' z, w z
  have hw (z) : 0 ≤ w z := (Real.exp_pos _).le
  have hs : Summable w := by
    have h := E.summable_iff.mpr (summable_gaussian_lattice L r hr)
    simpa only [Function.comp_def, he, w] using h
  have hp : 0 < Z := hs.tsum_pos hw 0 (Real.exp_pos _)
  refine ⟨fun z => by change 0 ≤ w z / Z; exact div_nonneg (hw z) hp.le, ?_⟩
  have h : HasSum (fun z => w z / Z) (Z / Z) := hs.hasSum.div_const Z
  rwa [div_self hp.ne'] at h

theorem gaussian_mgf (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (r : ℝ) (hr : 0 < r) (u : V) :
    let f := fun z => coefficientMass B r z * Real.exp (⟪u, latVec B z⟫ / r);
    Summable f ∧ (∑' z, f z) ≤ Real.exp (‖u‖ ^ 2 / (4 * Real.pi)) := by
  let L := inputLattice B hB
  let E : (Fin n → ℤ) ≃ L := (integerBasis B hB).equivFun.symm.toEquiv
  have he (z : Fin n → ℤ) : (E z : V) = latVec B z := coefficient_point B hB z
  let Z := ∑' z : Fin n → ℤ, rho r (latVec B z)
  let c : ℝ := r / (2 * Real.pi)
  have hZ : Z = rhoCoset r L 0 := by
    have h := E.tsum_eq (fun x : L => rho r (x : V))
    simpa only [Z, he, rhoCoset, add_zero] using h
  have hZp : 0 < Z := hZ ▸ rhoCoset_zero_pos L r hr
  let K := Real.exp (‖u‖ ^ 2 / (4 * Real.pi))
  let g := fun z : Fin n → ℤ => rho r (latVec B z + (-c) • u)
  have hgs : Summable g := by
    have h := E.summable_iff.mpr (summable_gaussian_coset L r hr ((-c) • u))
    simpa only [Function.comp_def, he, g] using h
  have hg : (∑' z, g z) = rhoCoset r L ((-c) • u) := by
    have h := E.tsum_eq (fun x : L => rho r ((x : V) + (-c) • u))
    simpa only [g, he, rhoCoset, add_comm] using h
  have hpoint (z : Fin n → ℤ) :
      coefficientMass B r z * Real.exp (⟪u, latVec B z⟫ / r) = (K / Z) * g z := by
    have hscalar : 0 ≤ c := by dsimp [c]; positivity
    have heq :
        rho r (latVec B z) * Real.exp (⟪u, latVec B z⟫ / r) = K * g z := by
      dsimp only [K, g, rho]
      rw [← Real.exp_add, ← Real.exp_add, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg hscalar, real_inner_smul_right, real_inner_comm (latVec B z) u]
      congr 1
      dsimp [c]
      field_simp [hr.ne', Real.pi_ne_zero]
      ring
    change rho r (latVec B z) / Z * _ = _
    calc
      _ = (rho r (latVec B z) * Real.exp (⟪u, latVec B z⟫ / r)) / Z := by ring
      _ = _ := by rw [heq]; ring
  dsimp only
  simp_rw [hpoint]
  refine ⟨hgs.mul_left _, ?_⟩
  rw [tsum_mul_left, hg]
  calc
    _ ≤ (K / Z) * rhoCoset r L 0 := mul_le_mul_of_nonneg_left
      (rhoCoset_shift_le_zero L r hr _) (div_nonneg (Real.exp_pos _).le hZp.le)
    _ = _ := by rw [← hZ]; field_simp; rfl

end

end InfoLossLAR.WorstCase.RegevSketch.PoolMoment

end P2MDyadicModule7

/- Helper module MomentSingle. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical RealInnerProductSpace

namespace InfoLossLAR.WorstCase.RegevSketch.PoolMoment

noncomputable section

private theorem sq_le_exp_add_exp_neg (x : ℝ) : x^2 ≤ Real.exp x + Real.exp (-x) - 2 := by
  have h : (x/2)^2 ≤ Real.sinh (x/2)^2 := by
    by_cases hx : 0 ≤ x/2
    · exact (sq_le_sq₀ hx (hx.trans (Real.self_le_sinh_iff.mpr hx))).mpr
        (Real.self_le_sinh_iff.mpr hx)
    · have hx' : x/2 ≤ 0 := le_of_not_ge hx
      have hy := Real.sinh_le_self_iff.mpr hx'
      nlinarith [mul_nonneg (sub_nonneg.mpr hy) (neg_nonneg.mpr (hy.trans hx')),
        mul_nonneg (sub_nonneg.mpr hy) (neg_nonneg.mpr hx')]
  have h₂ : Real.cosh x = 1 + 2 * Real.sinh (x/2)^2 := by
    conv_lhs => rw [show x = 2 * (x/2) by ring, Real.cosh_two_mul]
    rw [Real.cosh_sq']
    ring
  rw [Real.cosh_eq] at h₂
  linarith

private theorem pow_four_le_exp (x : ℝ) : x^4 ≤ 24 * (Real.exp x + Real.exp (-x)) := by
  by_cases hx : 0 ≤ x
  · have h := Real.pow_div_factorial_le_exp x hx 4
    norm_num at h
    linarith [Real.exp_pos (-x)]
  · have h := Real.pow_div_factorial_le_exp (-x) (by linarith) 4
    norm_num at h
    linarith [Real.exp_pos x]

section Scalar

variable {A : Type*} (P : A → ℝ) (y : A → ℝ)

theorem scalar_moments (hP : ∀ z, 0 ≤ P z) (hnorm : HasSum P 1)
    (hplus : Summable (fun z => P z * Real.exp (y z)))
    (hminus : Summable (fun z => P z * Real.exp (-y z)))
    (hplus' : (∑' z, P z * Real.exp (y z)) ≤ 12/11)
    (hminus' : (∑' z, P z * Real.exp (-y z)) ≤ 12/11) :
    (Summable (fun z => P z * y z ^ 2) ∧ (∑' z, P z * y z ^ 2) ≤ 1) ∧
    (Summable (fun z => P z * y z ^ 4) ∧ (∑' z, P z * y z ^ 4) ≤ 64) := by
  let U := fun z => P z * Real.exp (y z) + P z * Real.exp (-y z)
  have hU : Summable U := hplus.add hminus
  have hU' : (∑' z, U z) ≤ 24/11 := by
    change (∑' z, (P z * Real.exp (y z) + P z * Real.exp (-y z))) ≤ _
    rw [hplus.tsum_add hminus]
    linarith
  let W := fun z => U z - 2 * P z
  have hW : Summable W := hU.sub (hnorm.summable.mul_left 2)
  have hW' : (∑' z, W z) ≤ 1 := by
    change (∑' z, (U z - 2 * P z)) ≤ _
    rw [hU.tsum_sub (hnorm.summable.mul_left 2), tsum_mul_left, hnorm.tsum_eq]
    linarith
  have hbound₂ (z : A) : P z * y z ^ 2 ≤ W z := by
    have h := mul_le_mul_of_nonneg_left (sq_le_exp_add_exp_neg (y z)) (hP z)
    dsimp [W, U]
    linarith only [h]
  have hbound₄ (z : A) : P z * y z ^ 4 ≤ 24 * U z := by
    have h := mul_le_mul_of_nonneg_left (pow_four_le_exp (y z)) (hP z)
    dsimp [U]
    linarith only [h]
  have hs₂ : Summable (fun z => P z * y z ^ 2) := Summable.of_nonneg_of_le
    (fun z => mul_nonneg (hP z) (sq_nonneg (y z))) hbound₂ hW
  have hs₄ : Summable (fun z => P z * y z ^ 4) := Summable.of_nonneg_of_le
    (fun z => mul_nonneg (hP z) (by positivity)) hbound₄ (hU.mul_left 24)
  refine ⟨⟨hs₂, (hs₂.tsum_le_tsum hbound₂ hW).trans hW'⟩, ⟨hs₄, ?_⟩⟩
  have h := hs₄.tsum_le_tsum hbound₄ (hU.mul_left 24)
  rw [tsum_mul_left] at h
  linarith

end Scalar

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem unit_moments (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0)
    (r : ℝ) (hr : 0 < r) (u : V) (hu : ‖u‖ ≤ 1) :
    let P := coefficientMass D r;
    let y := fun z => ⟪u, latVec D z⟫ / r;
    (Summable (fun z => P z * y z ^ 2) ∧ (∑' z, P z * y z ^ 2) ≤ 1) ∧
    (Summable (fun z => P z * y z ^ 4) ∧ (∑' z, P z * y z ^ 4) ≤ 64) := by
  have hPi : 0 < 4*Real.pi := by positivity
  have hs : ‖u‖^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (norm_nonneg u)]
  have he : Real.exp (‖u‖ ^ 2 / (4 * Real.pi)) ≤ 12/11 := by
    calc
      _ ≤ Real.exp (1/12) := Real.exp_le_exp.mpr (by
        apply (div_le_iff₀ hPi).mpr
        linarith [Real.pi_gt_three])
      _ ≤ _ := by
        have h := Real.exp_bound_div_one_sub_of_interval (show (0:ℝ) ≤ 1/12 by norm_num)
          (show (1:ℝ)/12 < 1 by norm_num)
        norm_num at h ⊢
        exact h
  have ⟨hP, hnorm⟩ := coefficient_hasSum D hD r hr
  have ⟨hp, hp'⟩ := gaussian_mgf D hD r hr u
  have ⟨hm, hm'⟩ := gaussian_mgf D hD r hr (-u)
  simp only [inner_neg_left, neg_div, norm_neg] at hm hm'
  exact scalar_moments _ _ hP hnorm hp hm (hp'.trans he) (hm'.trans he)

end

end InfoLossLAR.WorstCase.RegevSketch.PoolMoment

end P2MDyadicModule8

/- Helper module MomentVariance. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSketch.PoolMoment

noncomputable section

variable {A : Type*} {m : ℕ} (P : A → ℝ)

theorem variance (hP : ∀ z, 0 ≤ P z) (hnorm : HasSum P 1) (f : A → ℝ)
    (hf : S P f) (hf₂ : S P (fun z => f z ^ 2)) :
    let g := fun z => f z - E P f;
    S (joint (m := m) P) (fun p => (∑ j, g (p j))^2) ∧
    E (joint (m := m) P) (fun p => (∑ j, g (p j))^2) ≤ (m:ℝ) * E P (fun z => f z ^ 2) := by
  let μ := E P f
  let g := fun z => f z - μ
  have hμ : S P (fun _ => μ) := s_const P hnorm _
  have hg : S P g := s_sub P hf hμ
  have hEg : E P g = 0 := by
    change E P (fun z => f z - μ) = 0
    rw [e_sub P hf hμ, e_const P hnorm]
    exact sub_self _
  have hg₂eq : (fun z => g z ^ 2) = (fun z => f z ^ 2 - (2 * μ) * f z + μ ^ 2) := by
    funext z; dsimp [g]; ring
  have hmid := s_scale P (2*μ) hf
  have hlast : S P (fun _ => μ ^ 2) := s_const P hnorm _
  have hdiff := s_sub P hf₂ hmid
  have hg₂ : S P (fun z => g z ^ 2) := hg₂eq ▸ s_add P hdiff hlast
  have hEg₂ : E P (fun z => g z ^ 2) ≤ E P (fun z => f z ^ 2) := by
    rw [hg₂eq, e_add P hdiff hlast, e_sub P hf₂ hmid, e_scale P, e_const P hnorm]
    change _ - (2*μ)*μ + μ^2 ≤ _
    nlinarith [sq_nonneg μ]
  let K := joint (m := m) P
  have hprod (i j : Fin m) : S K (fun p => g (p i) * g (p j)) ∧
      E K (fun p => g (p i) * g (p j)) = if i = j then E P (fun z => g z ^ 2) else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [if_true, pow_two] using joint_one P hnorm (fun z => g z ^ 2) hg₂ i
    · simp only [if_neg hij]
      simpa only [hEg, mul_zero] using joint_two P hnorm g g hg hg i j hij
  have hs (i : Fin m) : S K (fun p => ∑ j, g (p i) * g (p j)) :=
    s_sum K (fun j _ => (hprod i j).1)
  have hexpand : (fun p : Fin m → A => (∑ j, g (p j))^2) =
      (fun p : Fin m → A => ∑ i, ∑ j, g (p i) * g (p j)) := by
    funext p; rw [pow_two, Finset.sum_mul]; simp only [Finset.mul_sum]
  change S K (fun p => (∑ j, g (p j))^2) ∧ _
  rw [hexpand]
  refine ⟨s_sum K (fun i _ => hs i), ?_⟩
  have he (i : Fin m) : E K (fun p => ∑ j, g (p i) * g (p j)) = E P (fun z => g z ^ 2) := by
    rw [e_sum K (fun j _ => (hprod i j).1)]
    simp only [fun j => (hprod i j).2, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [e_sum K (fun i _ => hs i)]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hEg₂ (by positivity)

end

end InfoLossLAR.WorstCase.RegevSketch.PoolMoment

end P2MDyadicModule9

/- Helper module MomentFrob. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSketch.PoolMoment

noncomputable section

variable {A I : Type*} [Fintype I] {m : ℕ} (P : A → ℝ) (Y : A → I → ℝ)

def centered (p : Fin m → A) (i j : I) : ℝ :=
  ∑ k, (Y (p k) i * Y (p k) j - E P (fun z => Y z i * Y z j))

def frob (p : Fin m → A) : ℝ := ∑ ij : I × I, centered P Y p ij.1 ij.2 ^ 2

theorem coordinate_moments (hP : ∀ z, 0 ≤ P z) (hnorm : HasSum P 1)
    (hfour : ∀ i, S P (fun z => Y z i ^ 4) ∧ E P (fun z => Y z i ^ 4) ≤ 64) (i j : I) :
    let f := fun z => Y z i * Y z j;
    S P f ∧ S P (fun z => f z ^ 2) ∧ E P (fun z => f z ^ 2) ≤ 64 := by
  let f := fun z => Y z i * Y z j
  let g := fun z => (Y z i ^ 4 + Y z j ^ 4) / 2
  have hfg (z : A) : f z ^ 2 ≤ g z := by
    dsimp [f, g]
    nlinarith only [sq_nonneg (Y z i ^ 2 - Y z j ^ 2)]
  have hg_eq : g = fun z => (1/2:ℝ) * (Y z i ^ 4 + Y z j ^ 4) := by
    funext z; dsimp [g]; ring
  have hs_sum := s_add P (hfour i).1 (hfour j).1
  have hg : S P g := by rw [hg_eq]; exact s_scale P _ hs_sum
  have hEg : E P g ≤ 64 := by
    rw [hg_eq, e_scale P, e_add P (hfour i).1 (hfour j).1]
    linarith [(hfour i).2, (hfour j).2]
  have hf₂ : S P (fun z => f z ^ 2) := s_mono P hP (fun z => sq_nonneg _) hfg hg
  have hEf₂ := e_mono P hP hf₂ hfg hg
  have hf : S P f := by
    unfold S
    apply Summable.of_norm
    have hg' : S P (fun z => (1:ℝ) + f z ^ 2) := s_add P (s_const P hnorm 1) hf₂
    exact Summable.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => by
      rw [norm_mul, Real.norm_of_nonneg (hP z), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (f z + 1), sq_nonneg (f z - 1)]) (hP z)) hg'
  exact ⟨hf, hf₂, hEf₂.trans hEg⟩

theorem frob_expectation (hP : ∀ z, 0 ≤ P z) (hnorm : HasSum P 1)
    (hfour : ∀ i, S P (fun z => Y z i ^ 4) ∧ E P (fun z => Y z i ^ 4) ≤ 64) :
    S (joint P) (frob P Y (m := m)) ∧
    E (joint P) (frob P Y (m := m)) ≤ (Fintype.card I : ℝ)^2 * m * 64 := by
  have hvar (i j : I) : S (joint P) (fun p : Fin m → A => centered P Y p i j ^ 2) ∧
      E (joint P) (fun p : Fin m → A => centered P Y p i j ^ 2) ≤ (m:ℝ)*64 := by
    let f := fun z => Y z i * Y z j
    have ⟨hf, hf₂, hfbound⟩ := coordinate_moments P Y hP hnorm hfour i j
    have ⟨hs, hE⟩ := variance (m := m) P hP hnorm f hf hf₂
    exact ⟨hs, hE.trans (mul_le_mul_of_nonneg_left hfbound (by positivity))⟩
  refine ⟨s_sum _ (fun ij _ => (hvar ij.1 ij.2).1), ?_⟩
  unfold frob
  rw [e_sum _ (fun ij _ => (hvar ij.1 ij.2).1)]
  calc
    _ ≤ ∑ _ : I × I, (m:ℝ)*64 := Finset.sum_le_sum (fun ij _ => (hvar ij.1 ij.2).2)
    _ = _ := by simp [Fintype.card_prod, pow_two, mul_assoc]

theorem quadratic_point (p : Fin m → A) (x : I → ℝ)
    (h : E P (fun z => (∑ i, x i * Y z i)^2) ≤ ∑ i, x i ^ 2)
    (hs : ∀ i j, S P (fun z => Y z i * Y z j))
    (hfrob : frob P Y p ≤ ((m:ℝ)*100)^2) :
    (∑ k, (∑ i, x i * Y (p k) i)^2) ≤ ((m:ℝ)*101) * ∑ i, x i ^ 2 := by
  let Q := ∑ i, x i ^ 2
  let B := fun ij : I × I => x ij.1 * x ij.2
  let C := fun ij : I × I => centered P Y p ij.1 ij.2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hprod (z : A) : (∑ i, x i * Y z i)^2 = ∑ ij : I × I, B ij * (Y z ij.1 * Y z ij.2) := by
    rw [Fintype.sum_prod_type, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    dsimp [B]; ring
  have hE : E P (fun z => (∑ i, x i * Y z i)^2) =
      ∑ ij : I × I, B ij * E P (fun z => Y z ij.1 * Y z ij.2) := by
    simp_rw [hprod, e_sum P (fun ij _ => s_scale P (B ij) (hs ij.1 ij.2)), e_scale]
  have hcenter : (∑ ij, B ij * C ij) =
      (∑ k, (∑ i, x i * Y (p k) i)^2) - m * E P (fun z => (∑ i, x i * Y z i)^2) := by
    rw [hE]
    simp_rw [C, centered, Finset.mul_sum, mul_sub]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← hprod]
    rw [Finset.mul_sum]
  have hx : (∑ ij, B ij ^ 2) = Q^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [B, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    simp only [Q, pow_two]
  have hc : (∑ ij, C ij ^ 2) = frob P Y p := rfl
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ B C
  rw [hx, hc] at hCauchy
  have hsq : (∑ ij, B ij * C ij)^2 ≤ (((m:ℝ)*100) * Q)^2 := by
    calc
      _ ≤ Q^2 * frob P Y p := hCauchy
      _ ≤ Q^2 * ((m:ℝ)*100)^2 := mul_le_mul_of_nonneg_left hfrob (sq_nonneg _)
      _ = _ := by ring
  have habs : |∑ ij, B ij * C ij| ≤ ((m:ℝ)*100)*Q := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) hQ)).mp
    rwa [sq_abs]
  have hle := (le_abs_self _).trans habs
  rw [hcenter] at hle
  have he := mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ m by positivity)
  change E P (fun z => (∑ i, x i * Y z i)^2) ≤ Q at h
  change _ ≤ ((m:ℝ)*101)*Q
  linarith only [hle, he]

end

end InfoLossLAR.WorstCase.RegevSketch.PoolMoment

end P2MDyadicModule10

/- Helper module MomentFinal. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped Classical BigOperators RealInnerProductSpace

namespace InfoLossLAR.WorstCase.RegevSketch.PoolMoment

noncomputable section

private theorem direction_moment {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0)
    (r : ℝ) (hr : 0 < r) (x : Fin n → ℝ) :
    E (coefficientMass D r) (fun z => (∑ a, x a * (((D.mulVec z) a : ℤ) : ℝ) / r)^2)
      ≤ ∑ a, x a ^ 2 := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let P := coefficientMass D r
  have hnorm : ‖v‖ ^ 2 = ∑ a, x a ^ 2 := EuclideanSpace.real_norm_sq_eq v
  have hx (z : Fin n → ℤ) : (∑ a, x a * (((D.mulVec z) a : ℤ) : ℝ) / r) =
      ⟪v, latVec D z⟫ / r := by
    rw [PiLp.inner_apply, Finset.sum_div]
    apply Finset.sum_congr rfl; intro a _
    change x a * (((D.mulVec z) a : ℤ) : ℝ) / r = inner ℝ (x a) (((D.mulVec z) a : ℤ) : ℝ) / r
    rw [Real.inner_apply, mul_comm]
  simp_rw [hx, ← hnorm]
  by_cases hv : ‖v‖ = 0
  · have hv' := norm_eq_zero.mp hv
    simp [hv', E]
  · let u : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v
    have hup : ‖u‖ = 1 := by
      rw [show u = ‖v‖⁻¹ • v from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ hv]
    have hu := (unit_moments D hD r hr u hup.le).1.2
    change E P (fun z => (⟪u, latVec D z⟫ / r)^2) ≤ 1 at hu
    have heq (z : Fin n → ℤ) : (⟪v, latVec D z⟫ / r)^2 = ‖v‖^2 * (⟪u, latVec D z⟫ / r)^2 := by
      dsimp only [u]; rw [real_inner_smul_left]; field_simp
    simp_rw [heq, e_scale]
    exact (mul_le_mul_of_nonneg_left hu (sq_nonneg ‖v‖)).trans_eq (mul_one _)

/-- The exact rational moment-failure probability at the specified width. This result does not
need a smoothing hypothesis; the positive integer `d` is the determinant clearing factor. -/
theorem empiricalMoment_failure {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0)
    (d : ℤ) (hd : d ≠ 0) (δ : ℚ) (hδ : 0 < δ) :
    let m := (n+1)^3;
    let r := (Int.natAbs d : ℚ) / (100*δ);
    let M (p : Fin m → Fin n → ℤ) : Prop := ∀ x : Fin n → ℤ,
      64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
        (m : ℚ) * (d : ℚ)^2 * (∑ a, (x a : ℚ)^2);
    (∑' p : Fin m → Fin n → ℤ,
      (∏ j, coefficientMass D (r : ℝ) (p j)) * (if ¬ M p then 1 else 0))
      ≤ 1 / (32 * ((n:ℝ)+1)) := by
  let m := (n+1)^3
  let r : ℚ := (Int.natAbs d : ℚ) / (100*δ)
  have hdabs : 0 < Int.natAbs d := Int.natAbs_pos.mpr hd
  have hrQ : 0 < r := div_pos (by exact_mod_cast hdabs) (by positivity)
  have hr : 0 < (r:ℝ) := by exact_mod_cast hrQ
  have hmNat : 0 < m := by dsimp [m]; positivity
  have hm : 0 < (m:ℝ) := by exact_mod_cast hmNat
  let P := coefficientMass D (r:ℝ)
  let Y : (Fin n → ℤ) → Fin n → ℝ := fun z a => (((D.mulVec z) a : ℤ) : ℝ) / (r:ℝ)
  have ⟨hP, hnorm⟩ := coefficient_hasSum D hD (r:ℝ) hr
  have hfour (a : Fin n) : S P (fun z => Y z a ^ 4) ∧ E P (fun z => Y z a ^ 4) ≤ 64 := by
    let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i : Fin n => if i = a then (1:ℝ) else 0)
    have hu : ‖u‖ ≤ 1 := by
      have hsq : ‖u‖^2 = 1 := by rw [EuclideanSpace.real_norm_sq_eq]; simp [u, ite_pow]
      nlinarith [norm_nonneg u]
    have he (z : Fin n → ℤ) : ⟪u, latVec D z⟫ / (r:ℝ) = Y z a := by
      rw [PiLp.inner_apply]
      change (∑ i, inner ℝ (if i = a then (1:ℝ) else 0) (((D.mulVec z) i : ℤ) : ℝ)) / (r:ℝ) = _
      simp only [Real.inner_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Y]
    simpa only [he, S, E, P] using (unit_moments D hD (r:ℝ) hr u hu).2
  have hF := frob_expectation (m:=m) P Y hP hnorm hfour
  have hGood (p : Fin m → Fin n → ℤ) (hp : frob P Y p ≤ ((m:ℝ)*100)^2) (x : Fin n → ℤ) :
      64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
        (m : ℚ) * (d : ℚ)^2 * (∑ a, (x a : ℚ)^2) := by
    have hs (i j : Fin n) := (coordinate_moments P Y hP hnorm hfour i j).1
    have hdir (x' : Fin n → ℝ) : E P (fun z => (∑ a, x' a * Y z a)^2) ≤ ∑ a, x' a ^ 2 := by
      simpa only [Y, mul_div_assoc] using direction_moment D hD (r:ℝ) hr x'
    have hb := quadratic_point P Y p (fun a => (x a : ℝ)) (hdir _) hs hp
    have hY (j : Fin m) : (∑ a, (x a : ℝ) * Y (p j) a) = (∑ a, (x a : ℝ) * (((D.mulVec (p j)) a : ℤ) : ℝ)) / (r:ℝ) := by
      simp only [Y, Finset.sum_div, mul_div_assoc]
    simp_rw [hY, div_pow, ← Finset.sum_div] at hb
    have hb' := (div_le_iff₀ (sq_pos_of_pos hr)).mp hb
    have hd2 : ((Int.natAbs d : ℝ))^2 = (d:ℝ)^2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    have hscl : 64 * (δ:ℝ)^2 * (r:ℝ)^2 * 101 ≤ (d:ℝ)^2 := by
      have hrdef : ((r:ℚ):ℝ) = (Int.natAbs d : ℝ) / (100*(δ:ℝ)) := by dsimp [r]; push_cast; rfl
      rw [hrdef, div_pow, ← hd2]
      have hδR : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
      field_simp
      nlinarith [mul_nonneg (sq_nonneg (δ:ℝ)) (sq_nonneg (Int.natAbs d : ℝ))]
    have hcast : 64 * (δ:ℝ)^2 * (∑ j, (∑ a, (x a:ℝ) * (((D.mulVec (p j)) a : ℤ) : ℝ))^2) ≤
        (m:ℝ) * (d:ℝ)^2 * (∑ a, (x a:ℝ)^2) := by
      calc
        _ ≤ (64 * (δ:ℝ)^2) * (((m:ℝ)*101) * (∑ a, (x a:ℝ)^2) * (r:ℝ)^2) :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
        _ = (m:ℝ) * (∑ a, (x a:ℝ)^2) * (64 * (δ:ℝ)^2 * (r:ℝ)^2 * 101) := by ring
        _ ≤ (m:ℝ) * (∑ a, (x a:ℝ)^2) * (d:ℝ)^2 := mul_le_mul_of_nonneg_left hscl (by positivity)
        _ = _ := by ring
    exact_mod_cast hcast
  dsimp only
  change E (joint P) (fun p => if ¬ (∀ x : Fin n → ℤ,
    64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
      (m : ℚ) * (d : ℚ)^2 * (∑ a, (x a : ℚ)^2)) then 1 else 0) ≤ _
  let bad : (Fin m → Fin n → ℤ) → ℝ := fun p => if ¬ (∀ x : Fin n → ℤ,
    64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
      (m : ℚ) * (d : ℚ)^2 * (∑ a, (x a : ℚ)^2)) then 1 else 0
  change E (joint P) bad ≤ _
  let T : ℝ := ((m:ℝ)*100)^2
  have hT : 0 < T := by dsimp [T]; positivity
  have hpt (p : Fin m → Fin n → ℤ) : bad p ≤ T⁻¹ * frob P Y p := by
    by_cases hbad : ¬ (∀ x : Fin n → ℤ,
      64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
        (m : ℚ) * (d : ℚ)^2 * (∑ a, (x a : ℚ)^2))
    · simp only [bad, if_pos hbad]
      have hh : ¬ frob P Y p ≤ T := fun hp => hbad (hGood p hp)
      rw [← div_eq_inv_mul, le_div_iff₀ hT, one_mul]
      exact le_of_lt (lt_of_not_ge hh)
    · simp only [bad, if_neg hbad]
      exact mul_nonneg (inv_nonneg.mpr hT.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hscaled := s_scale (joint P) T⁻¹ hF.1
  have hsb := s_mono (joint P) (joint_nonneg P hP) (fun p => by dsimp [bad]; split <;> norm_num) hpt hscaled
  calc
    _ ≤ T⁻¹ * E (joint P) (frob P Y (m := m)) := by
      rw [← e_scale]; exact e_mono (joint P) (joint_nonneg P hP) hsb hpt hscaled
    _ ≤ T⁻¹ * ((n:ℝ)^2 * (m:ℝ) * 64) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hT.le)
      simpa only [Fintype.card_fin] using hF.2
    _ ≤ 1 / (32 * ((n:ℝ)+1)) := by
      have hp : 0 < (n:ℝ) + 1 := by positivity
      have hsq : (n:ℝ)^2 ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
      have hmdef : (m:ℝ) = ((n:ℝ)+1)^3 := by dsimp [m]; push_cast; rfl
      rw [← div_eq_inv_mul]
      apply (div_le_div_iff₀ hT (by positivity)).mpr
      rw [one_mul]
      have hle := mul_le_mul_of_nonneg_right hsq (show 0 ≤ (m:ℝ)*64*(32*((n:ℝ)+1)) by positivity)
      calc
        _ ≤ (((n:ℝ)+1)^2) * ((m:ℝ)*64*(32*((n:ℝ)+1))) := by
          calc
            _ = (n:ℝ)^2 * ((m:ℝ)*64*(32*((n:ℝ)+1))) := by ring
            _ ≤ _ := hle
        _ = (m:ℝ) * (m:ℝ) * 2048 := by rw [hmdef]; ring
        _ ≤ T := by dsimp only [T]; nlinarith only [sq_nonneg (m:ℝ)]

end

end InfoLossLAR.WorstCase.RegevSketch.PoolMoment

end P2MDyadicModule11

/- Helper module Solution. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option maxHeartbeats 200000

open QAlgorithms.Complexity

open scoped BigOperators Classical

open InfoLossLAR.WorstCase.RegevSketch

private theorem massIteEq (w : ℝ) (A B : Prop) (h : A ↔ B)
    (da : Decidable A) (db : Decidable B) :
    w * (@ite ℝ A da 1 0) = w * (@ite ℝ B db 1 0) := by
  have hAB := propext h
  subst B
  rw [Subsingleton.elim da db]

theorem solution :
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n → ∀ (D : Matrix (Fin n) (Fin n) ℤ), D.det ≠ 0 →
      ∀ (s : ℤ) (δ : ℚ), s ≠ 0 → 0 < δ →
      let r : ℚ := (Int.natAbs s : ℚ) / (100*δ)
      let m := (n+1)^3
      (∑' p : Fin m → Fin n → ℤ, (∏ j, coefficientMass D r (p j)) *
        (@ite ℝ (¬ ∀ x : Fin n → ℤ,
          64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
            (m : ℚ) * (s : ℚ)^2 * (∑ a, (x a : ℚ)^2)) (Classical.propDecidable _) 1 0))
        ≤ 1/(32*((n : ℝ)+1)) := by
  refine ⟨0,?_⟩
  intro n _ _ D hD s δ hs hδ
  dsimp only
  convert PoolMoment.empiricalMoment_failure D hD s hs δ hδ using 1
  apply tsum_congr
  intro p
  apply massIteEq
  exact Iff.rfl

end P2MDyadicModule12
