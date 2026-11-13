-- Prove2me | solution 1 for OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:09:42.242398+00:00
-- url     : https://prove2.me/submissions/961492d4-412b-4bb1-a98d-4ebad5ff1bc1

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T261

section
-- module Solutions.OAIQ262_TG.Triangular_Energy_Mixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Classical Filter
namespace TriangularUniversal

lemma triangularPoint_coord_zero (j k : ℤ) :
    triangularPoint (j, k) 0 = Real.sqrt (2 / Real.sqrt 3) * ((j : ℝ) + (k : ℝ) / 2) := by
  simp [triangularPoint]

lemma triangularPoint_coord_one (j k : ℤ) :
    triangularPoint (j, k) 1 = Real.sqrt (2 / Real.sqrt 3) * ((k : ℝ) * Real.sqrt 3 / 2) := by
  simp [triangularPoint]

lemma triangularPoint_norm_sq (j k : ℤ) :
    b * ‖triangularPoint (j, k)‖ ^ 2 = (j : ℝ) ^ 2 + (j : ℝ) * (k : ℝ) + (k : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [triangularPoint_coord_zero, triangularPoint_coord_one, Real.norm_eq_abs,
    sq_abs, mul_pow]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (2 / Real.sqrt (3 : ℝ))) ^ 2 = 2 / Real.sqrt 3 :=
    Real.sq_sqrt (by positivity)
  rw [hc]
  dsimp [b]
  field_simp
  nlinarith [hs]

end TriangularUniversal

open scoped BigOperators Topology NNReal ENNReal Polynomial
open Filter Finset MeasureTheory
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Lattice_LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace AtomicTriangular
lemma triangular_scale_eq : (Real.sqrt b)⁻¹=Real.sqrt (2/Real.sqrt 3) := by
  rw [←Real.sqrt_inv]
  congr 1
  simp [b,inv_div]
lemma triangularPoint_eq_support (v : ℤ × ℤ) : triangularPoint v=TriangularUniversal.triangularPoint v := by
  unfold triangularPoint TriangularUniversal.triangularPoint
  rw [triangular_scale_eq]
  congr 2
  unfold b
  ring_nf
lemma b_pos : 0 < b := by unfold b; positivity
lemma b_sq : b^2=3/4 := by
  unfold b
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
lemma triangularPoint_norm_sq (j k : ℤ) :
    b*‖triangularPoint (j,k)‖^2=(j:ℝ)^2+(j:ℝ)*k+(k:ℝ)^2 := by
  rw [triangularPoint_eq_support]
  exact TriangularUniversal.triangularPoint_norm_sq j k
lemma eisenstein_mod36_finite : ∀ j k : Fin 36,
    ((j.val:ℤ)^2+(j.val:ℤ)*k.val+(k.val:ℤ)^2)%36∈Construction.residues := by decide +kernel
lemma eisenstein_mod36 (j k : ℤ) :
    (j^2+j*k+k^2)%36∈Construction.residues := by
  let j' : Fin 36 := ⟨(j%36).toNat,by have := Int.emod_nonneg j (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos j (by norm_num : (0:ℤ)<36); omega⟩
  let k' : Fin 36 := ⟨(k%36).toNat,by have := Int.emod_nonneg k (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos k (by norm_num : (0:ℤ)<36); omega⟩
  have hj : (j'.val:ℤ)=j%36 := Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))
  have hk : (k'.val:ℤ)=k%36 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
  have hh := eisenstein_mod36_finite j' k'
  rw [hj,hk] at hh
  simpa [Int.add_emod,Int.mul_emod,pow_two,Int.emod_emod] using hh
lemma A_radial_node {x : Plane} (hx : x∈A) (hx0 : x≠0) :
    ∃ n : Construction.Node,Construction.radial x=n.val := by
  obtain ⟨⟨j,k⟩,rfl⟩ := hx
  let n : ℤ := j^2+j*k+k^2
  have he : Construction.radial (triangularPoint (j,k))=(n:ℝ) := by
    change b*‖triangularPoint (j,k)‖^2=_
    rw [triangularPoint_norm_sq]
    dsimp [n]
    push_cast
    rfl
  have hn : 0 < n := by
    have hp : 0 < Construction.radial (triangularPoint (j,k)) :=
      mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr hx0))
    rw [he] at hp
    exact_mod_cast hp
  exact ⟨⟨n,hn,eisenstein_mod36 j k⟩,he⟩
lemma dualA_integer_coordinates {w : Plane} (hw : w∈dualA) :
    ∃ j k : ℤ,w 0=(Real.sqrt b)*(j:ℝ) ∧ (Real.sqrt b)*w 1=(k:ℝ)-(j:ℝ)/2 := by
  obtain ⟨j,hj⟩ := hw (triangularPoint (1,0)) ⟨(1,0),rfl⟩
  obtain ⟨k,hk⟩ := hw (triangularPoint (0,1)) ⟨(0,1),rfl⟩
  have hr : (Real.sqrt b)^2=b := Real.sq_sqrt b_pos.le
  have hp : 0 < Real.sqrt b := Real.sqrt_pos.mpr b_pos
  simp [triangularPoint,inner_smul_left,inner_add_left,EuclideanSpace.inner_single_left] at hj hk
  refine ⟨j,k,?_,?_⟩
  · field_simp at hj
    nlinarith
  · field_simp at hj hk
    apply (mul_left_cancel₀ hp.ne')
    nlinarith [congrArg (fun t : ℝ => t*w 1) hr]
lemma dualA_radial_node {w : Plane} (hw : w∈dualA) (hw0 : w≠0) :
    ∃ n : Construction.Node,Construction.radial w=n.val := by
  obtain ⟨j,k,hj,hk⟩ := dualA_integer_coordinates hw
  let n : ℤ := j^2-j*k+k^2
  have he : Construction.radial w=(n:ℝ) := by
    change b*‖w‖^2=_
    rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    simp only [Real.norm_eq_abs,sq_abs]
    have hr : (Real.sqrt b)^2=b := Real.sq_sqrt b_pos.le
    have hb := b_sq
    have hk' := congrArg (fun t : ℝ => t^2) hk
    rw [mul_pow,hr] at hk'
    rw [hj,mul_pow,hr]
    dsimp [n]
    push_cast
    nlinarith
  have hn : 0 < n := by
    have hpos : 0 < Construction.radial w := mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr hw0))
    rw [he] at hpos
    exact_mod_cast hpos
  have hm : n%36∈Construction.residues := by
    convert eisenstein_mod36 j (-k) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [n]
    congr 1
    ring
  exact ⟨⟨n,hn,hm⟩,he⟩
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap lp
open Complex Matrix

namespace AtomicTriangular.Construction

lemma finiteCoordinates_coefficientInput (C : ℝ) (a : TrigonometricCoefficients)
    (w : TailCoefficients) (i : Fin 22) :
    finiteCoordinates (coefficientInput C a w) i = a i := by
  unfold finiteCoordinates coefficientInput
  split_ifs with hi
  · exact congrArg (fun j : Fin 22 => a j) (Fin.ext (by dsimp; omega))
  · exact congrArg (fun j : Fin 22 => a j) (Fin.ext (by dsimp; omega))

lemma actualInput_fixed_zero (side : Fin 2) {z : ℝ} (hz : 0 < z) (hzB : z ≤ Z) :
    (actualInput side z hz hzB).finiteC 0 = 11/25 ∧
    (actualInput side z hz hzB).finiteD 0 = 0 := by
  constructor
  · change finiteApprox side (actualParameter z) 0 +
      extendFiniteError (actualFiniteError side z hz hzB) 0 = 11/25
    erw [finiteApprox_fixed side (actualParameter z) 0,
      extendFiniteError_fixed (actualFiniteError side z hz hzB) 0,
      add_zero, gamma_actual]
    rfl
  · change finiteApprox side (actualParameter z) 1 +
      extendFiniteError (actualFiniteError side z hz hzB) 1 = 0
    erw [finiteApprox_fixed side (actualParameter z) 1,
      extendFiniteError_fixed (actualFiniteError side z hz hzB) 1,
      add_zero, gamma_actual]
    rfl

lemma largeGaussian_hasAtomicConstruction {α : ℝ} (hα : 1 ≤ α) :
    HasAtomicConstruction α (largeGaussianPair hα).first := by
  let z := gaussianZ α
  have hz : 0 < z := (gaussianZ_bounds hα).1
  have hzB : z ≤ Z := (gaussianZ_bounds hα).2.le
  refine ⟨FiniteCertificate.minusBlock_isUnit, FiniteCertificate.plusBlock_isUnit,
    Uplus_equation, Uminus_equation,
    (fun side => actualInput side z hz hzB),
    (fun side i => actualFiniteError side z hz hzB i), ?_, ?_, ?_⟩
  · intro side
    obtain ⟨hc, hd⟩ := actualInput_fixed_zero side hz hzB
    refine ⟨rfl, hc, hd, ?_⟩
    intro i
    dsimp only
    rw [actualInput, finiteCoordinates_coefficientInput]
    rfl
  · intro side
    refine ⟨?_, (actualInput side z hz hzB).summable, ?_⟩
    · simpa only [AtomicTriangular.L1Kernel.l1_norm, tsum_fintype] using
        actualFiniteError_norm side hz hzB
    · change (∑' n : TailNode,
        (|actualTail side z hz hzB (n,0)| + |actualTail side z hz hzB (n,1)|)) < _
      rw [tail_pairs_norm]
      exact actualTail_norm side hz hzB
  · intro x
    change ((((normalizingDen z)⁻¹ *
        pairSchwartz (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) x : ℝ) : ℂ)) = _
    rw [Complex.ofReal_mul, Complex.ofReal_inv, ← pairComplex_eq, fourier_inputComplex]
    simp only [pairComplex, Pi.add_apply]
    ring

end AtomicTriangular.Construction

namespace AtomicTriangular

theorem sharp_gaussian_minorants_atomic (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → Construction.HasAtomicConstruction α f) := by
  let p := gaussianPair α hα
  refine ⟨p.first, p.first_radial, p.minorant, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [p.fourier_first]
    exact ⟨rfl, p.positive w⟩
  · intro a ha ha0
    obtain ⟨n, hn⟩ := A_radial_node ha ha0
    exact p.contact a n hn
  · intro w hw hw0
    obtain ⟨n, hn⟩ := dualA_radial_node hw hw0
    rw [p.fourier_first, p.zeros w n hn, ofReal_zero]
  · intro hlarge
    change Construction.HasAtomicConstruction α (gaussianPair α hα).first
    rw [gaussianPair, dite_eq_left hlarge]
    exact Construction.largeGaussian_hasAtomicConstruction hlarge

end AtomicTriangular

end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_GaussianMinorants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian minorants with explicit interpolation coefficients

The atomic construction of the sharp Gaussian minorants gives the two
order-twenty interpolation blocks and an absolutely summable correction.
This formulation records the finite coefficients separately for the two
Hermite basis functions, as in the atomic certificate of OpenAI.
-/

noncomputable section

open scoped BigOperators FourierTransform

namespace AtomicTriangular

open Construction

attribute [local instance] OAI.AtomicTriangular.finite_pair_neZero
attribute [local instance] OAI.AtomicTriangular.three_atLeastTwo
attribute [local instance] OAI.AtomicTriangular.ten_atLeastTwo
attribute [local instance] OAI.AtomicTriangular.five_hundred_atLeastTwo
attribute [local instance] OAI.AtomicTriangular.plane_borelSpace
attribute [local instance] OAI.AtomicTriangular.plane_finite
lemma Construction.HasAtomicConstruction.atomicConstruction {α : ℝ} {f : Plane → ℝ}
    (hf : HasAtomicConstruction α f) : AtomicConstruction α f := by
  obtain ⟨hminus, hplus, heqplus, heqminus, a, δ, ha, hδ, hf⟩ := hf
  refine ⟨hminus, hplus, heqplus, heqminus, δ, a,
    (fun side => (hδ side).1), (fun side => (ha side).1), ?_,
    (fun side => (hδ side).2), hf⟩
  intro side j
  constructor
  · have hj := (ha side).2.2.2 ⟨2 * j.val, by omega⟩
    simpa [finiteCoordinates, correctedFinite] using hj
  · have hj := (ha side).2.2.2 ⟨2 * j.val + 1, by omega⟩
    simpa [finiteCoordinates, correctedFinite, Nat.add_div] using hj

/-- Sharp radial Gaussian minorants have nonnegative Fourier transform, exact
lattice contacts, and the atomic construction when the parameter is at least one. -/
theorem sharp_gaussian_minorants_with_construction_oai (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → AtomicConstruction α f) := by
  obtain ⟨f, hradial, hminorant, hfourier, hcontact, hzero, hconstruction⟩ :=
    sharp_gaussian_minorants_atomic α hα
  exact ⟨f, hradial, hminorant, hfourier, hcontact, hzero,
    fun hlarge => (hconstruction hlarge).atomicConstruction⟩

end AtomicTriangular

end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction_oai := @OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction_oai
