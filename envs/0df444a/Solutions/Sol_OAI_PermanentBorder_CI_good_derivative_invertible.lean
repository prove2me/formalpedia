-- Prove2me | solution 1 for OAI.PermanentBorder.CI.good_derivative_invertible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:06:56.810932+00:00
-- url     : https://prove2.me/submissions/1364d993-7f4e-42f4-af18-8c0568d11c72

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SmoothSlices.lean:L43-L58
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.CI.good_derivative_invertible. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Theorems.Thm_OAI_PermanentBorder_CI_hasFDerivAt_eval

-- ---- from OAI.Algebra.Determinantal.RegularSections ----
namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

lemma pderiv_linear (l : Option ι → R) (j : Option ι) : pderiv j (linear l) = C (l j) := by
  classical
  cases j <;> simp [linear, pderiv_X, Pi.single_apply]

lemma pderiv_normalized (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (i j : Option ι) : pderiv j (normalized H l i) = square H l i j := by
  cases i <;> simp [normalized, square, pderiv_linear]

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

lemma system_fderiv (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ) :
    fderiv ℂ (fun y i => eval y (P i)) x =
      ContinuousLinearMap.pi (fun i => polynomialDerivative (P i) x) :=
  (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_eval (P i) x)).fderiv

lemma system_fderiv_apply (P : σ → MvPolynomial σ ℂ) (x v : σ → ℂ) :
    fderiv ℂ (fun y i => eval y (P i)) x v = (jacobian P x).mulVec v := by
  rw [system_fderiv]
  ext i
  simp [jacobian, Matrix.mulVec, dotProduct]

lemma system_fderiv_invertible [DecidableEq σ] (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ)
    (h : (jacobian P x).det ≠ 0) :
    (fderiv ℂ (fun y i => eval y (P i)) x).IsInvertible := by
  have hu : IsUnit (jacobian P x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have he : ⇑(fderiv ℂ (fun y i => eval y (P i)) x) = (jacobian P x).mulVec :=
    funext (system_fderiv_apply P x)
  have hb : Function.Bijective (fderiv ℂ (fun y i => eval y (P i)) x) := by
    rw [he]
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩
  obtain ⟨u,hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr hb
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.SmoothSlices ----
namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

lemma normalized_eval_zero_iff (H : ι → MvPolynomial (Option ι) ℂ) (l y : Option ι → ℂ) :
    (fun i => eval y (normalized H l i)) = 0 ↔
      (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1 := by
  constructor
  · intro h
    constructor
    · intro i; exact congrFun h (some i)
    · have hh := congrFun h none
      simpa [normalized, sub_eq_zero] using hh
  · rintro ⟨hH,hl⟩
    funext i
    cases i <;> simp [normalized, hH, hl]

lemma good_derivative_invertible (H : ι → MvPolynomial (Option ι) ℂ)
    (l y : Option ι → ℂ) (h : Good H l)
    (hy : (fun i => eval y (normalized H l i)) = 0) :
    (fderiv ℂ (fun y i => eval y (normalized H l i)) y).IsInvertible := by
  have hh := (normalized_eval_zero_iff H l y).mp hy
  have hn : y ≠ 0 := by
    intro hz
    have := hh.2
    rw [eval_linear] at this
    simp [hz] at this
  have hd := (h y hn hh.1).2
  have hj : jacobian (normalized H l) y = (square H l).map (eval y) := by
    ext i j
    exact congrArg (eval y) (pderiv_normalized H l i j)
  apply system_fderiv_invertible
  rwa [hj]

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

end Surjectivity
end PermanentBorder.SliceParameters

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.CI.good_derivative_invertible := @_root_.OAI.PermanentBorder.CI.good_derivative_invertible
