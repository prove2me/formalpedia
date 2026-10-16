-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.generic_no_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:28:17.259999+00:00
-- url     : https://prove2.me/submissions/e19563ed-90ff-46f6-b978-790c38a58cd6

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/GenericPolars.lean:L229-L245
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.generic_no_infinity. The node keeps its source
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
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Theorems.Thm_OAI_PermanentBorder_Polar_rows_independent_of_derivations
import Theorems.Thm_OAI_PermanentBorder_Polar_square_isUnit_of_independent

-- ---- from OAI.Algebra.Determinantal.SliceCertificates ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters
namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open Polynomial Matrix
open scoped Classical

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

lemma extendDerivation_algebraMap [Algebra.FormallyEtale R L]
    (D : Derivation K R L) (x : R) :
    extendDerivation D (algebraMap R L x) = D x := by
  simp [extendDerivation, LinearMap.compDer,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

lemma parameterDerivation_parameter [DecidableEq ι] (i j : ι) :
    parameterDerivation K ι i (genericParameter K ι j) = if i = j then 1 else 0 := by
  classical
  simp [parameterDerivation, genericParameter, extendDerivation_algebraMap, Pi.single_apply,
    eq_comm]

end Generic

section ChainRule
variable {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]

end ChainRule
end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.GenericPolars ----
namespace OAI
namespace PermanentBorder.Polar
open MvPolynomial

section Parametric
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]
lemma euler_aeval {σ : Type*} [Fintype σ] {f : MvPolynomial σ K} {r : ℕ}
    (hf : f.IsHomogeneous r) (y : σ → L) :
    ∑ j, aeval y (pderiv j f) * y j = (r : L) * aeval y f := by
  classical
  have h := congrArg (aeval y) hf.sum_X_mul_pderiv
  simpa [map_sum, mul_comm] using h

lemma polar_euler_aeval (w : τ → PolarVars τ → L)
    {f : MvPolynomial (PolarVars τ) K} {r : ℕ} (hf : f.IsHomogeneous r)
    (y : PolarVars τ → L) (i : τ) :
    ∑ j, polarGradient w f y i j * y j = ((r-1 : ℕ) : L) * polarValue w f y i := by
  classical
  simp only [polarGradient, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, euler_aeval hf.pderiv]
  simp only [polarValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma square_mulVec_zero (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    {f : MvPolynomial (PolarVars τ) K} {r : ℕ} (hhom : f.IsHomogeneous r)
    (y : PolarVars τ → L) (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hl : ∑ j, l j * y j = 0) : (squareJacobian w l f y).mulVec y = 0 := by
  classical
  funext i
  rcases i with _ | (_ | i)
  · simpa [Matrix.mulVec, dotProduct, squareJacobian, hf] using euler_aeval hhom y
  · exact hl
  · simpa [Matrix.mulVec, dotProduct, squareJacobian, hp] using polar_euler_aeval w hhom y i

end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

lemma generic_no_infinity (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (hn : ∑ j, genericLinear j * y j = 0) : y = 0 := by
  classical
  by_contra hy
  have hyy : ∃ j, y j ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using hy
  have hu : IsUnit (squareJacobian genericDirections genericLinear f y) :=
    square_isUnit_of_independent _ _ _ _ (fun c z cfs hdep =>
      rows_independent_of_derivations _ _ _ _ (parameterDerivation K P)
        (by intros; exact parameterDerivation_parameter K P _ _)
        (by intros; exact parameterDerivation_parameter K P _ _)
        hf hp (Or.inl hn) hyy hg c z cfs hdep)
  have hh := square_mulVec_zero genericDirections genericLinear hhom y hf hp hn
  apply hy
  exact Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa using hh)

end GenericSquare
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Polynomials
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

end Polynomials

section Evaluation
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ] [Fintype τ]

end Evaluation
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Map
variable {R S σ τ : Type*} [CommRing R] [CommRing S] [Fintype σ] [Fintype τ]

end Map
end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open MvPolynomial Matrix


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.generic_no_infinity := @_root_.OAI.PermanentBorder.Polar.generic_no_infinity
