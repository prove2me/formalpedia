-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.square_isUnit_of_independent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:25:36.801987+00:00
-- url     : https://prove2.me/submissions/8570760a-3900-4525-a235-ca52c91351fd

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/GenericPolars.lean:L165-L184
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.square_isUnit_of_independent. The node keeps its source
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
lemma square_isUnit_of_independent [DecidableEq τ]
    (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L)
    (h : ∀ (c z : L) (cfs : τ → L), (∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) →
      c = 0 ∧ z = 0 ∧ cfs = 0) : IsUnit (squareJacobian w l f y) := by
  apply Matrix.vecMul_injective_iff_isUnit.mp
  apply (squareJacobian w l f y).vecMulLinear.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨hc,hz,hs⟩ := h (v none) (v (some none)) (fun i => v (some (some i))) (by
    intro j
    have hh := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, squareJacobian, Fintype.sum_option, add_assoc,
      add_comm, add_left_comm] using hh)
  funext i
  rcases i with _ | (_ | i)
  · exact hc
  · exact hz
  · exact congrFun hs i

end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

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


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.square_isUnit_of_independent := @_root_.OAI.PermanentBorder.Polar.square_isUnit_of_independent
