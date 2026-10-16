-- Prove2me | solution 1 for OAI.PermanentBorder.CI.hasFDerivAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:59:37.059849+00:00
-- url     : https://prove2.me/submissions/ec739b13-4be9-4fcb-bb27-ea2430ea2ae3

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RegularSections.lean:L222-L249
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.CI.hasFDerivAt_eval. The node keeps its source
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

-- ---- from OAI.Algebra.Determinantal.RegularSections ----
namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

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

lemma hasFDerivAt_eval (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDerivative p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : polynomialDerivative (C a) x = 0 := by ext v; simp
    rw [he]
    simpa only [eval_C] using (hasFDerivAt_const (𝕜 := ℂ) a x)
  | add p q hp hq =>
    have he : polynomialDerivative (p+q) x = polynomialDerivative p x + polynomialDerivative q x := by
      ext v
      simp [add_mul, Finset.sum_add_distrib]
    have hd := (hp.add hq).congr_fderiv he.symm
    convert! hd using 1
    ext y
    simp
  | mul_X p i hp =>
    have he : polynomialDerivative (p*X i) x =
        (eval x p) • ContinuousLinearMap.proj i + (x i) • polynomialDerivative p x := by
      ext v
      simp [polynomialDerivative, pderiv_X, Pi.single_apply,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_comm, mul_left_comm, apply_ite]
    have hd := hp.mul ((ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := x))
    have hd' := hd.congr_fderiv he.symm
    convert! hd' using 1
    ext y
    simp

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

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.CI
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.CI.hasFDerivAt_eval := @_root_.OAI.PermanentBorder.CI.hasFDerivAt_eval
