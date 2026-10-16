-- Prove2me | solution 1 for OAI.PermanentBorder.CI.powers_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:57:43.043317+00:00
-- url     : https://prove2.me/submissions/c51f233e-a957-4bfc-84ca-4d3a20819e97

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RegularSections.lean:L120-L169
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.CI.powers_good. The node keeps its source
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

lemma powers_good (e : ι → ℕ) (he : ∀ i, 0 < e i) : Good (powers e) coordinate := by
  intro y hy hH
  have hp (i : ι) : y (some i) ^ e i = y none ^ e i := by
    simpa [powers, sub_eq_zero] using hH i
  have hn : y none ≠ 0 := by
    intro hn
    apply hy
    funext i
    cases i with
    | none => exact hn
    | some i =>
      have hh : y (some i) ^ e i = 0 := by rw [hp i, hn, zero_pow (ne_of_gt (he i))]
      exact eq_zero_of_pow_eq_zero hh
  have hs (i : ι) : y (some i) ≠ 0 := by
    intro hz
    have hh := hp i
    rw [hz, zero_pow (ne_of_gt (he i))] at hh
    exact (pow_ne_zero _ hn) hh.symm
  refine ⟨by simpa only [eval_coordinate] using hn, ?_⟩
  let A := (square (powers e) (coordinate (ι := ι))).map (eval y)
  have h0 (v : Option ι → ℂ) : A.mulVec v none = v none := by
    simp [A, square, coordinate, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hd (i : ι) (j : Option ι) : eval y (pderiv j (powers e i)) =
      (if some i = j then (e i : ℂ) * y (some i) ^ (e i - 1) else 0) -
      (if none = j then (e i : ℂ) * y none ^ (e i - 1) else 0) := by
    by_cases ha : some i = j <;> by_cases hb : none = j <;>
      simp [powers, pderiv_X, ha, hb]
  have h1 (v : Option ι → ℂ) (i : ι) :
      A.mulVec v (some i) = (e i : ℂ) * y (some i) ^ (e i - 1) * v (some i) -
        (e i : ℂ) * y none ^ (e i - 1) * v none := by
    change (∑ j, eval y (pderiv j (powers e i)) * v j) = _
    simp only [hd, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hi : Function.Injective A.mulVec := by
    change Function.Injective A.mulVecLin
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A.mulVec v = 0 at hv
    have hv0 : v none = 0 := by simpa only [h0, Pi.zero_apply] using congrFun hv none
    funext j
    cases j with
    | none => exact hv0
    | some i =>
      have hh := congrFun hv (some i)
      rw [h1, hv0, mul_zero, sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left
        (mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt (he i))) (pow_ne_zero _ (hs i)))
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

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
open MvPolynomial Matrix
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.CI.powers_good := @_root_.OAI.PermanentBorder.CI.powers_good
