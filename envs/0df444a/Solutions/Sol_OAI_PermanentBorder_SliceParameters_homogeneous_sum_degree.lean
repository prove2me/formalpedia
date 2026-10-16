-- Prove2me | solution 1 for OAI.PermanentBorder.SliceParameters.homogeneous_sum_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:14:24.214453+00:00
-- url     : https://prove2.me/submissions/41e24004-a5e5-4c8f-a253-52f73eba0129

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SmoothSlices.lean:L271-L293
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.SliceParameters.homogeneous_sum_degree. The node keeps its source
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

-- ---- from OAI.Algebra.Determinantal.SmoothSlices ----
namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma intWeight_degree {σ : Type*} (s : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) s = (s.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

lemma homogeneous_sum_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f = ∑ s : DegreeIndex σ d, monomial s.val (f.coeff s.val) := by
  classical
  ext t
  rw [coeff_sum]
  by_cases ht : (t.degree : ℤ) = d
  · rw [Finset.sum_eq_single (⟨t,ht⟩ : DegreeIndex σ d)]
    · simp
    · intro s _ hs
      have he : s.val ≠ t := fun h => hs (Subtype.ext h)
      simp [coeff_monomial, he]
    · simp
  · have hz : f.coeff t = 0 := by
      by_contra hn
      exact ht (intWeight_degree t ▸ hf hn)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro s _
    have he : s.val ≠ t := fun h => ht (h ▸ s.property)
    simp [coeff_monomial, he]

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
open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.SliceParameters.homogeneous_sum_degree := @_root_.OAI.PermanentBorder.SliceParameters.homogeneous_sum_degree
