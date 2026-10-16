-- Prove2me | solution 1 for OAI.PermanentBorder.SliceParameters.monomial_mem_of_variable_powers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:11:05.810191+00:00
-- url     : https://prove2.me/submissions/f8e6799d-31f7-42a6-8f57-7b8958725c02

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SmoothSlices.lean:L195-L211
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.SliceParameters.monomial_mem_of_variable_powers. The node keeps its source
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

lemma monomial_mem_of_variable_powers {K σ : Type*} [CommSemiring K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (N : σ → ℕ)
    (hN : ∀ j, (X j : MvPolynomial σ K)^(N j) ∈ I)
    (s : σ →₀ ℕ) (c : K) (hs : (∑ j, N j) < s.degree) : monomial s c ∈ I := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, N j ≤ s j := by
    by_contra h
    have hle (j : σ) : s j ≤ N j := le_of_lt (not_le.mp (not_exists.mp h j))
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle j)
    have hd : s.degree = ∑ j, s j := by
      exact Finsupp.sum_fintype s (fun _ n => n) (fun _ => rfl)
    rw [hd] at hs
    exact (not_le_of_gt hs) hh
  have he : Finsupp.single j (N j) + (s - Finsupp.single j (N j)) = s :=
    add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hj)
  rw [← he, monomial_single_add]
  exact I.mul_mem_right _ (hN j)

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
open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.SliceParameters.monomial_mem_of_variable_powers := @_root_.OAI.PermanentBorder.SliceParameters.monomial_mem_of_variable_powers
