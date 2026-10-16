-- Prove2me | solution 1 for OAI.PermanentBorder.SliceParameters.homogeneous_piece_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:12:46.123972+00:00
-- url     : https://prove2.me/submissions/46f3fbab-18de-40ac-9a35-55d2aba6718e

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SmoothSlices.lean:L213-L228
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.SliceParameters.homogeneous_piece_certificate. The node keeps its source
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
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_monomial_mem_of_variable_powers

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

lemma variable_power_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) (j : σ) :
    ∃ n : ℕ, (X j : MvPolynomial σ K)^n ∈ I := by
  have hx : (X j : MvPolynomial σ K) ∈ vanishingIdeal K (zeroLocus L I) := by
    intro y hy
    rw [hz y hy]
    simp
  rw [vanishingIdeal_zeroLocus_eq_radical] at hx
  exact hx

theorem homogeneous_piece_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ D : ℕ, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by
  classical
  choose N hN using variable_power_certificate I hz
  refine ⟨(∑ j, N j)+1, ?_⟩
  intro f hf
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro s hs
  apply monomial_mem_of_variable_powers I N hN
  have hd : s.degree = (∑ j, N j)+1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  omega

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


theorem solution : type_of% @_root_.OAI.PermanentBorder.SliceParameters.homogeneous_piece_certificate := @_root_.OAI.PermanentBorder.SliceParameters.homogeneous_piece_certificate
