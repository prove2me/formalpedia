-- Prove2me | solution 1 for OAI.PermanentBorder.CI.good_iff_bad
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:56:17.997516+00:00
-- url     : https://prove2.me/submissions/2fcb1ca5-19a0-43c1-b8ac-4551d6e7b38d

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RegularSections.lean:L82-L98
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.CI.good_iff_bad. The node keeps its source
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

lemma good_iff_bad (H : ι → MvPolynomial (Option ι) K) (l : Option ι → K) :
    Good H l ↔ ∀ y : Option ι → K, (∀ i, eval y (bad H l i) = 0) → y = 0 := by
  classical
  constructor
  · intro hg y hy
    by_contra hn
    obtain ⟨hl,hj⟩ := hg y hn (fun i => hy (some i))
    have h := hy none
    change eval y (linear l * (square H l).det) = 0 at h
    rw [map_mul, RingHom.map_det] at h
    exact (mul_ne_zero hl hj) h
  · intro hz y hn hH
    have h : eval y (linear l * (square H l).det) ≠ 0 := by
      intro h
      exact hn (hz y (by intro i; cases i; exact h; exact hH _))
    rw [map_mul, RingHom.map_det] at h
    exact mul_ne_zero_iff.mp h

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


theorem solution : type_of% @_root_.OAI.PermanentBorder.CI.good_iff_bad := @_root_.OAI.PermanentBorder.CI.good_iff_bad
