-- Prove2me | solution 1 for GlobalTheory.eq_of_specializes_of_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:11.793217+00:00
-- url     : https://prove2.me/submissions/7982614f-e0ad-4df9-9729-a05498d3e559

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiFiniteAtAffineSpaceHomOfVectorOfCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} {y x : X} (h : y ⤳ x)
    (H : ∀ (U : X.Opens) (_ : x ∈ U) (s : Γ(X, U)), y ∈ X.basicOpen s → x ∈ X.basicOpen s) : y = x := by
  refine (h.antisymm ?_).eq
  rw [specializes_iff_forall_open]
  intro V hV hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  obtain ⟨s, hs, hys⟩ := IsAffineOpen.exists_basicOpen_le hU (V := ⟨V, hV⟩) ⟨y, hy⟩ hyU
  exact hs (H U hxU s hys)
end GlobalTheory
