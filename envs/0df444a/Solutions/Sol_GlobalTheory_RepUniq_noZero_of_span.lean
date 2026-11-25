-- Prove2me | solution 1 for GlobalTheory.RepUniq.noZero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:22:54.673803+00:00
-- url     : https://prove2.me/submissions/cd0dce0d-03ca-4db1-b320-14784a186b71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}
variable {A : Type} [CommRing A]
namespace GlobalTheory.RepUniq
theorem _root_.solution {W : T.Opens} {f : σ → Γ(T, W)} (h : Ideal.span (Set.range f) = ⊤) : NoZero f := by
  intro t ht
  by_contra hn
  push_neg at hn
  have : Ideal.span (Set.range f) ≤
      (IsLocalRing.maximalIdeal _).comap (T.presheaf.germ W t ht).hom :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hn i)
  have h1 := this (h.ge (Submodule.mem_top (x := 1)))
  rw [Ideal.mem_comap, map_one] at h1
  exact h1 isUnit_one
end GlobalTheory.RepUniq
