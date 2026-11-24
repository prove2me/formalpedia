-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.sum_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:27.207944+00:00
-- url     : https://prove2.me/submissions/be615dd9-1b2d-41f3-bd5c-d5499b3eacea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_sum_lamK
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_lamPt_values

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
open scoped Classical
namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
theorem _root_.solution {T : Over S} (x z : T ⟶ G) (h : x = 1 ∨ z = 1) (ψ : T.left ⟶ G.left) :
    (∑ I, if lamPt G x z I = ψ then lamExp I else 0) = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := lamPt_values G x z
  have e0 : lamExp ⟨∅⟩ = 1 := rfl
  have e1 : lamExp ⟨{0}⟩ = -1 := rfl
  have e2 : lamExp ⟨{1}⟩ = -1 := rfl
  have e3 : lamExp ⟨{0, 1}⟩ = 1 := rfl
  rw [sum_lamK, h0, h1, h2, h3, e0, e1, e2, e3]
  rcases h with rfl | rfl
  · rw [_root_.one_mul]; split_ifs <;> simp
  · rw [_root_.mul_one]; split_ifs <;> simp
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
