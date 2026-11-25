-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.sameSum_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:59.000361+00:00
-- url     : https://prove2.me/submissions/f6bd1e5b-e518-4d56-b7f8-2e0204bfd042

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_lamPt_comp
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_sum_lam

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
theorem _root_.solution (w : G ⟶ G) :
    LB.SameSum (fun k => eSec G ≫ primPt G w k) primExp
      (fun _ : PUnit.{1} => eSec G) (fun _ => 1) := by
  classical
  intro ψ
  have h1 := sum_lam G (η[G] ≫ 𝟙 G) (η[G] ≫ w) (Or.inl (by simp [Hom.one_def])) ψ
  rw [Fintype.sum_sum_type]
  simp only [primPt, primExp, Sum.elim_inl, Sum.elim_inr, eSec, lamPt_comp, Category.comp_id] at h1 ⊢
  have h3 : ∀ (p : Prop) [Decidable p] (n : ℤ), (if p then -n else 0) = -(if p then n else 0) := by
    intro p _ n; split_ifs <;> simp
  simp only [h3, Finset.sum_neg_distrib]
  erw [h1]
  rw [neg_zero, add_zero]
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
