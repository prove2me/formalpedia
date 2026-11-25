-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.sameSum_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:54.17946+00:00
-- url     : https://prove2.me/submissions/1090f492-2620-49ea-9516-e9d4cfe7bd9a

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
theorem _root_.solution (a b : G ⟶ G) [IsMonHom a] [IsMonHom b] {T : Over S} (h : T ⟶ G ⊗ G)
    (hh : h ≫ fst G G = 1 ∨ h ≫ snd G G = 1) :
    LB.SameSum (fun k => h.left ≫ adjPt G a b k) adjExp
      (PEmpty.elim : PEmpty.{1} → (T.left ⟶ G.left)) PEmpty.elim := by
  classical
  intro ψ
  have ha : (1 : T ⟶ G) ≫ a = 1 := by simp [Hom.one_def]
  have hb : (1 : T ⟶ G) ≫ b = 1 := by simp [Hom.one_def]
  have h1 := sum_lam G (h ≫ fst G G) (h ≫ snd G G ≫ b)
    (hh.imp id fun e => by rw [← Category.assoc, e, hb]) ψ
  have h2 := sum_lam G (h ≫ fst G G ≫ a) (h ≫ snd G G)
    (hh.imp (fun e => by rw [← Category.assoc, e, ha]) id) ψ
  rw [Fintype.sum_sum_type]
  simp only [adjPt, adjExp, Sum.elim_inl, Sum.elim_inr, lamPt_comp, Finset.univ_eq_empty,
    Finset.sum_empty]
  have h3 : ∀ (p : Prop) [Decidable p] (n : ℤ), (if p then -n else 0) = -(if p then n else 0) := by
    intro p _ n; split_ifs <;> simp
  simp only [h3, Finset.sum_neg_distrib]
  rw [h1, h2]; rfl
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
