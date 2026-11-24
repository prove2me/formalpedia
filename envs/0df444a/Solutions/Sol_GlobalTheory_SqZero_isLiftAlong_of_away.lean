-- Prove2me | solution 1 for GlobalTheory.SqZero.isLiftAlong_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:13.038337+00:00
-- url     : https://prove2.me/submissions/01af90ac-cef4-4775-9739-b709797cd14a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_away_ext
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
import Theorems.Thm_GlobalTheory_SqZero_span_range_map
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
namespace GlobalTheory.SqZero
theorem _root_.solution {X : Over (Spec (CommRingCat.of R))} {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X}
    {φ : A →ₐ[R] T} {y : sp T ⟶ X} {κ : Type} {s : κ → T} (hs : Ideal.span (Set.range s) = ⊤)
    (h : ∀ i, IsLiftAlong y₀ ((awayHom R (s i)).comp φ) (spMap (awayHom R (s i)) ≫ y)) :
    IsLiftAlong y₀ φ y := by
  intro T₀ _ _ q q₀ hq
  have hs' : Ideal.span (Set.range fun i => q (s i)) = ⊤ := span_range_map hs q
  apply away_ext hs' (fun i => awayHom R (q (s i))) (fun i => isAway_awayHom _)
  intro i
  obtain ⟨ψ, hψ⟩ := (isAway_awayHom (R := R) (s i)).lift ((awayHom R (q (s i))).comp q)
    (isAway_awayHom (R := R) (q (s i))).unit
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, ← hψ, ← spMap_comp (awayHom R (s i)) ψ,
    Category.assoc]
  exact h i _ ψ _ (by rw [← AlgHom.comp_assoc, hψ, AlgHom.comp_assoc, hq, AlgHom.comp_assoc])
end GlobalTheory.SqZero
