-- Prove2me | solution 1 for GlobalTheory.exists_linearEquiv_expandsF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:25.179286+00:00
-- url     : https://prove2.me/submissions/73c720cd-4105-49fa-ada0-f8c50fd4508c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_expandsF_lin
import Theorems.Thm_GlobalTheory_FieldBaseChange_expandsF_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR FieldBaseChange
namespace GlobalTheory
theorem _root_.solution (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) :
    ∃ e : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) ≃ₗ[F] Fam D.toPre F k,
      ∀ t s, U.toUnifPre.ExpandsF F k w t s ↔ e t = s := by
  obtain ⟨h₁, h₂⟩ := expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw
  choose f hf using fun t : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) => (h₁ t).exists
  have iff : ∀ t s, U.toUnifPre.ExpandsF F k w t s ↔ f t = s := fun t s =>
    ⟨fun h => (h₁ t).unique (hf t) h, fun h => h ▸ hf t⟩
  have lin : ∀ (c : F) t t', f (c • t + t') = c • f t + f t' := fun c t t' =>
    (iff _ _).1 (expandsF_lin U.toUnifPre F c (hf t) (hf t'))
  have f0 : f 0 = 0 := by
    have := lin 1 0 0
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  let l : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) →ₗ[F] Fam D.toPre F k :=
    { toFun := f
      map_add' := fun t t' => by simpa only [one_smul] using lin 1 t t'
      map_smul' := fun c t => by simpa only [add_zero, f0, RingHom.id_apply] using lin c t 0 }
  refine ⟨LinearEquiv.ofBijective l ⟨fun t t' e => ?_, fun s => ?_⟩, iff⟩
  · exact (h₂ (f t')).unique ((iff t _).2 e) (hf t')
  · obtain ⟨t, ht⟩ := (h₂ s).exists
    exact ⟨t, (iff t s).1 ht⟩
end GlobalTheory
