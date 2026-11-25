-- Prove2me | solution 1 for GlobalTheory.ConstFam.expandsAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:36.096259+00:00
-- url     : https://prove2.me/submissions/7b1e297e-d474-421a-ab99-ddde43bc3184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Theorems.Thm_GlobalTheory_ConstFam_expandsAt_smul
import Theorems.Thm_GlobalTheory_expandsAt_sub


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) {j n : ℕ}
namespace GlobalTheory.ConstFam
theorem _root_.solution
    {σ τ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f g : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) (h' : U.ExpandsAt n j τ g) :
    U.ExpandsAt n j (σ + τ : SecOver G.hom _) (f + g : ∀ χ, SecBMod D.toPre j χ) := by
  refine expandsAt_sub R I D A G U n j σ ((-1 : R) • τ : SecOver G.hom _) _ f
    ((-1 : R) • g : ∀ χ, SecBMod D.toPre j χ) _ (fun i => ?_) (fun α i => ?_) h (expandsAt_smul U (-1) h')
  · show chartLin G.hom _ i (σ + τ) = chartLin G.hom _ i σ - chartLin G.hom _ i ((-1 : R) • τ)
    rw [← map_sub, neg_one_smul, sub_neg_eq_add]
  · show chartLin D.toPre.P.A.hom _ i (f α + g α) =
      chartLin D.toPre.P.A.hom _ i (f α) - chartLin D.toPre.P.A.hom _ i ((-1 : R) • g α)
    rw [← map_sub, neg_one_smul, sub_neg_eq_add]
end GlobalTheory.ConstFam
