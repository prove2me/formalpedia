-- Prove2me | solution 1 for GlobalTheory.ConstFam.expandsAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:28:57.819155+00:00
-- url     : https://prove2.me/submissions/96bae35a-c236-453e-8aec-0cbb571aa355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Theorems.Thm_GlobalTheory_expandsAt_secIsMul


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
theorem _root_.solution (a : R)
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) :
    U.ExpandsAt n j (a • σ : SecOver G.hom _) (a • f : ∀ χ, SecBMod D.toPre j χ) :=
  expandsAt_secIsMul R I D A G U n j a σ _ f _ (fun _ => rfl) (fun _ _ => rfl) h
end GlobalTheory.ConstFam
