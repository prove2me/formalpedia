-- Prove2me | solution 1 for GlobalTheory.ConstFam.expandsAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:04.626261+00:00
-- url     : https://prove2.me/submissions/ee36f16f-11e6-40d3-aa77-a3b73ab261c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Theorems.Thm_GlobalTheory_ConstFam_expandsAt_smul

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
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) :
    U.ExpandsAt n j (0 : SecOver G.hom _) (0 : ∀ χ, SecBMod D.toPre j χ) := by
  have e₁ : (0 : R) • σ = 0 := zero_smul R σ
  have e₂ : (0 : R) • f = 0 := zero_smul R f
  exact e₁ ▸ e₂ ▸ expandsAt_smul U (0 : R) h
end GlobalTheory.ConstFam
