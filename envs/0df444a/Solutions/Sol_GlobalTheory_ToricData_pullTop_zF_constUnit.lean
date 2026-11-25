-- Prove2me | solution 1 for GlobalTheory.ToricData.pullTop_zF_constUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:41.591553+00:00
-- url     : https://prove2.me/submissions/98ccc4d4-c084-41cf-aedd-80c4d79695ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]
namespace GlobalTheory.ToricData
theorem _root_.solution (c : Fˣ) :
    pullTop (DegPre.zF (toricPre K X q) F).left (constUnit q F c) = unitOn c := by
  have h : (DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, DegPre.zF, lift_fst, Over.id_left]
  ext
  change ((DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left).appTop.hom
    (unitOn c).val = _
  rw [h]
  rfl
end GlobalTheory.ToricData
