-- Prove2me | solution 1 for GlobalTheory.ToricData.secVal_of_phiRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:55:02.002861+00:00
-- url     : https://prove2.me/submissions/ebff152b-9001-4a1e-bfdb-58d6a703658d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Theorems.Thm_GlobalTheory_ToricData_secVal_of_secRel
import Theorems.Thm_GlobalTheory_ToricData_trPt_eq_id
import Theorems.Thm_GlobalTheory_ToricData_pullTop_zF_constUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution {n : ℕ} (p : QkPt (toricPre K X q) F n) (t : Multiplicative X →* Fˣ)
    (hp : p.g = pt q F t)
    (w : LB.Gen (LB.LinComb (toricPre K X q).P.L (DegPre.lineφ _ F p.g.b) (DegPre.lineε n))) (c : Fˣ)
    (hw : IsConst w (unitOn c)) {s s' : Fam (toricPre K X q) F n} (h : PhiRel _ F n p w s s') (α β : X)
    (hβ : β = α + (show X from p.y)) :
    secVal (s'.s β) = secVal (s.s α) * (constUnit q F (t (Multiplicative.ofAdd α) * c)).val := by
  subst hβ
  have hg : IsConst (p.g.s α) (unitOn (t (Multiplicative.ofAdd α))) := by
    rw [hp]
    exact pt_isConst q F t α
  refine secVal_of_secRel (congrArg CommaMorphism.left (trPt_eq_id q F p.g.b)) (cg_isConst _ _ _)
    (h α (cg _ _ (constUnit q F (t (Multiplicative.ofAdd α) * c))) (cg_isGen _ _ _) ?_)
  exact corr_of_isConst
    ((isConst_pullGen (cg_isConst _ _ _) _).of_eq ((pullTop_zF_constUnit q F _).trans (unitOn_mul _ _)))
    (isConst_mulGen hg hw)
end GlobalTheory.ToricData
