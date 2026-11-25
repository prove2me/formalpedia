-- Prove2me | solution 1 for GlobalTheory.ToricData.qkExt_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:08.986723+00:00
-- url     : https://prove2.me/submissions/e35e1044-a4e8-4266-8fdb-b4612d1c1b71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Theorems.Thm_GlobalTheory_ToricData_zeroF_left_ext
import Theorems.Thm_GlobalTheory_ToricData_pullTop_unitOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
variable (q : X → (FractionRing K)ˣ) (F : Type) [Field F] [Algebra (FractionRing K) F]
namespace GlobalTheory.ToricData
theorem _root_.solution {F' : Type} [Field F'] [Algebra (FractionRing K) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing K) F) = algebraMap (FractionRing K) F') {n : ℕ}
    (p : QkPt (toricPre K X q) F n) (p' : QkPt (toricPre K X q) F' n) (t t') (hp : p.g = pt q F t)
    (hp' : p'.g = pt q F' t') :
    QkExt f p p' ↔ p'.y = p.y ∧ ∀ χ, (t' χ : F') = f (t χ) := by
  obtain ⟨y, g, e⟩ := p
  obtain ⟨y', g', e'⟩ := p'
  dsimp only at hp hp'
  subst hp hp'
  refine and_congr_right' ((and_iff_right (zeroF_left_ext q F f hf)).trans ?_)
  refine (forall_congr' fun (χ : X) => (corr_iff_eq (pt_isConst q F' t' χ)
      ((isConst_pullGen (pt_isConst q F t χ) (spMap f)).of_eq (pullTop_unitOn _ _))).trans
      (unitOn_inj.trans Units.ext_iff)).trans ?_
  exact ⟨fun H χ => H χ.toAdd, fun H χ => H _⟩
end GlobalTheory.ToricData
