-- Prove2me | solution 1 for GlobalTheory.ToricData.zeroF_left_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:27.563963+00:00
-- url     : https://prove2.me/submissions/3f126d91-7ef1-47dd-b25f-0ad2f4bcc8ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
    (hf : f.comp (algebraMap (FractionRing K) F) = algebraMap (FractionRing K) F') :
    (DegPre.zeroF (toricPre K X q) F').left = spMap f ≫ (DegPre.zeroF (toricPre K X q) F).left := by
  have w : spMap f ≫ (TF (R := K) F).hom = (TF (R := K) F').hom := by
    change spMap f ≫ jFK (R := K) F ≫ jK K = jFK (R := K) F' ≫ jK K
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  let φ : TF (R := K) F' ⟶ TF (R := K) F := Over.homMk (spMap f) w
  have e : DegPre.zeroF (toricPre K X q) F' = φ ≫ DegPre.zeroF (toricPre K X q) F := toUnit_unique _ _
  rw [e]
  rfl
end GlobalTheory.ToricData
