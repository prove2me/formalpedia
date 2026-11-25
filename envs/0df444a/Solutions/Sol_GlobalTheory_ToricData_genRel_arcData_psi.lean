-- Prove2me | solution 1 for GlobalTheory.ToricData.genRel_arcData_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:40:35.87573+00:00
-- url     : https://prove2.me/submissions/8525c551-9820-4a26-9761-640258556b09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Theorems.Thm_GlobalTheory_ToricData_genRel_psi_iff

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
namespace GlobalTheory.ToricData
theorem _root_.solution (k : Type) [Field k] (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (hp : ∀ y, y ≠ 0 → 0 < be y y) (he : ∀ y, (2 : ℤ) ∣ be y y)
    (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (u : F)
    (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
    (hu : u = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))
    (y' y : X) (h : be y' y' = be y y) :
    GenRel (baseIso (fun _ : X => (1 : (FractionRing k)ˣ)) (PowerSeries.C (R := k)) (arcExp k be))
      (LB.pullGen _ _ _ ((arcData k be hs hp he).toPre.psi y') (jFK (R := PowerSeries k) F))
      (LB.pullGen _ _ _ ((toricPre k X fun _ => 1).psi y) (jFK (R := k) F)) (u ^ (be y y / 2)) :=
  (genRel_psi_iff _ _ _ F hF y' y _).2 (by
    rw [arcExp_val, map_zpow₀, h, hu, Units.val_one, map_one, _root_.mul_one])
end GlobalTheory.ToricData
