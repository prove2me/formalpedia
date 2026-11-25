-- Prove2me | solution 1 for GlobalTheory.ToricData.hom_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:51:56.223978+00:00
-- url     : https://prove2.me/submissions/8bc9d7e5-6bfb-496d-a208-3348ef7344ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt

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
omit [Module.Free ℤ X] [Module.Finite ℤ X]
namespace GlobalTheory.ToricData
theorem _root_.solution {F : Type} [Field F] {t t' : Multiplicative X →* Fˣ} :
    (∀ χ : X, t (Multiplicative.ofAdd χ) = t' (Multiplicative.ofAdd χ)) ↔ t = t' :=
  ⟨fun h => MonoidHom.ext fun χ => h χ.toAdd, fun h _ => h ▸ rfl⟩
end GlobalTheory.ToricData
