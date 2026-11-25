-- Prove2me | solution 1 for GlobalTheory.HolZeros.continuousAt_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:40:25.276961+00:00
-- url     : https://prove2.me/submissions/2cc876fc-4711-4640-8ed5-c43a0b158bd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SimpleZerosMoveHolomorphically
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
open GlobalTheory GlobalTheory.HolZeros
namespace GlobalTheory.HolZeros
theorem _root_.solution {g : ℕ} {P : Type*} [TopologicalSpace P]
    {τ : P → Matrix (Fin g) (Fin g) ℂ} {w : P → Fin g → ℂ} {p : P} (hτ : Continuous τ)
    (hw : ContinuousAt w p) (h : IsUnit ((τ p).map Complex.im).det) :
    ContinuousAt (fun q => coords (τ q) (w q)) p := by
  have him : Continuous fun q => (τ q).map Complex.im := hτ.matrix_map Complex.continuous_im
  have hre : Continuous fun q => (τ q).map Complex.re := hτ.matrix_map Complex.continuous_re
  have hinv : ContinuousAt (fun q => ((τ q).map Complex.im)⁻¹) p := by
    refine ContinuousAt.comp (f := fun q => (τ q).map Complex.im) ?_ him.continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ h.ne_zero
  have hmv : Continuous fun x : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => x.1.mulVec x.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  have hwi : ContinuousAt (fun q i => (w q i).im) p :=
    continuousAt_pi.2 fun i => Complex.continuous_im.continuousAt.comp (continuousAt_pi.1 hw i)
  have hwr : ContinuousAt (fun q i => (w q i).re) p :=
    continuousAt_pi.2 fun i => Complex.continuous_re.continuousAt.comp (continuousAt_pi.1 hw i)
  have hb := hmv.continuousAt.comp (hinv.prodMk hwi)
  exact (hwr.sub (hmv.continuousAt.comp (hre.continuousAt.prodMk hb))).prodMk hb
end GlobalTheory.HolZeros
