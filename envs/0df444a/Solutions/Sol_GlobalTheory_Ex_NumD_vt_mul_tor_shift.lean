-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.vt_mul_tor_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:30:09.799898+00:00
-- url     : https://prove2.me/submissions/c0ff14e1-3979-4e25-b2e3-aac2a04ca9b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_mul_s_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution (g : N.Gt) (t : Multiplicative N.X →* Oˣ) (χ : N.X) :
    N.vt (g * N.tor t) χ = (t (Multiplicative.ofAdd χ) : Oˣ) * N.vt g χ := by
  rw [vt, vt, mul_comm g, N.tor_mul_s_apply, Gt.mul_b, tor_b, one_mul, mul_left_comm (N.ψ χ), Units.val_mul, mul_assoc]
end GlobalTheory.Ex.NumD
