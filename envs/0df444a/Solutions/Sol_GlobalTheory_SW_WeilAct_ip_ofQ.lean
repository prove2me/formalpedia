-- Prove2me | solution 1 for GlobalTheory.SW.WeilAct.ip_ofQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:03:00.943291+00:00
-- url     : https://prove2.me/submissions/7d5df2b2-e996-4d2a-bfcd-3141e0267b49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Theorems.Thm_GlobalTheory_T_rationalSchwartzBruhat_algebra_integral_linear
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_rationalCoords_integral_proportional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.WeilAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.WeilAct
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ψ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB ψ →
      ip (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) (fun m => ψ (ofQ m)) = d * ip φ ψ := by
  obtain ⟨d, hd, h⟩ := GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional E n N
  refine ⟨d, by exact_mod_cast hd.ne', fun φ ψ hφ hψ => ?_⟩
  have h1 : IsSB fun x => conj (ψ x) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ ψ ψ hψ hψ).2.2.2.1
  exact h (fun x => φ x * conj (ψ x)) (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ _ hφ h1).2.2.1
end GlobalTheory.SW.WeilAct
