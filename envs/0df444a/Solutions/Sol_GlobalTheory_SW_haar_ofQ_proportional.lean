-- Prove2me | solution 1 for GlobalTheory.SW.haar_ofQ_proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:02.98949+00:00
-- url     : https://prove2.me/submissions/9df7eee0-e4da-4e0e-9dbc-34ccbb69310b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
import Theorems.Thm_GlobalTheory_SW_HaarProp_haar_comp
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den_ofQ
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den_symm


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
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  intro E _ _ _ n N
  obtain ⟨D, hD, h⟩ := Dict.exists_den_ofQ (E := E) (n := n) (N := N)
  obtain ⟨D', hD', h'⟩ := Dict.exists_den_symm (E := E) (n := n) (N := N)
  exact HaarProp.haar_comp (Dict.ofQEquiv E n N) D D' hD hD' h h' (by simp; ring)
end GlobalTheory.SW
