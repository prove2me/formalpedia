-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.gidx_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:39.407264+00:00
-- url     : https://prove2.me/submissions/264f9cf9-23c5-4eb6-9a37-11770c92b21f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_relIndex_ne_zero
import Theorems.Thm_GlobalTheory_SW_TwistAdm_std_fg
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_relIndex_ne_zero


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.SW.TwistAdm
theorem _root_.solution {m : ℕ} {𝔛 : Lt E N} (hfg : 𝔛.FG) (hA : Agree m 𝔛 (stdL E N)) : 0 < gidx 𝔛 := by
  obtain ⟨t, ht, -, h1, h2⟩ := hA
  exact div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_ne_zero _ _ hfg ht h1)))
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_ne_zero _ _ std_fg ht h2)))
end GlobalTheory.SW.TwistAdm
