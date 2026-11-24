-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.inf_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:27.523392+00:00
-- url     : https://prove2.me/submissions/1c3e9347-8c26-45d7-be8b-205a1e196390

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_relIndex_inf

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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h' : Λ' ∈ Nb M P Λ) : P • Λ ≤ Λ ⊓ Λ' ∧
      (Λ ⊓ Λ').toAddSubgroup.relIndex Λ.toAddSubgroup = q :=
  ⟨le_inf Submodule.smul_le_right h'.2.1, by rw [relIndex_inf, h'.2.2, hP.2.2.1]⟩
end GlobalTheory.SW.Nbr
