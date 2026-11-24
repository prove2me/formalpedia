-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.mem_Nb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:56.596321+00:00
-- url     : https://prove2.me/submissions/87478bb2-17a8-4196-bafa-ad071ce3be1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
import Theorems.Thm_GlobalTheory_SW_Nbr_agree_trans
import Theorems.Thm_GlobalTheory_SW_Nbr_agree_symm
import Theorems.Thm_GlobalTheory_SW_Nbr_agree_of_le
import Theorems.Thm_GlobalTheory_SW_Nbr_fg_of_agree

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
    (h : Λ ∈ Vset E n M) : Λ' ∈ Nb M P Λ ↔
      SD Λ' ∧ P • Λ ≤ Λ' ∧ Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.2.1, h2, h3.trans hP.2.2.1⟩
  · rintro ⟨h1, h2, h3⟩
    have ha := agree_of_le hP hP.2.1 h.2.1 h1 h2
    exact ⟨⟨fg_of_agree h.1 ha, h1, agree_trans (agree_symm ha) h.2.2⟩, h2, h3.trans hP.2.2.1.symm⟩
end GlobalTheory.SW.Nbr
