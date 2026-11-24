-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.nbOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:24:47.340288+00:00
-- url     : https://prove2.me/submissions/294acd69-69bc-4660-ba8c-6c57bfeea6bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_mem_Nb
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_spec
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
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ₀ : Lt E n}
    (h : Λ ∈ Vset E n M) (h1 : P • Λ ≤ Λ₀) (h2 : Λ₀ ≤ Λ)
    (h3 : Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q) : nbOf P Λ₀ ∈ Nb M P Λ := by
  obtain ⟨h4, h5⟩ := nbOf_spec hP h h1 h2 h3
  refine (mem_Nb hP h).2 ⟨h4, h1.trans (h5.ge.trans inf_le_right), ?_⟩
  rw [← relIndex_inf, h5, h3]
end GlobalTheory.SW.Nbr
