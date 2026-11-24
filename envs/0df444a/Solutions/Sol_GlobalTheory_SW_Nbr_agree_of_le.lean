-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.agree_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:04.198808+00:00
-- url     : https://prove2.me/submissions/409b153e-d81d-485e-afab-d8e0176bad5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_conj_le

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
theorem _root_.solution {M q m : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) (hm : q.Coprime m)
    {Λ Λ' : Lt E n} (h : SD Λ) (h' : SD Λ') (hle : P • Λ ≤ Λ') : Agree m Λ Λ' := by
  have h1 : ((q : ℕ) : 𝓞 E) ∈ P := hP.2.2.1 ▸ Ideal.absNorm_mem P
  have h2 : ((q : ℕ) : 𝓞 E) ∈ conjI P := (good_conj hP).2.2.1 ▸ Ideal.absNorm_mem _
  exact ⟨q, hP.1.pos, hm, fun v hv => smul_le_iff.1 hle _ h1 v hv,
    fun v hv => smul_le_iff.1 (conj_le h h' hle) _ h2 v hv⟩
end GlobalTheory.SW.Nbr
