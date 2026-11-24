-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.eq_nbOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:28.548844+00:00
-- url     : https://prove2.me/submissions/50e8d493-0fc9-4fe8-af61-f3a7c8a1cfc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_SD_eq_of_le
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_conj_le
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_spec
import Theorems.Thm_GlobalTheory_SW_Nbr_inf_spec

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
    (h : Λ ∈ Vset E n M) (h' : Λ' ∈ Nb M P Λ) : Λ' = nbOf P (Λ ⊓ Λ') := by
  have hS' : SD Λ' := h'.1.2.1
  refine hS'.eq_of_le (nbOf_spec hP h (inf_spec hP h').1 inf_le_left (inf_spec hP h').2).1
    fun x hx => ⟨fun y hy => (hS' x).1 hx y hy.2, fun c hc => ⟨?_, Λ'.smul_mem c hx⟩⟩
  exact smul_le_iff.1 (conj_le h.2.1 hS' h'.2.1) c hc x hx
end GlobalTheory.SW.Nbr
