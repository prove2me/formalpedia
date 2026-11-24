-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.cmType_host
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:52.970804+00:00
-- url     : https://prove2.me/submissions/9619094f-db7a-4b06-9ec0-d60807bbe974

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_ConjugateMembership_mem_iff_conjugate_notMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (H : Host E) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (τ : E →+* ℂ) : τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  first
  | exact @_root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem
  | exact _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem
  | (apply _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem ..)
end GlobalTheory.PeriodOnto
