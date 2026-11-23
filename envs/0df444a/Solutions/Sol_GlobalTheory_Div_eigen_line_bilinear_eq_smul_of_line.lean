-- Prove2me | solution 1 for GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:04:14.437803+00:00
-- url     : https://prove2.me/submissions/1c1d4e42-aa5d-4b86-b621-0ecac7bdcea0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.eigen_line_bilinear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.Div.eigen_line_bilinear
theorem _root_.solution {ρ : orderC c →+* Module.End O H} {τ : E →+* K} (hline : Module.finrank K (eigK ρ τ) = 1)
    {v : K ⊗[O] H} (hv : v ∈ eigK ρ τ) (hv0 : v ≠ 0) {x : K ⊗[O] H} (hx : x ∈ eigK ρ τ) : ∃ a : K, x = a • v := by
  have hne : (⟨v, hv⟩ : eigK ρ τ) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hline ⟨x, hx⟩
  exact ⟨a, (congrArg Subtype.val ha).symm⟩
end GlobalTheory.Div.eigen_line_bilinear
