-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.UnitaryConv.rep_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:11.073984+00:00
-- url     : https://prove2.me/submissions/fb78644b-9ecb-4646-b178-b9b3b7513821

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_mk_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv
theorem _root_.solution {P Γ : Subgroup G} (a : Γ) :
    ∃ p ∈ Γ, p ∈ P ∧ rep (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = p * a := by
  refine ⟨rep (Quotient.mk _ a : Cos P Γ) * (a : G)⁻¹, ?_, ?_, ?_⟩
  · exact Γ.mul_mem (Quotient.out (Quotient.mk _ a : Cos P Γ)).2 (Γ.inv_mem a.2)
  · exact (cos_mk_eq_iff (P := P) (Γ := Γ) a (Quotient.out (Quotient.mk _ a : Cos P Γ))).mp
      (Quotient.out_eq _).symm
  · exact (inv_mul_cancel_right _ _).symm
end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
