-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_sq_le_be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:23.239432+00:00
-- url     : https://prove2.me/submissions/e61ed58d-a88a-4106-8654-8e6d66e21dd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_be_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (n : A.X →ₗ[ℤ] ℤ) : ∃ C : ℤ, 0 ≤ C ∧ ∀ μ, n μ ^ 2 ≤ C * A.be μ μ := by
  have hinj : Function.Injective A.be := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have := A.be_pos x h
    simp [hx] at this
  have h0 : Module.finrank ℤ ((A.X →ₗ[ℤ] ℤ) ⧸ LinearMap.range A.be) = 0 := by
    have h1 := (LinearMap.range A.be).finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_linearMap, Module.finrank_self, mul_one] at h1
    omega
  obtain ⟨a, ha, h⟩ := Module.finrank_eq_zero_iff.1 h0 (Submodule.Quotient.mk n)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨y, hy⟩ := h
  refine ⟨A.be y y, A.be_self_nonneg y, fun μ => ?_⟩
  have h2 := A.be_sq_le y μ
  rw [hy] at h2 ⊢
  have h3 : 1 ≤ a ^ 2 := by have := sq_pos_of_ne_zero ha; omega
  have h4 : ((a • n) μ) ^ 2 = a ^ 2 * n μ ^ 2 := by simp [mul_pow]
  nlinarith [sq_nonneg (n μ)]
end GlobalTheory.AnArc
