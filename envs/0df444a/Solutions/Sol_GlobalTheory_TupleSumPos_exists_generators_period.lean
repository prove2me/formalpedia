-- Prove2me | solution 1 for GlobalTheory.TupleSumPos.exists_generators_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:27:37.293478+00:00
-- url     : https://prove2.me/submissions/694f43f0-480f-4b6c-b20a-e76662647f41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorsLattice
import Theorems.Thm_GlobalTheory_TupleSumPos_exists_generators_lattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_card_Psi_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open scoped TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.TupleSumPos
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.TupleSumPos
theorem _root_.solution {r : ℕ} {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) :
    ∃ e : Fin A.T.r → Vsp A.T.dim, (∀ j, e j ∈ A.T.L) ∧ ∀ v ∈ A.T.L,
      ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, v = ∑ j, act (c j) (e j) + (5 : ℂ) • y := by
  obtain ⟨τ⟩ : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos X)
  have hr : A.T.r = r := by
    have h1 := A.T.dim_conj τ.1
    rw [A.dim_pos, A.dim_neg] at h1
    have := X.p0_le
    omega
  rw [hr]
  obtain ⟨e, he⟩ := exists_generators_lattice X.Λ X.Λ_fg X.Λ_span
  refine ⟨fun j => A.φ (e j), fun j => (A.lat _).2 ⟨_, (e j).2, rfl⟩, fun v hv => ?_⟩
  obtain ⟨u, hu, rfl⟩ := (A.lat v).1 hv
  obtain ⟨c, y, h⟩ := he ⟨u, hu⟩
  refine ⟨c, A.φ y, (A.lat _).2 ⟨_, y.2, rfl⟩, ?_⟩
  have h2 : u = ∑ k, (c k : E) • (e k : Fin r → E) + 5 • (y : Fin r → E) := by
    have := congrArg Subtype.val h
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at this
    rw [this, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_ofNat]
    rfl
  rw [h2, map_add, map_sum, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat]
  simp only [A.act_eq]
end GlobalTheory.TupleSumPos
