-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.exists_ok_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:10.924802+00:00
-- url     : https://prove2.me/submissions/0bd74e18-66a6-43a5-a8b3-0bb0e0554955

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Theorems.Thm_GlobalTheory_exists_variableChange_eq_latticeCurve
import Theorems.Thm_P2M_GlobalTheory_latticeCurve_c__6ffa6b5cc0c0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution (ι : ℂ ≃+* ℂ_[q]) (W : WeierstrassCurve ℂ_[q]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (L : PeriodPair) (c : ℂ), Mdl.Ok ⟨ι, L, c, W⟩ := by
  have hne : W.Δ ≠ 0 := by intro h; simp [h] at hΔ
  haveI : W.IsElliptic := ⟨hne.isUnit⟩
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve (W.map (ι.symm : ℂ_[q] →+* ℂ))
  have e4 := congrArg WeierstrassCurve.c₄ hC
  have e6 := congrArg WeierstrassCurve.c₆ hC
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄, latticeCurve_c₄] at e4
  have l6 : (latticeCurve L).c₆ = 216 * L.g₃ := by
    simp only [latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring
  rw [WeierstrassCurve.variableChange_c₆, WeierstrassCurve.map_c₆, l6] at e6
  have hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  refine ⟨L, ((C.u⁻¹ : ℂˣ) : ℂ), hu, h1, h2, h3, h4, h6, hΔ, ?_, ?_⟩
  · have : L.g₂ / ((C.u⁻¹ : ℂˣ) : ℂ) ^ 4 = ι.symm W.c₄ / 12 := by
      have e : (ι.symm : ℂ_[q] →+* ℂ) W.c₄ = ι.symm W.c₄ := rfl
      rw [e] at e4
      field_simp
      linear_combination -e4
    show W.c₄ / 12 = ι _
    rw [this, map_div₀, RingEquiv.apply_symm_apply, map_ofNat]
  · have : L.g₃ / ((C.u⁻¹ : ℂˣ) : ℂ) ^ 6 = ι.symm W.c₆ / 216 := by
      have e : (ι.symm : ℂ_[q] →+* ℂ) W.c₆ = ι.symm W.c₆ := rfl
      rw [e] at e6
      field_simp
      linear_combination -e6
    show W.c₆ / 216 = ι _
    rw [this, map_div₀, RingEquiv.apply_symm_apply, map_ofNat]
end GlobalTheory.MomOne.Basic
