-- Prove2me | solution 1 for GlobalTheory.HalfLevelDet.det_eq_one_of_trivial_on_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:56:41.021055+00:00
-- url     : https://prove2.me/submissions/7ef464fe-ae47-4fc0-b1b5-a85909c403f8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryMatrixOfLatticeIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetEqOneOfTrivialOnHalf
import Theorems.Thm_GlobalTheory_HalfLevelDet_det_baseChange_eq
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_CongruenceDet_det_eq_one
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_IsoExt_exists_unitary_of_isometry
import Theorems.Thm_GlobalTheory_LevelHalf_trivial_mod_of_trivial_on_half
import Theorems.Thm_GlobalTheory_exists_herm_coord_of_datum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.HalfLevelDet
namespace GlobalTheory.HalfLevelDet
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : Dw.La ≃ₗ[𝓞 E] Dw.La), (∀ a b, Dw.EF (γ a) (γ b) = Dw.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ e, γ a = a + l.M • e) → LinearMap.det (LinearMap.baseChange E (γ : Dw.La →ₗ[𝓞 E] Dw.La)) = 1 := by
  intro E _ _ _ H Dw l γ hiso hhalf
  have := Dw.fin
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Dw l γ hiso hhalf
  obtain ⟨ξ, hξ0, hξ⟩ : ∃ δ : E, δ ≠ 0 ∧ cc δ = -δ := by
    have hne : IsCMField.complexConj E ≠ 1 := IsCMField.complexConj_ne_one E
    obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra h
      push Not at h
      exact hne (AlgEquiv.ext h)
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    unfold cc
    rw [map_sub, IsCMField.complexConj_apply_apply]
    ring
  obtain ⟨Gm, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw ξ hξ hξ0 _ rfl
  obtain ⟨g, hgu, hg⟩ :=
    GlobalTheory.IsoExt.exists_unitary_of_isometry E H Dw Dw _ ξ Gm φ φ γ hξ hM hM hiso
  rw [det_baseChange_eq Dw.rank φ hM.2.1 (γ : Dw.La →ₗ[𝓞 E] Dw.La) g hg]
  refine GlobalTheory.CongruenceDet.det_eq_one E _ l.M Gm (LinearMap.range φ) g hM.2.2.2.1
    (Submodule.fg_range φ) hM.2.1 l.three_le ⟨hgu, fun x => ⟨?_, ?_⟩⟩ ?_
  · rintro ⟨a, rfl⟩
    exact ⟨γ a, hg a⟩
  · rintro ⟨a, ha⟩
    refine ⟨γ.symm a, ?_⟩
    have h := hg (γ.symm a)
    rw [LinearEquiv.apply_symm_apply, ha] at h
    have h' := congrArg (fun v => (g⁻¹ : GL _ E).1 *ᵥ v) h
    simpa [Matrix.mulVec_mulVec] using h'.symm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ e, ⟨e, rfl⟩, by rw [← hg, he, map_add, map_nsmul]⟩
end GlobalTheory.HalfLevelDet
