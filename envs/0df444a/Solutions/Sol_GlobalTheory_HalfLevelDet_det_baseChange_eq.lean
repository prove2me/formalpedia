-- Prove2me | solution 1 for GlobalTheory.HalfLevelDet.det_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:39:59.826276+00:00
-- url     : https://prove2.me/submissions/c1b36a87-b06e-482e-bb8a-5be1bf354a8d

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
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
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
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] (hr : Module.finrank (𝓞 E) L = r)
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (f : L →ₗ[𝓞 E] L) (g : Matrix (Fin r) (Fin r) E) (hg : ∀ a, φ (f a) = g *ᵥ φ a) :
    LinearMap.det (LinearMap.baseChange E f) = g.det := by
  have hb := TensorProduct.isBaseChange (𝓞 E) L E
  have hl := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E _).2 hb
  have h1 : Module.finrank E (E ⊗[𝓞 E] L) = Module.finrank E (Fin r → E) := by
    rw [IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
      IsLocalizedModule.finrank_eq (𝓞 E)⁰ (TensorProduct.mk (𝓞 E) E L 1) le_rfl, hr]
    simp
  let F : E ⊗[𝓞 E] L →ₗ[E] (Fin r → E) := φ.liftBaseChange E
  have hF : ∀ (c : E) (a : L), F (c ⊗ₜ a) = c • φ a := fun c a => by simp [F]
  have hsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, by rw [hF, one_smul]⟩
  have hinj : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h1).2 hsurj
  let e : (E ⊗[𝓞 E] L) ≃ₗ[E] (Fin r → E) := LinearEquiv.ofBijective F ⟨hinj, hsurj⟩
  have hc : ∀ x, e (LinearMap.baseChange E f x) = g *ᵥ e x := by
    intro x
    change F _ = g *ᵥ F x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [LinearMap.baseChange_tmul, hF, hF, hg, Matrix.mulVec_smul]
    | add x y hx hy => rw [map_add, map_add, map_add, Matrix.mulVec_add, hx, hy]
  rw [← LinearMap.det_conj (LinearMap.baseChange E f) e, ← LinearMap.det_toLin']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [hc]
end GlobalTheory.HalfLevelDet
