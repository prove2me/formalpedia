-- Prove2me | solution 1 for GlobalTheory.FrameUnif.exists_den_herm_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:57:41.506476+00:00
-- url     : https://prove2.me/submissions/f262e99f-475b-4e66-865b-ae73db14ae50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LandherrStOfHasseNormSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalLevelGroupFiniteIndexUnitaryStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalGroupActsFreelyOnFlagsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TransvectionMemPrincipalCongruenceGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LatticeModelOfSameSignatureHasseNorm
import Theorems.Thm_GlobalTheory_HermModel_herm_zero_right
import Theorems.Thm_GlobalTheory_HermModel_rank_integral_selfDual
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.FrameUnif
namespace GlobalTheory.FrameUnif
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ,
      IsIntegral ℤ ((den : E) * herm Gm x y) := by
  by_cases hξ0 : ξ = 0
  · have hz : ∀ z : D.La, z = 0 := fun z => by
      apply D.unimod.1
      ext y
      have := h.2.2.2.2 z y
      rw [hξ0, zero_mul, map_zero] at this
      simpa using this
    refine ⟨1, one_ne_zero, ?_⟩
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hz y, map_zero, GlobalTheory.HermModel.herm_zero_right, mul_zero]
    exact isIntegral_zero
  · have hint := (GlobalTheory.HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ h).2.2.1
    have halg : IsAlgebraic ℤ ξ :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic ξ)
    obtain ⟨n, hn0, hn⟩ := halg.exists_integral_multiple
    have hd : IsIntegral ℤ ((NumberField.discr E : E) * (n • ξ)) :=
      (isIntegral_algebraMap (R := ℤ) (A := E) (x := NumberField.discr E)).mul hn
    refine ⟨⟨_, hd⟩, ?_, ?_⟩
    · intro h0
      have h1 : (NumberField.discr E : E) * (n • ξ) = 0 := congrArg Subtype.val h0
      rw [zsmul_eq_mul] at h1
      exact mul_ne_zero (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
        (mul_ne_zero (Int.cast_ne_zero.2 hn0) hξ0) h1
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have h2 := (isIntegral_algebraMap (R := ℤ) (A := E) (x := n)).mul (hint x y)
      have e : (NumberField.discr E : E) * (n • ξ) * herm Gm (φ x) (φ y) =
          algebraMap ℤ E n * ((NumberField.discr E : E) * (ξ * herm Gm (φ x) (φ y))) := by
        rw [zsmul_eq_mul, eq_intCast]; ring
      change IsIntegral ℤ ((NumberField.discr E : E) * (n • ξ) * herm Gm (φ x) (φ y))
      rw [e]; exact h2
end GlobalTheory.FrameUnif
