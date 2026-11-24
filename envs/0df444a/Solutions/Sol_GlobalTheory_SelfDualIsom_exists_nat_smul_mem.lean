-- Prove2me | solution 1 for GlobalTheory.SelfDualIsom.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:42:45.769397+00:00
-- url     : https://prove2.me/submissions/68876f28-615a-4532-b93e-b0abdee5e26a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LandherrStOfHasseNormSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsScaledIsometry
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
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
open GlobalTheory GlobalTheory.SelfDualIsom
namespace GlobalTheory.SelfDualIsom
theorem _root_.solution {E : Type} [Field E] [NumberField E] {M₁ M₂ V : Type}
    [AddCommGroup M₁] [Module (𝓞 E) M₁] [Module.Finite (𝓞 E) M₁]
    [AddCommGroup M₂] [Module (𝓞 E) M₂] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (φ₁ : M₁ →ₗ[𝓞 E] V) (φ₂ : M₂ →ₗ[𝓞 E] V)
    (hspan : Submodule.span E (Set.range φ₂) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (N : 𝓞 E) • φ₁ x ∈ LinearMap.range φ₂ := by
  classical
  have h1 : ∀ v : V, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ LinearMap.range φ₂ := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ₂) := by rw [hspan]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hm := Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)})
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    · rw [← hc, mul_smul]
      exact Submodule.smul_mem _ _ ht
  choose n hn hmem using h1
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M₁)
  refine ⟨∏ x ∈ s, n (φ₁ x), Finset.prod_pos fun x _ => hn _, fun x => ?_⟩
  have hx : x ∈ Submodule.span (𝓞 E) (s : Set M₁) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ₁ x)) (Finset.mem_coe.1 hy)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hmem _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ _ ha
end GlobalTheory.SelfDualIsom
