-- Prove2me | solution 1 for GlobalTheory.SmGL.ContraTrace.contra_admissible_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:19:14.891106+00:00
-- url     : https://prove2.me/submissions/8ada3f71-c022-4189-b074-5b404571d5f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
import Theorems.Thm_GlobalTheory_SmGL_ContraTrace_res_bijective
import Theorems.Thm_GlobalTheory_SmGL_ContraTrace_isAdmissible_contra
import Theorems.Thm_GlobalTheory_SmGL_ContraTrace_smoothOp_contra
import Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq
import Theorems.Thm_GlobalTheory_OpTrace_isOpen_leftStabilizer
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_mem_fixed
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_contra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.ContraTrace
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.SmGL.ContraTrace
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ π hπ
  refine ⟨isAdmissible_contra hπ, fun f hf hc => ?_⟩
  have hf' : IsLocallyConstant fun g => f g⁻¹ := hf.comp_continuous continuous_inv
  have hc' : HasCompactSupport fun g => f g⁻¹ := hc.comp_homeomorph (Homeomorph.inv G)
  obtain ⟨K, ho, hK, hle⟩ := hG _ (Filter.inter_mem
    ((isOpen_leftStabilizer hf hc).mem_nhds (one_mem _))
    ((isOpen_leftStabilizer hf' hc').mem_nhds (one_mem _)))
  have := hπ.2 K ho hK
  have := (isAdmissible_contra hπ).2 K ho hK
  have m1 := (isSmooth_contra π).smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk => (hle hk).1
  have m2 := hπ.1.smoothOp_mem_fixed (μ := μ) hf' hc' (K := K) fun k hk => (hle hk).2
  let e := LinearEquiv.ofBijective _ (res_bijective hπ.1 ho hK)
  rw [smoothTrace, smoothTrace, finRankTrace_eq _ _ m1, finRankTrace_eq _ _ m2,
    ← LinearMap.trace_transpose' (M := fixed π K), ← LinearMap.trace_conj' _ e.symm]
  congr 1
  refine LinearMap.ext fun l => e.injective ?_
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
  exact LinearMap.ext fun v => smoothOp_contra μ hπ.1 hf hc l.1 v.1
end GlobalTheory.SmGL.ContraTrace
