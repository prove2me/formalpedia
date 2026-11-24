-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.pair_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:58:03.865243+00:00
-- url     : https://prove2.me/submissions/5a170448-ecf7-4468-9c13-17e7a1d51875

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_smInd_apply
import Theorems.Thm_GlobalTheory_SmGL_IndDual_smInd_bump
import Theorems.Thm_GlobalTheory_SmGL_IndDual_mem_span_bump
import Theorems.Thm_GlobalTheory_SmGL_IndDual_dual_ext
import Theorems.Thm_GlobalTheory_SmGL_IndDual_pair_bump
import Theorems.Thm_GlobalTheory_SmGL_IndDual_vol_ne_zero
import Theorems.Thm_GlobalTheory_SmGL_DualAverage_exists_invariant_form
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_smoothRep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}
variable [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
  (hK : IsCompact (K : Set G)) (σ : Representation ℂ P W) (τ : Representation ℂ P W')
  (B : W' →ₗ[ℂ] Module.Dual ℂ W)
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution (hKo : IsOpen (K : Set G)) (hP : IsClosed (P : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hσ : IsSmooth σ) (hB : ∀ p : P, (p : G) ∈ K → ∀ w' w, B (τ p w') (σ p w) = B w' w)
    (hBi : Function.Injective B)
    (hBs : ∀ l : Module.Dual ℂ W, (∀ᶠ p in 𝓝 (1 : P), ∀ w, l (σ p w) = l w) → l ∈ LinearMap.range B)
    (hinv : ∀ g f' f, pair μ hK σ τ B (smInd P τ g f') (smInd P σ g f) = pair μ hK σ τ B f' f) :
    Function.Injective (pair μ hK σ τ B) ∧
      ∀ l ∈ smoothPart (smInd P σ).dual, l ∈ LinearMap.range (pair μ hK σ τ B) := by
  have hinv' : ∀ g f' f, pair μ hK σ τ B f' (smInd P σ g⁻¹ f) = pair μ hK σ τ B (smInd P τ g f') f := by
    intro g f' f
    rw [← hinv g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f' h0
    refine Subtype.ext (Subtype.ext (funext fun g => hBi (LinearMap.ext fun w => ?_)))
    obtain ⟨U, hU, hU'⟩ := (mem_nhds_subtype _ _ _).1 ((hσ w).mem_nhds (x := 1) (by simp))
    obtain ⟨J, hJ, hJU, hle, -⟩ := hbasis _ (Filter.inter_mem hU
      (IsOpen.mem_nhds (isSmooth_smoothRep _ (smInd P τ g f')) (by simp)))
    have h1 := pair_bump μ hK σ τ B hB hJ hle (smInd P τ g f') (fun j hj => by
      have h2 : (smInd P τ g f').1.1 (1 * j) = _ := congrArg (fun φ => φ.1.1 1) (hJU hj).2
      rwa [one_mul] at h2) ⟨w, mem_fixed_iff.2 fun h hh => hU' (hJU hh).1⟩
    rw [← hinv', h0, LinearMap.zero_apply, smInd_apply, one_mul] at h1
    simpa [vol_ne_zero μ hK hKo hJ] using h1
  · intro l hl
    obtain ⟨J, hJ, hJU, hle, hn⟩ := hbasis _ (IsOpen.mem_nhds hl (by
      rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply]))
    have hlJ : ∀ j ∈ J, ∀ f, l (smInd P σ j f) = l f := fun j hj f => by
      have h2 : l (smInd P σ j⁻¹⁻¹ f) = l f := LinearMap.congr_fun (hJU (inv_mem hj)) f
      rwa [inv_inv] at h2
    have hJc : IsCompact (J : Set G) := hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) hle
    have hHc : IsCompact (J.subgroupOf P : Set P) := hP.isClosedEmbedding_subtypeVal.isCompact_preimage hJc
    set c : ℂ := ((μ.real (K ∩ cell P J) : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := vol_ne_zero μ hK hKo hJ
    have hex : ∀ z : G, ∃ w' : W', (∀ h ∈ J.subgroupOf P, ∀ w, B w' (σ h w) = B w' w) ∧
        ∀ w : fixed σ (J.subgroupOf P), B w' w = c⁻¹ * l (smInd P σ z⁻¹ (bump σ hJ w)) := by
      intro z
      obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend (c⁻¹ • (l ∘ₗ smInd P σ z⁻¹ ∘ₗ bump σ hJ))
      obtain ⟨l₁, h1, h2⟩ := GlobalTheory.SmGL.DualAverage.exists_invariant_form P W σ hσ _ hHc l₀
      obtain ⟨w', rfl⟩ := hBs l₁ (Filter.mem_of_superset
        ((hJ.preimage continuous_subtype_val).mem_nhds (one_mem J)) h1)
      exact ⟨w', h1, fun w => (h2 _ (mem_fixed_iff.1 w.2)).trans (LinearMap.congr_fun hl₀ w)⟩
    choose φ hφ1 hφ2 using hex
    have hφr : ∀ i ∈ J, ∀ j ∈ K, φ (j * i) = φ j := fun i hi j _ =>
      hBi (dual_ext hσ hHc (hφ1 _) (hφ1 _) fun w hw => by
        rw [hφ2 _ ⟨w, hw⟩, hφ2 _ ⟨w, hw⟩, mul_inv_rev, map_mul, Module.End.mul_apply, hlJ _ (inv_mem hi)])
    have hφl : ∀ p : P, (p : G) ∈ K → ∀ j ∈ K, φ (p * j) = τ p (φ j) := by
      intro p hp z _
      have h1 : ∀ w, B (τ p (φ z)) w = B (φ z) (σ p⁻¹ w) := fun w => by
        rw [← hB p hp (φ z), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have h2 : ∀ q : P, (q : G) ∈ K → ∀ h ∈ J.subgroupOf P, q * h * q⁻¹ ∈ J.subgroupOf P :=
        fun q hq h hh => hn q hq h hh
      refine hBi (dual_ext hσ hHc (hφ1 _) (fun h hh w => ?_) fun w hw => ?_)
      · rw [h1, h1, ← hφ1 z _ (h2 p⁻¹ (inv_mem hp) h hh) (σ p⁻¹ w)]
        simp only [← Module.End.mul_apply, ← map_mul]
        simp [mul_assoc]
      · have hv : σ p⁻¹ w ∈ fixed σ (J.subgroupOf P) := mem_fixed_iff.2 fun h hh => by
          conv_rhs => rw [← mem_fixed_iff.1 hw _ (h2 p hp h hh)]
          simp only [← Module.End.mul_apply, ← map_mul]
          simp [mul_assoc]
        rw [h1, hφ2 _ ⟨w, hw⟩, hφ2 _ ⟨_, hv⟩, mul_inv_rev, map_mul, Module.End.mul_apply,
          ← smInd_bump σ hJ p⁻¹ (hn _ (inv_mem hp)) (fun j hj => by simpa using hn _ hp j hj) ⟨w, hw⟩ ⟨_, hv⟩ rfl]
        rfl
    let f' := extInd τ hJ hle φ hφl hφr
    have hf1 : ∀ z ∈ K, f'.1.1 z = φ z := fun z hz => by
      show extFun τ K φ z = φ z
      simpa using extFun_mul hφl 1 hz
    have hf2 : ∀ j ∈ J, smInd P τ j f' = f' := fun j hj =>
      Subtype.ext (Subtype.ext (funext fun g => extFun_right hφl (hle hj) (hφr j hj) g))
    refine ⟨f', dual_ext (isSmooth_smoothRep _) hJc (fun j hj f => ?_) hlJ fun f hf => ?_⟩
    · conv_lhs => rw [← hf2 j hj]
      exact hinv j f' f
    · refine LinearMap.eqOn_span' ?_ (mem_span_bump σ hJ hK hle hn hPK f (mem_fixed_iff.1 hf))
      rintro _ ⟨z, hz, w, rfl⟩
      rw [hinv', pair_bump μ hK σ τ B hB hJ hle, smInd_apply, one_mul, hf1 z hz, hφ2, mul_inv_cancel_left₀ hc0]
      intro j hj
      rw [smInd_apply, smInd_apply, one_mul, hf1 z hz, hf1 _ (mul_mem (hle hj) hz),
        ← hφr _ (hn _ (inv_mem hz) j hj) z hz]
      simp [mul_assoc]
end GlobalTheory.SmGL.IndDual
