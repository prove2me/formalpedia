-- Prove2me | solution 1 for GlobalTheory.ScaledRestr.exists_scaled_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:49.045209+00:00
-- url     : https://prove2.me/submissions/3a61f8b0-84d5-46d3-94d9-0448ee2b3eed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegrality
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.ScaledRestr
namespace GlobalTheory.ScaledRestr
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {H : Type} [AddCommGroup H] [Module O H] {I : Type}
    (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (D : O) (e f : I → H)
    (hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ) (hG : IsGens φ ρ e f)
    (N : Module.End K (K ⊗[O] H)) (i : I) (hN : IsLower ρ (φ i) (e i) (f i) N) (h : H) :
    ∃ m : H, inK K H m = algebraMap O K D • N (inK K H h) := by
  have key : ∀ x ∈ ⨆ σ : E →+* K, eigLat ρ σ, ∃ m : H, inK K H m = N (inK K H x) := by
    intro x hx
    refine Submodule.iSup_induction (fun σ : E →+* K => eigLat ρ σ)
      (motive := fun x => ∃ m : H, inK K H m = N (inK K H x)) hx ?_ ?_ ?_
    · intro σ x hx
      by_cases hσ : σ = φ i
      · subst hσ
        rw [(hG i).1, Submodule.mem_span_singleton] at hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨u • f i, ?_⟩
        rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul_of_tower, hN.1]
      · refine ⟨0, ?_⟩
        have hx' : inK K H x ∈ eigK ρ σ := hx
        rw [hN.2 σ hσ _ hx', LinearMap.map_zero]
    · exact ⟨0, by simp⟩
    · intro x y hx hy
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ha, hb]⟩
  obtain ⟨m, hm⟩ := key _ (hD h)
  refine ⟨m, ?_⟩
  rw [hm, LinearMap.map_smul, LinearMap.map_smul_of_tower, algebraMap_smul]
end GlobalTheory.ScaledRestr
