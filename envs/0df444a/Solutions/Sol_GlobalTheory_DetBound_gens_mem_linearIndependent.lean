-- Prove2me | solution 1 for GlobalTheory.DetBound.gens_mem_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:40.87444+00:00
-- url     : https://prove2.me/submissions/2efcbac4-68ac-4b9c-aed6-283cff46048c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
import Theorems.Thm_GlobalTheory_DetBound_cmType_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {D : O} {I : Type} [Fintype I] {φ : I → E →+* K} (hφ : IsCMTypeIn φ)
    {H : Type} [AddCommGroup H] [Module O H] {ρ : orderC c →+* Module.End O H} {Fil : Submodule O H}
    {B : LinearMap.BilinForm O H} (hL : IsCMLattice φ ρ Fil B) (hE : EigenClaims φ ρ Fil B D) {e f : I → H}
    (hG : IsGens φ ρ e f) : (∀ i, e i ∈ Fil) ∧ LinearIndependent O e := by
  haveI : Module.Free O H := hL.1
  have hself : ∀ i, e i ∈ eigLat (K := K) ρ (φ i) := fun i => (hG i).1 ▸ Submodule.mem_span_singleton_self _
  refine ⟨fun i => ?_, ?_⟩
  · have h := hE.2.2.2.1 i
    exact (inf_eq_right.1 h) (hself i)
  · have hi : iSupIndep (fun σ : E →+* K => eigLat (K := K) ρ σ) := hE.2.2.1.1
    refine iSupIndep.linearIndependent _ (hi.comp (cmType_injective hφ)) hself ?_
    intro i h0
    obtain ⟨g, hg, hgs⟩ := (hE.2.1 (φ i)).2.1
    have : g ∈ eigLat (K := K) ρ (φ i) := hgs ▸ Submodule.mem_span_singleton_self _
    rw [(hG i).1, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this
    exact hg this
end GlobalTheory.DetBound
