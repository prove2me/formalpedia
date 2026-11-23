-- Prove2me | solution 1 for GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:45.672858+00:00
-- url     : https://prove2.me/submissions/7cacf1de-fe4e-47e4-b496-d3d439d60455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsNhdsZeroPrincipalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.AdeleDiscrete
namespace GlobalTheory.AdeleDiscrete
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∃ U ∈ nhds (0 : AdeleRing (𝓞 F) F), ∀ x : F, algebraMap F (AdeleRing (𝓞 F) F) x ∈ U → x = 0 := by
  intro F _ _
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (0 : v.Completion) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  refine ⟨_, (hU.prod hV).mem_nhds ⟨fun v _ => Metric.mem_ball_self one_pos,
    fun v => zero_mem _⟩, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by
    have h := h2 v
    rw [AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  have hlt : ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F a) < 1 := fun w => by
    have h := h1 w trivial
    rw [mem_ball_zero_iff, AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.norm_coe] at h
    exact h
  by_contra h0
  have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))
end GlobalTheory.AdeleDiscrete
