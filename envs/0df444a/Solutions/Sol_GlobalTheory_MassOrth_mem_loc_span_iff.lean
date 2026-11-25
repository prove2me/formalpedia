-- Prove2me | solution 1 for GlobalTheory.MassOrth.mem_loc_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:59:35.627968+00:00
-- url     : https://prove2.me/submissions/946023dc-7a3c-4180-9898-e64bafd59a8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_int_mem_biInt
import Theorems.Thm_GlobalTheory_MassOrth_inv_mem_biInt
import Theorems.Thm_GlobalTheory_MassOrth_exists_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.MassOrth
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (S : Set V) (x : V) :
    x ∈ loc (K := K) w.asIdeal (Submodule.span (𝓞 K) S) ↔
      x ∈ Submodule.span (biInt (w.valuation K)) S := by
  constructor
  · rintro ⟨s, hs, hx⟩
    have h1 : ∀ y ∈ Submodule.span (𝓞 K) S, y ∈ Submodule.span (biInt (w.valuation K)) S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span hy
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul r a _ ha =>
        rw [← algebraMap_smul K r a]
        exact Submodule.smul_mem _ (⟨_, int_mem_biInt w r⟩ : biInt (w.valuation K)) ha
    obtain ⟨s0, s1⟩ := inv_mem_biInt w hs
    have h2 : (algebraMap (𝓞 K) K s)⁻¹ • (s • x) ∈ Submodule.span (biInt (w.valuation K)) S :=
      Submodule.smul_mem _ (⟨_, s1⟩ : biInt (w.valuation K)) (h1 _ hx)
    rwa [← algebraMap_smul K s x, inv_smul_smul₀ s0] at h2
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, Submonoid.one_mem _, by simpa using Submodule.subset_span hy⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul r y _ hy =>
      obtain ⟨t, ht, a, hta⟩ := exists_denom w r.2
      obtain ⟨s, hs, hsy⟩ := hy
      refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
      have e : (s * t) • r • y = a • s • y := by
        rw [Subring.smul_def, mul_smul, ← algebraMap_smul K t, smul_smul (algebraMap (𝓞 K) K t), hta,
          algebraMap_smul, smul_comm]
      rw [e]
      exact Submodule.smul_mem _ a hsy
end GlobalTheory.MassOrth
