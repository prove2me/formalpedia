-- Prove2me | solution 1 for GlobalTheory.PlaceOver.valuation_lt_one_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:41.264682+00:00
-- url     : https://prove2.me/submissions/d3199007-a609-4f4d-bda4-66a1e111a256

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapEqOfContinuousAdicCompletionIso
import Theorems.Thm_GlobalTheory_PlaceOver_isOpen_valuation_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.PlaceOver
open Filter Topology
namespace GlobalTheory.PlaceOver
theorem _root_.solution {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F']
    {P : HeightOneSpectrum (𝓞 F)} {P' : HeightOneSpectrum (𝓞 F')}
    (i : P.adicCompletion F →+* P'.adicCompletion F') (hi : Continuous i)
    {x : P.adicCompletion F} (hx : Valued.v x < 1) : Valued.v (i x) < 1 := by
  have hU : {y : P'.adicCompletion F' | Valued.v y < 1} ∈ 𝓝 (i 0) := by
    rw [map_zero]
    exact (isOpen_valuation_lt_one P').mem_nhds (by simp)
  have hV := hi.continuousAt.preimage_mem_nhds hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hV
  have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by
    simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx (Units.mk0 _ hγ0)
  have hxn : x ^ n ∈ i ⁻¹' {y : P'.adicCompletion F' | Valued.v y < 1} := by
    apply hγ
    show Valued.v.restrict (x ^ n) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
    exact hn
  have h1 : Valued.v (i x) ^ n < 1 := by simpa [map_pow] using hxn
  by_contra h
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 h)))
end GlobalTheory.PlaceOver
