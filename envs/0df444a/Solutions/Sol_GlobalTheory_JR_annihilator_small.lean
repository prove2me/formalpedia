-- Prove2me | solution 1 for GlobalTheory.JR.annihilator_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:13.03116+00:00
-- url     : https://prove2.me/submissions/e3006597-3503-466f-bafa-99e1619ead79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ScaledIntegersKAnnihilatorSmallNearZero
import Theorems.Thm_GlobalTheory_JR_exists_small_dual_lattices
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  intro F E _ _ _ _ hU A ψ hψ U hUmem
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hnd : (Algebra.traceForm F A.K).Nondegenerate := hfacts.2.2.1
  have hOKopen : IsOpen A.OK := hfacts.2.2.2.2.2.2.2.2.2.1
  obtain ⟨R, hR⟩ := hfacts.2.2.2.2.2.2.2.2.2.2.2
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K)
    (Algebra.traceForm_isSymm F (S := A.K)) hnd
  obtain ⟨M, N, hMU, -, -, -, hNc, -, hM⟩ := hsmall U hUmem
  have hev : ∀ᶠ c in 𝓝 (0 : F), ∀ y ∈ (N : Set A.K), c • y ∈ A.OK := by
    refine hNc.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : ContinuousAt (fun p : F × A.K => p.1 • p.2) ((0 : F), y) := continuous_smul.continuousAt
    have : A.OK ∈ 𝓝 ((fun p : F × A.K => p.1 • p.2) ((0 : F), y)) := by
      simpa using hOKopen.mem_nhds h0
    exact hc this
  filter_upwards [nhdsWithin_le_nhds hev] with c hc b hb
  apply hMU
  rw [SetLike.mem_coe, hM]
  intro y hy
  have := hb y (hc y hy)
  simpa [Et.psiK, Algebra.traceForm_apply, mul_comm] using this
end GlobalTheory.JR
