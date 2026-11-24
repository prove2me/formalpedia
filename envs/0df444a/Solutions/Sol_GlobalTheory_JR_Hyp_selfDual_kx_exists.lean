-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.selfDual_kx_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:17.374985+00:00
-- url     : https://prove2.me/submissions/6273f8fa-d878-41b4-8c0d-3cd2a3fc19e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualHaarHyperbolicKernelPsiK
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_selfDual_measure_exists_unique_fourier_inversion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  intro F E _ _ _ _ _ A ψ hψ x
  have hT := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  obtain ⟨hL, -⟩ := hT
  have hsymm : (trxForm A (x : A.K)).IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [trxForm, LinearMap.mk₂_apply, RingHom.id_apply]
    ring_nf
  have hleft : ∀ u : A.K, (∀ b, trxForm A (x : A.K) u b = 0) → u = 0 := by
    intro u hu
    have h0 : (x : A.K) * u = 0 := hL _ (fun b => by
      have := hu b
      simpa [trxForm, Algebra.traceForm_apply, mul_assoc] using this)
    have := congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h0
    simpa [← mul_assoc] using this
  have hnd : (trxForm A (x : A.K)).Nondegenerate := by
    refine ⟨hleft, fun b hb => hleft b (fun u => ?_)⟩
    have := hb u
    simp only [trxForm, LinearMap.mk₂_apply] at this ⊢
    rw [show (x : A.K) * b * u = x * u * b by ring]
    exact this
  obtain ⟨⟨μ, hμ, -⟩, -⟩ := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (trxForm A (x : A.K)) hsymm hnd
  refine ⟨μ, ?_⟩
  have hk : (fun u b => ψ (trxForm A (x : A.K) u b)) = Hyp.kx A ψ x := by
    funext u b
    simp [trxForm, Hyp.kx, Et.psiK]
  rw [← hk]
  exact hμ
end GlobalTheory.JR.Hyp
