-- Prove2me | solution 1 for GlobalTheory.JR.charIntegral_inv_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:13.888205+00:00
-- url     : https://prove2.me/submissions/8833fafd-9659-4620-b7be-f48bbcc9b0b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralPsiKOverScaledIntegersEqVolumeIndicator
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_selfDual_iff_lattice_volume_and_plancherel_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ c : F, c ≠ 0 → ∀ b : A.K, ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * b) ∂μK = Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => ((μK {z : A.K | c • z ∈ A.OK}).toReal : ℂ)) b := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ c hc b
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hO, hC, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z
    simp [M, ← hR]
  have hMO : IsOpen (M : Set A.K) := by
    rw [hM]
    exact hO.preimage (continuous_const_smul c)
  have hMC : IsCompact (M : Set A.K) := by
    rw [hM]
    exact (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).mpr hC
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hμ).1
    M hMO hMC).2 b
  have hpsi : ∀ z y : A.K, A.psiK ψ (z * y) = ψ (Algebra.traceForm F A.K z y) := by
    intro z y
    simp [Et.psiK, Algebra.traceForm_apply]
  simp_rw [hpsi]
  rw [← hM]
  convert key using 2
  ext y
  simp only [Set.mem_setOf_eq, Algebra.traceForm_apply]
  constructor
  · intro h x hx
    exact h x (by simpa [hM] using (show x ∈ (M : Set A.K) from hx))
  · intro h z hz
    exact h z (show z ∈ (M : Set A.K) by rw [hM]; exact hz)
end GlobalTheory.JR
