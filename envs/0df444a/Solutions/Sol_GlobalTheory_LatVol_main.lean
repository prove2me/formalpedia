-- Prove2me | solution 1 for GlobalTheory.LatVol.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:19.392474+00:00
-- url     : https://prove2.me/submissions/e80e648e-21ef-46fe-866c-3793360d9641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_VolumeScaledIntegersMulVolumeDualEqOne
import Theorems.Thm_GlobalTheory_LatVol_stdChar_continuous
import Theorems.Thm_GlobalTheory_JR_DualLattice_stdChar_continuous
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
open GlobalTheory GlobalTheory.LatVol
namespace GlobalTheory.LatVol
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd c hc
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hψc := stdChar_continuous ψ hψ

  have hcl : IsClosed {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    have : {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} =
        ⋂ x : A.K, ⋂ (_ : c • x ∈ A.OK), {y : A.K | ψ (Algebra.trace F A.K (x * y)) = 1} := by
      ext y; simp [Et.psiK]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    have htr : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hψc.comp (htr.comp (continuous_const.mul continuous_id))
  refine ⟨hcl.measurableSet, ?_⟩

  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z; simp [M, ← hR]
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hMo : IsOpen (M : Set A.K) := by rw [hM]; exact hOpen.preimage hsm
  have hMc : IsCompact (M : Set A.K) := by
    have : (M : Set A.K) = (fun w : A.K => c⁻¹ • w) '' A.OK := by
      rw [hM]; ext z; constructor
      · intro hz; exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_inv_smul₀ hc] using hw
    rw [this]; exact hCpt.image (continuous_const_smul _)
  have hk : (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) = A.kerK ψ := by
    funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
  have hsd' : SelfDual μK (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) := by rw [hk]; exact hsd
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hsd.1).1
    M hMo hMc).1.1 hsd'
  have hN : {y : A.K | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} =
      {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    ext y; simp [M, ← hR, Et.psiK, Algebra.traceForm_apply]
  rw [hN, show ((M : Set A.K)) = {z : A.K | c • z ∈ A.OK} from hM] at key
  have h1 : (μK {z : A.K | c • z ∈ A.OK}).toReal * (μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal = 1 := by
    rw [← ENNReal.toReal_mul, key, ENNReal.toReal_one]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one]
end GlobalTheory.LatVol
