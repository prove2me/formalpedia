-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.exists_local_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:19.913007+00:00
-- url     : https://prove2.me/submissions/67e3ac71-a15c-4dd2-91ad-392a4815fe97

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroupStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianLocalContinuousCongruenceSection
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_T_hermitian_orbit_local_section_subgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR n S hS
  obtain ⟨Q, o, -, -, ho, hform⟩ := GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS
  have hc : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have ho1 : o 1 = S := by
    apply Subtype.ext
    rw [hform]
    simp [hc]
  have hinv : Function.LeftInverse (Function.invFun o) o := Function.leftInverse_invFun ho.injective
  refine ⟨Set.range o, fun S' => ((Function.invFun o S' : Q) : GL (Fin n) (R ⊗[F] E)),
    ho.isOpen_range, ⟨1, ho1⟩, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn (Function.invFun o) (Set.range o) := by
      rw [continuousOn_iff_continuous_restrict]
      have h1 : (fun y : Set.range o => Function.invFun o y.1) = ho.isEmbedding.toHomeomorph.symm := by
        funext y
        obtain ⟨_, x, rfl⟩ := y
        show Function.invFun o (o x) = _
        rw [hinv x]
        exact ho.isEmbedding.toHomeomorph.eq_symm_apply.2 (Subtype.ext rfl)
      have h2 : Continuous (fun y : Set.range o => Function.invFun o y.1) := by
        rw [h1]
        exact Homeomorph.continuous _
      exact h2
    exact continuous_subtype_val.comp_continuousOn hcont
  · show ((Function.invFun o S : Q) : GL (Fin n) (R ⊗[F] E)) = 1
    rw [← ho1, hinv 1]
    rfl
  · rintro _ ⟨x, rfl⟩
    simp only [hinv x]
    exact hform x
end GlobalTheory.CompanionTheory.SW
