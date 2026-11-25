-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:06.770171+00:00
-- url     : https://prove2.me/submissions/73c41bf3-c46c-4475-9572-47dbac678eae

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RestrFamily
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureDisintegrationFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsGramFiberMeasures
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreGlue_glue
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_T_gram_fiber_measure_disintegration_formula
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_units_open_embedding_local_tensor
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramExist
namespace GlobalTheory.CompanionTheory.SW.GramExist
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν hμ hν
  have hR' := hR
  obtain ⟨htr, hlc, hsc, ht2, -, -, -, -⟩ := hR'
  obtain ⟨hKtr, hKlc, hKsc, hKt2, -, -, -, hKb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  have hKu := GlobalTheory.T.units_open_embedding_local_tensor F E σ hCM R hR
  obtain ⟨hXlc, hXsc, hXt2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM R n
  obtain ⟨g, hg, hgf⟩ := hlift M J hJ
  haveI := hKb n M
  have hinj : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage hc
  have hpre : ∀ B' : Set (HermR R σ n), gramR R σ J ⁻¹' (Subtype.val '' B') = g ⁻¹' B' := by
    intro B'
    ext X
    simp only [Set.mem_preimage, Set.mem_image, hgf X]
    exact hinj.mem_set_image
  have hglue := GlobalTheory.CompanionTheory.SW.FibreGlue.glue (Fin n → Fin M → R ⊗[F] E) (HermR R σ n)
    (Matrix (Fin n) (Fin n) (R ⊗[F] E)) μ ν (gramR R σ J) g Subtype.val hinj hg hgf
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} hBo ?_
  · obtain ⟨fib, hfib⟩ := hglue
    refine ⟨fib, ?_⟩
    have hU : {X | IsUnit (gramR R σ J X).det} =
        g ⁻¹' {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hgf X]
    unfold IsGramFib
    rw [hU]
    exact hfib
  · intro S hS
    obtain ⟨B, hB, hSB, hBu, fib, hfib⟩ :=
      GlobalTheory.T.gram_fiber_measure_disintegration_formula F E σ hCM M J hJ R hR n μ ν hμ hν S hS
    refine ⟨B, hB, hSB, fun S' hS' => hBu S' hS', fib, ?_⟩
    rw [← hpre]
    exact hfib
end GlobalTheory.CompanionTheory.SW.GramExist
