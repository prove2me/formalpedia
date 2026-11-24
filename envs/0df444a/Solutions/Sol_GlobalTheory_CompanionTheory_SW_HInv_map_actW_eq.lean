-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:16.521356+00:00
-- url     : https://prove2.me/submissions/460727f2-2290-4d26-94af-bc3545c6b69b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HInv_det_mul_conj_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HInv_map_tuple_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_algebra_tensor_invol
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HInv
namespace GlobalTheory.CompanionTheory.SW.HInv
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R],
    IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure →
    ∀ h : HA R σ J, μ.map (actW R σ J h) = μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ hμ h
  obtain ⟨r1, r2, r3, r4, r5, r6, -, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI := r5
  haveI := r6
  obtain ⟨t1, t2, t3, t4, tc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨a1, a2, -, ai, -⟩ := KAlg.algebra_tensor_invol F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := a1
  haveI := a2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, JR]
    rw [e]
    exact (IsUnit.mk0 _ hJ.2).map (inclR (F := F) R)
  have hg : cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      JR (F := F) R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R J :=
    (show (h : HR R σ J).1 ∈ HR R σ J from (h : HR R σ J).2)
  exact map_tuple_eq (sigR R σ) tc ai _ (det_mul_conj_eq_one _ _ _ hg hJu) μ
end GlobalTheory.CompanionTheory.SW.HInv
