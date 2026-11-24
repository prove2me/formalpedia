-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:42.871498+00:00
-- url     : https://prove2.me/submissions/f17f2536-62ab-4694-ae8d-42f6ff0ac6bc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_fixed_eq_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_half_trace_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_hermMat_mem

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution [IsTopologicalRing R] [CharZero F] {σ : E →ₐ[F] E}
    (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (n : ℕ) [ContinuousAdd (R ⊗[F] E)] [ContinuousSMul R (R ⊗[F] E)]
    (hsig : Continuous (sigR R σ)) (htr : Continuous (Algebra.trace R (R ⊗[F] E))) :
    IsHomeomorph (hermCoord R σ n) := by
  have hincl : Continuous fun r : R => r ⊗ₜ[F] (1 : E) := by
    have : IsModuleTopology R R := inferInstance
    have := IsModuleTopology.continuous_of_linearMap (R := R) (A := R) (B := R ⊗[F] E)
      (Algebra.linearMap R (R ⊗[F] E))
    have e : (fun r : R => r ⊗ₜ[F] (1 : E)) = ⇑(Algebra.linearMap R (R ⊗[F] E)) := by
      funext r
      simp [Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [e]
    exact this
  let h : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    { toFun := hermCoord R σ n
      invFun := fun x => ⟨hermMat R σ n x, hermMat_mem R hinv n x⟩
      left_inv := by
        intro S
        apply Subtype.ext
        funext a b
        rcases lt_trichotomy a b with hab | hab | hab
        · simp [hermMat, dif_pos hab, hermCoord]
        · subst hab
          obtain ⟨r, hr⟩ := fixed_eq_tmul R hinv h2 hδ hσδ
            ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a a) (S.2 a a)
          simp only [hermMat, lt_irrefl, dite_false, hermCoord]
          rw [hr, half_trace_tmul R h2]
        · simp only [hermMat, dif_pos hab, dif_neg (not_lt_of_gt hab), hermCoord]
          exact S.2 a b
      right_inv := by
        intro x
        refine Prod.ext ?_ ?_
        · funext i
          simp only [hermCoord, hermMat, lt_irrefl, dite_false]
          exact half_trace_tmul R h2 _
        · funext p
          obtain ⟨⟨a, b⟩, hp⟩ := p
          simp only [hermCoord, hermMat]
          exact dif_pos hp
      continuous_toFun := by
        refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
        · exact continuous_const.mul (htr.comp
            ((continuous_apply_apply i i).comp continuous_subtype_val))
        · exact (continuous_apply_apply p.1.1 p.1.2).comp continuous_subtype_val
      continuous_invFun := by
        refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
        by_cases hab : a < b
        · simp only [hermMat, dif_pos hab]
          exact (continuous_apply _).comp continuous_snd
        · by_cases hba : b < a
          · simp only [hermMat, dif_neg hab, dif_pos hba]
            exact hsig.comp ((continuous_apply _).comp continuous_snd)
          · simp only [hermMat, dif_neg hab, dif_neg hba]
            exact hincl.comp ((continuous_apply _).comp continuous_fst) }
  exact h.isHomeomorph
end GlobalTheory.CompanionTheory.SW.HaarCoord
