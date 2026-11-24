-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:09.697331+00:00
-- url     : https://prove2.me/submissions/3ac36176-c4ec-4959-b91c-dcc684dfd3b8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtension
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TupFubini_measurable_cons_tail
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TupFubini_lintegral_tuple_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TupFubini_lintegral_tuple_first_coord
import Theorems.Thm_GlobalTheory_T_adelic_unitary_group_locally_compact
import Theorems.Thm_GlobalTheory_T_coordinate_haar_measure
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_unitary_action_preserves_haar_local


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR d b lam hlam n s _ φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hact : ∀ h : HA R σ J, Measurable (actW R σ J h :
      (Fin n → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin (M + 1) → R ⊗[F] E) := by
    intro h
    have := hBorel n (M + 1)
    have hc := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) J hJ R).2.2.2.2.2 n).1
    exact (hc.comp (Continuous.prodMk_right h)).measurable
  have key : ∀ y : Fin 1 → Fin (M + 1) → R ⊗[F] E,
      ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1)) =
      ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a))))
        ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) := by
    intro y
    have hinv := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hCM (M + 1) J hJ R hR n (coordW R b lam n (M + 1)) (hW n (M + 1)) (s y)
    have hf : Measurable fun Y : Fin n → Fin (M + 1) → R ⊗[F] E =>
        φ (Fin.cons (y 0) Y) := hφ.comp (TupFubini.measurable_cons_tail (y 0))
    calc ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1))
        = ∫⁻ Y, φ (Fin.cons (y 0) Y) ∂((coordW R b lam n (M + 1)).map (actW R σ J (s y))) := by
          rw [hinv]
      _ = ∫⁻ Y, φ (Fin.cons (y 0) (actW R σ J (s y) Y)) ∂(coordW R b lam n (M + 1)) :=
          lintegral_map hf (hact (s y))
      _ = _ := TupFubini.lintegral_tuple_first_coord (coordK R b lam) n M _ (hf.comp (hact (s y)))
  calc ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y)
          ∂(coordW R b lam n (M + 1)) ∂(coordW R b lam 1 (M + 1)) :=
        TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 1) φ hφ
    _ = _ := lintegral_congr key
end GlobalTheory.CompanionTheory.SW
