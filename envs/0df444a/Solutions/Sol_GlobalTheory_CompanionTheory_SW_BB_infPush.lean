-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.infPush
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:25:59.083202+00:00
-- url     : https://prove2.me/submissions/f7bbd69c-0f86-472e-8056-f21dd204e6c3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuplesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanCoordinateMeasureTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_InfPush_map_coord_pi
import Theorems.Thm_GlobalTheory_T_coordinate_homeomorph_rank_one_tuples
import Theorems.Thm_GlobalTheory_T_infinite_adeles_local_ring_totally_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory.CompanionTheory.SW.BB.InfPush
namespace GlobalTheory.CompanionTheory.SW.BB
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → (coordW (Ainf F) b laminf 1 M).map (fun X w => xw e b X w) = ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) := by
  intro F E _ _ _ _ _ σ hσ M d b e he laminf hH hmap
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨h1, h2, h3, h4, -⟩ := hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hemb, hcoord⟩ := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hσ (Ainf F) d b laminf hH M
  have hem : Measurable (fun x : Ainf F => (e x : InfinitePlace F → ℝ)) := he.continuous.measurable
  have hΦ : Measurable (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w) :=
    measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply w).comp (hem.comp (measurable_pi_apply p))
  have hcomp : (fun (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) => xw e b X w) =
      (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w) ∘
        (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => cv (Ainf F) b (X 0)) := rfl
  have hr : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hcomp, ← Measure.map_map hΦ hemb.measurable, hcoord,
    map_coord_pi laminf (fun x => e x) hem _ hmap, ENNReal.ofReal_pow hr]
  simp [Fintype.card_prod, ENNReal.ofReal]
end GlobalTheory.CompanionTheory.SW.BB
