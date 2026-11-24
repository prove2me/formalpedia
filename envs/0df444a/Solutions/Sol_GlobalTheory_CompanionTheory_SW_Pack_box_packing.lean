-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Pack.box_packing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:07.909887+00:00
-- url     : https://prove2.me/submissions/0052be2c-20b0-45b4-8aa6-dd6bb7774482

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBoundStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicBoxLatticeCountRatio
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Pack_norm_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Pack_finrank_coord
import Theorems.Thm_GlobalTheory_T_lattice_ball_count_ratio_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Pack
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.Pack
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  intro F E _ _ _ _ _ σ hσ d b M Λ _ e N r R hr hrR
  obtain ⟨hF, -, h2, -⟩ := hσ
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have key := GlobalTheory.T.lattice_ball_count_ratio_bound (PiLp 1 (fun _ : Fin 1 × Fin M × Fin 2 × InfinitePlace F => ℝ)) (intSub b e N)
    ((coord hF b).comp (e.comp (intSub b e N).subtype)) r R hr hrR
  rw [finrank_coord hF 2 M] at key
  have conv : ∀ t : ℝ, ∑' l : Λ, (Set.indicator (box b N t) (fun _ => (1 : ℝ≥0∞))) (e l) =
      ∑' l : intSub b e N, Set.indicator {l : intSub b e N |
        ‖((coord hF b).comp (e.comp (intSub b e N).subtype)) l‖ ≤ t} (fun _ => (1 : ℝ≥0∞)) l := by
    intro t
    have h := tsum_subtype ((intSub b e N : AddSubgroup Λ) : Set Λ)
      (fun l => Set.indicator {l : Λ | sizeTup b (projInf (e l)) ≤ t} (fun _ => (1 : ℝ≥0∞)) l)
    refine Eq.trans ?_ (Eq.trans h.symm ?_)
    · refine tsum_congr fun l => ?_
      have hb : e l ∈ box b N t ↔ l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ) ∧
          l ∈ {l : Λ | sizeTup b (projInf (e l)) ≤ t} := Iff.rfl
      by_cases hm : e l ∈ box b N t
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hb.1 hm).1, Set.indicator_of_mem (hb.1 hm).2]
      · rw [Set.indicator_of_notMem hm]
        by_cases h1 : l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem fun h => hm (hb.2 ⟨h1, h⟩)]
        · rw [Set.indicator_of_notMem h1]
    · refine tsum_congr fun l => ?_
      simp [Set.indicator, norm_coord]
  rw [conv R, conv r]
  exact key
end GlobalTheory.CompanionTheory.SW.Pack
