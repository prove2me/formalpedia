-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.red_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:58.62626+00:00
-- url     : https://prove2.me/submissions/c2a565f1-1f0c-463d-8edd-c5df95b2673c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_measurePreserving_adjoin
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k), Integrable (fun y : ↥(insert e I : Finset (R × Q)) → k => Φ (fillAt β E (insert e I) x y) * (ψ (-w (fillAt β E (insert e I) x y)) : ℂ)) (Measure.pi fun _ => ν) → red ψ ν w β E (insert e I) Φ x = ∫ s, red ψ ν w β E I Φ (x + Matrix.single e.1 e.2 (s - x e.1 e.2)) ∂ν := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ w β E I e hE hI Φ x hint
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hmp := measurePreserving_adjoin ν I e hI
  have hfill : ∀ p : k × (I → k), fillAt β E (insert e I) x
      (fun i => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) =
      fillAt β E I (x + Matrix.single e.1 e.2 (p.1 - x e.1 e.2)) p.2 := by
    intro p
    obtain ⟨r₀, q₀⟩ := e
    ext r q
    by_cases h1 : (r, q) ∈ I
    · simp [fillAt, h1]
    · by_cases h2 : (r, q) = (r₀, q₀)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        simp [fillAt, h1, hE]
      · have h3 : (r, q) ∉ insert (r₀, q₀) I := by
          rw [Finset.mem_insert, not_or]; exact ⟨h2, h1⟩
        have h4 : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact h2 rfl
        simp only [fillAt, Matrix.of_apply, dif_neg h1, dif_neg h3, Matrix.add_apply, Matrix.single_apply,
          if_neg h4, add_zero]
  have h1 := hmp.integrable_comp_of_integrable hint
  unfold red
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hint.1)]
  refine (integral_prod _ h1).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact congrArg (fun t => Φ t * (ψ (-w t) : ℂ)) (hfill (s, y))
end GlobalTheory.PartRed.IntEntry
