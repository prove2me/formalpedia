-- Prove2me | solution 1 for GlobalTheory.LatPair.VolStep.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:33.164812+00:00
-- url     : https://prove2.me/submissions/4d15355c-3eec-4024-b312-7db0d7c2244a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlagVolumeOpenFiniteNonzero
import Theorems.Thm_GlobalTheory_LatPair_VolStep_isCompact_lat
import Theorems.Thm_GlobalTheory_LatPair_VolStep_continuous_flagIn
import Theorems.Thm_GlobalTheory_LatPair_VolStep_region_eq
import Theorems.Thm_GlobalTheory_LatPair_isClopen_lattice
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
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.VolStep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LatPair.VolStep
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (q : Unif k) (ν : Measure k) [ν.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k] (i : ℕ), i ≤ c → IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} ∧ volStep ν q L i ≠ 0 ∧ volStep ν q L i ≠ ⊤ := by
  intro k _ _ _ _ _ _ n _ _ c q ν _ L _ i hi
  haveI := secondCountable k
  haveI := t2Space k
  have ho : IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} := by
    rw [region_eq]
    exact (isClopen_lattice L).2.preimage ((continuous_flagIn c i).const_smul q.inv)
  refine ⟨ho, ?_, ?_⟩
  · refine ho.measure_ne_zero _ ⟨0, ?_⟩
    rw [region_eq]
    have : flagIn (k := k) (n := n) c i 0 = 0 := by
      funext j
      rcases j with r | l <;> simp [flagIn]
    simp [this]
  · have hK := (isCompact_lat L).image
      (f := fun (z : n ⊕ Fin c → k) (j : n ⊕ Fin i) => ((q.1 : 𝒪[k]) : k) * z (Sum.map id (Fin.castLE hi) j)) (by fun_prop)
    refine ne_top_of_le_ne_top (hK.measure_lt_top (μ := Measure.pi fun _ : n ⊕ Fin i => ν)).ne (measure_mono ?_)
    rw [region_eq]
    intro y hy
    refine ⟨_, hy, ?_⟩
    funext j
    rcases j with r | l
    · simp [flagIn, Unif.inv, q.ne_zero]
    · simp [flagIn, Unif.inv, q.ne_zero]
end GlobalTheory.LatPair.VolStep
