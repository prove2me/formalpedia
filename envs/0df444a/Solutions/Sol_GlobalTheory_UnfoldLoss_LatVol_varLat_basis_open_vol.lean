-- Prove2me | solution 1 for GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:36.218704+00:00
-- url     : https://prove2.me/submissions/9f011032-c23a-405a-b607-9f76e7d2fb00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemVarLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VariablesUniformizerPowerLatticeBasisOpenVolume
import Theorems.Thm_GlobalTheory_UnfoldLoss_LatVol_varLat_eq_pi
import Theorems.Thm_GlobalTheory_UnfoldLoss_LatVol_eventually_cball_subset
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_irreducible
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_measure_cball
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss
open GlobalTheory GlobalTheory.UnfoldLoss GlobalTheory.UnfoldLoss.LatVol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.UnfoldLoss.LatVol
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  intro k _ _ _ _ _ _ G ν hν ϖ hϖ
  classical
  refine ⟨fun s hs => ?_, fun n => ?_⟩
  · rw [nhds_pi, Filter.mem_pi'] at hs
    obtain ⟨I, t, ht, hts⟩ := hs
    have key : ∀ j, ∀ᶠ n : ℕ in Filter.atTop, (Set.univ.pi fun _ => cball (ϖ ^ n)) ⊆ t j := fun j => by
      have hj := ht j
      rw [nhds_pi, Filter.mem_pi'] at hj
      obtain ⟨J, u, hu, hut⟩ := hj
      filter_upwards [Filter.eventually_all.2 fun r => eventually_cball_subset hϖ (hu r)] with n hn e he
      exact hut fun r _ => hn r (he r trivial)
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 key).exists
    refine ⟨n, fun e he => hts fun j _ => hn j fun r _ => he j r⟩
  · haveI := hν.1
    haveI := secondCountable k
    have h1 : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      nabs_uniformiser hϖ.irreducible rfl
    have hv : varsVol G ν (varLat G ϖ n : Set (Vars G)) =
        ((distribHaarChar k ϖ ^ (n * varCount G) : NNReal) : ENNReal) := by
      rw [varLat_eq_pi, varsVol, Measure.pi_pi]
      simp only [Measure.pi_pi, measure_cball, hν.2, mul_one, Finset.prod_const, Finset.card_univ, map_pow,
        varCount, ← Nat.card_eq_fintype_card, ENNReal.coe_pow, ← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · rw [varLat_eq_pi]
      exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _
    · rw [hv]; exact ENNReal.coe_ne_top
    · rw [Measure.real, hv, ENNReal.coe_toReal, NNReal.coe_pow, h1]
end GlobalTheory.UnfoldLoss.LatVol
