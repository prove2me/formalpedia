-- Prove2me | solution 1 for HighUncertHT.Game.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:13:44.038033+00:00
-- url     : https://prove2.me/submissions/150cefb7-0f19-4998-836a-1a86fc20da15

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Control

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Aux_HighUncertHT_Game_lemma_2

open HighUncertHT.Game ProbabilityTheory

lemma ae_nonneg {L : ℕ} (S : Setting L) (n : ℕ) (f : AdversaryControl S n) (i : ℕ) :
    ∀ᵐ ω ∂f.law, ∀ ℓ, 0 ≤ ω (i + 1) ℓ := by
  set E : Set (Fin L → ℝ) := ⋃ ℓ, (fun y : Fin L → ℝ => y ℓ) ⁻¹' Set.Iio 0 with hE
  have hEm : MeasurableSet E :=
    MeasurableSet.iUnion (fun ℓ => measurableSet_Iio.preimage (measurable_pi_apply ℓ))
  have hκ : ∀ x, f.kernel i x E = 0 := by
    intro x
    rw [f.kernel_eq]
    apply measure_iUnion_null
    intro ℓ
    exact Measure.pi_eval_preimage_null _ (S.cls_support n ℓ _ (f.policy_mem i x ℓ))
  set g : (ℕ → Fin L → ℝ) → ((i : Finset.Iic i) → (Fin L → ℝ)) × (Fin L → ℝ) :=
    fun x => (Preorder.frestrictLe i x, x (i + 1)) with hg
  have hgm : Measurable g := by
    simp only [hg]
    fun_prop
  rw [ae_iff]
  have hset : {ω : ℕ → Fin L → ℝ | ¬ ∀ ℓ, 0 ≤ ω (i + 1) ℓ} = g ⁻¹' (Set.univ ×ˢ E) := by
    ext ω
    simp [hg, hE, not_le]
  rw [hset, ← Measure.map_apply hgm (MeasurableSet.univ.prod hEm)]
  unfold AdversaryControl.law
  rw [hg, ← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.compProd_apply (MeasurableSet.univ.prod hEm)]
  have hpre : ∀ a : ((j : Finset.Iic i) → (Fin L → ℝ)), Prod.mk a ⁻¹' (Set.univ ×ˢ E) = E :=
    fun a => Set.mk_preimage_prod_right (Set.mem_univ a)
  simp only [hpre, hκ, lintegral_zero]

end Aux_HighUncertHT_Game_lemma_2

open Aux_HighUncertHT_Game_lemma_2 in
open HighUncertHT.Game in
theorem solution {L : ℕ} (S : Setting L) (n : ℕ) (hn : 1 ≤ n) (f : AdversaryControl S n)
    (β β' : ControlPath L → EffortPath L)
    (hβ : β ∈ admissibleStrategies S n) (hβ' : β' ∈ admissibleStrategies S n) :
    ∀ᵐ ω ∂f.law, ∀ t : ℝ, 0 ≤ t →
      ∑ ℓ, workload n (f.ctrlPath ω) (β (f.ctrlPath ω)) t ℓ =
        ∑ ℓ, workload n (f.ctrlPath ω) (β' (f.ctrlPath ω)) t ℓ := by
  have hall : ∀ᵐ ω ∂f.law, ∀ i : ℕ, ∀ ℓ, 0 ≤ ω (i + 1) ℓ := ae_all_iff.2 (ae_nonneg S n f)
  filter_upwards [hall] with ω hω t ht
  have hmem : f.ctrlPath ω ∈ pathSpace S n := fun i =>
    ⟨fun ℓ => f.policy_mem i _ ℓ, fun ℓ => hω i ℓ⟩
  obtain ⟨_, _, _, h4, _⟩ := hβ
  obtain ⟨_, _, _, h4', _⟩ := hβ'
  simp only [workload, Finset.sum_sub_distrib, ← Finset.mul_sum, h4 _ hmem t ht, h4' _ hmem t ht]
