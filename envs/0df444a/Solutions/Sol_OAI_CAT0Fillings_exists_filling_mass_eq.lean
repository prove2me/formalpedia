-- Prove2me | solution 1 for OAI.CAT0Fillings.exists_filling_mass_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:07:23.524205+00:00
-- url     : https://prove2.me/submissions/cf7a44d9-8e49-4d86-934c-c0c7da9a59ab

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_Slicing_exists_integral_weak_subsequence

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_Attainment
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem mass_le_of_mass_tendsto {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {Ts : ℕ → Functional X k}
    {T : Functional X k} (hTs : ∀ j, IsMetricCurrent (Ts j)) {m : ℝ}
    (hm : Tendsto (fun j => mass (Ts j)) atTop (𝓝 m))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    mass T ≤ m := by
  have hm0 : 0 ≤ m := ge_of_tendsto hm (Eventually.of_forall fun j => mass_nonneg (Ts j))
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.eventually (gt_mem_nhds (lt_add_of_pos_right m hε)))
  exact mass_le_of_bounded_weak_limit (⟨m+ε,by positivity⟩ : ℝ≥0)
    (fun j => hTs (j+N)) (fun j => (hN (j+N) (Nat.le_add_left N j)).le)
    (fun b π _ => (hlim b π).comp (tendsto_add_atTop_nat N))

lemma fillingVolume_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ}
    {T : Functional X (k+1)} {S : Functional X (k+2)}
    (hS : IsIntegral (k+2) S) (hb : boundarySucc S = T) : fillingVolume T ≤ mass S := by
  apply csInf_le
  · exact ⟨0,by rintro r ⟨U,_,_,rfl⟩; exact mass_nonneg U⟩
  · exact ⟨S,hS,hb,rfl⟩

theorem exists_filling_mass_eq_oai (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hex : ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S = fillingVolume T := by
  let A : Set ℝ := {r | ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧
    boundarySucc S = T ∧ r = mass S}
  have hA : A.Nonempty := by
    obtain ⟨S,hS,hb⟩ := hex
    exact ⟨mass S,S,hS,hb,rfl⟩
  have hAl : BddBelow A := ⟨0,by rintro r ⟨S,_,_,rfl⟩; exact mass_nonneg S⟩
  obtain ⟨u,hu,hlim,huA⟩ := exists_seq_tendsto_sInf hA hAl
  choose Ts hTs hb hm using huA
  have hu0 : 0 ≤ u 0 := by rw [hm]; exact mass_nonneg _
  obtain ⟨ψ,hψ,S,hS,_,_,hweak⟩ := exists_integral_weak_subsequence hTs
    (⟨u 0,hu0⟩ : ℝ≥0) (⟨mass T,mass_nonneg T⟩ : ℝ≥0)
    (fun j => by rw [←hm]; exact hu (Nat.zero_le j)) (fun j => by simp only [hb]; rfl) hX
  have hboundary : boundarySucc S = T := by
    funext b π
    apply tendsto_nhds_unique (boundarySucc_weak_limit hweak b π)
    simpa only [hb] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => T b π) atTop (𝓝 (T b π)))
  refine ⟨S,hS,hboundary,le_antisymm ?_ (fillingVolume_le hS hboundary)⟩
  apply mass_le_of_mass_tendsto (fun j => (hTs (ψ j)).1) _ hweak
  simpa only [Function.comp_def,hm,fillingVolume,A] using hlim.comp hψ.tendsto_atTop

end CAT0Fillings
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.exists_filling_mass_eq_oai.{u_1} := @OAI.CAT0Fillings.exists_filling_mass_eq_oai.{u_1}
