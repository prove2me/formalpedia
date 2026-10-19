-- Prove2me | solution 1 for OAI.KervaireSpectral.sum_fract_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:17:25.296227+00:00
-- url     : https://prove2.me/submissions/e8532d16-d66c-4e70-94c2-131cd3a1c096

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
theorem solution (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
    (∑ j : Fin d, Int.fract (x + (j.val : ℝ) / d)) =
      ((d : ℝ)-1)/2 + Int.fract ((d : ℝ)*x) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set k : ℕ := ⌊(d : ℝ) * x⌋₊ with hk
  have hk1 : (k : ℝ) ≤ d * x := Nat.floor_le (by positivity)
  have hk2 : (d : ℝ) * x < k + 1 := Nat.lt_floor_add_one _
  have hkd : k < d := by
    have : (d : ℝ) * x < d := by nlinarith
    exact_mod_cast (lt_of_le_of_lt hk1 this)
  have hfr : Int.fract ((d : ℝ) * x) = d * x - k := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor (by positivity)]; push_cast; ring
  have hterm : ∀ j : ℕ, j < d → Int.fract (x + (j : ℝ) / d) =
      x + (j : ℝ) / d - (if d ≤ j + k then 1 else 0) := by
    intro j hj
    rw [Int.fract_eq_iff]
    have hjd : (j : ℝ) < d := by exact_mod_cast hj
    split_ifs with h
    · have h' : (d : ℝ) ≤ j + k := by exact_mod_cast h
      refine ⟨?_, ?_, ⟨1, by push_cast; ring⟩⟩
      · have : 1 ≤ x + j / d := by
          rw [← sub_nonneg]
          have : x + j / d - 1 = (d * x + j - d) / d := by field_simp
          rw [this]; apply div_nonneg _ hdpos.le; linarith
        linarith
      · have : x + j / d < 2 := by
          have : (j : ℝ) / d < 1 := (div_lt_one hdpos).2 hjd
          linarith
        linarith
    · have h' : (j : ℝ) + k + 1 ≤ d := by
        have : j + k + 1 ≤ d := by omega
        exact_mod_cast this
      refine ⟨?_, ?_, ⟨0, by push_cast; ring⟩⟩
      · have : 0 ≤ (j : ℝ) / d := by positivity
        linarith
      · rw [sub_zero]
        have : x + j / d = (d * x + j) / d := by field_simp
        rw [this, div_lt_one hdpos]; linarith
  rw [Fin.sum_univ_eq_sum_range (fun j => Int.fract (x + (j : ℝ) / d)) d]
  rw [Finset.sum_congr rfl (fun j hj => hterm j (Finset.mem_range.1 hj))]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range]
  have hsum : (∑ j ∈ Finset.range d, (j : ℝ)) = d * (d - 1) / 2 := by
    have := Finset.sum_range_id_mul_two d
    have h2 : ((∑ j ∈ Finset.range d, j : ℕ) : ℝ) * 2 = (d * (d - 1) : ℕ) := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d)] at h2
    push_cast at h2 ⊢; linarith
  have hcnt : (∑ j ∈ Finset.range d, (if d ≤ j + k then (1 : ℝ) else 0)) = k := by
    rw [Finset.sum_boole]
    have : (Finset.range d).filter (fun j => d ≤ j + k) = Finset.Ico (d - k) d := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Nat.card_Ico]; push_cast [Nat.cast_sub (by omega : d - k ≤ d)]
    rw [Nat.cast_sub (by omega : k ≤ d)]; ring
  rw [hsum, hcnt, hfr, nsmul_eq_mul]
  field_simp
  ring
