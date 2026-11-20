-- Prove2me | solution 1 for HighMagSampling.SK.downUp_reversible
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:05:32.230114+00:00
-- url     : https://prove2.me/submissions/3b3e4638-b2b1-429a-8ffa-5e39744d396c

import Mathlib
import Definitions.Def_HighMagSampling_SK_MarkovChain
import Definitions.Def_HighMagSampling_SK_DownUp

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open HighMagSampling.SK

variable {d k : ℕ}

lemma kernel_apply (π : Measure (Slice d k)) (S : Slice d k) (t : Set (Slice d k)) :
    downUp π S t = ∑ S' : Slice d k, downUpProb π S S' * t.indicator 1 S' := by
  classical
  show (∑ S' : Slice d k, downUpProb π S S' • Measure.dirac S') t = _
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun S' _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet t)]

lemma detailed_balance (π : Measure (Slice d k)) (S S' : Slice d k) :
    π {S} * downUpProb π S S' = π {S'} * downUpProb π S' S := by
  classical
  unfold downUpProb
  rw [Finset.mul_sum, Finset.mul_sum]
  have hset : S.1.powerset.filter (fun T => T.card + 1 = k ∧ T ⊆ S'.1)
      = S'.1.powerset.filter (fun T => T.card + 1 = k ∧ T ⊆ S.1) := by
    ext T; simp only [Finset.mem_filter, Finset.mem_powerset]; tauto
  rw [hset]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv]; ring

lemma lintegral_discrete (π : Measure (Slice d k)) (s : Set (Slice d k)) (f : Slice d k → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂π = ∑ x : Slice d k, s.indicator 1 x * (f x * π {x}) := by
  classical
  rw [lintegral_fintype]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Measure.restrict_apply (DiscreteMeasurableSpace.forall_measurableSet _)]
  by_cases hx : x ∈ s
  · simp [hx, Set.singleton_inter_of_mem hx]
  · simp [hx, Set.singleton_inter_of_notMem hx]

lemma row_sum (hk : 1 ≤ k) (π : Measure (Slice d k)) [IsFiniteMeasure π] (S : Slice d k)
    (hS : π {S} ≠ 0) : ∑ S' : Slice d k, downUpProb π S S' = 1 := by
  classical
  set F := S.1.powerset.filter (fun T => T.card + 1 = k) with hF
  have hsplit : ∀ S' : Slice d k, downUpProb π S S'
      = ∑ T ∈ F, if T ⊆ S'.1 then (k : ℝ≥0∞)⁻¹ * (π {S'} / upMass π T) else 0 := by
    intro S'
    unfold downUpProb
    rw [← Finset.sum_filter, hF, Finset.filter_filter]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  have hinner : ∀ T ∈ F, (∑ S' : Slice d k,
      if T ⊆ S'.1 then (k : ℝ≥0∞)⁻¹ * (π {S'} / upMass π T) else 0) = (k : ℝ≥0∞)⁻¹ := by
    intro T hT
    have hTS : T ⊆ S.1 := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hu0 : upMass π T ≠ 0 := by
      intro h0
      have : (if T ⊆ S.1 then π {S} else 0) ≤ upMass π T :=
        Finset.single_le_sum (f := fun S'' : Slice d k => if T ⊆ S''.1 then π {S''} else 0)
          (fun _ _ => bot_le) (Finset.mem_univ S)
      rw [if_pos hTS, h0] at this
      exact hS (le_antisymm this bot_le)
    have hut : upMass π T ≠ ⊤ := by
      unfold upMass
      exact ENNReal.sum_ne_top.mpr (fun S'' _ => by split_ifs <;> simp [measure_ne_top])
    have e : ∀ S' : Slice d k, (if T ⊆ S'.1 then (k : ℝ≥0∞)⁻¹ * (π {S'} / upMass π T) else 0)
        = (k : ℝ≥0∞)⁻¹ * (upMass π T)⁻¹ * (if T ⊆ S'.1 then π {S'} else 0) := by
      intro S'; split_ifs <;> simp [div_eq_mul_inv]; ring
    simp_rw [e]
    rw [← Finset.mul_sum]
    change (k : ℝ≥0∞)⁻¹ * (upMass π T)⁻¹ * upMass π T = _
    rw [mul_assoc, ENNReal.inv_mul_cancel hu0 hut, mul_one]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  have hcard : F.card = k := by
    have : F = S.1.powersetCard (k - 1) := by
      ext T; simp only [hF, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
    rw [this, Finset.card_powersetCard, S.2, ← Nat.choose_symm (Nat.sub_le k 1), Nat.sub_sub_self hk,
      Nat.choose_one_right]
  rw [hcard]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : k ≠ 0)) (ENNReal.natCast_ne_top k)

theorem solution (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (π : Measure (Slice d k))
    [IsFiniteMeasure π] : IsReversibleWith (downUp π) π := by
  classical
  have hrev : Kernel.IsReversible (downUp π) π := by
      intro A B hA hB
      rw [lintegral_discrete, lintegral_discrete]
      have e : ∀ (x : Slice d k) (t : Set (Slice d k)), (downUp π) x t
          = ∑ S' : Slice d k, downUpProb π x S' * t.indicator 1 S' := fun x t => kernel_apply π x t
      simp only [e, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      have := detailed_balance π y x
      calc A.indicator 1 y * (downUpProb π y x * B.indicator 1 x * π {y})
          = A.indicator 1 y * B.indicator 1 x * (π {y} * downUpProb π y x) := by ring
        _ = A.indicator 1 y * B.indicator 1 x * (π {x} * downUpProb π x y) := by rw [this]
        _ = B.indicator 1 x * (downUpProb π x y * A.indicator 1 y * π {x}) := by ring

  refine ⟨?_, hrev⟩
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  have h1 := hrev MeasurableSet.univ hs
  rw [setLIntegral_univ] at h1
  rw [h1, lintegral_discrete]
  have hπs : π s = ∫⁻ x in s, 1 ∂π := by rw [setLIntegral_one]
  rw [hπs, lintegral_discrete]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h0 : π {x} = 0
  · simp [h0]
  · rw [kernel_apply π x Set.univ]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    rw [row_sum hk π x h0]
