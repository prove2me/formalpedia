-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StoppedDriftSumIntegralV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:38:32.140622+00:00
-- url     : https://prove2.me/submissions/85a9b58b-788c-45da-bcf9-542684635cb1

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (T t : NNReal) (n : ℕ) (H : NNReal → ℝ) :
    let u : ℕ → NNReal := fun i => T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
    (∫ s in Ioc (0 : ℝ) (t : ℝ),
      ∑ i ∈ Finset.range (n+1),
        (Ioc (u i : ℝ) (u (i+1) : ℝ)).indicator (fun _ => H (u i)) s) =
      ∑ i ∈ Finset.range (n+1),
        H (u i) * ((min t (u (i+1)) : NNReal).toReal - (min t (u i) : NNReal).toReal) := by
  intro u
  let D := Ioc (0 : ℝ) (t : ℝ)
  let E := fun i : ℕ => Ioc (u i : ℝ) (u (i+1) : ℝ)
  have hmono : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  change (∫ s in D, ∑ i ∈ Finset.range (n+1),
    (E i).indicator (fun _ => H (u i)) s) = _
  rw [integral_finsetSum _ (fun i hi =>
    (integrable_const (H (u i))).indicator measurableSet_Ioc)]
  apply Finset.sum_congr rfl
  intro i hi
  have hEq : E i ∩ D = Ioc ((min t (u i) : NNReal) : ℝ) ((min t (u (i+1)) : NNReal) : ℝ) := by
    ext s
    simp only [E,D,Set.mem_inter_iff,Set.mem_Ioc,NNReal.coe_min,min_lt_iff,le_min_iff]
    constructor
    · rintro ⟨⟨ha,hb⟩,hc,hd⟩
      exact ⟨Or.inr ha,hd,hb⟩
    · rintro ⟨ha,hb,hc⟩
      have ha' : (u i : ℝ) < s := ha.resolve_left (not_lt_of_ge hb)
      exact ⟨⟨ha',hc⟩,(u i).coe_nonneg.trans_lt ha',hb⟩
  rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    hEq,setIntegral_const]
  have hle : (min t (u i) : NNReal) ≤ min t (u (i+1)) :=
    min_le_min le_rfl (hmono (Nat.le_succ i))
  simp only [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal
    (sub_nonneg.mpr (show ((min t (u i) : NNReal) : ℝ) ≤ _ from by exact_mod_cast hle)),smul_eq_mul]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (show ((min t (u i) : NNReal) : ℝ) ≤ ((min t (u (i+1)) : NNReal) : ℝ) by exact_mod_cast hle))]
  exact mul_comm _ _