-- Prove2me | solution 1 for LNTopology.RandomHerm.eq_11
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:00:57.695103+00:00
-- url     : https://prove2.me/submissions/87a4fe66-54a2-4f0a-a3db-56b5ffb82326

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNRHEq11CE
open LNTopology.Local LNTopology.Hermetic LNTopology.RandomHerm

noncomputable def cc : ℝ → ℝ := fun x => Real.sqrt |x|
noncomputable def gg : ℝ → ℝ := fun k => 9 / 10 * Real.sqrt k

lemma cc_cost : IsChannelCost cc where
  nonneg x := Real.sqrt_nonneg _
  mono x y hy hxy := by
    simp only [cc]
    rw [abs_of_nonneg hy, abs_of_nonneg (hy.trans hxy.le)]
    exact Real.sqrt_lt_sqrt hy hxy
  symm x := by simp [cc]
  zero := by simp [cc]
  subadd x y hx hy := by
    simp only [cc]
    rw [abs_of_pos (add_pos hx hy), abs_of_pos hx, abs_of_pos hy]
    rw [Real.sqrt_lt' (add_pos (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hy))]
    have h1 := Real.sq_sqrt hx.le
    have h2 := Real.sq_sqrt hy.le
    have h3 := mul_pos (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hy)
    nlinarith

lemma gg_sa : SAPlus cc gg := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [gg]
    have := Real.sqrt_lt_sqrt (Set.mem_Ici.1 hx) hxy
    linarith
  · intro k hk; simp only [gg]; positivity
  · intro k x hk hx
    simp only [cc, gg]
    have hk0 : 0 < k := by linarith
    rw [abs_mul, abs_of_pos hk0, Real.sqrt_mul hk0.le]
    set r := Real.sqrt k with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 hk0
    have hrk : r ^ 2 = k := Real.sq_sqrt hk0.le
    set u := Real.sqrt |x|
    have hu : 0 < u := Real.sqrt_pos.2 (abs_pos.2 hx.ne')
    rw [← hrk]
    rw [show r ^ 2 / (9 / 10 * r) * u = r * u * (10 / 9) by field_simp]
    nlinarith [mul_pos hrpos hu]

noncomputable def Λ0 : Bool → Fin 10 → Fin 10 → ℝ := fun ω i j =>
  if i = j then 0 else if (ω = false ∧ j = 1) then (1 / 4 : ℝ) else 3 / 2

lemma Λ0_ne (ω : Bool) (i j : Fin 10) : Λ0 ω i j ≠ 0 ↔ (⊤ : SimpleGraph (Fin 10)).Adj i j := by
  simp only [Λ0, SimpleGraph.top_adj]
  by_cases h : i = j
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, iff_true]
    split_ifs <;> norm_num

lemma nbrs0 (ω : Bool) : chanNbrs (Λ0 ω) Finset.univ 0 = Finset.univ.erase 0 := by
  ext j
  simp only [chanNbrs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    and_true, Λ0_ne, SimpleGraph.top_adj]
  exact ne_comm

lemma ne0 (ω : Bool) : (chanNbrs (Λ0 ω) Finset.univ 0).Nonempty := by
  rw [nbrs0]; exact ⟨2, by simp⟩

lemma vals (ω : Bool) (j : Fin 10) (hj : j ∈ chanNbrs (Λ0 ω) Finset.univ 0) :
    1 / 4 ≤ |Λ0 ω 0 j| ∧ |Λ0 ω 0 j| ≤ 3 / 2 := by
  rw [nbrs0] at hj
  have hj0 : (0 : Fin 10) ≠ j := (Finset.ne_of_mem_erase hj).symm
  simp only [Λ0, hj0, if_false]
  split_ifs <;> norm_num

lemma max0 (ω : Bool) : maxChanOn (Λ0 ω) Finset.univ 0 = 3 / 2 := by
  simp only [maxChanOn, dif_pos (ne0 ω)]
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun j hj => (vals ω j hj).2)
  · have h2 : (2 : Fin 10) ∈ chanNbrs (Λ0 ω) Finset.univ 0 := by rw [nbrs0]; simp
    refine le_trans ?_ (Finset.le_sup' (fun j => |Λ0 ω 0 j|) h2)
    simp [Λ0]
    norm_num [abs_of_pos]

lemma min0 : minChanOn (Λ0 false) Finset.univ 0 = 1 / 4 := by
  simp only [minChanOn, dif_pos (ne0 false)]
  apply le_antisymm
  · have h1 : (1 : Fin 10) ∈ chanNbrs (Λ0 false) Finset.univ 0 := by rw [nbrs0]; simp
    refine le_trans (Finset.inf'_le (fun j => |Λ0 false 0 j|) h1) ?_
    simp [Λ0]
  · exact Finset.le_inf' _ _ (fun j hj => (vals false j hj).1)

lemma sqrt_32_gt : 1 < Real.sqrt (3 / 2) := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma sqrt_32_lt : Real.sqrt (3 / 2) < 27 / 20 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma gg9 : gg 9 = 27 / 10 := by
  simp only [gg]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

lemma deg0 (i : Fin 10) : (⊤ : SimpleGraph (Fin 10)).degree i = 9 := by
  simp

lemma bot_one (s : Set Bool) (hs : s.Nonempty) : (@Measure.dirac Bool ⊥ true) s = 1 := by
  letI : MeasurableSpace Bool := ⊥
  have h1 := measurableSet_toMeasurable (Measure.dirac true) s
  rw [MeasurableSpace.measurableSet_bot_iff] at h1
  rcases h1 with h | h
  · exfalso
    obtain ⟨x, hx⟩ := hs
    have := subset_toMeasurable (Measure.dirac true) s hx
    rw [h] at this; exact this
  · rw [← measure_toMeasurable, h, measure_univ]

end LNRHEq11CE

open LNTopology.RandomHerm LNRHEq11CE

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (E : SimpleGraph V) [DecidableRel E.Adj]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → V → V → ℝ) (c g : ℝ → ℝ) (hc : LNTopology.Local.IsChannelCost c) (hg : LNTopology.Hermetic.SAPlus c g)
    (hE : ∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j) (ε : ℝ) (hε : 0 < ε)
    (hii : ∀ i j, E.Adj i j → P {ω | ε < c (Λ ω i j)} = 1) (i : V) (hi : 0 < E.degree i),
    P {ω | g (E.degree i) ≤
        2 * c (maxChanOn (Λ ω) Finset.univ i) / c (minChanOn (Λ ω) Finset.univ i)}
      ≤ P {ω | ε / 2 * g (E.degree i) ≤ c (maxChanOn (Λ ω) Finset.univ i)}) := by
  intro h
  letI mΩ : MeasurableSpace Bool := ⊥
  have hP : IsProbabilityMeasure (@Measure.dirac Bool ⊥ true) := inferInstance
  have hii : ∀ i j, (⊤ : SimpleGraph (Fin 10)).Adj i j →
      (@Measure.dirac Bool ⊥ true) {ω | 1 < cc (Λ0 ω i j)} = 1 := by
    intro i j hij
    apply bot_one
    refine ⟨true, ?_⟩
    have hij' : i ≠ j := hij
    simp only [Set.mem_setOf_eq, cc, Λ0, hij', if_false]
    simp only [Bool.true_eq_false, false_and, if_false]
    rw [abs_of_pos (by norm_num)]
    exact sqrt_32_gt
  have hdeg : 0 < (⊤ : SimpleGraph (Fin 10)).degree 0 := by rw [deg0]; norm_num
  have key := @h (Fin 10) _ _ ⊤ _ Bool mΩ (@Measure.dirac Bool ⊥ true) hP Λ0 cc gg cc_cost gg_sa
    Λ0_ne 1 one_pos hii 0 hdeg
  rw [deg0] at key
  push_cast at key
  rw [gg9] at key
  have hA : (@Measure.dirac Bool ⊥ true) {ω | (27 / 10 : ℝ) ≤
      2 * cc (maxChanOn (Λ0 ω) Finset.univ 0) / cc (minChanOn (Λ0 ω) Finset.univ 0)} = 1 := by
    apply bot_one
    refine ⟨false, ?_⟩
    simp only [Set.mem_setOf_eq, max0, min0, cc]
    rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num : (0:ℝ) < 1 / 4)]
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have := sqrt_32_gt
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hB : {ω : Bool | (1 : ℝ) / 2 * (27 / 10) ≤ cc (maxChanOn (Λ0 ω) Finset.univ 0)} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, max0, cc, Set.mem_empty_iff_false, iff_false, not_le]
    rw [abs_of_pos (by norm_num)]
    have := sqrt_32_lt
    linarith
  rw [hA, hB, measure_empty] at key
  exact absurd key (by norm_num)
