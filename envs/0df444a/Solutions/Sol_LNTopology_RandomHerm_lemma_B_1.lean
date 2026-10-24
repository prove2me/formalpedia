-- Prove2me | solution 1 for LNTopology.RandomHerm.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:50:25.982408+00:00
-- url     : https://prove2.me/submissions/16fe6848-a89e-4f48-8421-a478b61e4315

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNRHHelp
open LNTopology.Local LNTopology.Hermetic LNTopology.RandomHerm

lemma c_le {c : ℝ → ℝ} (hc : IsChannelCost c) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    c y ≤ c x := by
  rcases hxy.lt_or_eq with h | h
  · exact (hc.mono x y hy h).le
  · rw [h]

lemma c_abs {c : ℝ → ℝ} (hc : IsChannelCost c) (x : ℝ) : c |x| = c x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact hc.symm x

lemma c_pos {c : ℝ → ℝ} (hc : IsChannelCost c) {x : ℝ} (hx : 0 < x) : 0 < c x := by
  have := hc.mono x 0 le_rfl hx
  rwa [hc.zero] at this

lemma g_one_lt {c g : ℝ → ℝ} (hc : IsChannelCost c) (hg : SAPlus c g) : g 1 < 2 := by
  have h := hg.2.2 2 1 (by norm_num) one_pos
  norm_num at h
  have h1 : 0 < c 1 := c_pos hc one_pos
  have h2 : c 1 ≤ c 2 := c_le hc (by norm_num) (by norm_num)
  have hg2 : 0 < g 2 := by
    by_contra hneg
    push Not at hneg
    have : 2 / g 2 * c 1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonneg_of_nonpos (by norm_num) hneg) h1.le
    linarith [hc.nonneg 2]
  have hlt : g 2 < 2 := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hg2] at h
    nlinarith
  have := hg.1 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 (by norm_num : (0:ℝ) ≤ 2))
    (by norm_num : (1:ℝ) < 2)
  linarith

lemma cost_hermetize {V : Type*} [Fintype V] [DecidableEq V] {c : ℝ → ℝ} (hc : IsChannelCost c)
    (Λ : V → V → ℝ) (U : Finset V) :
    cost c (hermetize Λ U) = cost c Λ - (1/2) * ∑ i ∈ U, ∑ j ∈ U, c (Λ i j)
      + ∑ i ∈ U, c (∑ j ∈ U, Λ i j) := by
  have key1 : ∀ i j, c (if i ∈ U ∧ j ∈ U then 0 else Λ i j)
      = c (Λ i j) - if i ∈ U ∧ j ∈ U then c (Λ i j) else 0 := by
    intro i j; split_ifs <;> simp [hc.zero]
  have key2 : ∀ i, c (if i ∈ U then ∑ j ∈ U, Λ i j else 0)
      = if i ∈ U then c (∑ j ∈ U, Λ i j) else 0 := by
    intro i; split_ifs <;> simp [hc.zero]
  have key3 : ∀ j, c (if j ∈ U then -∑ i ∈ U, Λ j i else 0)
      = if j ∈ U then c (∑ i ∈ U, Λ j i) else 0 := by
    intro j; split_ifs <;> simp [hc.zero, hc.symm]
  have key4 : ∑ i, ∑ j, (if i ∈ U ∧ j ∈ U then c (Λ i j) else 0)
      = ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
    calc ∑ i, ∑ j, (if i ∈ U ∧ j ∈ U then c (Λ i j) else 0)
        = ∑ i, (if i ∈ U then ∑ j ∈ U, c (Λ i j) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          split_ifs with hi
          · simp [hi, Finset.sum_ite_mem]
          · simp [hi]
      _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
  unfold cost
  simp only [Fintype.sum_option, hermetize, key1, key2, key3, hc.zero, Finset.sum_sub_distrib,
    key4, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib]
  ring

lemma node_ineq {V : Type*} [DecidableEq V] {c g : ℝ → ℝ} (hc : IsChannelCost c)
    (hg : SAPlus c g) (Λ : V → V → ℝ) (U : Finset V) (i : V) (hdeg : 1 ≤ degOn Λ U i)
    (hcond : 2 * c (maxChanOn Λ U i) / c (minChanOn Λ U i) < g (degOn Λ U i)) :
    2 * c (∑ j ∈ U, Λ i j) < ∑ j ∈ U, c (Λ i j) := by
  set N := chanNbrs Λ U i with hNdef
  have hN : N.Nonempty := Finset.card_pos.1 (by simpa [degOn] using hdeg)
  have hmax : maxChanOn Λ U i = N.sup' hN (fun j => |Λ i j|) := by
    simp only [maxChanOn, ← hNdef, dif_pos hN]
  have hmin : minChanOn Λ U i = N.inf' hN (fun j => |Λ i j|) := by
    simp only [minChanOn, ← hNdef, dif_pos hN]
  have hd : (degOn Λ U i) = N.card := rfl
  rw [hmax, hmin, hd] at hcond
  rw [hd] at hdeg
  set S := N.sup' hN (fun j => |Λ i j|)
  set s := N.inf' hN (fun j => |Λ i j|)
  have memN : ∀ j ∈ N, Λ i j ≠ 0 := by
    intro j hj; simp [hNdef, chanNbrs] at hj; exact hj.2
  have hsum1 : ∑ j ∈ U, Λ i j = ∑ j ∈ N, Λ i j := (Finset.sum_filter_ne_zero _).symm
  have hsum2 : ∑ j ∈ U, c (Λ i j) = ∑ j ∈ N, c (Λ i j) := by
    rw [hNdef, chanNbrs]
    refine (Finset.sum_filter_of_ne (fun j _ hcj => ?_)).symm
    intro h0; apply hcj; rw [h0, hc.zero]
  obtain ⟨j0, hj0, hs⟩ := Finset.exists_mem_eq_inf' hN (fun j => |Λ i j|)
  have spos : 0 < s := by change 0 < N.inf' hN (fun j => |Λ i j|); rw [hs]; exact abs_pos.2 (memN j0 hj0)
  have hsS : s ≤ S := (Finset.inf'_le _ hj0).trans (Finset.le_sup' (fun j => |Λ i j|) hj0)
  have Spos : 0 < S := spos.trans_le hsS
  have cs_pos : 0 < c s := c_pos hc spos
  have hcsS : c s ≤ c S := c_le hc spos.le hsS
  have hlow : (N.card : ℝ) * c s ≤ ∑ j ∈ N, c (Λ i j) := by
    have := Finset.card_nsmul_le_sum N (fun j => c (Λ i j)) (c s) (fun j hj => by
      rw [← c_abs hc (Λ i j)]; exact c_le hc spos.le (Finset.inf'_le _ hj))
    simpa [nsmul_eq_mul] using this
  have hup : |∑ j ∈ N, Λ i j| ≤ (N.card : ℝ) * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul N (fun j => |Λ i j|) S (fun j hj => Finset.le_sup' (fun j => |Λ i j|) hj)
    simpa [nsmul_eq_mul] using this
  have hcup : c (∑ j ∈ N, Λ i j) ≤ c ((N.card : ℝ) * S) := by
    rw [← c_abs hc]; exact c_le hc (abs_nonneg _) hup
  rw [hsum1, hsum2]
  rcases Nat.lt_or_ge 1 N.card with h2 | h1
  · have hk : (1:ℝ) < N.card := by exact_mod_cast h2
    have hSA := hg.2.2 (N.card : ℝ) S hk Spos
    have hgpos : 0 < g N.card := lt_of_le_of_lt (div_nonneg (mul_nonneg zero_le_two (hc.nonneg S)) cs_pos.le) hcond
    have hc2 : 2 * c S < g N.card * c s := by
      rw [div_lt_iff₀ cs_pos] at hcond; linarith
    have : (N.card : ℝ) / g N.card * c S * 2 < (N.card : ℝ) * c s := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hgpos]
      have hk0 : (0:ℝ) < N.card := by linarith
      nlinarith
    linarith
  · exfalso
    have hc1 : N.card = 1 := le_antisymm h1 hdeg
    rw [hc1] at hcond
    have := g_one_lt hc hg
    have h2 : 2 ≤ 2 * c S / c s := by
      rw [le_div_iff₀ cs_pos]; linarith
    push_cast at hcond
    linarith

end LNRHHelp

open LNTopology.RandomHerm LNRHHelp

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (c g : ℝ → ℝ) (Λ : V → V → ℝ)
    (U : Finset V) (hc : LNTopology.Local.IsChannelCost c) (hg : LNTopology.Hermetic.SAPlus c g) (hΛ : LNTopology.Local.IsLN Λ) (hU : U.Nonempty)
    (hdeg : ∀ i ∈ U, 1 ≤ degOn Λ U i)
    (hcond : ∀ i ∈ U, 2 * c (maxChanOn Λ U i) / c (minChanOn Λ U i) < g (degOn Λ U i)) :
    IsHermetizable c Λ U := by
  unfold IsHermetizable
  rw [cost_hermetize hc]
  have := Finset.sum_lt_sum_of_nonempty hU (fun i hi => node_ineq hc hg Λ U i (hdeg i hi) (hcond i hi))
  rw [← Finset.mul_sum] at this
  linarith


