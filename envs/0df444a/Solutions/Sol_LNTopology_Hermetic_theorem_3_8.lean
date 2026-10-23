-- Prove2me | solution 1 for LNTopology.Hermetic.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T13:42:32.851202+00:00
-- url     : https://prove2.me/submissions/a2d967d1-6991-4331-ad51-49081b65459f

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_Hermetic_Degree
import Definitions.Def_LNTopology_Hermetic_Hermetization

set_option autoImplicit false

namespace LNHerm38

open LNTopology.Hermetic LNTopology.Local

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def A (Λ : V → V → ℝ) (v w : V) : ℝ := if Λ v w ≠ 0 then 1 else 0

lemma degIn_eq (Λ : V → V → ℝ) (U : Finset V) (v : V) :
    (degIn Λ U v : ℝ) = ∑ w ∈ U, A Λ v w := by
  unfold degIn A
  rw [Finset.card_filter]
  push_cast
  rfl

lemma A_symm {Λ : V → V → ℝ} (hΛ : IsLN Λ) (v w : V) : A Λ v w = A Λ w v := by
  unfold A
  rw [hΛ v w]
  simp only [ne_eq, neg_eq_zero]

lemma A_self {Λ : V → V → ℝ} (hΛ : IsLN Λ) (v : V) : A Λ v v = 0 := by
  unfold A
  have h := hΛ v v
  have h0 : Λ v v = 0 := by linarith
  simp [h0]

lemma e_insert {Λ : V → V → ℝ} (hΛ : IsLN Λ) (U : Finset V) (v : V) (hv : v ∉ U) :
    ∑ w ∈ insert v U, (degIn Λ (insert v U) w : ℝ)
      = ∑ w ∈ U, (degIn Λ U w : ℝ) + 2 * (degIn Λ (insert v U) v : ℝ) := by
  simp only [degIn_eq, Finset.sum_insert hv, A_self hΛ, Finset.sum_add_distrib]
  have : ∑ x ∈ U, A Λ x v = ∑ x ∈ U, A Λ v x :=
    Finset.sum_congr rfl (fun x _ => A_symm hΛ x v)
  linarith

lemma dense_sub {Λ : V → V → ℝ} (hΛ : IsLN Λ) (a : ℝ) (U0 : Finset V)
    (h0 : a * U0.card ≤ ∑ w ∈ U0, (degIn Λ U0 w : ℝ)) (hne : U0.Nonempty) :
    ∃ U : Finset V, U.Nonempty ∧ ∀ v ∈ U, a / 2 ≤ (degIn Λ U v : ℝ) := by
  classical
  let S := U0.powerset.filter
    (fun U => U.Nonempty ∧ a * U.card ≤ ∑ w ∈ U, (degIn Λ U w : ℝ))
  have hS : S.Nonempty := ⟨U0, by simp [S, hne, h0]⟩
  obtain ⟨U, hUS, hmin⟩ := Finset.exists_min_image S Finset.card hS
  simp only [S, Finset.mem_filter, Finset.mem_powerset] at hUS
  obtain ⟨hsub, hUne, hUe⟩ := hUS
  refine ⟨U, hUne, fun v hv => ?_⟩
  by_contra hlt
  push_neg at hlt
  have key := e_insert hΛ (U.erase v) v (Finset.notMem_erase v U)
  rw [Finset.insert_erase hv] at key
  have hcard : (U.card : ℝ) = ((U.erase v).card : ℝ) + 1 := by
    rw [← Finset.card_erase_add_one hv]
    push_cast
    ring
  have hU'ne : (U.erase v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.card_empty, Nat.cast_zero] at hcard
    rw [hemp, Finset.sum_empty] at key
    rw [hcard] at hUe
    linarith
  have hmem : U.erase v ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨(Finset.erase_subset v U).trans hsub, hU'ne, ?_⟩
    have : a * (U.card : ℝ) = a * ((U.erase v).card : ℝ) + a := by rw [hcard]; ring
    linarith
  exact absurd (hmin _ hmem) (not_le.mpr (Finset.card_erase_lt_of_mem hv))

lemma c_abs {c : ℝ → ℝ} (hc : IsChannelCost c) (x : ℝ) : c |x| = c x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact hc.symm x

lemma c_mono_le {c : ℝ → ℝ} (hc : IsChannelCost c) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    c y ≤ c x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (hc.mono x y hy h).le

lemma c_pos {c : ℝ → ℝ} (hc : IsChannelCost c) {x : ℝ} (hx : 0 < x) : 0 < c x := by
  have := hc.mono x 0 le_rfl hx
  rwa [hc.zero] at this

/-- Facts about the whole-network flows of a node `i` having a channel. -/
lemma node_facts {c : ℝ → ℝ} (hc : IsChannelCost c) (Λ : V → V → ℝ) (i j : V) (hij : Λ i j ≠ 0) :
    0 < minFlowIn Λ Finset.univ i ∧
    (∀ k, Λ i k ≠ 0 → minFlowIn Λ Finset.univ i ≤ |Λ i k|) ∧
    (∀ k, |Λ i k| ≤ maxFlowIn Λ Finset.univ i) ∧
    c (maxFlowIn Λ Finset.univ i) ≤ disc c Λ * c (minFlowIn Λ Finset.univ i) := by
  have hF : (Finset.univ.filter (fun k => Λ i k ≠ 0)).Nonempty :=
    ⟨j, by simp [hij]⟩
  have hmin_eq : minFlowIn Λ Finset.univ i =
      (Finset.univ.filter (fun k => Λ i k ≠ 0)).inf' hF (fun k => |Λ i k|) := by
    unfold minFlowIn; rw [dif_pos hF]
  have hmax_eq : maxFlowIn Λ Finset.univ i =
      (Finset.univ : Finset V).sup' ⟨i, Finset.mem_univ i⟩ (fun k => |Λ i k|) := by
    unfold maxFlowIn; rw [dif_pos ⟨i, Finset.mem_univ i⟩]
  have hspos : 0 < minFlowIn Λ Finset.univ i := by
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hF (fun k => |Λ i k|)
    rw [hmin_eq, hkeq]
    simp only [Finset.mem_filter] at hk
    exact abs_pos.mpr hk.2
  have hsle : ∀ k, Λ i k ≠ 0 → minFlowIn Λ Finset.univ i ≤ |Λ i k| := by
    intro k hk
    rw [hmin_eq]
    exact Finset.inf'_le (fun k => |Λ i k|) (by simp [hk])
  have hSge : ∀ k, |Λ i k| ≤ maxFlowIn Λ Finset.univ i := by
    intro k
    rw [hmax_eq]
    exact Finset.le_sup' (fun k => |Λ i k|) (Finset.mem_univ k)
  refine ⟨hspos, hsle, hSge, ?_⟩
  have hcs : 0 < c (minFlowIn Λ Finset.univ i) := c_pos hc hspos
  have hdeg : (Finset.univ.filter (fun v => degIn Λ Finset.univ v ≠ 0)).Nonempty := by
    refine ⟨i, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold degIn
    exact (Finset.card_pos.mpr hF).ne'
  have hi : i ∈ Finset.univ.filter (fun v => degIn Λ Finset.univ v ≠ 0) := by
    obtain ⟨w, hw⟩ := hdeg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold degIn
    exact (Finset.card_pos.mpr hF).ne'
  have hle : c (maxFlowIn Λ Finset.univ i) / c (minFlowIn Λ Finset.univ i) ≤ disc c Λ := by
    unfold disc discIn
    rw [dif_pos hdeg]
    exact Finset.le_sup'
      (fun v => c (maxFlowIn Λ Finset.univ v) / c (minFlowIn Λ Finset.univ v)) hi
  rwa [div_le_iff₀ hcs] at hle

lemma node_bound {c g : ℝ → ℝ} (hc : IsChannelCost c) (hg : SAPlus c g) (Λ : V → V → ℝ)
    (U : Finset V) (i : V) (hi : i ∈ U)
    (hd : 1 < (degIn Λ U i : ℝ)) (hgd : 2 * disc c Λ < g (degIn Λ U i)) :
    c (∑ j ∈ U, Λ i j) < (1 / 2) * ∑ j ∈ U, c (Λ i j) := by
  set F := U.filter (fun j => Λ i j ≠ 0) with hFdef
  have hdF : degIn Λ U i = F.card := rfl
  set d : ℝ := (degIn Λ U i : ℝ) with hddef
  have hFne : F.Nonempty := by
    rw [← Finset.card_pos, ← hdF]
    have : (0 : ℝ) < (degIn Λ U i : ℝ) := by linarith
    exact_mod_cast this
  have hUne : U.Nonempty := ⟨i, hi⟩
  set SU := maxFlowIn Λ U i with hSUdef
  set sU := minFlowIn Λ U i with hsUdef
  have hSU_eq : SU = U.sup' hUne (fun k => |Λ i k|) := by
    rw [hSUdef]; unfold maxFlowIn; rw [dif_pos hUne]
  have hsU_eq : sU = F.inf' hFne (fun k => |Λ i k|) := by
    rw [hsUdef]; unfold minFlowIn; rw [dif_pos hFne]
  obtain ⟨j0, hj0F⟩ := hFne
  have hj0 : Λ i j0 ≠ 0 := (Finset.mem_filter.mp hj0F).2
  obtain ⟨hspos, hsle, hSge, hdisc⟩ := node_facts hc Λ i j0 hj0
  -- comparisons with the whole-network values
  have hSU_le : SU ≤ maxFlowIn Λ Finset.univ i := by
    rw [hSU_eq]; exact Finset.sup'_le _ _ (fun k _ => hSge k)
  have hs_le : minFlowIn Λ Finset.univ i ≤ sU := by
    rw [hsU_eq]
    exact Finset.le_inf' _ _ (fun k hk => hsle k (Finset.mem_filter.mp hk).2)
  have hsUpos : 0 < sU := lt_of_lt_of_le hspos hs_le
  have hSUpos : 0 < SU := by
    rw [hSU_eq]
    exact lt_of_lt_of_le (abs_pos.mpr hj0)
      (Finset.le_sup' (fun k => |Λ i k|) (Finset.mem_filter.mp hj0F).1)
  -- (a) |T| ≤ d * SU
  have hT : |∑ j ∈ U, Λ i j| ≤ d * SU := by
    calc |∑ j ∈ U, Λ i j| ≤ ∑ j ∈ U, |Λ i j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ F, |Λ i j| := by
          rw [hFdef]
          exact (Finset.sum_filter_of_ne (fun x _ hx => abs_ne_zero.mp hx)).symm
      _ ≤ F.card • SU := by
          apply Finset.sum_le_card_nsmul
          intro k hk
          rw [hSU_eq]
          exact Finset.le_sup' (fun k => |Λ i k|) (Finset.mem_filter.mp hk).1
      _ = d * SU := by rw [nsmul_eq_mul, hddef, hdF]
  have hdisc0 : 0 ≤ disc c Λ := by
    have h1 := c_pos hc hspos
    have h2 := hc.nonneg (maxFlowIn Λ Finset.univ i)
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hgpos : 0 < g d := by linarith
  have hd0 : 0 < d := by linarith
  -- (h) d * c sU ≤ ∑ c
  have hsum : d * c sU ≤ ∑ j ∈ U, c (Λ i j) := by
    calc d * c sU = F.card • c sU := by rw [nsmul_eq_mul, hddef, hdF]
      _ ≤ ∑ j ∈ F, c (Λ i j) := by
          apply Finset.card_nsmul_le_sum
          intro k hk
          rw [← c_abs hc (Λ i k)]
          apply c_mono_le hc hsUpos.le
          rw [hsU_eq]
          exact Finset.inf'_le (fun k => |Λ i k|) hk
      _ ≤ ∑ j ∈ U, c (Λ i j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro k _ _
          exact hc.nonneg _
  have h1 : c (∑ j ∈ U, Λ i j) ≤ c (d * SU) := by
    rw [← c_abs hc]
    exact c_mono_le hc (abs_nonneg _) hT
  have h2 : c (d * SU) < d / g d * c SU := hg.2.2 d SU hd hSUpos
  have h3 : c SU ≤ disc c Λ * c sU := by
    calc c SU ≤ c (maxFlowIn Λ Finset.univ i) := c_mono_le hc hSUpos.le hSU_le
      _ ≤ disc c Λ * c (minFlowIn Λ Finset.univ i) := hdisc
      _ ≤ disc c Λ * c sU :=
          mul_le_mul_of_nonneg_left (c_mono_le hc hspos.le hs_le) hdisc0
  have hcsU : 0 ≤ c sU := hc.nonneg _
  have h4 : d / g d * c SU ≤ d / g d * (disc c Λ * c sU) :=
    mul_le_mul_of_nonneg_left h3 (div_nonneg hd0.le hgpos.le)
  have h5 : d / g d * (disc c Λ * c sU) ≤ d / 2 * c sU := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hgpos]
    have : 0 ≤ d * c sU * (g d - 2 * disc c Λ) :=
      mul_nonneg (mul_nonneg hd0.le hcsU) (by linarith)
    nlinarith
  have : d / 2 * c sU = (1 / 2) * (d * c sU) := by ring
  linarith

lemma cost_herm {c : ℝ → ℝ} (hc : IsChannelCost c) (Λ : V → V → ℝ) (U : Finset V) :
    cost c (hermetize Λ U) = cost c Λ + ∑ i ∈ U, c (∑ j ∈ U, Λ i j)
      - (1 / 2) * ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
  have h1 : ∀ j, c (if j ∈ U then -∑ i ∈ U, Λ j i else 0)
      = if j ∈ U then c (∑ i ∈ U, Λ j i) else 0 := by
    intro j; split_ifs <;> simp [hc.symm, hc.zero]
  have h2 : ∀ i, c (if i ∈ U then ∑ j ∈ U, Λ i j else 0)
      = if i ∈ U then c (∑ j ∈ U, Λ i j) else 0 := by
    intro i; split_ifs <;> simp [hc.zero]
  have h3 : ∀ i j, c (if i ∈ U ∧ j ∈ U then 0 else Λ i j)
      = c (Λ i j) - if i ∈ U ∧ j ∈ U then c (Λ i j) else 0 := by
    intro i j; split_ifs <;> simp [hc.zero]
  have h4 : ∑ i, ∑ j, (if i ∈ U ∧ j ∈ U then c (Λ i j) else 0)
      = ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
    calc ∑ i, ∑ j, (if i ∈ U ∧ j ∈ U then c (Λ i j) else 0)
        = ∑ i, if i ∈ U then ∑ j ∈ U, c (Λ i j) else 0 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hi : i ∈ U
          · simp [hi, Finset.sum_ite_mem]
          · simp [hi]
      _ = ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
  have E : ∑ a : Option V, ∑ b : Option V, c (hermetize Λ U a b)
      = 2 * ∑ i ∈ U, c (∑ j ∈ U, Λ i j) + ∑ i, ∑ j, c (Λ i j)
        - ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
    simp only [Fintype.sum_option, hermetize, hc.zero, h1, h2, h3, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, h4, Finset.sum_ite_mem, Finset.univ_inter]
    ring
  unfold cost
  rw [E]
  ring

end LNHerm38

open LNHerm38 LNTopology.Hermetic in
/-- Theorem 3.8 (existence part): under (MO)–(SA+), a Lightning Network with at least one channel
and `g₊(d̄(G)/2) > 2 disc(G)` (the paper's `d̄(G) > 2 g₊⁻¹(2 disc(G))`) is hermetizable. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (c g : ℝ → ℝ)
    (hc : LNTopology.Local.IsChannelCost c) (hg : LNTopology.Hermetic.SAPlus c g)
    (Λ : V → V → ℝ) (hΛ : LNTopology.Local.IsLN Λ)
    (hchan : ∃ u v, Λ u v ≠ 0)
    (hdisc : 2 * LNTopology.Hermetic.disc c Λ < g (LNTopology.Hermetic.avgDeg Λ / 2)) :
    LNTopology.Hermetic.IsHermetizableLN c Λ := by
  obtain ⟨u, v, huv⟩ := hchan
  obtain ⟨hspos, hsle, hSge, hd⟩ := node_facts hc Λ u v huv
  -- disc ≥ 1
  have hdisc1 : 1 ≤ disc c Λ := by
    have hcs := c_pos hc hspos
    have hsS : minFlowIn Λ Finset.univ u ≤ maxFlowIn Λ Finset.univ u :=
      (hsle v huv).trans (hSge v)
    have := c_mono_le hc hspos.le hsS
    nlinarith
  -- g 2 < 2
  have hc1 : 0 < c 1 := c_pos hc one_pos
  have hc12 : c 1 < c 2 := hc.mono 2 1 zero_le_one one_lt_two
  have hSA := hg.2.2 2 1 one_lt_two one_pos
  rw [mul_one] at hSA
  have hg20 : 0 ≤ g 2 := hg.2.1 2 zero_le_two
  have hg2pos : 0 < g 2 := by
    rcases eq_or_lt_of_le hg20 with h | h
    · rw [← h, div_zero, zero_mul] at hSA; linarith [hc.nonneg 2]
    · exact h
  have hg2 : g 2 < 2 := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hg2pos] at hSA
    nlinarith
  -- avgDeg ≥ 0 and avgDeg / 2 > 1
  have hcardpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have havg0 : 0 ≤ avgDeg Λ := by
    unfold avgDeg
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hcardpos.le
  have havg1 : 1 < avgDeg Λ / 2 := by
    by_contra hle
    push_neg at hle
    have hmono := hg.1.monotoneOn
    have : g (avgDeg Λ / 2) ≤ g 2 :=
      hmono (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr zero_le_two) (by linarith)
    linarith
  -- dense subnetwork
  have h0 : avgDeg Λ * (Finset.univ : Finset V).card
      ≤ ∑ w ∈ Finset.univ, (degIn Λ Finset.univ w : ℝ) := by
    rw [Finset.card_univ]
    unfold avgDeg deg
    rw [div_mul_cancel₀ _ hcardpos.ne']
  obtain ⟨U, hUne, hU⟩ := dense_sub hΛ (avgDeg Λ) Finset.univ h0 Finset.univ_nonempty
  refine ⟨U, ?_⟩
  unfold IsHermetizable
  rw [cost_herm hc]
  have hlt : ∑ i ∈ U, c (∑ j ∈ U, Λ i j) < ∑ i ∈ U, (1 / 2) * ∑ j ∈ U, c (Λ i j) := by
    apply Finset.sum_lt_sum_of_nonempty hUne
    intro i hi
    have hdi := hU i hi
    apply node_bound hc hg Λ U i hi (by linarith)
    have : g (avgDeg Λ / 2) ≤ g (degIn Λ U i) :=
      hg.1.monotoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (Nat.cast_nonneg _)) hdi
    linarith
  rw [← Finset.mul_sum] at hlt
  linarith
