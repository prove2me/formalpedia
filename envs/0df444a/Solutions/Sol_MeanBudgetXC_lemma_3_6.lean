-- Prove2me | solution 1 for MeanBudgetXC.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:40:47.324473+00:00
-- url     : https://prove2.me/submissions/7392ef97-7a78-465b-a67f-81a402bb2e26

import Mathlib
import Definitions.Def_MeanBudgetXC_topSum
import Definitions.Def_MeanBudgetXC_rltPolytope
import Definitions.Def_MeanBudgetXC_rltObjective

namespace MeanBudgetXC

theorem entry_comm_aux {V : Type*} [DecidableEq V] (q : Pair V → ℝ) (i j : V) :
    entry q i j = entry q j i := by
  unfold entry
  by_cases h : i = j
  · subst h; rfl
  · rw [dif_neg h, dif_neg (Ne.symm h)]
    exact congrArg q (Subtype.ext Sym2.eq_swap)

theorem entry_self_aux {V : Type*} [DecidableEq V] (q : Pair V → ℝ) (i : V) :
    entry q i i = 0 := by
  simp [entry]

theorem entry_nonneg_aux {V : Type*} [DecidableEq V] (q : Pair V → ℝ) (hq : ∀ e, 0 ≤ q e)
    (i j : V) : 0 ≤ entry q i j := by
  unfold entry
  split_ifs
  · exact le_refl 0
  · exact hq _

theorem sum_entry_mul_aux {V : Type*} [Fintype V] [DecidableEq V] (q y : Pair V → ℝ) :
    ∑ i, ∑ j, entry q i j * entry y i j = 2 * ∑ e, q e * y e := by
  classical
  let g : Sym2 V → ℝ := fun z => if hz : z.IsDiag then 0 else q ⟨z, hz⟩ * y ⟨z, hz⟩
  have h1 : ∀ i j, entry q i j * entry y i j = g s(i, j) := by
    intro i j
    by_cases h : i = j
    · subst h; simp [entry, g]
    · have hd : ¬ (s(i, j)).IsDiag := Sym2.mk_isDiag_iff.not.mpr h
      simp only [entry, dif_neg h, g, dif_neg hd]
  have h2 : ∑ i, ∑ j, entry q i j * entry y i j = ∑ p : V × V, g s(p.1, p.2) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [h1]
  have h3 : ∑ p : V × V, g s(p.1, p.2) = ∑ z : Sym2 V, 2 * g z := by
    rw [← Finset.sum_fiberwise Finset.univ (fun p : V × V => s(p.1, p.2))
      (fun p => g s(p.1, p.2))]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
      Finset.sum_const, nsmul_eq_mul]
    induction z using Sym2.ind with
    | h a b =>
      by_cases hab : a = b
      · subst hab; simp [g]
      · have hf : (Finset.univ.filter (fun p : V × V => s(p.1, p.2) = s(a, b))) =
            {(a, b), (b, a)} := by
          ext ⟨u, v⟩
          simp [Sym2.eq_iff]
        rw [hf, Finset.card_pair (fun h => hab (congrArg Prod.fst h))]
        norm_num
  have h4 : ∑ z : Sym2 V, g z = ∑ e : Pair V, q e * y e := by
    rw [← Finset.sum_filter_of_ne (p := fun z : Sym2 V => ¬ z.IsDiag)
      (fun z _ hz => fun hd => hz (by simp [g, hd]))]
    rw [Finset.sum_subtype (Finset.univ.filter fun z : Sym2 V => ¬ z.IsDiag)
      (p := fun z : Sym2 V => ¬ z.IsDiag) (by simp) g]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp [g, e.2]
  rw [h2, h3, ← Finset.mul_sum, h4]

theorem frac_le_topSum_aux {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd1 : 1 ≤ d)
    (hdN : d ≤ Fintype.card V) (q : Pair V → ℝ) (hq : ∀ e, 0 ≤ q e) (i : V) (c : V → ℝ)
    (σ : ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ σ)
    (hcs : ∑ j, c j ≤ ((d : ℝ) - 1) * σ) (hci : c i = 0) :
    ∑ j, entry q i j * c j ≤ σ * topSum d q i := by
  classical
  have hσ : 0 ≤ σ := le_trans (hc0 i) (hc1 i)
  set U : Finset V := Finset.univ.erase i with hU
  have hUcard : U.card = Fintype.card V - 1 := by
    rw [hU, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hne : (U.powersetCard (d - 1)).Nonempty := by
    rw [Finset.powersetCard_nonempty]; omega
  obtain ⟨T, hTmem, hTmax⟩ := Finset.exists_max_image (U.powersetCard (d - 1))
    (fun T => ∑ j ∈ T, entry q i j) hne
  have hTop : ∑ j ∈ T, entry q i j ≤ topSum d q i := by
    unfold topSum
    rw [dif_pos hne]
    exact Finset.le_sup' (fun T => ∑ j ∈ T, entry q i j) hTmem
  rw [Finset.mem_powersetCard] at hTmem
  obtain ⟨hTU, hTcard⟩ := hTmem
  have hswap : ∀ j ∈ T, ∀ l, l ∉ T → l ≠ i → entry q i l ≤ entry q i j := by
    intro j hj l hl hli
    have hmem : insert l (T.erase j) ∈ U.powersetCard (d - 1) := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with hz | hz
        · rw [hz]; simp [hU, hli]
        · exact hTU (Finset.mem_of_mem_erase hz)
      · rw [Finset.card_insert_of_notMem (fun h => hl (Finset.mem_of_mem_erase h)),
          Finset.card_erase_of_mem hj]
        have : 1 ≤ T.card := Finset.card_pos.mpr ⟨j, hj⟩
        omega
    have h := hTmax _ hmem
    rw [Finset.sum_insert (fun h => hl (Finset.mem_of_mem_erase h))] at h
    have h2 : ∑ x ∈ T.erase j, entry q i x + entry q i j = ∑ x ∈ T, entry q i x :=
      Finset.sum_erase_add T (fun x => entry q i x) hj
    linarith
  by_cases hTe : T.Nonempty
  · set θ := T.inf' hTe (fun j => entry q i j) with hθ
    have hθle : ∀ j ∈ T, θ ≤ entry q i j := fun j hj => Finset.inf'_le _ hj
    have hθ0 : 0 ≤ θ := Finset.le_inf' hTe _ (fun j _ => entry_nonneg_aux q hq i j)
    have hθge : ∀ l, l ∉ T → entry q i l * c l ≤ θ * c l := by
      intro l hl
      by_cases hli : l = i
      · rw [hli, hci]; simp
      · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hTe (fun j => entry q i j)
        have hs := hswap j hj l hl hli
        have hle : entry q i l ≤ θ := by rw [hθ, hjeq]; exact hs
        exact mul_le_mul_of_nonneg_right hle (hc0 l)
    have hsplit : ∑ j ∈ T, entry q i j * c j + ∑ j ∈ Tᶜ, entry q i j * c j =
        ∑ j, entry q i j * c j := Finset.sum_add_sum_compl T _
    have hsplitc : ∑ j ∈ T, c j + ∑ j ∈ Tᶜ, c j = ∑ j, c j := Finset.sum_add_sum_compl T _
    have h1 : ∑ j ∈ T, θ * (σ - c j) ≤ ∑ j ∈ T, entry q i j * (σ - c j) :=
      Finset.sum_le_sum (fun j hj =>
        mul_le_mul_of_nonneg_right (hθle j hj) (by linarith [hc1 j]))
    have h2 : ∑ j ∈ T, θ * (σ - c j) = θ * ((T.card : ℝ) * σ - ∑ j ∈ T, c j) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h3 : ∑ j ∈ T, entry q i j * (σ - c j) =
        σ * ∑ j ∈ T, entry q i j - ∑ j ∈ T, entry q i j * c j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hB : ∑ j ∈ Tᶜ, entry q i j * c j ≤ θ * ∑ j ∈ Tᶜ, c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun l hl => hθge l (Finset.mem_compl.mp hl))
    have hcardR : (T.card : ℝ) = (d : ℝ) - 1 := by
      rw [hTcard, Nat.cast_sub hd1, Nat.cast_one]
    have hmul : 0 ≤ θ * (((d : ℝ) - 1) * σ - ∑ j, c j) := mul_nonneg hθ0 (by linarith)
    have hTop' : σ * ∑ j ∈ T, entry q i j ≤ σ * topSum d q i :=
      mul_le_mul_of_nonneg_left hTop hσ
    rw [hcardR] at h2
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hTe
    have hd1' : d = 1 := by rw [hTe, Finset.card_empty] at hTcard; omega
    have hz : ((d : ℝ) - 1) = 0 := by rw [hd1']; norm_num
    have hsum0 : ∑ j, c j = 0 :=
      le_antisymm (by rw [hz, zero_mul] at hcs; exact hcs) (Finset.sum_nonneg (fun j _ => hc0 j))
    have hcz : ∀ j, c j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc0 j)).mp hsum0 j (Finset.mem_univ j)
    simp only [hcz, mul_zero, Finset.sum_const_zero]
    have h0 : 0 ≤ topSum d q i := by
      have := hTop; rw [hTe, Finset.sum_empty] at this; exact this
    exact mul_nonneg hσ h0

/-- Auxiliary per-pair weights used in the proof. -/
noncomputable def Faux {V : Type*} (x : V → ℝ) (Y : V → V → ℝ) (i j : V) : ℝ :=
  if 1 / 2 < x i then x i - 1 / 2 else
    if x i < 1 / 2 then -(if 1 / 2 < x j then max 0 (x j - 1 / 2 - Y i j) else 0) else 0

end MeanBudgetXC

open MeanBudgetXC in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd2 : 2 ≤ d)
    (hdN : d ≤ Fintype.card V) (p : V → ℝ) (q : Pair V → ℝ) (hq : ∀ e, 0 ≤ q e)
    (h5 : ∀ i, topSum d q i ≤ p i ∧ p i ≤ ∑ j, entry q i j)
    (xy : (V → ℝ) × (Pair V → ℝ)) (hxy : xy ∈ rltPolytope V d)
    (hJ : (∑ i, p i) / 2 < rltObjective p q xy) :
    (Finset.univ.filter fun i => 1 / 2 < xy.1 i).card = d ∧
      ∀ i, ¬ (1 / 2 < xy.1 i) → xy.1 i < 1 / 2 := by
  classical
  simp only [rltPolytope, Set.mem_ofPred_eq] at hxy
  obtain ⟨hx01, hsum, hmc, hrow⟩ := hxy
  have hYsym : ∀ i j, entry xy.2 j i = entry xy.2 i j := fun i j => entry_comm_aux xy.2 j i
  have hY0 : ∀ i j, 0 ≤ entry xy.2 i j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [entry_self_aux]
    · exact (hmc i j h).1
  have hYi : ∀ i j, entry xy.2 i j ≤ xy.1 i := by
    intro i j
    by_cases h : i = j
    · subst h; rw [entry_self_aux]; exact (hx01 i).1
    · exact (hmc i j h).2.1
  have hYj : ∀ i j, entry xy.2 i j ≤ xy.1 j := by
    intro i j; rw [← hYsym]; exact hYi j i
  have hMC : ∀ i j, i ≠ j → xy.1 i + xy.1 j - 1 ≤ entry xy.2 i j :=
    fun i j h => (hmc i j h).2.2
  have hQ0 : ∀ i j, 0 ≤ entry q i j := entry_nonneg_aux q hq
  have hQsym : ∀ i j, entry q j i = entry q i j := fun i j => entry_comm_aux q j i
  by_contra hcon
  have hfail : (Finset.univ.filter fun i => 1 / 2 < xy.1 i).card ≠ d ∨
      ∃ m, xy.1 m = 1 / 2 := by
    by_cases hc : (Finset.univ.filter fun i => 1 / 2 < xy.1 i).card = d
    · right
      by_contra hno
      push_neg at hno
      exact hcon ⟨hc, fun i hi => lt_of_le_of_ne (not_lt.mp hi) (hno i)⟩
    · left; exact hc
  -- the budget condition on the weights of a vertex below one half
  have hsumc : ∀ i, xy.1 i < 1 / 2 →
      ∑ j, (if 1 / 2 < xy.1 j then max 0 (xy.1 j - 1 / 2 - entry xy.2 i j) else 0) ≤
        ((d : ℝ) - 1) * (1 / 2 - xy.1 i) := by
    intro i hi
    set A := Finset.univ.filter
      (fun j => 1 / 2 < xy.1 j ∧ 0 < xy.1 j - 1 / 2 - entry xy.2 i j) with hA
    have hsA : ∑ j, (if 1 / 2 < xy.1 j then max 0 (xy.1 j - 1 / 2 - entry xy.2 i j) else 0) =
        ∑ j ∈ A, (xy.1 j - 1 / 2 - entry xy.2 i j) := by
      rw [hA, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h1 : 1 / 2 < xy.1 j
      · by_cases h2 : 0 < xy.1 j - 1 / 2 - entry xy.2 i j
        · rw [if_pos h1, if_pos ⟨h1, h2⟩, max_eq_right h2.le]
        · rw [if_pos h1, if_neg (fun h => h2 h.2), max_eq_left (not_lt.mp h2)]
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    rw [hsA]
    have hAi : i ∉ A := by
      intro h; rw [hA, Finset.mem_filter] at h; linarith [h.2.1]
    have hterm : ∀ j ∈ A, xy.1 j - 1 / 2 - entry xy.2 i j ≤ 1 / 2 - xy.1 i := by
      intro j hj
      have hji : i ≠ j := fun h => hAi (h ▸ hj)
      linarith [hMC i j hji]
    have hxi0 := (hx01 i).1
    rcases Nat.lt_or_ge A.card d with hlt | hge
    · calc ∑ j ∈ A, (xy.1 j - 1 / 2 - entry xy.2 i j) ≤ ∑ j ∈ A, (1 / 2 - xy.1 i) :=
            Finset.sum_le_sum hterm
        _ = (A.card : ℝ) * (1 / 2 - xy.1 i) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((d : ℝ) - 1) * (1 / 2 - xy.1 i) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            have h' : A.card + 1 ≤ d := hlt
            have h'' : ((A.card : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast h'
            linarith
    · have hrowi := hrow i
      have hs1 : ∑ j ∈ A, entry xy.2 i j + ∑ j ∈ Aᶜ, entry xy.2 i j = ∑ j, entry xy.2 i j :=
        Finset.sum_add_sum_compl A _
      have hs2 : ∑ j ∈ A, xy.1 j + ∑ j ∈ Aᶜ, xy.1 j = ∑ j, xy.1 j :=
        Finset.sum_add_sum_compl A _
      have hexp : ∑ j ∈ A, (xy.1 j - 1 / 2 - entry xy.2 i j) =
          ∑ j ∈ A, xy.1 j - (A.card : ℝ) / 2 - ∑ j ∈ A, entry xy.2 i j := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
      have hs3 : ∑ j ∈ Aᶜ, (xy.1 j - entry xy.2 i j) =
          ∑ j ∈ Aᶜ, xy.1 j - ∑ j ∈ Aᶜ, entry xy.2 i j := by
        rw [Finset.sum_sub_distrib]
      have hnn : ∀ j ∈ Aᶜ, 0 ≤ xy.1 j - entry xy.2 i j := fun j _ => by linarith [hYj i j]
      have hiAc : i ∈ Aᶜ := Finset.mem_compl.mpr hAi
      have hYii : entry xy.2 i i = 0 := entry_self_aux _ _
      rw [hexp]
      rcases Nat.lt_or_ge d A.card with hgt | hle
      · have hsingle : xy.1 i - entry xy.2 i i ≤ ∑ j ∈ Aᶜ, (xy.1 j - entry xy.2 i j) :=
          Finset.single_le_sum hnn hiAc
        have hcard : (d : ℝ) + 1 ≤ (A.card : ℝ) := by exact_mod_cast hgt
        linarith
      · have had : A.card = d := le_antisymm hle hge
        have hcard : (A.card : ℝ) = d := by exact_mod_cast had
        obtain ⟨w, hwA, hwi, hwb⟩ : ∃ w, w ∉ A ∧ w ≠ i ∧
            1 / 2 - xy.1 i ≤ xy.1 w - entry xy.2 i w := by
          rcases hfail with hH | ⟨m, hm⟩
          · have hsub : A ⊆ Finset.univ.filter (fun j => 1 / 2 < xy.1 j) := by
              intro j hj
              rw [hA, Finset.mem_filter] at hj
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.2.1⟩
            have hne : A ≠ Finset.univ.filter (fun j => 1 / 2 < xy.1 j) := by
              intro h; apply hH; rw [← h]; exact had
            obtain ⟨w, hwH, hwA⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
            have hw : 1 / 2 < xy.1 w := (Finset.mem_filter.mp hwH).2
            refine ⟨w, hwA, fun h => by rw [h] at hw; linarith, ?_⟩
            linarith [hYi i w]
          · refine ⟨m, fun h => ?_, fun h => by rw [h] at hm; linarith, ?_⟩
            · rw [hA, Finset.mem_filter] at h; linarith [h.2.1]
            · linarith [hYi i m]
        have hpair : ({i, w} : Finset V) ⊆ Aᶜ := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz | hz
          · rw [hz]; exact hiAc
          · rw [hz]; exact Finset.mem_compl.mpr hwA
        have hge2 := Finset.sum_le_sum_of_subset_of_nonneg hpair (fun j hj _ => hnn j hj)
        rw [Finset.sum_pair (Ne.symm hwi)] at hge2
        linarith
  have hstepA : ∀ i, p i * (xy.1 i - 1 / 2) ≤ ∑ j, entry q i j * Faux xy.1 (entry xy.2) i j := by
    intro i
    by_cases h1 : 1 / 2 < xy.1 i
    · simp only [Faux, if_pos h1]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (h5 i).2 (by linarith)
    · by_cases h2 : xy.1 i < 1 / 2
      · simp only [Faux, if_neg h1, if_pos h2]
        have hfr := frac_le_topSum_aux d (by omega) hdN q hq i
          (fun j => if 1 / 2 < xy.1 j then max 0 (xy.1 j - 1 / 2 - entry xy.2 i j) else 0)
          (1 / 2 - xy.1 i)
          (fun j => by
            split_ifs
            · exact le_max_left _ _
            · exact le_refl _)
          (fun j => by
            split_ifs with hj
            · have hji : i ≠ j := by rintro rfl; exact h1 hj
              exact max_le (by linarith) (by linarith [hMC i j hji])
            · linarith)
          (hsumc i h2) (if_neg h1)
        beta_reduce at hfr
        have hT : (1 / 2 - xy.1 i) * topSum d q i ≤ (1 / 2 - xy.1 i) * p i :=
          mul_le_mul_of_nonneg_left (h5 i).1 (by linarith)
        have hneg : ∑ j, entry q i j *
            -(if 1 / 2 < xy.1 j then max 0 (xy.1 j - 1 / 2 - entry xy.2 i j) else 0) =
            -∑ j, entry q i j *
              (if 1 / 2 < xy.1 j then max 0 (xy.1 j - 1 / 2 - entry xy.2 i j) else 0) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hneg]
        linarith
      · have hx : xy.1 i = 1 / 2 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
        have hF : ∀ j, Faux xy.1 (entry xy.2) i j = 0 := fun j => by
          unfold Faux; rw [if_neg h1, if_neg h2]
        rw [Finset.sum_congr rfl (fun j _ => by rw [hF j, mul_zero]), Finset.sum_const_zero, hx]
        norm_num
  have hstepB : 2 * ∑ i, ∑ j, entry q i j * Faux xy.1 (entry xy.2) i j ≤
      ∑ i, ∑ j, entry q i j * entry xy.2 i j := by
    have hsw : ∑ i, ∑ j, entry q i j * Faux xy.1 (entry xy.2) j i =
        ∑ i, ∑ j, entry q i j * Faux xy.1 (entry xy.2) i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hQsym]
    have hle : ∀ i j, entry q i j * (Faux xy.1 (entry xy.2) i j + Faux xy.1 (entry xy.2) j i) ≤
        entry q i j * entry xy.2 i j := by
      intro i j
      by_cases hij : i = j
      · subst hij; simp [entry_self_aux]
      · apply mul_le_mul_of_nonneg_left _ (hQ0 i j)
        have m1 := hMC i j hij
        have s := hYsym i j
        have y0 := hY0 i j
        have a1 := le_max_left 0 (xy.1 j - 1 / 2 - entry xy.2 i j)
        have a2 := le_max_right 0 (xy.1 j - 1 / 2 - entry xy.2 i j)
        have a3 := le_max_left 0 (xy.1 i - 1 / 2 - entry xy.2 j i)
        have a4 := le_max_right 0 (xy.1 i - 1 / 2 - entry xy.2 j i)
        unfold Faux
        split_ifs <;> linarith
    calc 2 * ∑ i, ∑ j, entry q i j * Faux xy.1 (entry xy.2) i j
        = ∑ i, ∑ j, entry q i j * Faux xy.1 (entry xy.2) i j +
            ∑ i, ∑ j, entry q i j * Faux xy.1 (entry xy.2) j i := by rw [hsw]; ring
      _ = ∑ i, ∑ j, entry q i j *
            (Faux xy.1 (entry xy.2) i j + Faux xy.1 (entry xy.2) j i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hle i j))
  have h1 : ∑ i, p i * (xy.1 i - 1 / 2) ≤
      ∑ i, ∑ j, entry q i j * Faux xy.1 (entry xy.2) i j :=
    Finset.sum_le_sum (fun i _ => hstepA i)
  have h2 := sum_entry_mul_aux q xy.2
  have hexp : ∑ i, p i * (xy.1 i - 1 / 2) = ∑ i, p i * xy.1 i - (∑ i, p i) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  unfold rltObjective at hJ
  linarith
