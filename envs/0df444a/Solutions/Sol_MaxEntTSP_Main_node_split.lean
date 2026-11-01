-- Prove2me | solution 1 for MaxEntTSP.Main.node_split
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:19:22.883772+00:00
-- url     : https://prove2.me/submissions/1fb225d5-e94d-4dd0-b0cf-f78cf51a0d9d

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model

open MaxEntTSP.Main MetricTSP Finset

namespace NodeSplitAux

variable {n : ℕ}

lemma proj_castSucc (u w : Fin n) : proj u (Fin.castSucc w) = w := by
  simp [proj]

lemma proj_last (u : Fin n) : proj u (Fin.last n) = u := by
  simp [proj]

lemma proj_u0 (u : Fin n) : proj u (u0 u) = u := by
  simp [proj, u0]

lemma proj_v0 (u : Fin n) : proj u (v0 n) = u := by
  simp [proj, v0]

lemma u0_ne_v0 (u : Fin n) : u0 u ≠ v0 n := by
  simp [u0, v0, Fin.castSucc_ne_last]

lemma halfAt_castSucc (u w : Fin n) :
    halfAt u (Fin.castSucc w) = if w = u then 1 / 2 else 1 := by
  unfold halfAt u0 v0
  by_cases h : w = u
  · simp [h]
  · simp [h, Fin.castSucc_ne_last, Fin.castSucc_inj]

lemma halfAt_last (u : Fin n) : halfAt u (Fin.last n) = 1 / 2 := by
  simp [halfAt, v0]

lemma halfAt_u0 (u : Fin n) : halfAt u (u0 u) = 1 / 2 := by
  simp [halfAt]

lemma halfAt_v0 (u : Fin n) : halfAt u (v0 n) = 1 / 2 := by
  simp [halfAt]

lemma halfAt_nonneg (u : Fin n) (i : Fin (n + 1)) : 0 ≤ halfAt u i := by
  unfold halfAt; split_ifs <;> norm_num

lemma halfAt_le_one (u : Fin n) (i : Fin (n + 1)) : halfAt u i ≤ 1 := by
  unfold halfAt; split_ifs <;> norm_num

/-- The key averaging identity: summing `halfAt · G ∘ proj` over the split vertex set
recovers the plain sum over the original vertices. -/
lemma sum_halfAt (u : Fin n) (G : Fin n → ℝ) :
    (∑ i, halfAt u i * G (proj u i)) = ∑ w, G w := by
  rw [Fin.sum_univ_castSucc]
  simp only [proj_castSucc, proj_last, halfAt_castSucc, halfAt_last]
  rw [← Finset.add_sum_erase univ G (mem_univ u),
    ← Finset.add_sum_erase univ _ (mem_univ u)]
  have : ∑ x ∈ univ.erase u, (if x = u then (1 / 2 : ℝ) else 1) * G x =
      ∑ x ∈ univ.erase u, G x := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [if_neg (Finset.ne_of_mem_erase hw), one_mul]
  rw [this, if_pos rfl]; ring

lemma pair_eq_e0 (u : Fin n) (i j : Fin (n + 1)) (h : s(i, j) = s(u0 u, v0 n)) :
    proj u i = u ∧ proj u j = u := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨proj_u0 u, proj_v0 u⟩
  · exact ⟨proj_v0 u, proj_u0 u⟩

noncomputable def dlt (u : Fin n) (i j : Fin (n + 1)) : ℝ :=
  if s(i, j) = s(u0 u, v0 n) then 1 else 0

lemma splitLP_eq (x : Fin n → Fin n → ℝ) (u : Fin n) (hxu : x u u = 0)
    (i j : Fin (n + 1)) :
    splitLP x u i j = halfAt u i * halfAt u j * x (proj u i) (proj u j) + dlt u i j := by
  unfold splitLP dlt
  split_ifs with h
  · obtain ⟨hi, hj⟩ := pair_eq_e0 u i j h
    rw [hi, hj, hxu]; ring
  · ring

lemma dlt_nonneg (u : Fin n) (i j : Fin (n + 1)) : 0 ≤ dlt u i j := by
  unfold dlt; split_ifs <;> norm_num

lemma sum_dlt (u : Fin n) (i : Fin (n + 1)) :
    (∑ j, dlt u i j) = if i = u0 u ∨ i = v0 n then 1 else 0 := by
  unfold dlt
  by_cases h1 : i = u0 u
  · subst h1
    simp only [true_or, if_true]
    have : ∀ j, (s(u0 u, j) = s(u0 u, v0 n)) ↔ j = v0 n := fun j => Sym2.congr_right
    simp_rw [this]; simp
  · by_cases h2 : i = v0 n
    · subst h2
      simp only [or_true, if_true]
      have : ∀ j, (s(v0 n, j) = s(u0 u, v0 n)) ↔ j = u0 u := fun j => by
        rw [Sym2.eq_swap (a := u0 u), Sym2.congr_right]
      simp_rw [this]; simp
    · simp only [h1, h2, or_self, if_false]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h3, _⟩ | ⟨h3, _⟩
      · exact h1 h3
      · exact h2 h3

lemma metric (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (u : Fin n) :
    IsMetricCost (splitCost c u) := by
  refine ⟨fun i j => hc.1 _ _, fun i => hc.2.1 _, fun i j k => hc.2.2 _ _ _⟩

lemma cost_sum (c x : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (u : Fin n)
    (hxu : x u u = 0) :
    (∑ i, ∑ j, splitCost c u i j * splitLP x u i j) = ∑ i, ∑ j, c i j * x i j := by
  have h1 : ∀ i j, splitCost c u i j * splitLP x u i j =
      halfAt u i * (halfAt u j * (c (proj u i) (proj u j) * x (proj u i) (proj u j))) := by
    intro i j
    rw [splitLP_eq x u hxu, splitCost]
    unfold dlt
    split_ifs with h
    · obtain ⟨hi, hj⟩ := pair_eq_e0 u i j h
      rw [hi, hj, hc.2.1 u]; ring
    · ring
  simp_rw [h1, ← Finset.mul_sum]
  rw [sum_halfAt u (fun v => ∑ j, halfAt u j * (c v (proj u j) * x v (proj u j)))]
  apply Finset.sum_congr rfl
  intro v _
  exact sum_halfAt u (fun w => c v w * x v w)


noncomputable def F (x : Fin n → Fin n → ℝ) (u : Fin n) (i j : Fin (n + 1)) : ℝ :=
  halfAt u i * halfAt u j * x (proj u i) (proj u j)

lemma F_nonneg (x : Fin n → Fin n → ℝ) (hx0 : ∀ i j, 0 ≤ x i j) (u : Fin n)
    (i j : Fin (n + 1)) : 0 ≤ F x u i j :=
  mul_nonneg (mul_nonneg (halfAt_nonneg u i) (halfAt_nonneg u j)) (hx0 _ _)

lemma row_F (x : Fin n → Fin n → ℝ) (hdeg : ∀ v, ∑ w, x v w = 2) (u : Fin n)
    (i : Fin (n + 1)) : (∑ j, F x u i j) = 2 * halfAt u i := by
  unfold F
  have : ∀ j, halfAt u i * halfAt u j * x (proj u i) (proj u j) =
      halfAt u i * (halfAt u j * x (proj u i) (proj u j)) := fun j => by ring
  simp_rw [this, ← Finset.mul_sum]
  rw [sum_halfAt u (fun w => x (proj u i) w), hdeg]; ring

/-- Cut bound when exactly one of the two copies lies in `S`. -/
lemma cut_one (x : Fin n → Fin n → ℝ) (hxs : ∀ i j, x i j = x j i) (hxd : ∀ v, x v v = 0)
    (hx0 : ∀ i j, 0 ≤ x i j) (hdeg : ∀ v, ∑ w, x v w = 2) (u : Fin n)
    (S : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hpa : proj u a = u) (hpb : proj u b = u) (hha : halfAt u a = 1 / 2)
    (hhb : halfAt u b = 1 / 2) (hdab : dlt u a b = 1) (ha : a ∈ S) (hb : b ∉ S) :
    2 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, splitLP x u i j := by
  have hxu := hxd u
  simp_rw [splitLP_eq x u hxu]
  simp_rw [Finset.sum_add_distrib]
  have hbc : b ∈ Sᶜ := Finset.mem_compl.mpr hb
  -- delta part ≥ 1
  have hd : 1 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, dlt u i j := by
    calc (1 : ℝ) = dlt u a b := hdab.symm
      _ ≤ ∑ j ∈ Sᶜ, dlt u a j :=
          Finset.single_le_sum (f := fun j => dlt u a j) (fun j _ => dlt_nonneg u a j) hbc
      _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, dlt u i j :=
          Finset.single_le_sum (f := fun i => ∑ j ∈ Sᶜ, dlt u i j)
            (fun i _ => Finset.sum_nonneg (fun j _ => dlt_nonneg u i j)) ha
  -- F part ≥ 1
  have hFsym : ∀ i, F x u i b = F x u a i := by
    intro i; unfold F; rw [hpa, hpb, hha, hhb, hxs]; ring
  have hF : 1 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, F x u i j := by
    rw [← Finset.add_sum_erase S _ ha]
    have h2 : ∑ i ∈ S.erase a, F x u a i ≤ ∑ i ∈ S.erase a, ∑ j ∈ Sᶜ, F x u i j := by
      apply Finset.sum_le_sum
      intro i _
      rw [← hFsym i]
      exact Finset.single_le_sum (f := fun j => F x u i j)
        (fun j _ => F_nonneg x hx0 u i j) hbc
    have h3 : ∑ i ∈ S.erase a, F x u a i = ∑ i ∈ S, F x u a i - F x u a a := by
      rw [← Finset.add_sum_erase S _ ha]; ring
    have h4 : F x u a a = 0 := by unfold F; rw [hpa, hxu, mul_zero]
    have h5 : ∑ j ∈ Sᶜ, F x u a j + ∑ i ∈ S, F x u a i = 2 * halfAt u a := by
      rw [add_comm, Finset.sum_add_sum_compl, row_F x hdeg u a]
    rw [hha] at h5
    linarith
  unfold F at hF
  linarith

/-- Cut bound when both or neither copy lies in `S`. -/
lemma cut_both (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) (u : Fin n)
    (S : Finset (Fin (n + 1))) (hS : S.Nonempty) (hSu : S ≠ univ)
    (hiff : u0 u ∈ S ↔ v0 n ∈ S) :
    2 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, splitLP x u i j := by
  have hxu := hx.2.1 u
  set S' : Finset (Fin n) := univ.filter (fun w => Fin.castSucc w ∈ S) with hS'
  have hmem : ∀ i, i ∈ S ↔ proj u i ∈ S' := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [proj_last, hS', mem_filter]
      simp only [mem_univ, true_and]
      exact (hiff.symm.trans (by rfl)).symm.symm.trans (by simp [u0, v0]) |>.symm.symm
    | cast w => rw [proj_castSucc, hS', mem_filter]; simp
  have hcross : ∀ i j, i ∈ S → j ∉ S → dlt u i j = 0 := by
    intro i j hi hj
    unfold dlt
    rw [if_neg]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hj (hiff.mp hi)
    · exact hj (hiff.mpr hi)
  have heq : ∑ i ∈ S, ∑ j ∈ Sᶜ, splitLP x u i j =
      ∑ i, halfAt u i * (if proj u i ∈ S' then
        ∑ j, halfAt u j * (if proj u j ∈ S' then 0 else x (proj u i) (proj u j)) else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => i ∈ S)]
    rw [Finset.sum_eq_zero (s := univ.filter (fun i => ¬ i ∈ S)), add_zero]
    · rw [Finset.filter_mem_eq_inter, univ_inter]
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos ((hmem i).mp hi), Finset.mul_sum]
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => j ∈ S)]
      rw [Finset.sum_eq_zero (s := univ.filter (fun j => j ∈ S)), zero_add]
      · have : univ.filter (fun j => ¬ j ∈ S) = Sᶜ := by ext; simp
        rw [this]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ∉ S := Finset.mem_compl.mp hj
        rw [if_neg (fun h => hj' ((hmem j).mpr h)), splitLP_eq x u hxu, hcross i j hi hj']
        ring
      · intro j hj
        rw [mem_filter] at hj
        rw [if_pos ((hmem j).mp hj.2)]; ring
    · intro i hi
      rw [mem_filter] at hi
      rw [if_neg (fun h => hi.2 ((hmem i).mpr h)), mul_zero]
  rw [heq, sum_halfAt u (fun v => if v ∈ S' then
        ∑ j, halfAt u j * (if proj u j ∈ S' then 0 else x v (proj u j)) else 0)]
  have h2 : ∀ v, (if v ∈ S' then
        ∑ j, halfAt u j * (if proj u j ∈ S' then 0 else x v (proj u j)) else 0) =
      if v ∈ S' then ∑ w ∈ S'ᶜ, x v w else 0 := by
    intro v
    split_ifs
    · rw [sum_halfAt u (fun w => if w ∈ S' then 0 else x v w)]
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun w => w ∈ S')]
      rw [Finset.sum_eq_zero (s := univ.filter (fun w => w ∈ S')), zero_add]
      · have : univ.filter (fun w => ¬ w ∈ S') = S'ᶜ := by ext; simp
        rw [this]
        apply Finset.sum_congr rfl
        intro w hw
        rw [if_neg (Finset.mem_compl.mp hw)]
      · intro w hw; rw [mem_filter] at hw; rw [if_pos hw.2]
    · rfl
  simp_rw [h2]
  rw [Finset.sum_ite_mem, univ_inter]
  apply hx.2.2.2.2.2 S'
  · obtain ⟨i, hi⟩ := hS
    exact ⟨proj u i, (hmem i).mp hi⟩
  · intro h
    apply hSu
    ext i
    simp only [mem_univ, iff_true]
    rw [hmem i, h]; exact mem_univ _

lemma heldKarp (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) (u : Fin n) :
    IsHeldKarp (splitLP x u) := by
  obtain ⟨hxs, hxd, hx0, hx1, hdeg, hcut⟩ := hx
  have hxu := hxd u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    unfold splitLP
    rw [Sym2.eq_swap (a := i), hxs (proj u i)]
    ring_nf
  · intro i
    rw [splitLP_eq x u hxu, hxd]
    unfold dlt
    rw [if_neg]
    · ring
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact u0_ne_v0 u (h1.symm.trans h2)
      · exact u0_ne_v0 u (h2.symm.trans h1)
  · intro i j
    rw [splitLP_eq x u hxu]
    exact add_nonneg (F_nonneg x hx0 u i j) (dlt_nonneg u i j)
  · intro i j
    unfold splitLP
    split_ifs
    · exact le_rfl
    · have := halfAt_le_one u i
      have := halfAt_le_one u j
      have := halfAt_nonneg u i
      have := halfAt_nonneg u j
      have := hx0 (proj u i) (proj u j)
      have := hx1 (proj u i) (proj u j)
      calc halfAt u i * halfAt u j * x (proj u i) (proj u j) ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by norm_num
  · intro i
    simp_rw [splitLP_eq x u hxu, Finset.sum_add_distrib]
    have := row_F x hdeg u i
    unfold F at this
    rw [this, sum_dlt]
    unfold halfAt
    split_ifs <;> norm_num
  · intro S hS hSu
    by_cases hiff : (u0 u ∈ S ↔ v0 n ∈ S)
    · exact cut_both x ⟨hxs, hxd, hx0, hx1, hdeg, hcut⟩ u S hS hSu hiff
    · have hd1 : dlt u (u0 u) (v0 n) = 1 := by simp [dlt]
      have hd2 : dlt u (v0 n) (u0 u) = 1 := by simp [dlt, Sym2.eq_swap]
      by_cases ha : u0 u ∈ S
      · have hb : v0 n ∉ S := fun hb => hiff ⟨fun _ => hb, fun _ => ha⟩
        exact cut_one x hxs hxd hx0 hdeg u S (u0 u) (v0 n) (proj_u0 u) (proj_v0 u)
          (halfAt_u0 u) (halfAt_v0 u) hd1 ha hb
      · have hb : v0 n ∈ S := by
          by_contra hb; exact hiff ⟨fun h => absurd h ha, fun h => absurd h hb⟩
        exact cut_one x hxs hxd hx0 hdeg u S (v0 n) (u0 u) (proj_v0 u) (proj_u0 u)
          (halfAt_v0 u) (halfAt_u0 u) hd2 hb ha

lemma tspOpt_le_tour {N : ℕ} (c : Fin N → Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    tspOpt c ≤ tourCost c π := by
  have hset : {t : ℝ | ∃ π : Equiv.Perm (Fin N), t = tourCost c π} =
      Set.range (tourCost c) := by
    ext t; simp [eq_comm]
  unfold tspOpt
  rw [hset]
  exact csInf_le (Set.toFinite _).bddBelow ⟨π, rfl⟩

lemma tspOpt_attained {N : ℕ} (c : Fin N → Fin N → ℝ) :
    ∃ π : Equiv.Perm (Fin N), tspOpt c = tourCost c π := by
  have hset : {t : ℝ | ∃ π : Equiv.Perm (Fin N), t = tourCost c π} =
      Set.range (tourCost c) := by
    ext t; simp [eq_comm]
  unfold tspOpt
  rw [hset]
  obtain ⟨π, hπ⟩ := (Set.range_nonempty (tourCost c)).csInf_mem (Set.toFinite _)
  exact ⟨π, hπ.symm⟩

lemma tour_rotate {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (d : Fin (m + 1)) :
    tourCost c (π * Equiv.addRight d) = tourCost c π := by
  unfold tourCost
  simp only [Equiv.Perm.mul_apply, Equiv.coe_addRight, finRotate_succ_apply]
  have : ∀ i : Fin (m + 1), c (π (i + d)) (π (i + 1 + d)) =
      (fun j => c (π j) (π (j + 1))) (Equiv.addRight d i) := by
    intro i; simp only [Equiv.coe_addRight]; rw [add_right_comm]
  simp_rw [this]
  exact Equiv.sum_comp (Equiv.addRight d) (fun j => c (π j) (π (j + 1)))

lemma finRotate_castSucc {k : ℕ} (i : Fin k) :
    finRotate (k + 1) (Fin.castSucc i) = i.succ := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
  simp

/-- Cost of a split tour whose last position holds `v₀` and which otherwise follows `π`. -/
lemma split_tour_cost {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (u : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 2))) (π : Equiv.Perm (Fin (m + 1)))
    (hσl : σ (Fin.last (m + 1)) = Fin.last (m + 1))
    (hσc : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (π i)) :
    tourCost (splitCost c u) σ + c (π (Fin.last m)) (π 0) =
      tourCost c π + c (π (Fin.last m)) u + c u (π 0) := by
  unfold tourCost
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc (f := fun i => c (π i) (π (finRotate (m + 1) i)))]
  simp only [finRotate_castSucc, finRotate_last, Fin.succ_last, hσl, hσc]
  have h0 : (0 : Fin (m + 2)) = Fin.castSucc 0 := rfl
  rw [h0, hσc]
  have hs : ∀ j : Fin m, (Fin.castSucc j).succ = Fin.castSucc j.succ := fun j => rfl
  simp only [hs, hσc, splitCost, proj_castSucc, proj_last]
  have hr : ∀ j : Fin m, finRotate (m + 1) (Fin.castSucc j) = j.succ := fun j =>
    finRotate_castSucc j
  try simp only [hr]
  ring

lemma tspOpt_split {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (hc : IsMetricCost c)
    (u : Fin (m + 1)) : tspOpt (splitCost c u) = tspOpt c := by
  apply le_antisymm
  · -- insert `v₀` after `u` in an optimal tour
    obtain ⟨π, hπ⟩ := tspOpt_attained c
    set d : Fin (m + 1) := π.symm u - Fin.last m
    set π₁ := π * Equiv.addRight d
    have hπ₁ : π₁ (Fin.last m) = u := by
      simp [π₁, d]
    let σ : Equiv.Perm (Fin (m + 2)) :=
      finSuccEquivLast.trans ((Equiv.optionCongr π₁).trans finSuccEquivLast.symm)
    have hσl : σ (Fin.last (m + 1)) = Fin.last (m + 1) := by
      simp [σ, finSuccEquivLast_last]
    have hσc : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (π₁ i) := by
      intro i; simp [σ, finSuccEquivLast_castSucc, finSuccEquivLast_symm_some]
    have h := split_tour_cost c u σ π₁ hσl hσc
    rw [hπ₁, hc.2.1 u, tour_rotate] at h
    rw [hπ]
    calc tspOpt (splitCost c u) ≤ tourCost (splitCost c u) σ := tspOpt_le_tour _ σ
      _ = tourCost c π := by linarith
  · -- shortcut `v₀` out of an optimal split tour
    obtain ⟨σ, hσ⟩ := tspOpt_attained (splitCost c u)
    set d : Fin (m + 2) := σ.symm (Fin.last (m + 1)) - Fin.last (m + 1)
    set σ₁ := σ * Equiv.addRight d
    have hσ₁ : σ₁ (Fin.last (m + 1)) = Fin.last (m + 1) := by
      simp [σ₁, d]
    have hne : ∀ i : Fin (m + 1), σ₁ (Fin.castSucc i) ≠ Fin.last (m + 1) := by
      intro i h
      rw [← hσ₁] at h
      exact Fin.castSucc_ne_last i (σ₁.injective h)
    let f : Fin (m + 1) → Fin (m + 1) := fun i => proj u (σ₁ (Fin.castSucc i))
    have hf : ∀ i, σ₁ (Fin.castSucc i) = Fin.castSucc (f i) := by
      intro i
      obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr (hne i)
      simp only [f, ← hj, proj_castSucc]
    have hfinj : Function.Injective f := by
      intro i j h
      have : σ₁ (Fin.castSucc i) = σ₁ (Fin.castSucc j) := by rw [hf, hf, h]
      exact Fin.castSucc_injective _ (σ₁.injective this)
    let π : Equiv.Perm (Fin (m + 1)) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
    have h := split_tour_cost c u σ₁ π hσ₁ (fun i => hf i)
    rw [tour_rotate] at h
    have htri : c (π (Fin.last m)) (π 0) ≤ c (π (Fin.last m)) u + c u (π 0) := hc.2.2 _ _ _
    rw [hσ]
    calc tspOpt c ≤ tourCost c π := tspOpt_le_tour c π
      _ ≤ tourCost (splitCost c u) σ := by linarith

end NodeSplitAux

theorem solution (n : ℕ) (hn : 3 ≤ n)
    (c x : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (hx : IsHeldKarp x)
    (hopt : (1 / 2) * (∑ i, ∑ j, c i j * x i j) = hkValue c)
    (u : Fin n) :
    IsMetricCost (splitCost c u) ∧
    IsHeldKarp (splitLP x u) ∧
    splitLP x u (u0 u) (v0 n) = 1 ∧
    (∑ i, ∑ j, splitCost c u i j * splitLP x u i j) =
      (∑ i, ∑ j, c i j * x i j) ∧
    tspOpt (splitCost c u) = tspOpt c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨NodeSplitAux.metric c hc u, NodeSplitAux.heldKarp x hx u, ?_,
    NodeSplitAux.cost_sum c x hc u (hx.2.1 u), NodeSplitAux.tspOpt_split c hc u⟩
  simp [splitLP]
