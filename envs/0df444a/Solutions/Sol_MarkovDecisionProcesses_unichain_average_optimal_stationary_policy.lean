-- Prove2me | solution 1 for MarkovDecisionProcesses.unichain_average_optimal_stationary_policy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T02:06:30.986863+00:00
-- url     : https://prove2.me/submissions/8277a6cf-d5df-4725-b158-e937a3a54c85

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward

set_option autoImplicit false

open MarkovDecisionProcesses in
theorem p016_acc_closed {S : Type*} {P : S → S → ℝ} {T : S → Prop}
    (hT : ∀ i j, T i → 0 < P i j → T j) {i j : S} (hi : T i) (h : Accessible P i j) : T j := by
  unfold Accessible at h
  induction h with
  | refl => exact hi
  | tail _ hbc ih => exact hT _ _ ih hbc

open MarkovDecisionProcesses in
theorem p016_acc_transfer {S : Type*} {P Q : S → S → ℝ} {T : S → Prop}
    (hT : ∀ i j, T i → 0 < P i j → T j) (hPQ : ∀ i, T i → ∀ j, P i j = Q i j)
    {i j : S} (hi : T i) (h : Accessible P i j) : Accessible Q i j := by
  unfold Accessible at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact ih.tail (by rw [← hPQ _ (p016_acc_closed hT hi hab)]; exact hbc)

open MarkovDecisionProcesses in
theorem p016_exists_recurrent {S : Type*} [Fintype S] (P : S → S → ℝ) (i : S) :
    ∃ j, Accessible P i j ∧ IsRecurrent P j := by
  classical
  let acc : S → Finset S := fun x => Finset.univ.filter (fun y => Accessible P x y)
  have hi : i ∈ acc i := by
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  obtain ⟨j, hj, hmin⟩ := (acc i).exists_min_image (fun x => (acc x).card) ⟨i, hi⟩
  have hij : Accessible P i j := by
    simpa only [acc, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  refine ⟨j, hij, ?_⟩
  intro k hjk
  have hsub : acc k ⊆ acc j := by
    intro y hy
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact Relation.ReflTransGen.trans hjk hy
  have hk : k ∈ acc i := by
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.trans hij hjk
  have hcard := hmin k hk
  have heq : acc k = acc j := Finset.eq_of_subset_of_card_le hsub hcard
  have hjj : j ∈ acc j := by
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  rw [← heq] at hjj
  simpa only [acc, Finset.mem_filter, Finset.mem_univ, true_and] using hjj

open MarkovDecisionProcesses in
theorem p016_closed_mem_recurrent {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hU : IsUnichainMatrix P) {T : S → Prop} (hT : ∀ i j, T i → 0 < P i j → T j)
    {i s0 : S} (hi : T i) (hs0 : IsRecurrent P s0) : T s0 := by
  obtain ⟨j, hij, hj⟩ := p016_exists_recurrent P i
  exact p016_acc_closed hT (p016_acc_closed hT hi hij) (hU j s0 hj hs0)

theorem p016_min_principle {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {u : S → ℝ} {s : S}
    (hmin : ∀ j, u s ≤ u j) (hle : ∑ j, P s j * u j ≤ u s) :
    ∀ j, 0 < P s j → u j = u s := by
  have hnn : ∀ j ∈ (Finset.univ : Finset S), 0 ≤ P s j * (u j - u s) :=
    fun j _ => mul_nonneg (hP0 s j) (sub_nonneg.2 (hmin j))
  have hsum : ∑ j, P s j * (u j - u s) = 0 := by
    have h1 : ∑ j, P s j * (u j - u s) = ∑ j, P s j * u j - u s := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1 s, one_mul]
    have hge : 0 ≤ ∑ j, P s j * (u j - u s) := Finset.sum_nonneg hnn
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
  intro j hj
  have := hz j (Finset.mem_univ j)
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

theorem p016_avg_ge {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {u : S → ℝ} {c : ℝ} (s : S)
    (hmin : ∀ j, c ≤ u j) : c ≤ ∑ j, P s j * u j := by
  have : ∑ j, P s j * c ≤ ∑ j, P s j * u j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmin j) (hP0 s j))
  rwa [← Finset.sum_mul, hP1 s, one_mul] at this

theorem p016_avg_ge_min {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {u : S → ℝ} {s : S}
    (hmin : ∀ j, u s ≤ u j) : u s ≤ ∑ j, P s j * u j :=
  p016_avg_ge hP0 hP1 s hmin

open MarkovDecisionProcesses in
theorem p016_poisson {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hU : IsUnichainMatrix P)
    (r : S → ℝ) : ∃ (g : ℝ) (h : S → ℝ), ∀ s, g + h s = r s + ∑ j, P s j * h j := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, 0, fun s => (IsEmpty.false s).elim⟩
  let L : (ℝ × (S → ℝ)) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun p s => p.1 + p.2 s - ∑ j, P s j * p.2 j
      map_add' := by
        intro p q; ext s
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c p; ext s
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show ∑ j, P s j * (c * p.2 j) = c * ∑ j, P s j * p.2 j by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)]
        ring }
  have hL : ∀ p : ℝ × (S → ℝ), ∀ s, L p s = p.1 + p.2 s - ∑ j, P s j * p.2 j := fun _ _ => rfl
  have hker : LinearMap.ker L ≤ Submodule.span ℝ {((0:ℝ), (fun _ : S => (1:ℝ)))} := by
    intro p hp
    rw [LinearMap.mem_ker] at hp
    have hp' : ∀ s, p.1 + p.2 s = ∑ j, P s j * p.2 j := by
      intro s; have := congrFun hp s; rw [hL] at this; simp only [Pi.zero_apply] at this; linarith
    obtain ⟨s1, hs1⟩ := Finite.exists_min p.2
    obtain ⟨s2, hs2⟩ := Finite.exists_max p.2
    have hg1 : 0 ≤ p.1 := by
      have := p016_avg_ge_min hP0 hP1 hs1; have := hp' s1; linarith
    have hneg : ∀ i, ∑ j, P i j * (fun k => - p.2 k) j = - ∑ j, P i j * p.2 j := by
      intro i; simp only [mul_neg, Finset.sum_neg_distrib]
    have hg2 : p.1 ≤ 0 := by
      have h1 := p016_avg_ge_min hP0 hP1 (u := fun k => - p.2 k) (s := s2)
        (fun j => by simp only [neg_le_neg_iff]; exact hs2 j)
      rw [hneg] at h1
      have := hp' s2; linarith
    have hg : p.1 = 0 := le_antisymm hg2 hg1
    have hTmin : ∀ i j, p.2 i = p.2 s1 → 0 < P i j → p.2 j = p.2 s1 := by
      intro i j hi hij
      have hmin' : ∀ k, p.2 i ≤ p.2 k := fun k => hi ▸ hs1 k
      have := p016_min_principle hP0 hP1 hmin' (by have := hp' i; linarith) j hij
      rw [this, hi]
    have hTmax : ∀ i j, p.2 i = p.2 s2 → 0 < P i j → p.2 j = p.2 s2 := by
      intro i j hi hij
      have hmin' : ∀ k, (fun k => - p.2 k) i ≤ (fun k => - p.2 k) k := fun k => by
        simp only [neg_le_neg_iff]; rw [hi]; exact hs2 k
      have := p016_min_principle hP0 hP1 hmin'
        (by rw [hneg]; have := hp' i; linarith) j hij
      simp only [neg_inj] at this; rw [this, hi]
    obtain ⟨t, -, ht⟩ := p016_exists_recurrent P s1
    have h1 := p016_closed_mem_recurrent hU (T := fun i => p.2 i = p.2 s1) hTmin rfl ht
    have h2 := p016_closed_mem_recurrent hU (T := fun i => p.2 i = p.2 s2) hTmax rfl ht
    have hconst : ∀ k, p.2 k = p.2 s1 := fun k =>
      le_antisymm (by have := hs2 k; linarith) (hs1 k)
    rw [Submodule.mem_span_singleton]
    refine ⟨p.2 s1, ?_⟩
    ext
    · simp [hg]
    · simp [hconst]
  have hne : ((0:ℝ), (fun _ : S => (1:ℝ))) ≠ (0 : ℝ × (S → ℝ)) := by
    intro h
    obtain ⟨s⟩ := hS
    have := congrFun (congrArg Prod.snd h) s
    simp at this
  have hfk : Module.finrank ℝ (LinearMap.ker L) ≤ 1 := by
    calc Module.finrank ℝ (LinearMap.ker L)
        ≤ Module.finrank ℝ (Submodule.span ℝ {((0:ℝ), (fun _ : S => (1:ℝ)))}) :=
          Submodule.finrank_mono hker
      _ = 1 := finrank_span_singleton hne
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hrn
  have hle := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have htop : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨p, hp⟩ : r ∈ LinearMap.range L := by rw [htop]; exact Submodule.mem_top
  refine ⟨p.1, p.2, fun s => ?_⟩
  have := congrFun hp s
  rw [hL] at this
  linarith

open MarkovDecisionProcesses in
theorem p016_exists_solution {S A : Type*} [Fintype S] [Fintype A] (M : StationaryMDP S A)
    (hM : IsUnichain M) : ∃ (g : ℝ) (h : S → ℝ),
      (∀ s, ∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s) ∧
      (∀ s, ∃ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j = g + h s) := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, 0, fun s => (IsEmpty.false s).elim, fun s => (IsEmpty.false s).elim⟩
  have hP0 : ∀ d : S → A, ∀ i j, 0 ≤ transMatrix M d i j := fun d i j => M.trans_nonneg _ _ _
  have hP1 : ∀ d : S → A, ∀ i, ∑ j, transMatrix M d i j = 1 := fun d i => M.trans_sum _ _
  have hpois : ∀ d : S → A, ∃ (g : ℝ) (h : S → ℝ), (∀ s, d s ∈ M.admissible s) →
      ∀ s, g + h s = M.reward s (d s) + ∑ j, M.trans s (d s) j * h j := by
    intro d
    by_cases hd : ∀ s, d s ∈ M.admissible s
    · obtain ⟨g, h, hgh⟩ := p016_poisson (hP0 d) (hP1 d) (hM d hd) (fun s => M.reward s (d s))
      exact ⟨g, h, fun _ => hgh⟩
    · exact ⟨0, 0, fun h => (hd h).elim⟩
  choose G H hGH using hpois
  let D : Finset (S → A) := Finset.univ.filter (fun d => ∀ s, d s ∈ M.admissible s)
  let d0 : S → A := fun s => (M.admissible_nonempty s).choose
  have hd0 : d0 ∈ D := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun s => (M.admissible_nonempty s).choose_spec
  let gs : ℝ := D.sup' ⟨d0, hd0⟩ G
  obtain ⟨d1, hd1D, hd1G⟩ := Finset.exists_mem_eq_sup' ⟨d0, hd0⟩ G
  obtain ⟨s0, -, hs0⟩ := p016_exists_recurrent (transMatrix M d1) hS.some
  let D0 : Finset (S → A) := D.filter (fun d => G d = gs ∧ IsRecurrent (transMatrix M d) s0)
  have hd1 : d1 ∈ D0 := by
    simp only [D0, Finset.mem_filter]
    exact ⟨hd1D, hd1G.symm, hs0⟩
  let Φ : (S → A) → ℝ := fun d => ∑ s, (H d s - H d s0)
  obtain ⟨d, hdD0, hdmax⟩ := D0.exists_max_image Φ ⟨d1, hd1⟩
  simp only [D0, D, Finset.mem_filter, Finset.mem_univ, true_and] at hdD0
  obtain ⟨hdadm, hdG, hdrec⟩ := hdD0
  have hpd := hGH d hdadm
  rw [hdG] at hpd
  refine ⟨gs, H d, ?_, fun s => ⟨d s, hdadm s, (hpd s).symm⟩⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨sv, av, hav, hviol⟩ := hcon
  let viol : S → A → Prop := fun s a =>
    a ∈ M.admissible s ∧ gs + H d s < M.reward s a + ∑ j, M.trans s a j * H d j
  let d' : S → A := fun s => if hs : ∃ a, viol s a then hs.choose else d s
  have hd'viol : ∀ s, (∃ a, viol s a) → viol s (d' s) := by
    intro s hs; simp only [d', dif_pos hs]; exact hs.choose_spec
  have hd'eq : ∀ s, ¬ (∃ a, viol s a) → d' s = d s := by
    intro s hs; simp only [d', dif_neg hs]
  have hd'adm : ∀ s, d' s ∈ M.admissible s := by
    intro s
    by_cases hs : ∃ a, viol s a
    · exact (hd'viol s hs).1
    · rw [hd'eq s hs]; exact hdadm s
  let δ : S → ℝ := fun s =>
    M.reward s (d' s) + ∑ j, M.trans s (d' s) j * H d j - gs - H d s
  have hδpos : ∀ s, (∃ a, viol s a) → 0 < δ s := by
    intro s hs; have := (hd'viol s hs).2; simp only [δ]; linarith
  have hδz : ∀ s, ¬ (∃ a, viol s a) → δ s = 0 := by
    intro s hs; simp only [δ]; rw [hd'eq s hs]; have := hpd s; linarith
  have hδnn : ∀ s, 0 ≤ δ s := by
    intro s; by_cases hs : ∃ a, viol s a
    · exact (hδpos s hs).le
    · exact (hδz s hs).ge
  have hsv : ∃ a, viol sv a := ⟨av, hav, hviol⟩
  have hpd' := hGH d' hd'adm
  have hd'D : d' ∈ D := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]; exact hd'adm
  have hG'le : G d' ≤ gs := Finset.le_sup' G hd'D
  let u : S → ℝ := fun s => H d' s - H d s
  let P' := transMatrix M d'
  have hu : ∀ s, (G d' - gs) + u s = δ s + ∑ j, P' s j * u j := by
    intro s
    have e1 := hpd' s
    have e2 : ∑ j, P' s j * u j =
        ∑ j, M.trans s (d' s) j * H d' j - ∑ j, M.trans s (d' s) j * H d j := by
      simp only [P', u, transMatrix, mul_sub, Finset.sum_sub_distrib]
    rw [e2]; simp only [δ, u]; linarith
  obtain ⟨s1, hs1⟩ := Finite.exists_min u
  have hGge : gs ≤ G d' := by
    have := hu s1
    have := p016_avg_ge_min (hP0 d') (hP1 d') hs1
    have := hδnn s1
    linarith
  have hGeq : G d' = gs := le_antisymm hG'le hGge
  have hu' : ∀ s, u s = δ s + ∑ j, P' s j * u j := by
    intro s; have := hu s; rw [hGeq] at this; linarith
  let T : S → Prop := fun i => u i = u s1
  have hTδ : ∀ i, T i → δ i = 0 := by
    intro i hi
    have h1 := hu' i
    have h2 := p016_avg_ge (hP0 d') (hP1 d') (u := u) i hs1
    have h3 := hδnn i
    have h4 : u i = u s1 := hi
    linarith
  have hTd : ∀ i, T i → d' i = d i := by
    intro i hi
    by_cases hs : ∃ a, viol i a
    · exact absurd (hTδ i hi) (hδpos i hs).ne'
    · exact hd'eq i hs
  have hTclosed' : ∀ i j, T i → 0 < P' i j → T j := by
    intro i j hi hij
    have h4 : u i = u s1 := hi
    have hmin' : ∀ k, u i ≤ u k := fun k => h4.trans_le (hs1 k)
    have := p016_min_principle (hP0 d') (hP1 d') hmin'
      (by have := hu' i; have := hTδ i hi; linarith) j hij
    show u j = u s1
    rw [this]; exact hi
  have hrows : ∀ i, T i → ∀ j, P' i j = transMatrix M d i j := by
    intro i hi j; simp only [P', transMatrix, hTd i hi]
  have hTclosed : ∀ i j, T i → 0 < transMatrix M d i j → T j := by
    intro i j hi hij; exact hTclosed' i j hi (by rw [hrows i hi]; exact hij)
  have hs0T : T s0 :=
    p016_closed_mem_recurrent (hM d hdadm) hTclosed (show T s1 from rfl) hdrec
  have hs0rec' : IsRecurrent P' s0 := by
    intro j hj
    have h1 : Accessible (transMatrix M d) s0 j := p016_acc_transfer hTclosed' hrows hs0T hj
    have h2 := hdrec j h1
    have hjT : T j := p016_acc_closed hTclosed' hs0T hj
    exact p016_acc_transfer hTclosed (fun i hi k => (hrows i hi k).symm) hjT h2
  have hd'D0 : d' ∈ D0 := by
    simp only [D0, D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hd'adm, hGeq, hs0rec'⟩
  have hmax := hdmax d' hd'D0
  have h0 : u s0 = u s1 := hs0T
  have hlt : Φ d < Φ d' := by
    show ∑ s, (H d s - H d s0) < ∑ s, (H d' s - H d' s0)
    apply Finset.sum_lt_sum
    · intro s _
      have := hs1 s
      simp only [u] at this h0
      linarith
    · refine ⟨sv, Finset.mem_univ _, ?_⟩
      have h1 := hu' sv
      have h2 := p016_avg_ge (hP0 d') (hP1 d') (u := u) sv hs1
      have h3 := hδpos sv hsv
      simp only [u] at h1 h2 h0
      linarith
  linarith

open MarkovDecisionProcesses in
theorem p016_tr_upper {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (g : ℝ) (h : S → ℝ) (m : ℝ) (hm : ∀ j, m ≤ h j)
    (hB : ∀ s, ∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s) :
    ∀ (N t : ℕ) (hist : List (S × A)) (s : S), totalReward π N t hist s ≤ N * g + h s - m := by
  intro N
  induction N with
  | zero =>
    intro t hist s
    simp only [totalReward, Nat.cast_zero, zero_mul, zero_add]
    linarith [hm s]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    calc ∑ a ∈ M.admissible s, π.q t hist s a *
          (M.reward s a + ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j)
        ≤ ∑ a ∈ M.admissible s, π.q t hist s a * (((k+1:ℕ):ℝ) * g + h s - m) := by
          apply Finset.sum_le_sum; intro a ha
          apply mul_le_mul_of_nonneg_left _ (π.nonneg t hist s a)
          have h1 : ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j
              ≤ ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m) :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (ih _ _ j) (M.trans_nonneg s a j))
          have h2 : ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m)
              = ((k:ℝ) * g - m) + ∑ j, M.trans s a j * h j := by
            have e : ∀ j, M.trans s a j * ((k:ℝ) * g + h j - m)
                = M.trans s a j * ((k:ℝ) * g - m) + M.trans s a j * h j := fun j => by ring
            simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, M.trans_sum, one_mul]
          have h3 := hB s a ha
          push_cast; linarith
      _ = ((k+1:ℕ):ℝ) * g + h s - m := by rw [← Finset.sum_mul, π.sum_one, one_mul]

open MarkovDecisionProcesses in
theorem p016_tr_lower {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (g : ℝ) (h : S → ℝ) (m : ℝ) (hm : ∀ j, h j ≤ m)
    (hB : ∀ (t : ℕ) (hist : List (S × A)) (s : S) (a : A), a ∈ M.admissible s →
      π.q t hist s a ≠ 0 → g + h s ≤ M.reward s a + ∑ j, M.trans s a j * h j) :
    ∀ (N t : ℕ) (hist : List (S × A)) (s : S), (N:ℝ) * g + h s - m ≤ totalReward π N t hist s := by
  intro N
  induction N with
  | zero =>
    intro t hist s
    simp only [totalReward, Nat.cast_zero, zero_mul, zero_add]
    linarith [hm s]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    calc ((k+1:ℕ):ℝ) * g + h s - m
        = ∑ a ∈ M.admissible s, π.q t hist s a * (((k+1:ℕ):ℝ) * g + h s - m) := by
          rw [← Finset.sum_mul, π.sum_one, one_mul]
      _ ≤ ∑ a ∈ M.admissible s, π.q t hist s a *
          (M.reward s a + ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j) := by
          apply Finset.sum_le_sum; intro a ha
          by_cases hq : π.q t hist s a = 0
          · rw [hq, zero_mul, zero_mul]
          apply mul_le_mul_of_nonneg_left _ (π.nonneg t hist s a)
          have h1 : ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m)
              ≤ ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (ih _ _ j) (M.trans_nonneg s a j))
          have h2 : ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m)
              = ((k:ℝ) * g - m) + ∑ j, M.trans s a j * h j := by
            have e : ∀ j, M.trans s a j * ((k:ℝ) * g + h j - m)
                = M.trans s a j * ((k:ℝ) * g - m) + M.trans s a j * h j := fun j => by ring
            simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, M.trans_sum, one_mul]
          have h3 := hB t hist s a ha hq
          push_cast; linarith

open MarkovDecisionProcesses in
theorem p016_gain_bounds {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) : ∃ R : ℝ, ∀ N : ℕ,
      -R ≤ totalReward π N 0 [] s / N ∧ totalReward π N 0 [] s / N ≤ R := by
  let R : ℝ := ∑ s, ∑ a, |M.reward s a|
  have hR : ∀ s a, |M.reward s a| ≤ R := by
    intro s a
    calc |M.reward s a| ≤ ∑ a, |M.reward s a| :=
          Finset.single_le_sum (f := fun a => |M.reward s a|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ a)
      _ ≤ R := Finset.single_le_sum (f := fun s => ∑ a, |M.reward s a|)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ s)
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hup := p016_tr_upper π R (fun _ => 0) 0 (fun _ => le_refl 0) (by
    intro s a _
    simp only [mul_zero, Finset.sum_const_zero, add_zero]
    exact (le_abs_self _).trans (hR s a))
  have hlo := p016_tr_lower π (-R) (fun _ => 0) 0 (fun _ => le_refl 0) (by
    intro t hist s a _ _
    simp only [mul_zero, Finset.sum_const_zero, add_zero]
    exact (neg_le_neg (hR s a)).trans (neg_abs_le _))
  refine ⟨R, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [hR0]
  · have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    have h1 := hup N 0 [] s
    have h2 := hlo N 0 [] s
    simp only [add_zero, sub_zero] at h1 h2
    constructor
    · rw [le_div_iff₀ hNpos]; linarith
    · rw [div_le_iff₀ hNpos]; linarith

open MarkovDecisionProcesses in
theorem p016_gainSup_le {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) (g C : ℝ)
    (hC : ∀ N : ℕ, totalReward π N 0 [] s ≤ N * g + C) : gainSup π s ≤ g := by
  obtain ⟨R, hR⟩ := p016_gain_bounds π s
  unfold gainSup
  have hv : Filter.Tendsto (fun N : ℕ => g + C / N) Filter.atTop (nhds g) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat C)
  calc Filter.limsup (fun N : ℕ => totalReward π N 0 [] s / N) Filter.atTop
      ≤ Filter.limsup (fun N : ℕ => g + C / N) Filter.atTop := by
        refine Filter.limsup_le_limsup ?_ ?_ ?_
        · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          have hNpos : (0:ℝ) < N := by exact_mod_cast hN
          rw [div_le_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']
          linarith [hC N]
        · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun N => (hR N).1)
        · exact hv.isBoundedUnder_le
    _ = g := hv.limsup_eq

open MarkovDecisionProcesses in
theorem p016_le_gainInf {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) (g C : ℝ)
    (hC : ∀ N : ℕ, (N:ℝ) * g - C ≤ totalReward π N 0 [] s) : g ≤ gainInf π s := by
  obtain ⟨R, hR⟩ := p016_gain_bounds π s
  unfold gainInf
  have hv : Filter.Tendsto (fun N : ℕ => g - C / N) Filter.atTop (nhds g) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat C)
  calc g = Filter.liminf (fun N : ℕ => g - C / N) Filter.atTop := hv.liminf_eq.symm
    _ ≤ Filter.liminf (fun N : ℕ => totalReward π N 0 [] s / N) Filter.atTop := by
        refine Filter.liminf_le_liminf ?_ ?_ ?_
        · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          have hNpos : (0:ℝ) < N := by exact_mod_cast hN
          rw [le_div_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ hNpos.ne']
          linarith [hC N]
        · exact hv.isBoundedUnder_ge
        · exact Filter.isCoboundedUnder_ge_of_le Filter.atTop (fun N => (hR N).2)

open MarkovDecisionProcesses in
theorem p016_inf_le_sup {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) : gainInf π s ≤ gainSup π s := by
  obtain ⟨R, hR⟩ := p016_gain_bounds π s
  exact Filter.liminf_le_limsup (Filter.isBoundedUnder_of ⟨R, fun N => (hR N).2⟩)
    (Filter.isBoundedUnder_of ⟨-R, fun N => (hR N).1⟩)

open MarkovDecisionProcesses in
theorem p016_residual_iff {S A : Type*} [Fintype S] [Fintype A] (M : StationaryMDP S A)
    (g : ℝ) (h : S → ℝ) (s : S) : optimalityResidual M g h s = 0 ↔
      ((∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s) ∧
       (∃ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j = g + h s)) := by
  unfold optimalityResidual
  constructor
  · intro h0
    refine ⟨fun a ha => ?_, ?_⟩
    · have := Finset.le_sup' (fun a => M.reward s a - g + ∑ j, M.trans s a j * h j - h s) ha
      rw [h0] at this; linarith
    · obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_sup' (M.admissible_nonempty s)
        (fun a => M.reward s a - g + ∑ j, M.trans s a j * h j - h s)
      refine ⟨a, ha, ?_⟩
      rw [h0] at hae; linarith
  · rintro ⟨h1, a, ha, hae⟩
    apply le_antisymm
    · apply Finset.sup'_le
      intro b hb; have := h1 b hb; linarith
    · apply Finset.le_sup'_of_le _ ha
      linarith

open MarkovDecisionProcesses in
theorem p016_bounds_of_improving {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    {M : StationaryMDP S A} (g : ℝ) (h : S → ℝ)
    (hres : ∀ s, optimalityResidual M g h s = 0) (d : S → A) (hd : IsImproving M h d) :
    (∀ (π : AvgHRPolicy M) (s : S), gainSup π s ≤ g) ∧
      (∀ s, g ≤ gainInf (stationaryPolicy M d (fun s => (hd s).1)) s) := by
  have hB : ∀ s, ∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s :=
    fun s => ((p016_residual_iff M g h s).1 (hres s)).1
  have hdeq : ∀ s, g + h s ≤ M.reward s (d s) + ∑ j, M.trans s (d s) j * h j := by
    intro s
    obtain ⟨a, ha, hae⟩ := ((p016_residual_iff M g h s).1 (hres s)).2
    rw [(hd s).2, ← hae]
    exact Finset.le_sup' (fun a => M.reward s a + ∑ j, M.trans s a j * h j) ha
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨fun _ s => (IsEmpty.false s).elim, fun s => (IsEmpty.false s).elim⟩
  obtain ⟨smin, hsmin⟩ := Finite.exists_min h
  obtain ⟨smax, hsmax⟩ := Finite.exists_max h
  constructor
  · intro π s
    apply p016_gainSup_le π s g (h s - h smin)
    intro N
    have := p016_tr_upper π g h (h smin) hsmin hB N 0 [] s
    linarith
  · intro s
    apply p016_le_gainInf _ s g (h smax - h s)
    intro N
    have := p016_tr_lower (stationaryPolicy M d (fun s => (hd s).1)) g h (h smax) hsmax
      (by
        intro t hist s' a ha hq
        have hads : a = d s' := by
          by_contra hne
          exact hq (by simp [stationaryPolicy, hne])
        subst hads; exact hdeq s') N 0 [] s
    linarith

open MarkovDecisionProcesses in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M) :
    (∃ (d : S → A) (hd : ∀ s, d s ∈ M.admissible s),
        IsAverageOptimal (stationaryPolicy M d hd)) ∧
    (∃ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) ∧
        ∀ s, optGainSup M s = gstar ∧ optGainInf M s = gstar) ∧
    (∀ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) →
        ∀ (d : S → A) (hd : IsImproving M hstar d),
          IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1))) := by
  have hc : ∀ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) →
      ∀ (d : S → A) (hd : IsImproving M hstar d),
        IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1)) := by
    intro g h hres d hd π s
    obtain ⟨h1, h2⟩ := p016_bounds_of_improving g h hres d hd
    exact (h1 π s).trans (h2 s)
  obtain ⟨g, h, hB, hex⟩ := p016_exists_solution M hM
  have hres : ∀ s, optimalityResidual M g h s = 0 :=
    fun s => (p016_residual_iff M g h s).2 ⟨hB s, hex s⟩
  have himp : ∀ s, ∃ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j =
      (M.admissible s).sup' (M.admissible_nonempty s)
        (fun a => M.reward s a + ∑ j, M.trans s a j * h j) := by
    intro s
    obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_sup' (M.admissible_nonempty s)
      (fun a => M.reward s a + ∑ j, M.trans s a j * h j)
    exact ⟨a, ha, hae.symm⟩
  choose d hdadm hdeq using himp
  have hdimp : IsImproving M h d := fun s => ⟨hdadm s, hdeq s⟩
  obtain ⟨h1, h2⟩ := p016_bounds_of_improving g h hres d hdimp
  refine ⟨⟨d, fun s => (hdimp s).1, hc g h hres d hdimp⟩, ⟨g, h, hres, fun s => ?_⟩, hc⟩
  have hne : Nonempty (AvgHRPolicy M) := ⟨stationaryPolicy M d (fun s => (hdimp s).1)⟩
  have hbS : BddAbove (Set.range fun π : AvgHRPolicy M => gainSup π s) :=
    ⟨g, by rintro _ ⟨π, rfl⟩; exact h1 π s⟩
  have hbI : BddAbove (Set.range fun π : AvgHRPolicy M => gainInf π s) :=
    ⟨g, by rintro _ ⟨π, rfl⟩; exact (p016_inf_le_sup π s).trans (h1 π s)⟩
  unfold optGainSup optGainInf
  constructor
  · apply le_antisymm
    · exact ciSup_le (fun π => h1 π s)
    · calc g ≤ gainInf (stationaryPolicy M d (fun s => (hdimp s).1)) s := h2 s
        _ ≤ gainSup (stationaryPolicy M d (fun s => (hdimp s).1)) s := p016_inf_le_sup _ s
        _ ≤ ⨆ π : AvgHRPolicy M, gainSup π s := le_ciSup hbS _
  · apply le_antisymm
    · exact ciSup_le (fun π => (p016_inf_le_sup π s).trans (h1 π s))
    · exact (h2 s).trans (le_ciSup hbI _)
