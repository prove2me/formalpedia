-- Prove2me | solution 1 for HeldWolfeCrowder.Assignment.optSet_dimension
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:01:54.497625+00:00
-- url     : https://prove2.me/submissions/e35e143a-b769-46e7-a2fc-6300234eb0b4

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting



namespace HeldWolfeCrowder.Assignment

section Gen
variable {α : Type*} [Fintype α] [DecidableEq α] (b : α → α → ℝ)

/-- reversed path weight: list x :: y :: l has edge y → x. -/
def hwcPW : List α → ℝ
  | x :: y :: l => b y x + hwcPW (y :: l)
  | _ => 0

lemma hwcPW_append (A B : List α) (s : α) :
    hwcPW b (A ++ s :: B) = hwcPW b (A ++ [s]) + hwcPW b (s :: B) := by
  induction A with
  | nil => simp [hwcPW]
  | cons x A ih =>
    cases A with
    | nil =>
      cases B <;> simp [hwcPW]
    | cons y A =>
      simp only [List.cons_append, hwcPW] at ih ⊢
      rw [ih]; ring

lemma hwc_swap_sum (ρ : Equiv.Perm α) (x y : α) (hxy : x ≠ y) (hx : ρ x = x) :
    ∑ t, b ((Equiv.swap x y * ρ) t) t
      = ∑ t, b (ρ t) t + b y x + b x (ρ.symm y) - b x x - b y (ρ.symm y) := by
  have e1 : ∀ g : α → α → ℝ, ∑ t, g (ρ t) t = ∑ u, g u (ρ.symm u) := by
    intro g
    rw [← Equiv.sum_comp ρ (fun u => g u (ρ.symm u))]
    simp
  have hxs : ρ.symm x = x := by rw [Equiv.symm_apply_eq]; exact hx.symm
  simp only [Equiv.Perm.coe_mul, Function.comp]
  rw [e1 (fun u t => b (Equiv.swap x y u) t), e1 (fun u t => b u t)]
  have : ∑ u, b (Equiv.swap x y u) (ρ.symm u) - ∑ u, b u (ρ.symm u)
      = (b (Equiv.swap x y x) (ρ.symm x) - b x (ρ.symm x))
        + (b (Equiv.swap x y y) (ρ.symm y) - b y (ρ.symm y)) := by
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_eq_add x y hxy
    intro u hu
    rw [Equiv.swap_apply_of_ne_of_ne hu.1 hu.2]; ring
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, hxs] at this
  linarith

lemma hwc_cycle (hb0 : ∀ t, b t t = 0) :
    ∀ (l : List α) (y : α), (y :: l).Nodup →
      ∑ t, b ((y :: l).formPerm t) t = hwcPW b (y :: l) + b y ((y :: l).getLast (List.cons_ne_nil _ _)) := by
  intro l
  induction l with
  | nil =>
    intro y _
    simp [hwcPW, hb0]
  | cons z l ih =>
    intro y hnd
    have hy : y ∉ z :: l := (List.nodup_cons.mp hnd).1
    have hnd' : (z :: l).Nodup := (List.nodup_cons.mp hnd).2
    have hyz : y ≠ z := fun h => hy (h ▸ List.mem_cons_self)
    rw [List.formPerm_cons_cons, hwc_swap_sum b _ y z hyz (List.formPerm_apply_of_notMem hy), ih z hnd']
    have hl : (z :: l).formPerm.symm z = (z :: l).getLast (List.cons_ne_nil _ _) := by
      rw [Equiv.symm_apply_eq]; simp
    rw [hl]
    have : (y :: z :: l).getLast (List.cons_ne_nil _ _) = (z :: l).getLast (List.cons_ne_nil _ _) :=
      List.getLast_cons _
    rw [this, hb0]
    simp only [hwcPW]; ring

theorem hwc_potential (hb0 : ∀ t, b t t = 0) (hperm : ∀ ρ : Equiv.Perm α, 0 ≤ ∑ t, b (ρ t) t) :
    ∃ π : α → ℝ, ∀ t s, π s ≤ π t + b t s := by
  classical
  set M : ℝ := ∑ u, ∑ v, |b u v| with hM
  have hM0 : ∀ u v, -M ≤ b u v := by
    intro u v
    have h1 : |b u v| ≤ ∑ v, |b u v| :=
      Finset.single_le_sum (f := fun v => |b u v|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    have h2 : ∑ v, |b u v| ≤ M :=
      Finset.single_le_sum (f := fun u => ∑ v, |b u v|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ u)
    linarith [neg_abs_le (b u v)]
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hlow : ∀ l : List α, -(l.length : ℝ) * M ≤ hwcPW b l := by
    intro l
    induction l with
    | nil => simp [hwcPW]
    | cons x l ih =>
      cases l with
      | nil => simp [hwcPW]; exact hMnn
      | cons y l =>
        simp only [hwcPW, List.length_cons] at ih ⊢
        push_cast at ih ⊢
        linarith [hM0 y x]
  let S : α → Set ℝ := fun s => {r | ∃ l : List α, (s :: l).Nodup ∧ r = hwcPW b (s :: l)}
  have hbdd : ∀ s, BddBelow (S s) := by
    intro s
    refine ⟨-(Fintype.card α : ℝ) * M, ?_⟩
    rintro r ⟨l, hl, rfl⟩
    have := hlow (s :: l)
    have hlen : ((s :: l).length : ℝ) ≤ Fintype.card α := by exact_mod_cast hl.length_le_card
    nlinarith
  have hne : ∀ s, (S s).Nonempty := fun s => ⟨_, [], by simp, rfl⟩
  refine ⟨fun s => sInf (S s), ?_⟩
  intro t s
  show sInf (S s) ≤ sInf (S t) + b t s
  rw [← sub_le_iff_le_add]
  apply le_csInf (hne t)
  rintro r ⟨l, hl, rfl⟩
  rw [sub_le_iff_le_add]
  by_cases hs : s ∈ t :: l
  · obtain ⟨A, B, hAB⟩ := List.append_of_mem hs
    have hndB : (s :: B).Nodup := by
      rw [hAB] at hl; exact (List.nodup_append.mp hl).2.1
    have h1 : sInf (S s) ≤ hwcPW b (s :: B) := csInf_le (hbdd s) ⟨B, hndB, rfl⟩
    have h2 : 0 ≤ hwcPW b (A ++ [s]) + b t s := by
      cases A with
      | nil =>
        simp at hAB
        rw [hAB.1]; simp [hwcPW, hb0]
      | cons x A =>
        simp only [List.cons_append, List.cons.injEq] at hAB
        obtain ⟨rfl, hAB2⟩ := hAB
        have hndc : (t :: (A ++ [s])).Nodup := by
          have : (t :: l).Nodup := hl
          rw [hAB2] at this
          have h3 : (t :: A ++ s :: B).Nodup := this
          have h4 : ((t :: A ++ [s]) ++ B).Nodup := by simpa using h3
          exact (List.nodup_append.mp h4).1
        have := hwc_cycle b hb0 (A ++ [s]) t hndc
        have hlast : (t :: (A ++ [s])).getLast (List.cons_ne_nil _ _) = s := by
          simp
        rw [hlast] at this
        have := hperm (t :: (A ++ [s])).formPerm
        simp only [List.cons_append]
        linarith
    rw [hAB, hwcPW_append]
    linarith
  · have hnd : (s :: t :: l).Nodup := List.nodup_cons.mpr ⟨hs, hl⟩
    have := csInf_le (hbdd s) ⟨t :: l, hnd, rfl⟩
    simp only [hwcPW] at this
    linarith

end Gen
section Main
variable {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)

lemma hwc_inf_le (π : Fin n → ℝ) (r s : Fin n) :
    Finset.univ.inf' ⟨r, Finset.mem_univ r⟩ (fun s => a s r - π s) ≤ a s r - π s :=
  Finset.inf'_le _ (Finset.mem_univ s)

lemma hwc_weak (π : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : w a π ≤ assignCost a σ := by
  unfold w assignCost
  have h1 : ∑ r, Finset.univ.inf' ⟨r, Finset.mem_univ r⟩ (fun s => a s r - π s)
      ≤ ∑ r, (a (σ r) r - π (σ r)) := Finset.sum_le_sum fun r _ => hwc_inf_le a π r (σ r)
  have h2 : ∑ r, π (σ r) = ∑ i, π i := Equiv.sum_comp σ π
  rw [Finset.sum_sub_distrib, h2] at h1
  linarith

/-- if σ r attains every minimum then w = cost σ -/
lemma hwc_w_eq (π : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (h : ∀ r s, a (σ r) r - π (σ r) ≤ a s r - π s) : w a π = assignCost a σ := by
  unfold w assignCost
  have h1 : ∀ r, Finset.univ.inf' ⟨r, Finset.mem_univ r⟩ (fun s => a s r - π s)
      = a (σ r) r - π (σ r) := by
    intro r
    apply le_antisymm (hwc_inf_le a π r (σ r))
    exact Finset.le_inf' _ _ fun s _ => h r s
  simp only [h1]
  have h2 : ∑ r, π (σ r) = ∑ i, π i := Equiv.sum_comp σ π
  rw [Finset.sum_sub_distrib, h2]; ring

lemma hwc_cost_comp (σ ρ : Equiv.Perm (Fin n)) :
    ∑ t, (a t (σ.symm (ρ t)) - a (ρ t) (σ.symm (ρ t))) = assignCost a (σ.trans ρ.symm) - assignCost a σ := by
  rw [Finset.sum_sub_distrib]
  unfold assignCost
  congr 1
  · rw [← Equiv.sum_comp (σ.trans ρ.symm) (fun t => a t (σ.symm (ρ t)))]
    simp
  · rw [Equiv.sum_comp ρ (fun u => a u (σ.symm u)), ← Equiv.sum_comp σ (fun u => a u (σ.symm u))]
    simp

lemma hwc_strong (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ) :
    ∃ π : Fin n → ℝ, ∀ r s, a (σ r) r - π (σ r) ≤ a s r - π s := by
  obtain ⟨π, hπ⟩ := hwc_potential (fun t s => a s (σ.symm t) - a t (σ.symm t)) (by simp)
    (fun ρ => by rw [hwc_cost_comp]; linarith [hσ (σ.trans ρ.symm)])
  refine ⟨π, fun r s => ?_⟩
  have := hπ (σ r) s
  simp at this
  linarith

theorem max_w_core (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ) :
    IsGreatest (Set.range (w a)) (assignCost a σ) := by
  obtain ⟨π, hπ⟩ := hwc_strong a σ hσ
  refine ⟨⟨π, hwc_w_eq a π σ hπ⟩, ?_⟩
  rintro _ ⟨π', rfl⟩
  exact hwc_weak a π' σ

lemma hwc_pi_opt (σ : Equiv.Perm (Fin n)) : PiSet a σ ⊆ optSet a := by
  intro π hπ π'
  rw [hwc_w_eq a π σ (fun r s => by
    by_cases h : s = σ r
    · rw [h]
    · exact (hπ r s h).le)]
  exact hwc_weak a π' σ

theorem unique_min_core (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ)
    (huniq : ∀ τ : Equiv.Perm (Fin n), IsOptimalAssignment a τ → τ = σ) :
    ∃ πbar : Fin n → ℝ, πbar ∈ optSet a ∧
      ∀ r s : Fin n, s ≠ σ r → a (σ r) r - πbar (σ r) < a s r - πbar s := by
  classical
  -- gap
  have hgap : ∃ ε > 0, ∀ τ : Equiv.Perm (Fin n), τ ≠ σ → assignCost a σ + ε * n ≤ assignCost a τ := by
    by_cases hne : (Finset.univ.filter fun τ : Equiv.Perm (Fin n) => τ ≠ σ).Nonempty
    · set m := (Finset.univ.filter fun τ : Equiv.Perm (Fin n) => τ ≠ σ).inf' hne (fun τ => assignCost a τ)
      obtain ⟨τ0, hτ0, hm⟩ := Finset.exists_mem_eq_inf' hne (fun τ => assignCost a τ)
      have hlt : assignCost a σ < m := by
        rw [show m = assignCost a τ0 from hm]
        simp only [Finset.mem_filter] at hτ0
        rcases (hσ τ0).lt_or_eq with h | h
        · exact h
        · exact absurd (huniq τ0 (fun τ => h ▸ hσ τ)) hτ0.2
      refine ⟨(m - assignCost a σ) / (n + 1), by positivity, fun τ hτ => ?_⟩
      have : m ≤ assignCost a τ := Finset.inf'_le _ (by simp [hτ])
      have hn : (0:ℝ) ≤ n := by positivity
      have : (m - assignCost a σ) / (n + 1) * n ≤ m - assignCost a σ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · refine ⟨1, one_pos, fun τ hτ => absurd ⟨τ, by simp [hτ]⟩ hne⟩
  obtain ⟨ε, hε, hgap⟩ := hgap
  let a' : Matrix (Fin n) (Fin n) ℝ := fun s r => if s = σ r then a s r else a s r - ε
  have hcost : ∀ τ : Equiv.Perm (Fin n), assignCost a σ ≤ assignCost a' τ := by
    intro τ
    have hle : assignCost a τ - ε * n ≤ assignCost a' τ := by
      unfold assignCost
      have : ∀ r, a (τ r) r - ε ≤ a' (τ r) r := by
        intro r; simp only [a']; split_ifs <;> linarith
      have := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => this r
      rw [Finset.sum_sub_distrib] at this
      simpa [mul_comm] using this
    by_cases h : τ = σ
    · subst h
      unfold assignCost; apply le_of_eq; apply Finset.sum_congr rfl; intro r _; simp [a']
    · linarith [hgap τ h]
  have hσ' : IsOptimalAssignment a' σ := by
    intro τ
    have : assignCost a' σ = assignCost a σ := by
      unfold assignCost; apply Finset.sum_congr rfl; intro r _; simp [a']
    rw [this]; exact hcost τ
  obtain ⟨π, hπ⟩ := hwc_strong a' σ hσ'
  have hP : π ∈ PiSet a σ := by
    intro r s hs
    have := hπ r s
    simp only [a', if_pos rfl, if_neg hs] at this
    linarith
  exact ⟨π, hwc_pi_opt a σ hP, hP⟩

theorem piSet_core (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ) :
    (∀ π ∈ PiSet a σ, ∀ A : Fin n → Fin n,
        assignCost a A + ∑ i, π i * assignVec A i ≤ assignCost a σ + ∑ i, π i * assignVec σ i →
          A = σ) ∧
      (∀ i, assignVec σ i = 0) ∧
      Convex ℝ (PiSet a σ) ∧ IsOpen (PiSet a σ) ∧ PiSet a σ ⊆ optSet a := by
  classical
  have hrep : ∀ (π : Fin n → ℝ) (A : Fin n → Fin n),
      assignCost a A + ∑ i, π i * assignVec A i = ∑ i, π i + ∑ r, (a (A r) r - π (A r)) := by
    intro π A
    unfold assignCost assignVec
    have : ∑ i, π i * ((Finset.univ.filter fun r => A r = i).card : ℝ) = ∑ r, π (A r) := by
      have := Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) A (fun r => π (A r))
      rw [← this]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_congr rfl (g := fun _ => π i) (fun r hr => by
        simp only [Finset.mem_filter] at hr; rw [hr.2])]
      simp [mul_comm]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, this]
    ring
  have hvec : ∀ i, assignVec σ i = 0 := by
    intro i
    unfold assignVec
    have : (Finset.univ.filter fun r => σ r = i) = {σ.symm i} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
    rw [this]; simp
  refine ⟨?_, hvec, ?_, ?_, hwc_pi_opt a σ⟩
  · intro π hπ A hA
    rw [hrep, hrep] at hA
    have hle : ∀ r, a (σ r) r - π (σ r) ≤ a (A r) r - π (A r) := by
      intro r
      by_cases h : A r = σ r
      · rw [h]
      · exact (hπ r (A r) h).le
    by_contra hne
    obtain ⟨r0, hr0⟩ : ∃ r, A r ≠ σ r := by
      by_contra hh; push_neg at hh; exact hne (funext hh)
    have : ∑ r, (a (σ r) r - π (σ r)) < ∑ r, (a (A r) r - π (A r)) :=
      Finset.sum_lt_sum (fun r _ => hle r) ⟨r0, Finset.mem_univ _, hπ r0 (A r0) hr0⟩
    linarith
  · have : PiSet a σ = ⋂ r, ⋂ i, {π : Fin n → ℝ | i ≠ σ r → a (σ r) r - π (σ r) < a i r - π i} := by
      ext π; simp [PiSet]
    rw [this]
    refine convex_iInter fun r => convex_iInter fun i => ?_
    by_cases h : i = σ r
    · simp [h, convex_univ]
    · simp only [ne_eq, h, not_false_eq_true, forall_const]
      have : {π : Fin n → ℝ | a (σ r) r - π (σ r) < a i r - π i}
          = {π : Fin n → ℝ | π i - π (σ r) < a i r - a (σ r) r} := by
        ext π; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [this]
      exact convex_halfSpace_lt (f := fun π : Fin n → ℝ => π i - π (σ r))
        (IsLinearMap.mk (fun x y => by simp; ring) (fun c x => by simp; ring)) _
  · have : PiSet a σ = ⋂ r, ⋂ i, {π : Fin n → ℝ | i ≠ σ r → a (σ r) r - π (σ r) < a i r - π i} := by
      ext π; simp [PiSet]
    rw [this]
    refine isOpen_iInter_of_finite fun r => isOpen_iInter_of_finite fun i => ?_
    by_cases h : i = σ r
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, forall_const]
      exact isOpen_lt (by fun_prop) (by fun_prop)

theorem optSet_dim_core (huniq : ∃! σ : Equiv.Perm (Fin n), IsOptimalAssignment a σ) :
    Module.finrank ℝ (vectorSpan ℝ (optSet a)) = n := by
  obtain ⟨σ, hσ, hu⟩ := huniq
  obtain ⟨π, hπo, hπ⟩ := unique_min_core a σ hσ hu
  have hP : π ∈ PiSet a σ := hπ
  have hopen := (piSet_core a σ hσ).2.2.2.1
  have htop : affineSpan ℝ (PiSet a σ) = ⊤ := hopen.affineSpan_eq_top ⟨π, hP⟩
  have htop2 : affineSpan ℝ (optSet a) = ⊤ :=
    top_unique (htop ▸ affineSpan_mono ℝ (hwc_pi_opt a σ))
  have : vectorSpan ℝ (optSet a) = ⊤ := by
    rw [← direction_affineSpan, htop2, AffineSubspace.direction_top]
  rw [this, finrank_top]
  simp

end Main

end HeldWolfeCrowder.Assignment

open HeldWolfeCrowder.Assignment


theorem solution {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (huniq : ∃! σ : Equiv.Perm (Fin n), IsOptimalAssignment a σ) :
    Module.finrank ℝ (vectorSpan ℝ (optSet a)) = n := by
  exact optSet_dim_core a huniq
