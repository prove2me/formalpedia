-- Prove2me | solution 1 for IncrKnapsack.PTAS.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:03:21.059924+00:00
-- url     : https://prove2.me/submissions/f5187465-004d-4528-a5ce-c3db27505c02

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

/-- weight of a subroutine answer, `0` for `none` -/
noncomputable def ikp10_wt {I : Instance} : Option (Sol I) → ℝ
  | some S => weight I S
  | none => 0

theorem ikp10_Ftil_zero (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I) (m : ℕ)
    (ϕ : ℝ) : Ftil I K ξ Φ A m 0 ϕ = if ϕ = 0 then 0 else ⊤ := by
  cases m <;> simp [Ftil]

theorem ikp10_Ftil_m0 (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I) (j : ℕ)
    (ϕ : ℝ) : Ftil I K ξ Φ A 0 j ϕ = if ϕ = 0 then 0 else ⊤ := by
  simp [Ftil]

theorem ikp10_ite_fin {x : ℝ} (h : (if x = 0 then (0 : WithTop ℝ) else ⊤) < ⊤) :
    (if x = 0 then (0 : WithTop ℝ) else ⊤) = 0 := by
  split_ifs at h ⊢ with hx
  · rfl
  · exact absurd h (lt_irrefl _)

theorem ikp10_weight_nonneg (I : Instance) (hI : I.Standing) (S : Sol I) : 0 ≤ weight I S := by
  unfold weight; exact Finset.sum_nonneg (fun i _ => (hI.w_pos i).le)

theorem ikp10_wt_nonneg (I : Instance) (hI : I.Standing) (o : Option (Sol I)) :
    0 ≤ ikp10_wt o := by
  cases o with
  | none => simp [ikp10_wt]
  | some S => exact ikp10_weight_nonneg I hI S

/-- Telescoping along the traceback. -/
theorem ikp10_telescope (I : Instance) (hI : I.Standing) (K ξ : ℕ)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (htr : IsTraceback I K ξ Φ A jt ϕt) :
    ∀ m, m ≤ Mcl I K ξ → Ftil I K ξ Φ A m (jt m) (ϕt m) =
      ((∑ m' ∈ Finset.Icc 1 m, ikp10_wt (outs I K ξ Φ A jt ϕt m') : ℝ) : WithTop ℝ) := by
  obtain ⟨hjM, _, hfinM, _, hstep⟩ := htr
  -- finiteness, downward
  have hfin : ∀ k, k ≤ Mcl I K ξ →
      Ftil I K ξ Φ A (Mcl I K ξ - k) (jt (Mcl I K ξ - k)) (ϕt (Mcl I K ξ - k)) < ⊤ := by
    intro k
    induction k with
    | zero => intro _; simpa [hjM] using hfinM
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have e : Mcl I K ξ - k = (Mcl I K ξ - (k + 1)) + 1 := by omega
      rw [e] at ih'
      obtain ⟨h0, h1⟩ := hstep (Mcl I K ξ - (k + 1) + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h0 h1
      by_cases hj : jt (Mcl I K ξ - (k + 1) + 1) = 0
      · obtain ⟨hj0, hp0⟩ := h0 hj
        rw [hj0, hp0, ikp10_Ftil_zero]; simp
      · obtain ⟨_, _, _, heq⟩ := h1 hj
        rw [heq] at ih'
        exact (WithTop.add_lt_top.1 ih').1
  have hfin' : ∀ m, m ≤ Mcl I K ξ → Ftil I K ξ Φ A m (jt m) (ϕt m) < ⊤ := by
    intro m hm
    have := hfin (Mcl I K ξ - m) (by omega)
    rwa [show Mcl I K ξ - (Mcl I K ξ - m) = m by omega] at this
  intro m
  induction m with
  | zero =>
    intro h0
    have := hfin' 0 h0
    rw [ikp10_Ftil_m0] at this ⊢
    rw [ikp10_ite_fin this]; simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_Icc_succ_top (by omega), WithTop.coe_add, ← ih (by omega)]
    obtain ⟨h0, h1⟩ := hstep (m + 1) (by omega) hm
    simp only [Nat.add_sub_cancel] at h0 h1
    by_cases hj : jt (m + 1) = 0
    · obtain ⟨hj0, hp0⟩ := h0 hj
      have hf := hfin' (m + 1) hm
      rw [hj, ikp10_Ftil_zero] at hf ⊢
      rw [ikp10_ite_fin hf, hj0, hp0, ikp10_Ftil_zero]
      have : outs I K ξ Φ A jt ϕt (m + 1) = none := by simp [outs, hj]
      rw [this]; simp [ikp10_wt]
    · obtain ⟨_, _, _, heq⟩ := h1 hj
      have hf := hfin' (m + 1) hm
      rw [heq] at hf ⊢
      have ho : outs I K ξ Φ A jt ϕt (m + 1) =
          A (m + 1) (jt m) (jt (m + 1) - 1) (phiReq I K ξ (ϕt (m + 1)) (ϕt m))
            (omegaOf I K ξ Φ A m (jt m) (ϕt m)) := by simp [outs, hj]
      rw [← ho] at hf ⊢
      congr 1
      have hw := (WithTop.add_lt_top.1 hf).2
      cases hS : outs I K ξ Φ A jt ϕt (m + 1) with
      | none => rw [hS] at hw; simp [wOpt] at hw
      | some S => simp [wOpt, ikp10_wt]

theorem ikp10_item (I : Instance) (K ξ : ℕ)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ) (i : Fin I.n) (s : Fin I.T)
    (h : algOut I K ξ Φ A jt ϕt i = some s) :
    ∃ S, outs I K ξ Φ A jt ϕt (clus I K ξ s) = some S ∧ S i = some s ∧ IsGood I K ξ s ∧
      1 ≤ clus I K ξ s ∧ clus I K ξ s ≤ Mcl I K ξ := by
  unfold algOut at h
  obtain ⟨m, hm, hi⟩ := List.exists_of_findSome?_eq_some h
  rw [List.mem_range'] at hm
  unfold introAt at hi
  cases hS : outs I K ξ Φ A jt ϕt m with
  | none => rw [hS] at hi; simp at hi
  | some S =>
    rw [hS] at hi
    simp only [Option.filter_eq_some_iff, decide_eq_true_eq] at hi
    obtain ⟨hSi, hg, hc⟩ := hi
    refine ⟨S, by rw [hc]; exact hS, hSi, hg, ?_, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hm; omega
    · obtain ⟨k, hk, rfl⟩ := hm; omega

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (hA : IsSubroutine I K ξ A) (htr : IsTraceback I K ξ Φ A jt ϕt) :
    Feasible I (algOut I K ξ Φ A jt ϕt) := by
  set So := algOut I K ξ Φ A jt ϕt with hSo
  set out := outs I K ξ Φ A jt ϕt with hout
  set M := Mcl I K ξ with hM
  set g : ℕ → ℝ := fun m => ∑ m' ∈ Finset.Icc 1 m, ikp10_wt (out m') with hg
  have htel := ikp10_telescope I hI K ξ Φ A jt ϕt htr
  have hg_nonneg : ∀ m, 0 ≤ g m := fun m =>
    Finset.sum_nonneg (fun m' _ => ikp10_wt_nonneg I hI (out m'))
  have hg_succ : ∀ m, g (m + 1) = g m + ikp10_wt (out (m + 1)) := by
    intro m; simp only [hg]; rw [Finset.sum_Icc_succ_top (by omega)]
  have homega : ∀ m, m ≤ M → omegaOf I K ξ Φ A m (jt m) (ϕt m) = g m := by
    intro m hm; unfold omegaOf; rw [htel m hm]; rfl
  let cl : Fin I.n → ℕ := fun i => match So i with | some s => clus I K ξ s | none => 0
  have hcl : ∀ i s, So i = some s → cl i = clus I K ξ s := by
    intro i s h; simp only [cl, h]
  -- the key invariant
  have key : ∀ m, m ≤ M → ∀ t : Fin I.T,
      ∑ i ∈ (Sol.set So t).filter (fun i => cl i ≤ m), I.w i ≤ I.W t ∧
      ∑ i ∈ (Sol.set So t).filter (fun i => cl i ≤ m), I.w i ≤ g m := by
    intro m
    induction m with
    | zero =>
      intro _ t
      have : (Sol.set So t).filter (fun i => cl i ≤ 0) = ∅ := by
        ext i
        simp only [Sol.set, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and, not_le]
        rintro ⟨s, hs, _⟩
        obtain ⟨_, _, _, _, h1, _⟩ := ikp10_item I K ξ Φ A jt ϕt i s hs
        rw [hcl i s hs]; omega
      rw [this, Finset.sum_empty]
      exact ⟨hI.W_nonneg t, hg_nonneg 0⟩
    | succ m ih =>
      intro hm t
      obtain ⟨ihW, ihg⟩ := ih (by omega) t
      set U := (Sol.set So t).filter (fun i => cl i ≤ m)
      set V := (Sol.set So t).filter (fun i => cl i = m + 1)
      have hsplit : (Sol.set So t).filter (fun i => cl i ≤ m + 1) = U ∪ V := by
        ext i; simp only [U, V, mem_union, mem_filter]; constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge m (cl i) with h | h
          · right; exact ⟨h1, by omega⟩
          · left; exact ⟨h1, h⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
      have hdisj : Disjoint U V := by
        rw [Finset.disjoint_filter]; intro i _ h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj]
      by_cases hV : V.Nonempty
      · obtain ⟨i0, hi0⟩ := hV
        have hi0' := hi0
        simp only [V, Sol.set, mem_filter, mem_univ, true_and] at hi0'
        obtain ⟨⟨s0, hs0, hs0t⟩, hcl0⟩ := hi0'
        obtain ⟨S, hS, hSi0, hgood0, _, _⟩ := ikp10_item I K ξ Φ A jt ϕt i0 s0 hs0
        rw [hcl i0 s0 hs0] at hcl0
        rw [hcl0] at hS
        -- the last good period of cluster m+1 up to t
        set C := univ.filter (fun s : Fin I.T => IsGood I K ξ s ∧ clus I K ξ s = m + 1 ∧ s ≤ t)
        have hCne : C.Nonempty := ⟨s0, by simp [C, hgood0, hcl0, hs0t]⟩
        set t' := C.max' hCne
        have ht'C : t' ∈ C := C.max'_mem hCne
        simp only [C, mem_filter, mem_univ, true_and] at ht'C
        obtain ⟨hgt', hct', ht't⟩ := ht'C
        -- S is the output at m+1
        have hj : jt (m + 1) ≠ 0 := by
          intro hj; simp [outs, hj] at hS
        have hSA : A (m + 1) (jt m) (jt (m + 1) - 1) (phiReq I K ξ (ϕt (m + 1)) (ϕt m))
            (g m) = some S := by
          rw [← homega m (by omega)]; simpa [out, outs, hj] using hS
        have hphi : 0 ≤ phiReq I K ξ (ϕt (m + 1)) (ϕt m) := by unfold phiReq; exact le_max_right _ _
        obtain ⟨⟨hadm1, hadm2⟩, _, _⟩ :=
          (hA (m + 1) (jt m) (jt (m + 1) - 1) _ (g m) hphi (hg_nonneg m)).1 S hSA
        have hVsub : V ⊆ Sol.set S t' := by
          intro i hi
          simp only [V, Sol.set, mem_filter, mem_univ, true_and] at hi ⊢
          obtain ⟨⟨s, hs, hst⟩, hcli⟩ := hi
          obtain ⟨S', hS', hS'i, hgs, _, _⟩ := ikp10_item I K ξ Φ A jt ϕt i s hs
          rw [hcl i s hs] at hcli
          rw [hcli, hS] at hS'
          cases hS'
          refine ⟨s, hS'i, ?_⟩
          exact C.le_max' s (by simp [C, hgs, hcli, hst])
        have hcap := hadm2 t' hgt' hct'
        have hpos : 0 < ∑ i ∈ Sol.set S t', I.w i := by
          apply Finset.sum_pos (fun i _ => hI.w_pos i)
          exact ⟨i0, hVsub hi0⟩
        have hVle : ∑ i ∈ V, I.w i ≤ ∑ i ∈ Sol.set S t', I.w i :=
          Finset.sum_le_sum_of_subset_of_nonneg hVsub (fun i _ _ => (hI.w_pos i).le)
        have hmax : ∑ i ∈ Sol.set S t', I.w i ≤ I.W t' - g m := by
          rcases le_or_gt (I.W t' - g m) 0 with h | h
          · rw [max_eq_right h] at hcap; linarith
          · rwa [max_eq_left h.le] at hcap
        have hWmono : I.W t' ≤ I.W t := hI.W_mono ht't
        have hVw : ∑ i ∈ V, I.w i ≤ weight I S := by
          unfold weight
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => (hI.w_pos i).le)
          intro i hi
          have := hVsub hi
          simp only [Sol.set, mem_filter, mem_univ, true_and] at this ⊢
          obtain ⟨s, hs, _⟩ := this
          simp [hs]
        have hwtS : ikp10_wt (out (m + 1)) = weight I S := by rw [hout, hS]; rfl
        refine ⟨by linarith, ?_⟩
        rw [hg_succ, hwtS]; linarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hV
        rw [hV, Finset.sum_empty, add_zero]
        refine ⟨ihW, ?_⟩
        rw [hg_succ]; linarith [ikp10_wt_nonneg I hI (out (m + 1))]
  intro t
  have hall : (Sol.set So t).filter (fun i => cl i ≤ M) = Sol.set So t := by
    apply Finset.filter_true_of_mem
    intro i hi
    simp only [Sol.set, mem_filter, mem_univ, true_and] at hi
    obtain ⟨s, hs, _⟩ := hi
    obtain ⟨_, _, _, _, _, h2⟩ := ikp10_item I K ξ Φ A jt ϕt i s hs
    rw [hcl i s hs]; exact h2
  have := (key M le_rfl t).1
  rwa [hall] at this
