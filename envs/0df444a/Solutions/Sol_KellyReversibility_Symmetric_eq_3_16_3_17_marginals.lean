-- Prove2me | solution 1 for KellyReversibility.Symmetric.eq_3_16_3_17_marginals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:38:26.308767+00:00
-- url     : https://prove2.me/submissions/30395448-8418-4a76-9500-07dc0ddf10b3

import Mathlib
import Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue

set_option autoImplicit false

namespace P2M8f58

open KellyReversibility.Symmetric

lemma prod_phi (φ : ℕ → ℝ) : ∀ n : ℕ, ∏ i : Fin n, φ ((i : ℕ) + 1) = ∏ l ∈ Finset.Icc 1 n, φ l
  | 0 => by simp
  | n + 1 => by
    simp only [Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [prod_phi φ n, Finset.prod_Icc_succ_top (by omega)]

lemma prod_get {α : Type*} (f : α → ℝ) : ∀ l : List α, ∏ i : Fin l.length, f (l.get i) = (l.map f).prod
  | [] => by simp
  | h :: t => by
    show ∏ i : Fin (t.length + 1), f ((h :: t).get i) = _
    rw [Fin.prod_univ_succ, List.map_cons, List.prod_cons, ← prod_get f t]
    rfl

lemma hasSum_lists {V : Type*} (G : V → ℝ) (A : ℝ) (hG : HasSum G A) (hG0 : ∀ v, 0 ≤ G v)
    (n : ℕ) : HasSum (fun l : List V => if l.length = n then (l.map G).prod else 0) (A ^ n) := by
  induction n with
  | zero =>
    have h : HasSum (fun l : List V => if l.length = 0 then (l.map G).prod else 0)
        ((fun l : List V => if l.length = 0 then (l.map G).prod else 0) []) := by
      apply hasSum_single
      intro l hl
      cases l with
      | nil => exact absurd rfl hl
      | cons h t => simp
    simpa using h
  | succ n ih =>
    have hinj : Function.Injective (fun p : V × List V => p.1 :: p.2) := by
      intro p q h
      simp only [List.cons.injEq] at h
      exact Prod.ext h.1 h.2
    have hcond : ∀ l, l ∉ Set.range (fun p : V × List V => p.1 :: p.2) →
        (fun l : List V => if l.length = n + 1 then (l.map G).prod else 0) l = 0 := by
      intro l hl
      cases l with
      | nil => simp
      | cons h t => exact absurd ⟨(h, t), rfl⟩ hl
    rw [← hinj.hasSum_iff hcond]
    have heq : ((fun l : List V => if l.length = n + 1 then (l.map G).prod else 0) ∘
        fun p : V × List V => p.1 :: p.2) =
        fun p => G p.1 * (fun l : List V => if l.length = n then (l.map G).prod else 0) p.2 := by
      funext p
      simp only [Function.comp_apply, List.length_cons, List.map_cons, List.prod_cons,
        Nat.add_right_cancel_iff]
      split_ifs <;> simp
    rw [heq, pow_succ']
    have h0 : 0 ≤ (fun l : List V => if l.length = n then (l.map G).prod else 0) := by
      intro l
      dsimp only
      split_ifs
      · apply List.prod_nonneg
        intro a ha
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
        exact hG0 v
      · exact le_rfl
    have key := HasSum.mul (f := G)
      (g := fun l : List V => if l.length = n then (l.map G).prod else 0) hG ih
      (hG.summable.mul_of_nonneg ih.summable (fun v => hG0 v) h0)
    exact key

variable {C : Type*}

lemma p_one (Q : SymmetricQueue C Unit) (hQ : Q.IsValid) (c : C) : Q.p c () = 1 := by
  have h := hQ.p_hasSum c
  have h2 : HasSum (Q.p c) (∑ z, Q.p c z) := hasSum_fintype _
  have := h.unique h2
  simpa using this.symm

lemma hasSum_valid (Q : SymmetricQueue C Unit) (hQ : Q.IsValid) (a : ℝ)
    (ha : HasSum (fun c => Q.ν c * Q.d c () * (Q.w c () : ℝ)) a) :
    HasSum (fun v : {e : Customer C Unit // Q.ValidCustomer e} =>
      Q.ν v.1.cls * Q.d v.1.cls ()) a := by
  classical
  let F : (Σ _ : C, ℕ) → ℝ := fun s =>
    if 1 ≤ s.2 ∧ s.2 ≤ Q.w s.1 () then Q.ν s.1 * Q.d s.1 () else 0
  have hF0 : ∀ s, 0 ≤ F s := by
    intro s
    simp only [F]
    split_ifs
    · exact mul_nonneg (hQ.ν_nonneg _) (hQ.d_pos _ _).le
    · exact le_rfl
  have hfib : ∀ c : C, HasSum (fun u : ℕ => F ⟨c, u⟩) (Q.ν c * Q.d c () * (Q.w c () : ℝ)) := by
    intro c
    have : HasSum (fun u : ℕ => F ⟨c, u⟩) (∑ u ∈ Finset.Icc 1 (Q.w c ()), F ⟨c, u⟩) :=
      hasSum_sum_of_ne_finset_zero (by
        intro u hu
        simp only [Finset.mem_Icc] at hu
        simp only [F]
        rw [if_neg hu])
    convert this using 1
    rw [Finset.sum_congr rfl (g := fun _ => Q.ν c * Q.d c ()) (by
      intro u hu
      simp only [Finset.mem_Icc] at hu
      simp only [F]
      rw [if_pos hu])]
    simp [Finset.sum_const, Nat.card_Icc]
    ring
  have hsum : Summable F := by
    rw [summable_sigma_of_nonneg hF0]
    refine ⟨fun c => (hfib c).summable, ?_⟩
    exact ha.summable.congr (fun c => ((hfib c).tsum_eq).symm)
  have hFa : HasSum F a := HasSum.sigma_of_hasSum ha hfib hsum
  let j : {e : Customer C Unit // Q.ValidCustomer e} → (Σ _ : C, ℕ) :=
    fun v => ⟨v.1.cls, v.1.stage⟩
  have hj : Function.Injective j := by
    rintro ⟨⟨c1, r1, u1⟩, h1⟩ ⟨⟨c2, r2, u2⟩, h2⟩ h
    simp only [j, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have hu : u1 = u2 := eq_of_heq h
    subst hu
    rfl
  have hcond : ∀ s, s ∉ Set.range j → F s = 0 := by
    rintro ⟨c, u⟩ hs
    simp only [F]
    split_ifs with h
    · rcases (hQ.ν_nonneg c).lt_or_eq with h' | h'
      · refine absurd ⟨⟨⟨c, (), u⟩, ?_⟩, rfl⟩ hs
        refine ⟨?_, h.1, h.2⟩
        simp only
        rw [p_one Q hQ c, mul_one]
        exact h'
      · rw [← h', zero_mul]
    · rfl
  have key := (hj.hasSum_iff hcond).mpr hFa
  convert key using 1
  funext v
  simp only [Function.comp, j, F]
  rw [if_pos ⟨v.2.2.1, v.2.2.2⟩]

lemma hasSum_states (Q : SymmetricQueue C Unit) (G : Customer C Unit → ℝ) (A : ℝ)
    (hG : HasSum (fun v : {e : Customer C Unit // Q.ValidCustomer e} => G v.1) A)
    (hG0 : ∀ v : {e : Customer C Unit // Q.ValidCustomer e}, 0 ≤ G v.1) (n : ℕ) :
    HasSum (fun x : Q.State => if x.1.length = n then (x.1.map G).prod else 0) (A ^ n) := by
  have h := hasSum_lists (fun v : {e : Customer C Unit // Q.ValidCustomer e} => G v.1) A hG hG0 n
  let ι : List {e : Customer C Unit // Q.ValidCustomer e} → Q.State :=
    fun l => Subtype.mk (p := fun x : List (Customer C Unit) => ∀ e ∈ x, Q.ValidCustomer e)
      (l.map Subtype.val) (by
        intro e he
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp he
        exact v.2)
  have hι : Function.Injective ι := by
    intro l1 l2 h
    have : l1.map Subtype.val = l2.map Subtype.val := congrArg Subtype.val h
    exact (List.map_injective_iff.mpr Subtype.val_injective) this
  have hcond : ∀ x, x ∉ Set.range ι →
      (fun x : Q.State => if x.1.length = n then (x.1.map G).prod else 0) x = 0 := by
    intro x hx
    exact absurd ⟨x.1.attach.map (fun e => ⟨e.1, x.2 e.1 e.2⟩), Subtype.ext (by simp [ι])⟩ hx
  rw [← (hι.hasSum_iff hcond)]
  convert h using 1
  funext l
  show (if (l.map Subtype.val).length = n then ((l.map Subtype.val).map G).prod else 0) =
    (if l.length = n then (l.map (fun v => G v.1)).prod else 0)
  rw [List.length_map, List.map_map]
  rfl

end P2M8f58

open KellyReversibility.Symmetric in
theorem solution {C : Type*} [Countable C] (Q : SymmetricQueue C Unit)
    (hQ : Q.IsValid) (a : ℝ) (ha : HasSum (fun c => Q.ν c * Q.d c () * (Q.w c () : ℝ)) a)
    (b : ℝ) (hb : HasSum (fun n : ℕ => a ^ n / ∏ l ∈ Finset.Icc 1 n, Q.φ l) b⁻¹) :
    let π : Q.State → ℝ := fun x => b * ∏ i : Fin x.1.length,
      Q.ν (x.1.get i).cls * Q.d (x.1.get i).cls () / Q.φ ((i : ℕ) + 1)
    (∀ n : ℕ, HasSum (fun x : Q.State => if x.1.length = n then π x else 0)
        (b * a ^ n / ∏ l ∈ Finset.Icc 1 n, Q.φ l)) ∧
    (∀ x : Q.State, π x =
        b * a ^ x.1.length / (∏ l ∈ Finset.Icc 1 x.1.length, Q.φ l) *
          ∏ i : Fin x.1.length,
            (Q.ν (x.1.get i).cls * Q.d (x.1.get i).cls () * (Q.w (x.1.get i).cls () : ℝ) / a) *
              (1 / (Q.w (x.1.get i).cls () : ℝ))) := by
  intro π
  let g : Customer C Unit → ℝ := fun e => Q.ν e.cls * Q.d e.cls ()
  have hπ : ∀ x : Q.State,
      π x = b / (∏ l ∈ Finset.Icc 1 x.1.length, Q.φ l) * (x.1.map g).prod := by
    intro x
    simp only [π]
    rw [Finset.prod_div_distrib, P2M8f58.prod_phi Q.φ x.1.length,
      ← P2M8f58.prod_get g x.1]
    ring
  refine ⟨fun n => ?_, fun x => ?_⟩
  · have hS := P2M8f58.hasSum_states Q g a (P2M8f58.hasSum_valid Q hQ a ha)
      (fun v => mul_nonneg (hQ.ν_nonneg _) (hQ.d_pos _ _).le) n
    have := hS.mul_left (b / ∏ l ∈ Finset.Icc 1 n, Q.φ l)
    have heq : (fun x : Q.State => if x.1.length = n then π x else 0) =
        fun x => (b / ∏ l ∈ Finset.Icc 1 n, Q.φ l) *
          (if x.1.length = n then (x.1.map g).prod else 0) := by
      funext x
      split_ifs with h
      · rw [hπ x, h]
      · rw [mul_zero]
    rw [heq, show b * a ^ n / ∏ l ∈ Finset.Icc 1 n, Q.φ l =
      (b / ∏ l ∈ Finset.Icc 1 n, Q.φ l) * a ^ n by ring]
    exact this
  · rw [hπ x]
    have hP : (∏ l ∈ Finset.Icc 1 x.1.length, Q.φ l) ≠ 0 := by
      apply ne_of_gt
      apply Finset.prod_pos
      intro l hl
      exact hQ.φ_pos l (by simp only [Finset.mem_Icc] at hl; omega)
    have han : a ^ x.1.length ≠ 0 := by
      rcases Nat.eq_zero_or_pos x.1.length with h0 | hpos
      · rw [h0, pow_zero]; exact one_ne_zero
      · apply pow_ne_zero
        have hmem : x.1.get ⟨0, hpos⟩ ∈ x.1 := List.get_mem _ _
        have hv := x.2 _ hmem
        set e := x.1.get ⟨0, hpos⟩
        have hνpos : 0 < Q.ν e.cls := by
          have := hv.1
          rw [P2M8f58.p_one Q hQ, mul_one] at this
          exact this
        have hle := le_hasSum ha e.cls (fun c _ =>
          mul_nonneg (mul_nonneg (hQ.ν_nonneg c) (hQ.d_pos c ()).le) (Nat.cast_nonneg _))
        have hpos' : 0 < Q.ν e.cls * Q.d e.cls () * (Q.w e.cls () : ℝ) := by
          apply mul_pos (mul_pos hνpos (hQ.d_pos _ _))
          exact_mod_cast hQ.w_pos _ _
        linarith
    have hprod : (∏ i : Fin x.1.length,
        (Q.ν (x.1.get i).cls * Q.d (x.1.get i).cls () * (Q.w (x.1.get i).cls () : ℝ) / a) *
          (1 / (Q.w (x.1.get i).cls () : ℝ))) =
        (x.1.map g).prod / a ^ x.1.length := by
      rw [← P2M8f58.prod_get g x.1]
      rw [Finset.prod_congr rfl (g := fun i : Fin x.1.length => g (x.1.get i) / a) (by
        intro i _
        have hw : (Q.w (x.1.get i).cls () : ℝ) ≠ 0 := by
          have := hQ.w_pos (x.1.get i).cls ()
          positivity
        simp only [g]
        field_simp)]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod]
    field_simp
