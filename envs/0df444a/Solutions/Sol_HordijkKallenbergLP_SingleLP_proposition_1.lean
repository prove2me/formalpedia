-- Prove2me | solution 1 for HordijkKallenbergLP.SingleLP.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:33:04.171703+00:00
-- url     : https://prove2.me/submissions/88355e55-c532-4bc4-a579-96635deec7a2

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model

set_option autoImplicit false

universe u v

namespace HK9d98

lemma exists_between_fin {ι : Type u} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type u} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ : Type v} {ι : Type u} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩


end HK9d98

namespace HK9d98b

open MarkovDecisionProcesses HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma sum_delta (M : StationaryMDP S A) (p : Pair M) (v : S → ℝ) :
    ∑ j, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * v j
      = v p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * v j := by
  simp [sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma stateSum_eq (M : StationaryMDP S A) (x : Pair M → ℝ) (j : S) :
    stateSum M x j = ∑ p : Pair M, (if p.1.1 = j then (1:ℝ) else 0) * x p := by
  unfold stateSum
  rw [Finset.sum_filter]
  simp [ite_mul]

lemma swap_sum {P T : Type*} [Fintype P] [Fintype T] (g : P → T → ℝ) (w : P → ℝ) (v : T → ℝ) :
    ∑ p, w p * ∑ j, g p j * v j = ∑ j, v j * ∑ p, g p j * w p := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun p _ => by ring))

lemma sum_comb {P : Type*} [Fintype P] (g w1 w2 : P → ℝ) (c : ℝ) :
    ∑ p, g p * ((w1 p + w2 p) / c) = (∑ p, g p * w1 p + ∑ p, g p * w2 p) / c := by
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl (fun p _ => by ring)

lemma sum_neg_swap {P : Type*} [Fintype P] (g w : P → ℝ) :
    ∑ p, -g p * w p = -∑ p, w p * g p := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun p _ => by ring)

lemma exists_primal (M : StationaryMDP S A) (β : S → ℝ)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hopt : IsDualOptimal M β z) :
    ∃ φ' u' : S → ℝ, Superharmonic M φ' u' ∧ ∑ j, β j * φ' j ≤ dualObjective M z.1 := by
  obtain ⟨⟨hz3, hz4, hz5⟩, hzmax⟩ := hopt
  let a : (Pair M ⊕ Pair M) ⊕ Unit → S ⊕ S → ℝ :=
    Sum.elim (Sum.elim
      (fun p => Sum.elim (fun j => M.trans p.1.1 p.1.2 j - (if p.1.1 = j then (1:ℝ) else 0))
        (fun _ => 0))
      (fun p => Sum.elim (fun j => -(if p.1.1 = j then (1:ℝ) else 0))
        (fun j => M.trans p.1.1 p.1.2 j - (if p.1.1 = j then (1:ℝ) else 0))))
      (fun _ => Sum.elim β (fun _ => 0))
  let b : (Pair M ⊕ Pair M) ⊕ Unit → ℝ :=
    Sum.elim (Sum.elim (fun _ => 0) (fun p => -M.reward p.1.1 p.1.2))
      (fun _ => dualObjective M z.1)
  rcases HK9d98.fm_alt' a b with ⟨w, hw⟩ | ⟨l, hl0, hl1, hl2⟩
  · refine ⟨fun j => w (Sum.inl j), fun j => w (Sum.inr j), ?_, ?_⟩
    · intro i act hact
      have h1 := hw (Sum.inl (Sum.inl ⟨(i, act), hact⟩))
      have h2 := hw (Sum.inl (Sum.inr ⟨(i, act), hact⟩))
      simp [a, b, Fintype.sum_sum_type, sub_mul, Finset.sum_sub_distrib, ite_mul] at h1 h2
      constructor <;> linarith
    · have h3 := hw (Sum.inr ())
      simpa [a, b, Fintype.sum_sum_type] using h3
  · exfalso
    have hcolφ : ∀ j, ∑ p : Pair M, l (Sum.inl (Sum.inl p)) *
          (M.trans p.1.1 p.1.2 j - (if p.1.1 = j then (1:ℝ) else 0)) +
        ∑ p : Pair M, l (Sum.inl (Sum.inr p)) * (-(if p.1.1 = j then (1:ℝ) else 0)) +
        l (Sum.inr ()) * β j = 0 := by
      intro j
      have := hl1 (Sum.inl j)
      simpa only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.sum_singleton] using this
    have hcolu : ∀ j, ∑ p : Pair M, l (Sum.inl (Sum.inr p)) *
          (M.trans p.1.1 p.1.2 j - (if p.1.1 = j then (1:ℝ) else 0)) = 0 := by
      intro j
      have := hl1 (Sum.inr j)
      simpa [a, Fintype.sum_sum_type] using this
    have hneg : ∑ p : Pair M, l (Sum.inl (Sum.inr p)) * (-M.reward p.1.1 p.1.2) +
        l (Sum.inr ()) * dualObjective M z.1 < 0 := by
      simpa [b, Fintype.sum_sum_type] using hl2
    set t := l (Sum.inr ()) with ht
    have ht0 : 0 ≤ t := hl0 _
    have hc : 0 < 1 + t := by linarith
    let z'' : (Pair M → ℝ) × (Pair M → ℝ) :=
      (fun p => (z.1 p + l (Sum.inl (Sum.inr p))) / (1 + t),
       fun p => (z.2 p + l (Sum.inl (Sum.inl p))) / (1 + t))
    have hfeas : z'' ∈ dualFeasible M β := by
      refine ⟨fun j => ?_, fun j => ?_, fun p => ⟨?_, ?_⟩⟩
      · simp only [z'']
        rw [sum_comb, hz3 j]
        have e : ∑ p : Pair M, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
            l (Sum.inl (Sum.inr p)) = -∑ p : Pair M, l (Sum.inl (Sum.inr p)) *
            (M.trans p.1.1 p.1.2 j - (if p.1.1 = j then (1:ℝ) else 0)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun p _ => by ring)
        rw [e, hcolu j]; simp
      · simp only [z'']
        rw [sum_comb, stateSum_eq, sum_comb, ← stateSum_eq]
        have h4 := hz4 j
        have e1 : ∑ p : Pair M, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
            l (Sum.inl (Sum.inl p)) = -∑ p : Pair M, l (Sum.inl (Sum.inl p)) *
            (M.trans p.1.1 p.1.2 j - (if p.1.1 = j then (1:ℝ) else 0)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun p _ => by ring)
        have e2 : ∑ p : Pair M, (if p.1.1 = j then (1:ℝ) else 0) * l (Sum.inl (Sum.inr p)) =
            -∑ p : Pair M, l (Sum.inl (Sum.inr p)) * (-(if p.1.1 = j then (1:ℝ) else 0)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun p _ => by ring)
        rw [e1, e2]
        have h := hcolφ j
        rw [← add_div, div_eq_iff hc.ne']
        linarith
      · exact div_nonneg (add_nonneg (hz5 p).1 (hl0 _)) hc.le
      · exact div_nonneg (add_nonneg (hz5 p).2 (hl0 _)) hc.le
    have hle := hzmax z'' hfeas
    simp only [z'', dualObjective] at hle
    rw [sum_comb, div_le_iff₀ hc] at hle
    have e : ∑ p : Pair M, l (Sum.inl (Sum.inr p)) * (-M.reward p.1.1 p.1.2) =
        -∑ p : Pair M, M.reward p.1.1 p.1.2 * l (Sum.inl (Sum.inr p)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [e] at hneg
    unfold dualObjective at hneg
    nlinarith

end HK9d98b

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology HordijkKallenbergLP.SingleLP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf)
    (u : S → ℝ) (hP : IsPrimalOptimal M β (optGainInf M) u) :
    (∀ i : S, optGainInf M i - ∑ j, M.trans i (f i) j * optGainInf M j = 0) ∧
      ∀ i ∈ Ex M z.1,
        optGainInf M i + (u i - ∑ j, M.trans i (f i) j * u j) = M.reward i (f i) := by
  obtain ⟨φ', u', hsh', hle'⟩ := HK9d98b.exists_primal M β z hopt
  set φ := optGainInf M with hφ
  have hstrong : ∑ j, β j * φ j ≤ dualObjective M z.1 := le_trans (hP.2 φ' u' hsh') hle'
  obtain ⟨⟨hz3, hz4, hz5⟩, _⟩ := hopt
  -- slacks
  let sa : Pair M → ℝ := fun p => φ p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * φ j
  let sb : Pair M → ℝ := fun p =>
    φ p.1.1 + (u p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * u j) - M.reward p.1.1 p.1.2
  have hsa : ∀ p, 0 ≤ sa p := fun p => by
    have := (hP.1 p.1.1 p.1.2 p.2).1; simp only [sa]; linarith
  have hsb : ∀ p, 0 ≤ sb p := fun p => by
    have := (hP.1 p.1.1 p.1.2 p.2).2; simp only [sb]; linarith
  -- (3) gives Σ x sa = 0 and Σ x (u_i - Σ P u) = 0
  have hD : ∀ v : S → ℝ, ∑ p : Pair M, z.1 p * (v p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * v j) = 0 := by
    intro v
    have : ∑ p : Pair M, z.1 p * (v p.1.1 - ∑ j, M.trans p.1.1 p.1.2 j * v j) =
        ∑ p : Pair M, z.1 p * ∑ j, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * v j := by
      exact Finset.sum_congr rfl (fun p _ => by rw [HK9d98b.sum_delta])
    rw [this, HK9d98b.swap_sum]
    simp [hz3]
  -- weak duality identity
  have hβφ : ∑ j, β j * φ j = ∑ p : Pair M, z.1 p * φ p.1.1 + ∑ p : Pair M, z.2 p * sa p := by
    have h1 : ∀ j, β j = ∑ p : Pair M, (if p.1.1 = j then (1:ℝ) else 0) * z.1 p +
        ∑ p : Pair M, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.2 p := by
      intro j; rw [← hz4 j, HK9d98b.stateSum_eq]
    have h2 : ∑ p : Pair M, z.2 p * sa p = ∑ p : Pair M, z.2 p *
        ∑ j, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * φ j :=
      Finset.sum_congr rfl (fun p _ => by simp only [sa]; rw [HK9d98b.sum_delta])
    have h3 : ∑ p : Pair M, z.1 p * φ p.1.1 = ∑ p : Pair M, z.1 p *
        ∑ j, (if p.1.1 = j then (1:ℝ) else 0) * φ j :=
      Finset.sum_congr rfl (fun p _ => by simp [ite_mul])
    have s1 := HK9d98b.swap_sum (fun (p : Pair M) (j : S) => (if p.1.1 = j then (1:ℝ) else 0)) z.1 φ
    have s2 := HK9d98b.swap_sum (fun (p : Pair M) (j : S) =>
      (if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) z.2 φ
    beta_reduce at s1 s2
    rw [h2, h3, s1, s2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [h1 j]; ring)
  have hobj : dualObjective M z.1 = ∑ p : Pair M, z.1 p * φ p.1.1 - ∑ p : Pair M, z.1 p * sb p := by
    have := hD u
    unfold dualObjective
    simp only [sb, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at this ⊢
    have e : ∑ p : Pair M, M.reward p.1.1 p.1.2 * z.1 p = ∑ p : Pair M, z.1 p * M.reward p.1.1 p.1.2 :=
      Finset.sum_congr rfl (fun p _ => by ring)
    linarith
  have hsum0 : ∑ p : Pair M, z.2 p * sa p + ∑ p : Pair M, z.1 p * sb p ≤ 0 := by linarith
  have hA : ∀ p, 0 ≤ z.2 p * sa p := fun p => mul_nonneg (hz5 p).2 (hsa p)
  have hB : ∀ p, 0 ≤ z.1 p * sb p := fun p => mul_nonneg (hz5 p).1 (hsb p)
  have hSA := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) => hA p)
  have hSB := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) => hB p)
  have hA0 : ∀ p, z.2 p * sa p = 0 := fun p =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hA p)).1 (by linarith) p (Finset.mem_univ _)
  have hB0 : ∀ p, z.1 p * sb p = 0 := fun p =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hB p)).1 (by linarith) p (Finset.mem_univ _)
  have hC0 : ∀ p, z.1 p * sa p = 0 := fun p =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg (hz5 p).1 (hsa p))).1
      (hD φ) p (Finset.mem_univ _)
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · by_cases hi : i ∈ Ex M z.1
    · have hx := (hsel i).1 hi
      have := hC0 ⟨(i, f i), hf i⟩
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hx.ne'
      · exact h
    · have hy := (hsel i).2 hi
      have := hA0 ⟨(i, f i), hf i⟩
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hy.ne'
      · exact h
  · have hx := (hsel i).1 hi
    have := hB0 ⟨(i, f i), hf i⟩
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hx.ne'
    · simp only [sb] at h; linarith
