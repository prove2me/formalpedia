-- Prove2me | solution 1 for NetworkQuality.PotentialMax.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T13:57:27.927827+00:00
-- url     : https://prove2.me/submissions/9bfd6feb-c430-4a1e-ac82-c02640bd60b5

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

set_option autoImplicit false

namespace P5885

open Finset

/-- A sum over the indices `i : Fin n` with `i < m` equals the corresponding `range m` sum. -/
lemma head_sum {β : Type} [AddCommMonoid β] (n m : ℕ) (hm : m ≤ n) (g : ℕ → β) :
    ∑ i ∈ (univ : Finset (Fin n)).filter (fun i => i.val < m), g i.val
      = ∑ k ∈ range m, g k := by
  rw [Finset.sum_filter]
  rw [← Finset.sum_range (fun k => if k < m then g k else 0), ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma card_tail (n m : ℕ) (hm : m ≤ n) :
    ((univ : Finset (Fin n)).filter (fun i => ¬ i.val < m)).card = n - m := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n))) (fun i : Fin n => i.val < m)
  have h2 : ((univ : Finset (Fin n)).filter (fun i => i.val < m)).card = m := by
    rw [Finset.card_eq_sum_ones, head_sum n m hm (fun _ => (1 : ℕ))]
    simp
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- Mediant inequality: a monotone ratio makes the tail mediant at least the head mediant. -/
lemma mediant {n : ℕ} (r w : Fin n → ℝ) (hr : Monotone r) (hw : ∀ i, 0 ≤ w i) (m : ℕ) :
    (∑ i ∈ (univ : Finset (Fin n)).filter (fun i => i.val < m), r i * w i) *
        (∑ i ∈ (univ : Finset (Fin n)).filter (fun i => ¬ i.val < m), w i)
      ≤ (∑ i ∈ (univ : Finset (Fin n)).filter (fun i => ¬ i.val < m), r i * w i) *
        (∑ i ∈ (univ : Finset (Fin n)).filter (fun i => i.val < m), w i) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hba : r b ≤ r a := hr (by rw [Fin.le_iff_val_le_val]; omega)
  have hab := mul_nonneg (hw a) (hw b)
  nlinarith

/-- Rearrangement: a set of the same size as the top block has no larger sum of a monotone weight. -/
lemma rearr {n : ℕ} (w : Fin n → ℝ) (hw : Monotone w) (m : ℕ) (C : Finset (Fin n))
    (hC : C.card = ((univ : Finset (Fin n)).filter (fun i => ¬ i.val < m)).card) :
    ∑ i ∈ C, w i ≤ ∑ i ∈ (univ : Finset (Fin n)).filter (fun i => ¬ i.val < m), w i := by
  set T := (univ : Finset (Fin n)).filter (fun i => ¬ i.val < m) with hT
  rw [← Finset.sum_inter_add_sum_sdiff C T w, ← Finset.sum_inter_add_sum_sdiff T C w,
    Finset.inter_comm T C]
  have hk : (C \ T).card = (T \ C).card := by
    have h1 := Finset.card_sdiff_add_card_inter C T
    have h2 := Finset.card_sdiff_add_card_inter T C
    rw [Finset.inter_comm] at h2
    omega
  have key : ∀ x ∈ C \ T, ∀ y ∈ T \ C, w x ≤ w y := by
    intro x hx y hy
    simp only [hT, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not] at hx hy
    apply hw
    rw [Fin.le_iff_val_le_val]
    omega
  have hd : ((C \ T).card : ℝ) * ∑ x ∈ C \ T, w x
      ≤ ((C \ T).card : ℝ) * ∑ y ∈ T \ C, w y := by
    calc ((C \ T).card : ℝ) * ∑ x ∈ C \ T, w x
        = ∑ _y ∈ T \ C, ∑ x ∈ C \ T, w x := by
          rw [Finset.sum_const, nsmul_eq_mul, hk]
      _ ≤ ∑ y ∈ T \ C, ∑ _x ∈ C \ T, w y :=
          Finset.sum_le_sum (fun y hy => Finset.sum_le_sum (fun x hx => key x hx y hy))
      _ = ∑ y ∈ T \ C, ((C \ T).card : ℝ) * w y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((C \ T).card : ℝ) * ∑ y ∈ T \ C, w y := by rw [Finset.mul_sum]
  rcases Nat.eq_zero_or_pos (C \ T).card with h0 | hpos
  · have e1 : C \ T = ∅ := Finset.card_eq_zero.mp h0
    have e2 : T \ C = ∅ := Finset.card_eq_zero.mp (hk ▸ h0)
    rw [e1, e2]
  · have hpos' : (0 : ℝ) < (C \ T).card := by exact_mod_cast hpos
    have := le_of_mul_le_mul_left hd hpos'
    linarith

open NetworkQuality.PotentialMax in
/-- Under strong network effects, all consumers buying maximizes the potential at the price
`(∑ f) / (∑ 1/v)`. -/
lemma potmax_at {n : ℕ} (M : Market n) (q : ℝ) (hv : ∀ i, 0 < M.v i) (hanti : Antitone M.v)
    (hf0 : ∀ i : Fin n, 0 ≤ M.f (i.val + 1) q) (hs : M.StrongNE q) :
    M.IsPotMax univ ((∑ i : Fin n, M.f (i.val + 1) q) / ∑ i : Fin n, 1 / M.v i) q := by
  intro B
  set w : Fin n → ℝ := fun i => 1 / M.v i with hwdef
  set r : Fin n → ℝ := fun i => M.v i * M.f (i.val + 1) q with hrdef
  have hw0 : ∀ i, 0 ≤ w i := fun i => le_of_lt (one_div_pos.mpr (hv i))
  have hwm : Monotone w := by
    intro a b hab
    exact one_div_le_one_div_of_le (hv b) (hanti hab)
  have hrm : Monotone r := hs.monotone
  have hfrw : ∀ i : Fin n, M.f (i.val + 1) q = r i * w i := by
    intro i
    simp only [hrdef, hwdef]
    field_simp [(hv i).ne']
  set m := B.card with hmdef
  have hm : m ≤ n := by
    have := Finset.card_le_univ B
    rwa [Fintype.card_fin] at this
  set Tc := (univ : Finset (Fin n)).filter (fun i => i.val < m) with hTc
  set T := (univ : Finset (Fin n)).filter (fun i => ¬ i.val < m) with hT
  have hhead : ∑ k ∈ range m, M.f (k + 1) q = ∑ i ∈ Tc, M.f (i.val + 1) q :=
    (head_sum n m hm (fun k => M.f (k + 1) q)).symm
  have hall : ∑ k ∈ range n, M.f (k + 1) q = ∑ i : Fin n, M.f (i.val + 1) q :=
    Finset.sum_range (fun k => M.f (k + 1) q)
  have hsplitF : ∑ i : Fin n, M.f (i.val + 1) q
      = ∑ i ∈ Tc, M.f (i.val + 1) q + ∑ i ∈ T, M.f (i.val + 1) q :=
    (Finset.sum_filter_add_sum_filter_not univ (fun i : Fin n => i.val < m) _).symm
  have hsplitW : ∑ i : Fin n, w i = ∑ i ∈ Tc, w i + ∑ i ∈ T, w i :=
    (Finset.sum_filter_add_sum_filter_not univ (fun i : Fin n => i.val < m) _).symm
  have hBc : ∑ i : Fin n, w i = ∑ i ∈ B, w i + ∑ i ∈ Bᶜ, w i :=
    (Finset.sum_add_sum_compl B w).symm
  have hcardT : T.card = n - m := card_tail n m hm
  have hcardBc : Bᶜ.card = T.card := by
    rw [Finset.card_compl, Fintype.card_fin, hcardT]
  have hre := rearr w hwm m Bᶜ hcardBc
  have hmed := mediant r w hrm hw0 m
  have hTf : ∑ i ∈ T, M.f (i.val + 1) q = ∑ i ∈ T, r i * w i :=
    Finset.sum_congr rfl (fun i _ => hfrw i)
  have hTcf : ∑ i ∈ Tc, M.f (i.val + 1) q = ∑ i ∈ Tc, r i * w i :=
    Finset.sum_congr rfl (fun i _ => hfrw i)
  have hF0 : 0 ≤ ∑ i : Fin n, M.f (i.val + 1) q := Finset.sum_nonneg (fun i _ => hf0 i)
  have hTcw0 : 0 ≤ ∑ i ∈ Tc, w i := Finset.sum_nonneg (fun i _ => hw0 i)
  have hTw0 : 0 ≤ ∑ i ∈ T, w i := Finset.sum_nonneg (fun i _ => hw0 i)
  -- unfold the potential
  show ∑ k ∈ range B.card, M.f (k + 1) q - _ * ∑ i ∈ B, 1 / M.v i
      ≤ ∑ k ∈ range (univ : Finset (Fin n)).card, M.f (k + 1) q - _ * ∑ i ∈ univ, 1 / M.v i
  rw [Finset.card_univ, Fintype.card_fin, ← hmdef, hhead, hall]
  change _ - _ * ∑ i ∈ B, w i ≤ _ - _ * ∑ i : Fin n, w i
  rcases (Finset.sum_nonneg (fun i _ => hw0 i) : 0 ≤ ∑ i : Fin n, w i).lt_or_eq with hH | hH
  · -- main case: positive total weight
    set F := ∑ i : Fin n, M.f (i.val + 1) q with hFdef
    set W := ∑ i : Fin n, w i with hWdef
    have hP0 : 0 ≤ F / W := div_nonneg hF0 hH.le
    have h1 : F / W * ∑ i ∈ Bᶜ, w i ≤ F / W * ∑ i ∈ T, w i :=
      mul_le_mul_of_nonneg_left hre hP0
    have h2 : F * ∑ i ∈ T, w i ≤ W * ∑ i ∈ T, M.f (i.val + 1) q := by
      rw [hsplitF, hsplitW, hTf, hTcf]
      nlinarith [hmed]
    have h3 : F / W * ∑ i ∈ T, w i ≤ ∑ i ∈ T, M.f (i.val + 1) q := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hH]
      linarith [h2]
    have e : F / W * W = F / W * ∑ i ∈ B, w i + F / W * ∑ i ∈ Bᶜ, w i := by
      rw [← mul_add, ← hBc]
    linarith [e, h1, h3, hsplitF]
  · -- degenerate: no weight at all (impossible when n > 0, harmless otherwise)
    have hzero : ∀ i ∈ (univ : Finset (Fin n)), w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw0 i)).mp hH.symm
    have hB0 : ∑ i ∈ B, w i = 0 := Finset.sum_eq_zero (fun i _ => hzero i (mem_univ i))
    rw [hB0, ← hH]
    simp only [mul_zero, sub_zero]
    rw [hsplitF]
    have : 0 ≤ ∑ i ∈ T, M.f (i.val + 1) q := Finset.sum_nonneg (fun i _ => hf0 i)
    linarith

end P5885

open NetworkQuality.PotentialMax NetworkQuality.PotentialMax.Market in
theorem solution {n : ℕ} (M : Market n) (hM : M.Standing)
    (hstrong : ∀ q : ℝ, 0 ≤ q → M.StrongNE q)
    (pstar qstar : ℝ) (hp : 0 ≤ pstar) (hq : 0 < qstar)
    (hopt : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → M.profitPM p q ≤ M.profitPM pstar qstar) :
    deriv M.c qstar =
      (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, 1 / M.v i)⁻¹ *
        ((1 / (n : ℝ)) * ∑ i : Fin n, deriv (M.f (i.val + 1)) qstar) := by
  obtain ⟨hn, hv, hanti, hf0, -, -, hfd, -, -, hcd⟩ := hM
  set H : ℝ := ∑ i : Fin n, 1 / M.v i with hHdef
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hH : 0 < H := Finset.sum_pos (fun i _ => one_div_pos.mpr (hv i)) hne
  set S : ℝ → ℝ := fun q => ∑ i : Fin n, M.f (i.val + 1) q with hSdef
  have hS0 : ∀ q, 0 ≤ q → 0 ≤ S q :=
    fun q hq0 => Finset.sum_nonneg (fun i _ => hf0 (i.val + 1) q (by omega) hq0)
  have hpm : ∀ q, 0 ≤ q → M.IsPotMax Finset.univ (S q / H) q := fun q hq0 =>
    P5885.potmax_at M q hv hanti (fun i => hf0 (i.val + 1) q (by omega) hq0) (hstrong q hq0)
  -- any price at which everyone buys is at most S q / H (compare with the empty buyer set)
  have hup : ∀ p q, M.IsPotMax Finset.univ p q → p ≤ S q / H := by
    intro p q h
    have h0 := h ∅
    simp only [Market.pot, Finset.card_empty, Finset.range_zero, Finset.sum_empty,
      mul_zero, sub_zero, Finset.card_univ, Fintype.card_fin] at h0
    rw [Finset.sum_range (fun k => M.f (k + 1) q)] at h0
    rw [le_div_iff₀ hH]
    linarith
  set g : ℝ → ℝ := fun q => (n : ℝ) * (S q / H) - M.c q with hgdef
  have hgle : ∀ q, 0 ≤ q → g q ≤ g qstar := by
    intro q hq0
    have h1 : M.profitPM (S q / H) q = g q := by
      simp only [Market.profitPM, if_pos (hpm q hq0), hgdef]
    have h2 := hopt (S q / H) q (div_nonneg (hS0 q hq0) hH.le) hq0
    have h3 : M.profitPM pstar qstar ≤ g qstar := by
      unfold Market.profitPM
      split_ifs with hpot
      · have := hup pstar qstar hpot
        simp only [hgdef]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      · simp only [hgdef]
        have := div_nonneg (hS0 qstar hq.le) hH.le
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
    linarith
  have hloc : IsLocalMax g qstar :=
    Filter.eventually_of_mem (Ioi_mem_nhds hq) (fun q hq' => hgle q (le_of_lt hq'))
  have hd0 := hloc.deriv_eq_zero
  have hfD : ∀ i : Fin n, HasDerivAt (M.f (i.val + 1)) (deriv (M.f (i.val + 1)) qstar) qstar :=
    fun i => ((hfd (i.val + 1) (by omega)).differentiableAt (Ioi_mem_nhds hq)).hasDerivAt
  have hcD : HasDerivAt M.c (deriv M.c qstar) qstar :=
    (hcd.differentiableAt (Ioi_mem_nhds hq)).hasDerivAt
  have hSD : HasDerivAt S (∑ i : Fin n, deriv (M.f (i.val + 1)) qstar) qstar := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hfD i)
  have hgD : HasDerivAt g ((n : ℝ) * ((∑ i : Fin n, deriv (M.f (i.val + 1)) qstar) / H)
      - deriv M.c qstar) qstar :=
    ((hSD.div_const H).const_mul (n : ℝ)).sub hcD
  rw [hgD.deriv] at hd0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  field_simp at hd0
  linarith
