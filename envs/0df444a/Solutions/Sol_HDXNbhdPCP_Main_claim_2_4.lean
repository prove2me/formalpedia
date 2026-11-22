-- Prove2me | solution 1 for HDXNbhdPCP.Main.claim_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T20:05:02.956797+00:00
-- url     : https://prove2.me/submissions/3b83c667-e72d-40c4-9cbe-33f926c74cf2

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex

open HDXNbhdPCP.Main

namespace HDXNbhdPCP.Main.Claim24Aux

open Classical

lemma left_w_nonneg {L R : Type} (G : BipGraph L R) (hG : FinDist.IsProb G) (l : L) :
    0 ≤ G.left.w l := by
  unfold BipGraph.left FinDist.map
  exact Finset.sum_nonneg (fun e he => le_of_lt (hG.1 e (Finset.mem_filter.1 he).1))

lemma right_w_nonneg {L R : Type} (G : BipGraph L R) (hG : FinDist.IsProb G) (r : R) :
    0 ≤ G.right.w r := by
  unfold BipGraph.right FinDist.map
  exact Finset.sum_nonneg (fun e he => le_of_lt (hG.1 e (Finset.mem_filter.1 he).1))

lemma right_w_pos {L R : Type} (G : BipGraph L R) (hG : FinDist.IsProb G) (r : R)
    (hr : r ∈ G.right.supp) : 0 < G.right.w r := by
  unfold BipGraph.right FinDist.map at *
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hr
  apply Finset.sum_pos (fun x hx => hG.1 x (Finset.mem_filter.1 hx).1)
  exact ⟨e, Finset.mem_filter.2 ⟨he, rfl⟩⟩

lemma left_sum {L R : Type} (G : BipGraph L R) (hG : FinDist.IsProb G) :
    ∑ l ∈ G.left.supp, G.left.w l = 1 := by
  unfold BipGraph.left FinDist.map
  rw [← hG.2]
  convert Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := G.supp.image Prod.fst)
    (fun e he => Finset.mem_image_of_mem Prod.fst he) (f := G.w)

end HDXNbhdPCP.Main.Claim24Aux

open Classical

open HDXNbhdPCP.Main.Claim24Aux in
theorem solution {L R : Type} (G : HDXNbhdPCP.Main.BipGraph L R)
    (hG : HDXNbhdPCP.Main.FinDist.IsProb G) (lam : ℝ)
    (hexp : G.IsExpander lam) : G.IsSampler (lam ^ 2) := by
  intro f hf ε hε
  set μ := G.left.expect f with hμ
  set g : L → ℝ := fun l => f l - μ with hg
  have hsumL := left_sum G hG
  -- mean zero
  have hg0 : G.left.expect g = 0 := by
    unfold HDXNbhdPCP.Main.FinDist.expect
    have : ∀ l, G.left.w l * g l = G.left.w l * f l - μ * G.left.w l := by
      intro l; simp only [hg]; ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumL]
    rw [hμ]; unfold HDXNbhdPCP.Main.FinDist.expect; ring
  -- variance bound
  have hvar : G.left.expect (fun l => g l ^ 2) ≤ μ := by
    unfold HDXNbhdPCP.Main.FinDist.expect
    calc ∑ l ∈ G.left.supp, G.left.w l * g l ^ 2
        ≤ ∑ l ∈ G.left.supp, ((1 - 2 * μ) * (G.left.w l * f l) + μ ^ 2 * G.left.w l) := by
          apply Finset.sum_le_sum
          intro l _
          have hw := left_w_nonneg G hG l
          have h1 := hf l
          have : g l ^ 2 ≤ f l - 2 * μ * f l + μ ^ 2 := by
            simp only [hg]; nlinarith [h1.1, h1.2]
          nlinarith [mul_le_mul_of_nonneg_left this hw]
      _ = (1 - 2 * μ) * μ + μ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumL, hμ]
          unfold HDXNbhdPCP.Main.FinDist.expect; ring
      _ = μ - μ ^ 2 := by ring
      _ ≤ μ := by nlinarith [sq_nonneg μ]
  -- averaging operator of g
  have havg : ∀ r ∈ G.right.supp, G.avg g r = G.avg f r - μ := by
    intro r hr
    have hpos := right_w_pos G hG r hr
    unfold HDXNbhdPCP.Main.BipGraph.avg
    have hrw : G.right.w r = ∑ e ∈ G.supp.filter (fun e : L × R => e.2 = r), G.w e := rfl
    have : ∀ e, G.w e * g e.1 = G.w e * f e.1 - μ * G.w e := by
      intro e; simp only [hg]; ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hrw]
    field_simp
  -- expander inequality squared
  have ha0 : 0 ≤ G.right.expect (fun r => G.avg g r ^ 2) :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (right_w_nonneg G hG r) (sq_nonneg _))
  have hb0 : 0 ≤ G.left.expect (fun l => g l ^ 2) :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (left_w_nonneg G hG l) (sq_nonneg _))
  have hE := hexp g hg0
  have hsq : G.right.expect (fun r => G.avg g r ^ 2) ≤
      lam ^ 2 * G.left.expect (fun l => g l ^ 2) := by
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hE 2
    rw [Real.sq_sqrt ha0, mul_pow, Real.sq_sqrt hb0] at h1
    exact h1
  -- Chebyshev
  have hcheb : G.right.prob (fun r => |G.avg f r - G.left.expect f| > ε) ≤
      G.right.expect (fun r => G.avg g r ^ 2) / ε ^ 2 := by
    unfold HDXNbhdPCP.Main.FinDist.prob HDXNbhdPCP.Main.FinDist.expect
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [Finset.sum_div]
    calc ∑ r ∈ G.right.supp.filter (fun r => |G.avg f r - G.left.expect f| > ε), G.right.w r
        ≤ ∑ r ∈ G.right.supp.filter (fun r => |G.avg f r - G.left.expect f| > ε),
            G.right.w r * G.avg g r ^ 2 / ε ^ 2 := by
          apply Finset.sum_le_sum
          intro r hr
          obtain ⟨hr1, hr2⟩ := Finset.mem_filter.1 hr
          rw [havg r hr1]
          have hw := right_w_nonneg G hG r
          have hlt : ε ^ 2 < (G.avg f r - μ) ^ 2 := by
            have : ε < |G.avg f r - μ| := hr2
            rw [← sq_abs (G.avg f r - μ)]
            exact pow_lt_pow_left₀ this hε.le (by norm_num)
          rw [le_div_iff₀ hε2]
          nlinarith
      _ ≤ ∑ r ∈ G.right.supp, G.right.w r * G.avg g r ^ 2 / ε ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro r _ _
          exact div_nonneg (mul_nonneg (right_w_nonneg G hG r) (sq_nonneg _)) hε2.le
  have hε2 : 0 < ε ^ 2 := by positivity
  calc G.right.prob (fun r => |G.avg f r - G.left.expect f| > ε)
      ≤ G.right.expect (fun r => G.avg g r ^ 2) / ε ^ 2 := hcheb
    _ ≤ lam ^ 2 * μ / ε ^ 2 := by
        apply div_le_div_of_nonneg_right _ hε2.le
        exact le_trans hsq (mul_le_mul_of_nonneg_left hvar (sq_nonneg lam))
    _ = lam ^ 2 / ε ^ 2 * G.left.expect f := by rw [hμ]; ring
