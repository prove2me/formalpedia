-- Prove2me | solution 1 for MulticlassQNet.FirstOrder.theorem_4_4_nonparametric_dominates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:24:41.849184+00:00
-- url     : https://prove2.me/submissions/af353e82-911e-462d-8bbf-f64fcd33f1a2

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints



namespace MulticlassQNet.FirstOrder

open Finset in
theorem nonparam_core {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam)
    (n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) (Nv : Fin N → Fin R → ℝ)
    (hI : ∀ r r', 0 ≤ I r r') (hNv : ∀ i r', 0 ≤ Nv i r')
    (h24 : net.Eq24 lam n I) (h25 : net.Eq25 lam n I) (h28 : net.Eq28 n I Nv)
    (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ)
    (hF : net.FCondition S f fi) (hf : ∀ r ∈ S, 0 ≤ f r) :
    net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * n r := by
  -- symmetric second-moment combination
  set H : Fin R → Fin R → ℝ := fun r r' =>
    net.μ r * I r r' - ∑ w, net.μ w * net.p w r' * I w r - net.lam0 r' * n r with hH
  set c : Fin R → Fin R → ℝ := fun r r' =>
    (if r = r' then 2 * lam r else 0) - lam r * net.p r r' - lam r' * net.p r' r with hc
  have hG : ∀ r r', H r r' + H r' r = c r r' := by
    intro r r'
    rcases lt_trichotomy r' r with h | h | h
    · have := h25 r r' h
      simp only [hH, hc, if_neg (ne_of_gt h)]
      linarith
    · subst h
      have e24 := h24 r'
      have ht := htraffic r'
      have hs : ∑ w ∈ univ.erase r', lam w * net.p w r' = ∑ w, lam w * net.p w r'
          - lam r' * net.p r' r' := by
        rw [← Finset.add_sum_erase _ _ (mem_univ r')]; ring
      rw [hs] at e24
      simp only [hH, hc, if_true]
      linarith
    · have := h25 r' r h
      simp only [hH, hc, if_neg (ne_of_lt h)]
      linarith
  set J : Fin R → ℝ := fun w => ∑ r' ∈ S, f r' * I w r' with hJ
  set Φ := ∑ r ∈ S, f r * n r with hΦ
  set L := ∑ r ∈ S, net.lam0 r * f r with hL
  have hJ0 : ∀ w, 0 ≤ J w := fun w => sum_nonneg (fun r' hr' => mul_nonneg (hf r' hr') (hI w r'))
  -- double sum of H
  have hsumH : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r r'
      = ∑ r ∈ S, f r * net.μ r * J r - ∑ w, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w - L * Φ := by
    simp only [hH, hJ, hL, hΦ, mul_sub, sum_sub_distrib, mul_sum, sum_mul]
    congr 1; congr 1
    · apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
    · rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]; rw [Finset.sum_comm]
      apply sum_congr rfl; intro w _
      apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring
    · apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
  have hsym : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * c r r'
      = 2 * ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r r' := by
    have e : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r' r = ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r r' := by
      rw [sum_comm]; apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
    rw [two_mul]; nth_rewrite 2 [← e]; rw [← sum_add_distrib]
    apply sum_congr rfl; intro r _; rw [← sum_add_distrib]
    apply sum_congr rfl; intro r' _; rw [← hG]; ring
  -- the c double sum equals N'
  have hN : net.Nprime lam S f = ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * c r r' := by
    have e1 : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * c r r'
        = 2 * ∑ r ∈ S, lam r * f r ^ 2 - 2 * ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r' := by
      simp only [hc, mul_sub, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq, mul_sum]
      have e : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * (lam r' * net.p r' r)
          = ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r' := by
        rw [sum_comm]; apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
      rw [e]
      have e2 : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * (lam r * net.p r r')
          = ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r' := by
        apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
      rw [e2]
      have e3 : ∑ r ∈ S, (if r ∈ S then f r * f r * (2 * lam r) else 0)
          = 2 * ∑ r ∈ S, lam r * f r ^ 2 := by
        rw [mul_sum]; apply sum_congr rfl; intro r hr; rw [if_pos hr]; ring
      rw [e3]; ring_nf; simp only [Finset.sum_mul]
    rw [e1]
    -- traffic: ∑_r lam r net.p r r' = lam r' - net.lam0 r'
    have htr : ∀ r', ∑ r, lam r * net.p r r' = lam r' - net.lam0 r' := by
      intro r'; have := htraffic r'; linarith
    have hall : ∑ r, lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2 = ∑ r' ∈ S, (lam r' - net.lam0 r') * f r' ^ 2 := by
      simp only [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro r' _
      rw [← htr r', sum_mul]; apply sum_congr rfl; intro r _; ring
    have hsplit := sum_add_sum_compl S (fun r => lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2)
    have hrow : ∀ r, ∑ r' ∈ Sᶜ, net.p r r' + net.exitProb r = 1 - ∑ r' ∈ S, net.p r r' := by
      intro r; simp only [Network.exitProb]; have := sum_add_sum_compl S (fun r' => net.p r r'); 
      linarith
    simp only [Network.Nprime]
    simp only [hrow]
    have e4 : ∑ r ∈ S, lam r * (∑ r' ∈ S, net.p r r' * (f r - f r') ^ 2 + (1 - ∑ r' ∈ S, net.p r r') * f r ^ 2)
        = ∑ r ∈ S, lam r * f r ^ 2 - 2 * ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r'
          + ∑ r ∈ S, lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2 := by
      have hexp : ∀ r, ∑ r' ∈ S, net.p r r' * (f r - f r') ^ 2 = (∑ r' ∈ S, net.p r r') * f r ^ 2
          - 2 * f r * ∑ r' ∈ S, net.p r r' * f r' + ∑ r' ∈ S, net.p r r' * f r' ^ 2 := by
        intro r; rw [sum_mul, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        apply sum_congr rfl; intro _ _; ring
      have hdbl : ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r'
          = ∑ r ∈ S, lam r * f r * ∑ r' ∈ S, net.p r r' * f r' := by
        apply sum_congr rfl; intro r _; rw [mul_sum]; apply sum_congr rfl; intro _ _; ring
      rw [hdbl]; simp only [hexp]
      rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]; apply sum_congr rfl; intro r _; ring
    rw [e4]
    have e5 : ∑ r' ∈ S, (lam r' - net.lam0 r') * f r' ^ 2 = ∑ r ∈ S, lam r * f r ^ 2
        - ∑ r ∈ S, net.lam0 r * f r ^ 2 := by rw [← sum_sub_distrib]; apply sum_congr rfl; intro r _; ring
    linarith
  -- use FCondition
  have hFw : ∀ w ∈ S, net.μ w * f w - net.μ w * ∑ s ∈ S, net.p w s * f s = fi (net.σ w) := by
    intro w hw
    have h1 := hF.1 w hw
    have hs := sum_add_sum_compl S (fun s => net.p w s)
    simp only [Network.exitProb] at h1
    rw [← h1]
    have : ∑ r' ∈ S, net.p w r' * (f w - f r') = f w * ∑ r' ∈ S, net.p w r' - ∑ s ∈ S, net.p w s * f s := by
      rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro _ _; ring
    rw [this]
    have : ∑ r' ∈ Sᶜ, net.p w r' + (1 - ∑ s, net.p w s) = 1 - ∑ r' ∈ S, net.p w r' := by linarith
    rw [this]; ring
  have hsplitW : ∑ w, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w
      = ∑ w ∈ S, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w
        + ∑ w ∈ Sᶜ, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w := (sum_add_sum_compl S _).symm
  have hnegpart : 0 ≤ ∑ w ∈ Sᶜ, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w := by
    apply sum_nonneg; intro w _
    apply mul_nonneg (mul_nonneg (le_of_lt (net.μ_pos w)) ?_) (hJ0 w)
    exact sum_nonneg (fun s hs => mul_nonneg (net.p_nonneg w s) (hf s hs))
  have hmain : ∑ r ∈ S, f r * net.μ r * J r - ∑ w ∈ S, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w
      = ∑ w ∈ S, fi (net.σ w) * J w := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro w hw; rw [← hFw w hw]; ring
  have hfiber : ∑ w ∈ S, fi (net.σ w) * J w ≤ (∑ i, fi i) * Φ := by
    calc ∑ w ∈ S, fi (net.σ w) * J w ≤ ∑ w, fi (net.σ w) * J w :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun w _ _ =>
            mul_nonneg (hF.2.1 _) (hJ0 w))
      _ = ∑ i, ∑ w ∈ net.C i, fi (net.σ w) * J w := by
          rw [← sum_fiberwise univ net.σ]; rfl
      _ = ∑ i, fi i * (Φ - ∑ r' ∈ S, f r' * Nv i r') := by
          apply sum_congr rfl; intro i _
          have : ∀ w ∈ net.C i, fi (net.σ w) * J w = fi i * J w := by
            intro w hw; simp [Network.C] at hw; rw [hw]
          rw [sum_congr rfl this, ← mul_sum]; congr 1
          simp only [hJ, hΦ]; rw [sum_comm, ← sum_sub_distrib]; apply sum_congr rfl
          intro r' _; rw [← mul_sum, ← h28 i r']; ring
      _ ≤ ∑ i, fi i * Φ := by
          apply sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (hF.2.1 i)
          have : 0 ≤ ∑ r' ∈ S, f r' * Nv i r' :=
            sum_nonneg (fun r' hr' => mul_nonneg (hf r' hr') (hNv i r'))
          linarith
      _ = (∑ i, fi i) * Φ := by rw [sum_mul]
  rw [hN, hsym, hsumH]
  simp only [Network.Dprime]
  rw [← hL]
  nlinarith [hfiber, hnegpart, hmain, hsplitW]

end MulticlassQNet.FirstOrder

open MulticlassQNet.FirstOrder


theorem solution {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (x : Fin R → ℝ) (I : Fin R → Fin R → ℝ) (Nv : Fin N → Fin R → ℝ)
    (hx : ∀ r, 0 ≤ x r) (hI : ∀ r r', 0 ≤ I r r') (hNv : ∀ i r', 0 ≤ Nv i r')
    (h24 : net.Eq24 lam (fun r => lam r * x r) I)
    (h25 : net.Eq25 lam (fun r => lam r * x r) I)
    (h28 : net.Eq28 (fun r => lam r * x r) I Nv) :
    ∀ (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ),
      net.FCondition S f fi → (∀ r ∈ S, 0 ≤ f r) →
        net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * (lam r * x r) := by
  exact fun S f fi hF hf => nonparam_core net lam htraffic (fun r => lam r * x r) I Nv hI hNv h24 h25 h28 S f fi hF hf
