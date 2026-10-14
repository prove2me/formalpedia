-- Prove2me | solution 1 for MetricTSP.tspOpt_le_hkValue_of_le_five
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T03:40:36.410005+00:00
-- url     : https://prove2.me/submissions/79bd0bf2-36aa-44e6-b69e-545660649dbe

import Mathlib
import Definitions.Def_MetricTSP_model

set_option autoImplicit false

namespace MetricTSP.SmallCasesT1
open MetricTSP

theorem tspOpt_le_tourCost {n : ℕ} (c : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    tspOpt c ≤ tourCost c π := by
  unfold tspOpt
  apply csInf_le
  · have hfin : {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = tourCost c π}.Finite := by
      have : {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = tourCost c π} =
          Set.range (fun π : Equiv.Perm (Fin n) => tourCost c π) := by
        ext t; simp [eq_comm]
      rw [this]; exact Set.finite_range _
    exact hfin.bddBelow
  · exact ⟨π, rfl⟩

/-- uniform feasible point -/
noncomputable def unif (n : ℕ) : Fin n → Fin n → ℝ :=
  fun u v => if u = v then 0 else 2 / ((n : ℝ) - 1)

theorem unif_isHeldKarp {n : ℕ} (hn : 3 ≤ n) : IsHeldKarp (unif n) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v; simp only [unif, eq_comm]
  · intro v; simp [unif]
  · intro u v; unfold unif; split_ifs
    · exact le_rfl
    · positivity
  · intro u v; unfold unif; split_ifs
    · norm_num
    · rw [div_le_one hpos]; linarith
  · intro v
    have h : ∀ u : Fin n, unif n v u = 2 / ((n : ℝ) - 1) - (if v = u then 2 / ((n : ℝ) - 1) else 0) := by
      intro u; unfold unif; split_ifs <;> ring
    simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro S hS hSu
    have h : ∀ u ∈ S, ∑ v ∈ Sᶜ, unif n u v = ∑ v ∈ Sᶜ, 2 / ((n : ℝ) - 1) := by
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have : u ≠ v := by
        rintro rfl; simp at hv; exact hv hu
      simp [unif, this]
    rw [Finset.sum_congr rfl h]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_compl, Fintype.card_fin]
    have hk1 : 1 ≤ S.card := Finset.card_pos.mpr hS
    have hk2 : S.card < n := by
      have := (Finset.card_lt_iff_ne_univ S).mpr hSu
      simpa using this
    rw [Nat.cast_sub hk2.le]
    have hk1' : (1 : ℝ) ≤ S.card := by exact_mod_cast hk1
    have hk2' : (S.card : ℝ) + 1 ≤ n := by exact_mod_cast hk2
    rw [show (S.card : ℝ) * (((n : ℝ) - S.card) * (2 / ((n : ℝ) - 1)))
        = 2 * (S.card * ((n : ℝ) - S.card)) / ((n : ℝ) - 1) by ring]
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1') (show (0:ℝ) ≤ (n:ℝ) - S.card - 1 by linarith)]

theorem hk_set_nonempty {n : ℕ} (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ) :
    {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}.Nonempty :=
  ⟨_, unif n, unif_isHeldKarp hn, rfl⟩

theorem le_hkValue_of_forall {n : ℕ} (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ) {a : ℝ}
    (h : ∀ x : Fin n → Fin n → ℝ, IsHeldKarp x → a ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v) :
    a ≤ hkValue c := by
  unfold hkValue
  apply le_csInf (hk_set_nonempty hn c)
  rintro t ⟨x, hx, rfl⟩
  exact h x hx

theorem cost_nonneg {n : ℕ} {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) (u v : Fin n) :
    0 ≤ c u v := by
  obtain ⟨hs, hd, ht⟩ := hc
  have := ht u v u
  rw [hd u, hs v u] at this
  linarith

theorem hkValue_nonneg {n : ℕ} (hn : 3 ≤ n) {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) :
    0 ≤ hkValue c := by
  apply le_hkValue_of_forall hn c
  intro x hx
  have : 0 ≤ ∑ u, ∑ v, c u v * x u v :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (cost_nonneg hc u v) (hx.2.2.1 u v)
  linarith

theorem le_obj_fin3 (c : Fin 3 → Fin 3 → ℝ) (hc : IsMetricCost c) (x : Fin 3 → Fin 3 → ℝ)
    (hx : IsHeldKarp x) : tspOpt c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  obtain ⟨hcs, hcd, -⟩ := hc
  obtain ⟨hxs, hxd, -, hx1, hdeg, -⟩ := hx
  have t1 := tspOpt_le_tourCost c 1
  have e1 : tourCost c 1 = c 0 1 + c 1 2 + c 2 0 := by
    simp [tourCost, Fin.sum_univ_three]
  have d0 := hdeg 0
  have d1 := hdeg 1
  simp only [Fin.sum_univ_three] at d0 d1 ⊢
  rw [hxd] at d0 d1
  rw [hxs 1 0] at d1
  have a01 : x 0 1 = 1 := by linarith [hx1 0 1, hx1 0 2]
  have a02 : x 0 2 = 1 := by linarith [hx1 0 1, hx1 0 2]
  have a12 : x 1 2 = 1 := by linarith [hx1 0 1, hx1 1 2]
  rw [hcd, hcd, hcd, hxs 1 0, hxs 2 0, hxs 2 1, hcs 1 0, hcs 2 0, hcs 2 1, a01, a02, a12]
  rw [hcs 2 0] at e1
  linarith

theorem le_obj_fin4 (c : Fin 4 → Fin 4 → ℝ) (hc : IsMetricCost c) (x : Fin 4 → Fin 4 → ℝ)
    (hx : IsHeldKarp x) : tspOpt c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  obtain ⟨hcs, hcd, -⟩ := hc
  obtain ⟨hxs, hxd, hx0, hx1, hdeg, -⟩ := hx
  have tab := tspOpt_le_tourCost c (Equiv.swap 2 3)
  have tae := tspOpt_le_tourCost c 1
  have tbe := tspOpt_le_tourCost c (Equiv.swap 1 2)
  have eab : tourCost c (Equiv.swap 2 3) = c 0 1 + c 1 3 + c 3 2 + c 2 0 := by
    simp [tourCost, Fin.sum_univ_four, Equiv.swap_apply_of_ne_of_ne]
  have eae : tourCost c 1 = c 0 1 + c 1 2 + c 2 3 + c 3 0 := by
    simp [tourCost, Fin.sum_univ_four]
  have ebe : tourCost c (Equiv.swap 1 2) = c 0 2 + c 2 1 + c 1 3 + c 3 0 := by
    simp [tourCost, Fin.sum_univ_four, Equiv.swap_apply_of_ne_of_ne]
  rw [eab] at tab
  rw [eae] at tae
  rw [ebe] at tbe
  have d0 := hdeg 0
  have d1 := hdeg 1
  have d2 := hdeg 2
  have d3 := hdeg 3
  simp only [Fin.sum_univ_four] at d0 d1 d2 d3 ⊢
  simp only [hxd, hcd, hxs 1 0, hxs 2 0, hxs 3 0, hxs 2 1, hxs 3 1, hxs 3 2,
    hcs 1 0, hcs 2 0, hcs 3 0, hcs 2 1, hcs 3 1, hcs 3 2] at d0 d1 d2 d3 tab tae tbe ⊢
  have h23 : x 2 3 = x 0 1 := by linarith
  have h13 : x 1 3 = x 0 2 := by linarith
  have h12 : x 1 2 = x 0 3 := by linarith
  have h03 : x 0 3 = 2 - x 0 1 - x 0 2 := by linarith
  rw [h23, h13, h12, h03]
  have ha := hx1 0 1
  have hb := hx1 0 2
  have he := hx1 0 3
  rw [h03] at he
  have ha0 := hx0 0 1
  have hb0 := hx0 0 2
  have he0 := hx0 0 3
  rw [h03] at he0
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr tab),
    mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr tae),
    mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr tbe)]

theorem tspOpt_le_of_bij {n : ℕ} (c : Fin n → Fin n → ℝ) (f : Fin n → Fin n)
    (hf : Function.Bijective f) : tspOpt c ≤ ∑ i, c (f i) (f (finRotate n i)) :=
  tspOpt_le_tourCost c (Equiv.ofBijective f hf)

theorem six_lemma (μ d : Fin 6 → ℝ) (K : ℝ) (hd : ∑ i, d i = 0)
    (hlo : ∀ i, -K ≤ d i) (hhi : ∀ i, d i ≤ K)
    (hA0 : ∀ a b c : Fin 6, a < b → b < c → -1 ≤ 2 * (μ a + μ b + μ c) - ∑ i, μ i) :
    0 ≤ K + ∑ i, μ i * d i := by
  have hA : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → -1 ≤ 2 * (μ a + μ b + μ c) - ∑ i, μ i := by
    intro a b c hab hac hbc
    rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
      rcases lt_or_gt_of_ne hbc with h3 | h3
    · linarith [hA0 a b c h1 h3]
    · linarith [hA0 a c b h2 h3]
    · exfalso; omega
    · linarith [hA0 c a b h2 h1]
    · linarith [hA0 b a c h1 h2]
    · exfalso; omega
    · linarith [hA0 b c a h3 h2]
    · linarith [hA0 c b a h3 h1]
  -- a 3-subset with minimal μ-sum
  have hne : (Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simp
  obtain ⟨A, hAmem, hAmin⟩ := Finset.exists_min_image _ (fun A : Finset (Fin 6) => ∑ i ∈ A, μ i) hne
  have hAcard : A.card = 3 := (Finset.mem_powersetCard.mp hAmem).2
  -- exchange property
  have hex : ∀ i ∈ A, ∀ j ∉ A, μ i ≤ μ j := by
    intro i hi j hj
    have hmem : insert j (A.erase i) ∈ (Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))) := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem (fun h => hj (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hi, hAcard]
    have h1 := hAmin _ hmem
    rw [Finset.sum_insert (fun h => hj (Finset.mem_of_mem_erase h))] at h1
    have h2 := Finset.sum_erase_add A μ hi
    linarith
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos, hAcard]; norm_num
  obtain ⟨i0, hi0, hi0max⟩ := Finset.exists_max_image A μ hAne
  set θ := μ i0 with hθ
  have hK : 0 ≤ K := by linarith [hlo 0, hhi 0]
  -- rewrite with θ
  have hsum : ∑ i, μ i * d i = ∑ i, (μ i - θ) * d i := by
    have : ∑ i, (μ i - θ) * d i = ∑ i, μ i * d i - θ * ∑ i, d i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hd]; ring
  rw [hsum, ← Finset.sum_add_sum_compl A]
  have hin : ∑ i ∈ A, (μ i - θ) * K ≤ ∑ i ∈ A, (μ i - θ) * d i := by
    apply Finset.sum_le_sum
    intro i hi
    have h1 : μ i - θ ≤ 0 := by linarith [hi0max i hi]
    nlinarith [hhi i]
  have hout : ∑ i ∈ Aᶜ, -((μ i - θ) * K) ≤ ∑ i ∈ Aᶜ, (μ i - θ) * d i := by
    apply Finset.sum_le_sum
    intro j hj
    have h1 : 0 ≤ μ j - θ := by
      have := hex i0 hi0 j (Finset.mem_compl.mp hj)
      linarith
    nlinarith [hlo j]
  have hAc : Aᶜ.card = 3 := by
    rw [Finset.card_compl, hAcard]; simp
  have e1 : ∑ i ∈ A, (μ i - θ) * K = K * (∑ i ∈ A, μ i) - K * θ * (A.card : ℝ) := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
    ring
  have e2 : ∑ i ∈ Aᶜ, -((μ i - θ) * K) = -(K * (∑ i ∈ Aᶜ, μ i)) + K * θ * (Aᶜ.card : ℝ) := by
    simp only [Finset.sum_neg_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.sum_mul]
    ring
  have hc1 : (A.card : ℝ) = 3 := by rw [hAcard]; norm_num
  have hc2 : (Aᶜ.card : ℝ) = 3 := by rw [hAc]; norm_num
  rw [hc1] at e1
  rw [hc2] at e2
  -- the 3|3 split bound
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hAcard
  have hsplit := hA a b c hab hac hbc
  have htot := Finset.sum_add_sum_compl ({a, b, c} : Finset (Fin 6)) μ
  have h3 : ∑ i ∈ ({a, b, c} : Finset (Fin 6)), μ i = μ a + μ b + μ c := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton]
    ring
  nlinarith [mul_nonneg hK (show 0 ≤ 1 + (2 * (μ a + μ b + μ c) - ∑ i, μ i) by linarith)]

theorem fin5_splits (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℝ)
    (lx01 : 0 ≤ x01) (lx02 : 0 ≤ x02) (lx03 : 0 ≤ x03) (lx04 : 0 ≤ x04) (lx12 : 0 ≤ x12) (lx13 : 0 ≤ x13) (lx14 : 0 ≤ x14) (lx23 : 0 ≤ x23) (lx24 : 0 ≤ x24) (lx34 : 0 ≤ x34)
    (ux01 : x01 ≤ 1) (ux02 : x02 ≤ 1) (ux03 : x03 ≤ 1) (ux04 : x04 ≤ 1) (ux12 : x12 ≤ 1) (ux13 : x13 ≤ 1) (ux14 : x14 ≤ 1) (ux23 : x23 ≤ 1) (ux24 : x24 ≤ 1) (ux34 : x34 ≤ 1)
    (d0 : x01 + x02 + x03 + x04 = 2) (d1 : x01 + x12 + x13 + x14 = 2) (d2 : x02 + x12 + x23 + x24 = 2) (d3 : x03 + x13 + x23 + x34 = 2) (d4 : x04 + x14 + x24 + x34 = 2) :
    ∀ p q r : Fin 6, p < q → q < r →
      -1 ≤ 2 * ((![((x01 + x12 + x23 + x34 + x04) - 5 / 2) / 3, ((x02 + x23 + x13 + x14 + x04) - 5 / 2) / 3, ((x02 + x12 + x14 + x34 + x03) - 5 / 2) / 3, ((x01 + x13 + x34 + x24 + x02) - 5 / 2) / 3, ((x01 + x14 + x24 + x23 + x03) - 5 / 2) / 3, ((x03 + x13 + x12 + x24 + x04) - 5 / 2) / 3] : Fin 6 → ℝ) p + (![((x01 + x12 + x23 + x34 + x04) - 5 / 2) / 3, ((x02 + x23 + x13 + x14 + x04) - 5 / 2) / 3, ((x02 + x12 + x14 + x34 + x03) - 5 / 2) / 3, ((x01 + x13 + x34 + x24 + x02) - 5 / 2) / 3, ((x01 + x14 + x24 + x23 + x03) - 5 / 2) / 3, ((x03 + x13 + x12 + x24 + x04) - 5 / 2) / 3] : Fin 6 → ℝ) q + (![((x01 + x12 + x23 + x34 + x04) - 5 / 2) / 3, ((x02 + x23 + x13 + x14 + x04) - 5 / 2) / 3, ((x02 + x12 + x14 + x34 + x03) - 5 / 2) / 3, ((x01 + x13 + x34 + x24 + x02) - 5 / 2) / 3, ((x01 + x14 + x24 + x23 + x03) - 5 / 2) / 3, ((x03 + x13 + x12 + x24 + x04) - 5 / 2) / 3] : Fin 6 → ℝ) r) - ∑ i, (![((x01 + x12 + x23 + x34 + x04) - 5 / 2) / 3, ((x02 + x23 + x13 + x14 + x04) - 5 / 2) / 3, ((x02 + x12 + x14 + x34 + x03) - 5 / 2) / 3, ((x01 + x13 + x34 + x24 + x02) - 5 / 2) / 3, ((x01 + x14 + x24 + x23 + x03) - 5 / 2) / 3, ((x03 + x13 + x12 + x24 + x04) - 5 / 2) / 3] : Fin 6 → ℝ) i := by
  intro p q r hpq hqr
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp [Fin.sum_univ_six] at hpq hqr ⊢ <;> linarith

theorem fin5_core (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℝ) (c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 m : ℝ)
    (lx01 : 0 ≤ x01) (lx02 : 0 ≤ x02) (lx03 : 0 ≤ x03) (lx04 : 0 ≤ x04) (lx12 : 0 ≤ x12) (lx13 : 0 ≤ x13) (lx14 : 0 ≤ x14) (lx23 : 0 ≤ x23) (lx24 : 0 ≤ x24) (lx34 : 0 ≤ x34)
    (ux01 : x01 ≤ 1) (ux02 : x02 ≤ 1) (ux03 : x03 ≤ 1) (ux04 : x04 ≤ 1) (ux12 : x12 ≤ 1) (ux13 : x13 ≤ 1) (ux14 : x14 ≤ 1) (ux23 : x23 ≤ 1) (ux24 : x24 ≤ 1) (ux34 : x34 ≤ 1)
    (d0 : x01 + x02 + x03 + x04 = 2) (d1 : x01 + x12 + x13 + x14 = 2) (d2 : x02 + x12 + x23 + x24 = 2) (d3 : x03 + x13 + x23 + x34 = 2) (d4 : x04 + x14 + x24 + x34 = 2)
    (t0 : m ≤ (c01 + c12 + c23 + c34 + c04)) (t1 : m ≤ (c02 + c23 + c13 + c14 + c04)) (t2 : m ≤ (c02 + c12 + c14 + c34 + c03)) (t3 : m ≤ (c01 + c13 + c34 + c24 + c02)) (t4 : m ≤ (c01 + c14 + c24 + c23 + c03)) (t5 : m ≤ (c03 + c13 + c12 + c24 + c04)) (t6 : m ≤ (c02 + c24 + c14 + c13 + c03)) (t7 : m ≤ (c01 + c12 + c24 + c34 + c03)) (t8 : m ≤ (c01 + c13 + c23 + c24 + c04)) (t9 : m ≤ (c03 + c23 + c12 + c14 + c04)) (t10 : m ≤ (c02 + c12 + c13 + c34 + c04)) (t11 : m ≤ (c01 + c14 + c34 + c23 + c02)) :
    m ≤ c01 * x01 + c02 * x02 + c03 * x03 + c04 * x04 + c12 * x12 + c13 * x13 + c14 * x14 + c23 * x23 + c24 * x24 + c34 * x34 := by
  have key := six_lemma (![((x01 + x12 + x23 + x34 + x04) - 5 / 2) / 3, ((x02 + x23 + x13 + x14 + x04) - 5 / 2) / 3, ((x02 + x12 + x14 + x34 + x03) - 5 / 2) / 3, ((x01 + x13 + x34 + x24 + x02) - 5 / 2) / 3, ((x01 + x14 + x24 + x23 + x03) - 5 / 2) / 3, ((x03 + x13 + x12 + x24 + x04) - 5 / 2) / 3] : Fin 6 → ℝ)
    (![(c01 + c12 + c23 + c34 + c04) - (c02 + c24 + c14 + c13 + c03), (c02 + c23 + c13 + c14 + c04) - (c01 + c12 + c24 + c34 + c03), (c02 + c12 + c14 + c34 + c03) - (c01 + c13 + c23 + c24 + c04), (c01 + c13 + c34 + c24 + c02) - (c03 + c23 + c12 + c14 + c04), (c01 + c14 + c24 + c23 + c03) - (c02 + c12 + c13 + c34 + c04), (c03 + c13 + c12 + c24 + c04) - (c01 + c14 + c34 + c23 + c02)] : Fin 6 → ℝ)
    ((c01 + c02 + c03 + c04 + c12 + c13 + c14 + c23 + c24 + c34) - 2 * m)
    (by simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring)
    (by intro i; fin_cases i <;> simp <;> linarith)
    (by intro i; fin_cases i <;> simp <;> linarith)
    (fin5_splits x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 lx01 lx02 lx03 lx04 lx12 lx13 lx14 lx23 lx24 lx34 ux01 ux02 ux03 ux04 ux12 ux13 ux14 ux23 ux24 ux34 d0 d1 d2 d3 d4)
  simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at key
  linear_combination (1 / 2 : ℝ) * key - ((1/3 : ℝ) * (c01 + c02 + c03 + c04) - (1/12 : ℝ) * (c01 + c02 + c03 + c04 + c12 + c13 + c14 + c23 + c24 + c34)) * d0 - ((1/3 : ℝ) * (c01 + c12 + c13 + c14) - (1/12 : ℝ) * (c01 + c02 + c03 + c04 + c12 + c13 + c14 + c23 + c24 + c34)) * d1 - ((1/3 : ℝ) * (c02 + c12 + c23 + c24) - (1/12 : ℝ) * (c01 + c02 + c03 + c04 + c12 + c13 + c14 + c23 + c24 + c34)) * d2 - ((1/3 : ℝ) * (c03 + c13 + c23 + c34) - (1/12 : ℝ) * (c01 + c02 + c03 + c04 + c12 + c13 + c14 + c23 + c24 + c34)) * d3 - ((1/3 : ℝ) * (c04 + c14 + c24 + c34) - (1/12 : ℝ) * (c01 + c02 + c03 + c04 + c12 + c13 + c14 + c23 + c24 + c34)) * d4

theorem le_obj_fin5 (c : Fin 5 → Fin 5 → ℝ) (hc : IsMetricCost c) (x : Fin 5 → Fin 5 → ℝ)
    (hx : IsHeldKarp x) : tspOpt c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  obtain ⟨hcs, hcd, -⟩ := hc
  obtain ⟨hxs, hxd, hx0, hx1, hdeg, -⟩ := hx
  have t0 : tspOpt c ≤ c 0 1 + c 1 2 + c 2 3 + c 3 4 + c 4 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 1, 2, 3, 4] (by decide)
  have t1 : tspOpt c ≤ c 0 2 + c 2 3 + c 3 1 + c 1 4 + c 4 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 2, 3, 1, 4] (by decide)
  have t2 : tspOpt c ≤ c 0 2 + c 2 1 + c 1 4 + c 4 3 + c 3 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 2, 1, 4, 3] (by decide)
  have t3 : tspOpt c ≤ c 0 1 + c 1 3 + c 3 4 + c 4 2 + c 2 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 1, 3, 4, 2] (by decide)
  have t4 : tspOpt c ≤ c 0 1 + c 1 4 + c 4 2 + c 2 3 + c 3 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 1, 4, 2, 3] (by decide)
  have t5 : tspOpt c ≤ c 0 3 + c 3 1 + c 1 2 + c 2 4 + c 4 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 3, 1, 2, 4] (by decide)
  have t6 : tspOpt c ≤ c 0 2 + c 2 4 + c 4 1 + c 1 3 + c 3 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 2, 4, 1, 3] (by decide)
  have t7 : tspOpt c ≤ c 0 1 + c 1 2 + c 2 4 + c 4 3 + c 3 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 1, 2, 4, 3] (by decide)
  have t8 : tspOpt c ≤ c 0 1 + c 1 3 + c 3 2 + c 2 4 + c 4 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 1, 3, 2, 4] (by decide)
  have t9 : tspOpt c ≤ c 0 3 + c 3 2 + c 2 1 + c 1 4 + c 4 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 3, 2, 1, 4] (by decide)
  have t10 : tspOpt c ≤ c 0 2 + c 2 1 + c 1 3 + c 3 4 + c 4 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 2, 1, 3, 4] (by decide)
  have t11 : tspOpt c ≤ c 0 1 + c 1 4 + c 4 3 + c 3 2 + c 2 0 := by
    simpa [Fin.sum_univ_five, finRotate_apply] using tspOpt_le_of_bij c ![0, 1, 4, 3, 2] (by decide)
  have d0 := hdeg 0
  have d1 := hdeg 1
  have d2 := hdeg 2
  have d3 := hdeg 3
  have d4 := hdeg 4
  simp only [Fin.sum_univ_five] at d0 d1 d2 d3 d4 ⊢
  simp only [hxd, hcd, hxs 1 0, hxs 2 0, hxs 3 0, hxs 4 0, hxs 2 1, hxs 3 1, hxs 4 1, hxs 3 2, hxs 4 2, hxs 4 3,
    hcs 1 0, hcs 2 0, hcs 3 0, hcs 4 0, hcs 2 1, hcs 3 1, hcs 4 1, hcs 3 2, hcs 4 2, hcs 4 3, mul_zero, add_zero, zero_add] at d0 d1 d2 d3 d4 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 ⊢
  have core := fin5_core (x 0 1) (x 0 2) (x 0 3) (x 0 4) (x 1 2) (x 1 3) (x 1 4) (x 2 3) (x 2 4) (x 3 4) (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 1 2) (c 1 3) (c 1 4) (c 2 3) (c 2 4) (c 3 4) (tspOpt c)
    (hx0 0 1) (hx0 0 2) (hx0 0 3) (hx0 0 4) (hx0 1 2) (hx0 1 3) (hx0 1 4) (hx0 2 3) (hx0 2 4) (hx0 3 4)
    (hx1 0 1) (hx1 0 2) (hx1 0 3) (hx1 0 4) (hx1 1 2) (hx1 1 3) (hx1 1 4) (hx1 2 3) (hx1 2 4) (hx1 3 4)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

theorem tspOpt_le_hkValue_le_five (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ hkValue c := by
  apply le_hkValue_of_forall hn c
  intro x hx
  interval_cases n
  · exact le_obj_fin3 c hc x hx
  · exact le_obj_fin4 c hc x hx
  · exact le_obj_fin5 c hc x hx

end MetricTSP.SmallCasesT1

open MetricTSP in
theorem solution (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ hkValue c :=
  MetricTSP.SmallCasesT1.tspOpt_le_hkValue_le_five n hn hn5 c hc
