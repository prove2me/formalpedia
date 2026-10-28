-- Prove2me | solution 1 for LiquidPoA.Kelly.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:06:44.106084+00:00
-- url     : https://prove2.me/submissions/3734099e-c86c-4d27-bf47-6de60c65ab54

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

open Set
open scoped ENNReal

section Aux

lemma tangent_convex {S : Set ℝ} {f : ℝ → ℝ} {f' x y : ℝ} (hc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivWithinAt f f' S x) :
    f x + f' * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with h | h | h
  · have h1 := hc.le_slope_of_hasDerivWithinAt hx hy h hd
    rw [slope_def_field] at h1
    have : 0 < y - x := sub_pos.mpr h
    rw [le_div_iff₀ this] at h1
    linarith
  · subst h; simp
  · have h1 := hc.slope_le_of_hasDerivWithinAt hy hx h hd
    rw [slope_def_field] at h1
    have : 0 < x - y := sub_pos.mpr h
    rw [div_le_iff₀ this] at h1
    nlinarith

lemma tangent_concave {S : Set ℝ} {f : ℝ → ℝ} {f' x y : ℝ} (hc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivWithinAt f f' S x) :
    f y ≤ f x + f' * (y - x) := by
  have := tangent_convex hc.neg hx hy hd.neg
  simp only [Pi.neg_apply] at this
  linarith


variable {n : ℕ} {M : Mechanism n}

lemma isSignal_update {s : Fin n → ℝ} (hs : IsSignal s) {y : ℝ} (hy : 0 ≤ y) (i : Fin n) :
    IsSignal (Function.update s i y) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hy
  · simpa [Function.update_of_ne h] using hs j

lemma alloc_le_one (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n) :
    M.alloc s i ≤ 1 := by
  obtain ⟨h0, h1 | h1⟩ := hM.alloc_mem s hs
  · calc M.alloc s i ≤ ∑ j, M.alloc s j :=
          Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
      _ = 1 := h1
  · rw [h1 i]; norm_num

lemma allocIn_mem (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n) :
    MapsTo (allocIn M s i) (Ici 0) (Icc 0 1) := by
  intro y hy
  have hsig := isSignal_update hs (show (0:ℝ) ≤ y from hy) i
  exact ⟨(hM.alloc_mem _ hsig).1 i, alloc_le_one hM hsig i⟩

lemma allocIn_self (s : Fin n → ℝ) (i : Fin n) : allocIn M s i (s i) = M.alloc s i := by
  simp [allocIn]

lemma payIn_self (s : Fin n → ℝ) (i : Fin n) : payIn M s i (s i) = M.pay s i := by
  simp [payIn]

lemma allocIn_zero (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n) :
    allocIn M s i 0 = 0 :=
  (hM.zero_sig _ (isSignal_update hs le_rfl i) i (by simp)).1

lemma payIn_zero (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n) :
    payIn M s i 0 = 0 :=
  (hM.zero_sig _ (isSignal_update hs le_rfl i) i (by simp)).2

lemma exists_other {s : Fin n → ℝ} (hs : InX s) (i : Fin n) : ∃ j, j ≠ i ∧ 0 < s j := by
  obtain ⟨_, i0, j0, hij, h0, h1⟩ := hs
  by_cases h : i = i0
  · exact ⟨j0, fun e => hij (h.symm.trans e.symm |>.symm ▸ rfl) , h1⟩
  · exact ⟨i0, fun e => h e.symm, h0⟩


lemma alloc_pos_of_pos (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (i : Fin n)
    (hi : 0 < s i) : 0 < M.alloc s i := by
  have h := hM.alloc_incr s hs.1 i (exists_other hs i)
  have := h (Set.mem_Ici.mpr le_rfl) (show s i ∈ Ici 0 from hs.1 i) hi
  rwa [allocIn_zero hM hs.1, allocIn_self] at this

lemma pay_pos_of_pos (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n)
    (hi : 0 < s i) : 0 < M.pay s i := by
  have h := hM.pay_incr s hs i
  have := h (Set.mem_Ici.mpr le_rfl) (show s i ∈ Ici 0 from hs i) hi
  rwa [payIn_zero hM hs, payIn_self] at this

lemma sum_alloc (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) :
    ∑ j, M.alloc s j = 1 := by
  obtain ⟨_, i0, _, _, h0, _⟩ := id hs
  rcases (hM.alloc_mem s hs.1).2 with h | h
  · exact h
  · exfalso
    have := alloc_pos_of_pos hM hs i0 h0
    rw [h i0] at this; exact lt_irrefl _ this

lemma lam_nonneg (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (i : Fin n) :
    0 ≤ lam M s i := by
  unfold lam
  apply mul_nonneg (inv_nonneg.2 (hM.deriv_pos s hs i).le)
  exact ((hM.pay_incr s hs.1 i).monotoneOn).derivWithin_nonneg

lemma eventually_afford {P : ℝ → ℝ} {S : Set ℝ} {x : ℝ} {c : ℝ≥0∞}
    (hc : ContinuousWithinAt P S x) (h : ENNReal.ofReal (P x) < c) :
    ∀ᶠ y in nhdsWithin x S, ENNReal.ofReal (P y) ≤ c := by
  have h1 : ContinuousWithinAt (fun y => ENNReal.ofReal (P y)) S x :=
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt hc
  exact (h1.eventually (Iio_mem_nhds h)).mono fun y hy => le_of_lt hy

lemma foc (hM : IsRAMechanism M) {G : RAGame n} (hG : G.IsAdmissible) {s : Fin n → ℝ}
    (hs : InX s) (heq : IsEquilibrium M G s) (i : Fin n)
    (hnb : ENNReal.ofReal (M.pay s i) < G.c i) :
    (∀ x ∈ Icc (0:ℝ) 1, G.v i x ≤ G.v i (M.alloc s i) + lam M s i * max (x - M.alloc s i) 0) ∧
    lam M s i * M.alloc s i ≤ G.v i (M.alloc s i) := by
  have hsig := hs.1
  obtain ⟨hdA, hdP⟩ := hM.diff s hsig i (exists_other hs i)
  have hmem : s i ∈ Ici (0:ℝ) := hsig i
  have hA := (hdA (s i) hmem).hasDerivWithinAt
  have hP := (hdP (s i) hmem).hasDerivWithinAt
  have hApos : 0 < derivWithin (allocIn M s i) (Ici 0) (s i) := hM.deriv_pos s hs i
  have hlam : lam M s i = (derivWithin (allocIn M s i) (Ici 0) (s i))⁻¹ *
      derivWithin (payIn M s i) (Ici 0) (s i) := rfl
  have hlam0 := lam_nonneg hM hs i
  set A' := derivWithin (allocIn M s i) (Ici 0) (s i)
  set P' := derivWithin (payIn M s i) (Ici 0) (s i)
  have hmaps := allocIn_mem hM hsig i
  have hva : M.alloc s i ∈ Icc (0:ℝ) 1 := by
    have := hmaps hmem; rwa [allocIn_self] at this
  have hv := ((hG.diff i) _ hva).hasDerivWithinAt
  set v' := derivWithin (G.v i) (Icc 0 1) (M.alloc s i)
  have hcomp : HasDerivWithinAt (fun y => G.v i (allocIn M s i y)) (v' * A') (Ici 0) (s i) := by
    have hv2 : HasDerivWithinAt (G.v i) v' (Icc 0 1) (allocIn M s i (s i)) := by
      rwa [allocIn_self]
    exact hv2.comp (s i) hA hmaps
  have hf := hcomp.sub hP
  have hlocal : IsLocalMaxOn (fun y => G.v i (allocIn M s i y) - payIn M s i y)
      (Ici 0) (s i) := by
    have hcont : ContinuousWithinAt (payIn M s i) (Ici 0) (s i) := hP.continuousWithinAt
    have hnb' : ENNReal.ofReal (payIn M s i (s i)) < G.c i := by rwa [payIn_self]
    filter_upwards [eventually_afford hcont hnb', self_mem_nhdsWithin] with y hy hy0
    have hdev := (heq.2 i).2 y hy0 hy
    have hu : utility M G s i = G.v i (allocIn M s i (s i)) - payIn M s i (s i) := by
      simp [utility, allocIn, payIn]
    simp only [utility, allocIn, payIn] at hdev hu ⊢
    simpa using hdev
  have hF := hf.hasFDerivWithinAt
  have hpos1 : (1:ℝ) ∈ posTangentConeAt (Ici (0:ℝ)) (s i) :=
    mem_posTangentConeAt_of_segment_subset
      ((convex_Ici (0:ℝ)).segment_subset hmem (show s i + 1 ∈ Ici (0:ℝ) from by
        have := hsig i; simp only [mem_Ici] at *; linarith))
  have hle := hlocal.hasFDerivWithinAt_nonpos hF hpos1
  simp at hle
  have htan : ∀ x ∈ Icc (0:ℝ) 1, G.v i x ≤ G.v i (M.alloc s i) + v' * (x - M.alloc s i) :=
    fun x hx => tangent_concave (hG.concave i) hva hx hv
  have hv0 : 0 ≤ G.v i 0 := hG.nonneg i 0 ⟨le_rfl, zero_le_one⟩
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rcases (hsig i).eq_or_lt with h0 | hpos
  · have ha0 : M.alloc s i = 0 := (hM.zero_sig s hsig i h0.symm).1
    have hv' : v' ≤ lam M s i := by
      rw [hlam, inv_mul_eq_div, le_div_iff₀ hApos]; linarith
    constructor
    · intro x hx
      have := htan x hx
      rw [ha0] at this ⊢
      have hmax : max (x - 0) 0 = x := by simp [hx.1]
      rw [hmax]
      nlinarith [mul_le_mul_of_nonneg_right hv' hx.1]
    · rw [ha0]; simpa using hv0
  · have hneg : (-(s i) : ℝ) ∈ posTangentConeAt (Ici (0:ℝ)) (s i) :=
      mem_posTangentConeAt_of_segment_subset
        ((convex_Ici (0:ℝ)).segment_subset hmem (show s i + -(s i) ∈ Ici (0:ℝ) from by simp))
    have hle2 := hlocal.hasFDerivWithinAt_nonpos hF hneg
    simp at hle2
    have hg : v' * A' - P' = 0 := by nlinarith
    have hvl : v' = lam M s i := by
      rw [hlam, inv_mul_eq_div, eq_div_iff hApos.ne']; linarith
    constructor
    · intro x hx
      have := htan x hx
      rw [hvl] at this
      have : lam M s i * (x - M.alloc s i) ≤ lam M s i * max (x - M.alloc s i) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hlam0
      linarith [htan x hx, hvl ▸ htan x hx]
    · have := htan 0 h0mem
      rw [hvl] at this
      nlinarith


lemma pay_le_val (hM : IsRAMechanism M) {G : RAGame n} (hG : G.IsAdmissible)
    {s : Fin n → ℝ} (hs : IsSignal s) (heq : IsEquilibrium M G s) (i : Fin n) :
    M.pay s i ≤ G.v i (M.alloc s i) := by
  have hafford : Affordable M G (Function.update s i 0) i := by
    have h0 := payIn_zero hM hs i
    simp only [payIn] at h0
    simp [Affordable, h0]
  have hdev := (heq.2 i).2 0 le_rfl hafford
  have h1 := allocIn_zero hM hs i
  have h2 := payIn_zero hM hs i
  simp only [allocIn] at h1
  simp only [payIn] at h2
  simp only [utility, h1, h2] at hdev
  have hv0 : 0 ≤ G.v i 0 := hG.nonneg i 0 ⟨le_rfl, zero_le_one⟩
  linarith

lemma lwterm_a_ge (hM : IsRAMechanism M) {G : RAGame n} (hG : G.IsAdmissible)
    {s : Fin n → ℝ} (hs : IsSignal s) (heq : IsEquilibrium M G s) (i : Fin n) :
    ENNReal.ofReal (M.pay s i) ≤ min (ENNReal.ofReal (G.v i (M.alloc s i))) (G.c i) :=
  le_min (ENNReal.ofReal_le_ofReal (pay_le_val hM hG hs heq i)) (heq.2 i).1

lemma isAlloc_mem {d : Fin n → ℝ} (hd : IsAllocation d) (i : Fin n) : d i ∈ Icc (0:ℝ) 1 := by
  obtain ⟨h0, h1 | h1⟩ := hd
  · refine ⟨h0 i, ?_⟩
    calc d i ≤ ∑ j, d j := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
      _ = 1 := h1
  · rw [h1 i]; norm_num

lemma lwterm_le (hM : IsRAMechanism M) {G : RAGame n} (hG : G.IsAdmissible)
    {s : Fin n → ℝ} (hs : InX s) (heq : IsEquilibrium M G s) {d : Fin n → ℝ}
    (hd : IsAllocation d) (i : Fin n) :
    min (ENNReal.ofReal (G.v i (d i))) (G.c i) ≤
      min (ENNReal.ofReal (G.v i (M.alloc s i))) (G.c i) +
        ENNReal.ofReal (if ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i then
          lam M s i * max (d i - M.alloc s i) 0 else 0) := by
  split_ifs with hT
  · have hnb : ENNReal.ofReal (M.pay s i) < G.c i :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (pay_le_val hM hG hs.1 heq i)) hT
    obtain ⟨h1, _⟩ := foc hM hG hs heq i hnb
    have hdi := isAlloc_mem hd i
    have hw0 : 0 ≤ G.v i (M.alloc s i) := by
      have := hM.alloc_mem s hs.1
      exact hG.nonneg i _ (isAlloc_mem this i)
    have hlam := lam_nonneg hM hs i
    rw [min_eq_left hT.le]
    calc min (ENNReal.ofReal (G.v i (d i))) (G.c i) ≤ ENNReal.ofReal (G.v i (d i)) := min_le_left _ _
      _ ≤ ENNReal.ofReal (G.v i (M.alloc s i) + lam M s i * max (d i - M.alloc s i) 0) :=
          ENNReal.ofReal_le_ofReal (h1 _ hdi)
      _ = _ := ENNReal.ofReal_add hw0 (mul_nonneg hlam (le_max_right _ _))
  · rw [ENNReal.ofReal_zero, add_zero, min_eq_right (not_lt.mp hT)]
    exact min_le_right _ _


lemma den_pos (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (j : Fin n) :
    0 < (∑ k ∈ Finset.univ.erase j, M.pay s k) + lam M s j * M.alloc s j := by
  obtain ⟨k, hkj, hk⟩ := exists_other hs j
  have h1 : 0 < M.pay s k := pay_pos_of_pos hM hs.1 k hk
  have h2 : M.pay s k ≤ ∑ k ∈ Finset.univ.erase j, M.pay s k :=
    Finset.single_le_sum (f := fun k => M.pay s k) (fun i _ => hM.pay_nonneg s hs.1 i)
      (Finset.mem_erase.2 ⟨hkj, Finset.mem_univ k⟩)
  have h3 : 0 ≤ lam M s j * M.alloc s j :=
    mul_nonneg (lam_nonneg hM hs j) ((hM.alloc_mem s hs.1).1 j)
  linarith

lemma ratio_eq (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (j : Fin n) :
    ratio M s j = ENNReal.ofReal (((∑ k ∈ Finset.univ.erase j, M.pay s k) + lam M s j) /
      ((∑ k ∈ Finset.univ.erase j, M.pay s k) + lam M s j * M.alloc s j)) := by
  unfold ratio
  rw [ENNReal.ofReal_div_of_pos (den_pos hM hs j)]

lemma one_le_ratio (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (j : Fin n) :
    1 ≤ ratio M s j := by
  rw [ratio_eq hM hs j, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ (den_pos hM hs j), one_mul]
  have := mul_le_mul_of_nonneg_left (alloc_le_one hM hs.1 j) (lam_nonneg hM hs j)
  linarith

lemma main_exists (hM : IsRAMechanism M) {G : RAGame n} (hG : G.IsAdmissible)
    {s : Fin n → ℝ} (hs : InX s) (heq : IsEquilibrium M G s) :
    ∃ j, ∀ d, IsAllocation d → LW G d ≤ ratio M s j * LW G (M.alloc s) := by
  classical
  have hsig := hs.1
  have hbound : ∀ d, IsAllocation d → LW G d ≤ LW G (M.alloc s) +
      ENNReal.ofReal (∑ i, (if ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i then
        lam M s i * max (d i - M.alloc s i) 0 else 0)) := by
    intro d hd
    have hnn : ∀ i, 0 ≤ (if ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i then
        lam M s i * max (d i - M.alloc s i) 0 else 0) := fun i => by
      split_ifs
      · exact mul_nonneg (lam_nonneg hM hs i) (le_max_right _ _)
      · exact le_rfl
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i)]
    unfold LW
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => lwterm_le hM hG hs heq hd i
  by_cases hT : ∃ i, ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i
  · obtain ⟨j, hjT, hjmax⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun i => ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i))
      (fun i => lam M s i * (1 - M.alloc s i))
      (by obtain ⟨i, hi⟩ := hT; exact ⟨i, by simp [hi]⟩)
    have hjT' : ENNReal.ofReal (G.v j (M.alloc s j)) < G.c j := by simpa using hjT
    refine ⟨j, fun d hd => ?_⟩
    have hm0 : 0 ≤ lam M s j * (1 - M.alloc s j) :=
      mul_nonneg (lam_nonneg hM hs j) (sub_nonneg.2 (alloc_le_one hM hsig j))
    have hsumE : (∑ i, (if ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i then
        lam M s i * max (d i - M.alloc s i) 0 else 0)) ≤ lam M s j * (1 - M.alloc s j) := by
      have hterm : ∀ i, (if ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i then
          lam M s i * max (d i - M.alloc s i) 0 else 0) ≤
          (lam M s j * (1 - M.alloc s j)) * d i := by
        intro i
        have hdi := isAlloc_mem hd i
        have hai : 0 ≤ M.alloc s i := (hM.alloc_mem s hsig).1 i
        split_ifs with hi
        · have hmax : max (d i - M.alloc s i) 0 ≤ (1 - M.alloc s i) * d i := by
            apply max_le
            · nlinarith [hdi.1, hdi.2]
            · exact mul_nonneg (sub_nonneg.2 (alloc_le_one hM hsig i)) hdi.1
          calc lam M s i * max (d i - M.alloc s i) 0
              ≤ lam M s i * ((1 - M.alloc s i) * d i) :=
                mul_le_mul_of_nonneg_left hmax (lam_nonneg hM hs i)
            _ = (lam M s i * (1 - M.alloc s i)) * d i := by ring
            _ ≤ (lam M s j * (1 - M.alloc s j)) * d i :=
                mul_le_mul_of_nonneg_right (hjmax i (by simpa using hi)) hdi.1
        · exact mul_nonneg hm0 hdi.1
      calc _ ≤ ∑ i, (lam M s j * (1 - M.alloc s j)) * d i := Finset.sum_le_sum fun i _ => hterm i
        _ = (lam M s j * (1 - M.alloc s j)) * ∑ i, d i := by rw [Finset.mul_sum]
        _ ≤ (lam M s j * (1 - M.alloc s j)) * 1 := by
            apply mul_le_mul_of_nonneg_left _ hm0
            obtain ⟨h0, h1 | h1⟩ := hd
            · exact h1.le
            · simp [h1]
        _ = _ := mul_one _
    -- lower bound for LW a
    have hnb : ENNReal.ofReal (M.pay s j) < G.c j :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (pay_le_val hM hG hsig heq j)) hjT'
    have hlamw := (foc hM hG hs heq j hnb).2
    set D := (∑ k ∈ Finset.univ.erase j, M.pay s k) + lam M s j * M.alloc s j with hD
    have hDpos : 0 < D := den_pos hM hs j
    have hLWD : ENNReal.ofReal D ≤ LW G (M.alloc s) := by
      unfold LW
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
      have hlamnn : 0 ≤ lam M s j * M.alloc s j :=
        mul_nonneg (lam_nonneg hM hs j) ((hM.alloc_mem s hsig).1 j)
      rw [hD, ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => hM.pay_nonneg s hsig k) hlamnn,
        ENNReal.ofReal_sum_of_nonneg fun k _ => hM.pay_nonneg s hsig k, add_comm]
      refine add_le_add ?_ (Finset.sum_le_sum fun k _ => lwterm_a_ge hM hG hsig heq k)
      rw [min_eq_left hjT'.le]
      exact ENNReal.ofReal_le_ofReal hlamw
    have hfin : LW G (M.alloc s) ≠ ⊤ := by
      unfold LW
      refine ENNReal.sum_ne_top.2 fun i _ => ?_
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
    set X := (LW G (M.alloc s)).toReal with hX
    have hXeq : LW G (M.alloc s) = ENNReal.ofReal X := (ENNReal.ofReal_toReal hfin).symm
    have hDX : D ≤ X := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hLWD
    have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
    have hrat := ratio_eq hM hs j
    have hN : (∑ k ∈ Finset.univ.erase j, M.pay s k) + lam M s j =
        D + lam M s j * (1 - M.alloc s j) := by rw [hD]; ring
    calc LW G d ≤ LW G (M.alloc s) + ENNReal.ofReal (∑ i, (if ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i then
        lam M s i * max (d i - M.alloc s i) 0 else 0)) := hbound d hd
      _ ≤ ENNReal.ofReal X + ENNReal.ofReal (lam M s j * (1 - M.alloc s j)) := by
          rw [hXeq]; exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hsumE)
      _ = ENNReal.ofReal (X + lam M s j * (1 - M.alloc s j)) := (ENNReal.ofReal_add hX0 hm0).symm
      _ ≤ ENNReal.ofReal ((D + lam M s j * (1 - M.alloc s j)) / D * X) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_mul_eq_mul_div, le_div_iff₀ hDpos]
          nlinarith [mul_le_mul_of_nonneg_left hDX hm0]
      _ = ratio M s j * LW G (M.alloc s) := by
          rw [hrat, hXeq, ← ENNReal.ofReal_mul (div_nonneg
            (by exact add_nonneg (Finset.sum_nonneg fun k _ => hM.pay_nonneg s hsig k) (lam_nonneg hM hs j)) hDpos.le), hN]
  · simp only [not_exists, not_lt] at hT
    obtain ⟨_, i0, _⟩ := id hs
    refine ⟨i0, fun d hd => ?_⟩
    have h := hbound d hd
    have hz : (∑ i, (if ENNReal.ofReal (G.v i (M.alloc s i)) < G.c i then
        lam M s i * max (d i - M.alloc s i) 0 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (not_lt.2 (hT i))]
    rw [hz, ENNReal.ofReal_zero, add_zero] at h
    calc LW G d ≤ LW G (M.alloc s) := h
      _ = 1 * LW G (M.alloc s) := (one_mul _).symm
      _ ≤ ratio M s i0 * LW G (M.alloc s) := mul_le_mul' (one_le_ratio hM hs i0) le_rfl


lemma LW_worst_unit (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (i : Fin n) :
    LW (worstGame M s i) (unitAlloc i) =
      ENNReal.ofReal ((∑ k ∈ Finset.univ.erase i, M.pay s k) + lam M s i) := by
  unfold LW
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have h1 : ∀ k ∈ Finset.univ.erase i,
      min (ENNReal.ofReal ((worstGame M s i).v k (unitAlloc i k))) ((worstGame M s i).c k) =
        ENNReal.ofReal (M.pay s k) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp [worstGame, unitAlloc, hki]
  rw [Finset.sum_congr rfl h1,
    ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => hM.pay_nonneg s hs.1 k) (lam_nonneg hM hs i),
    ENNReal.ofReal_sum_of_nonneg fun k _ => hM.pay_nonneg s hs.1 k, add_comm]
  simp [worstGame, unitAlloc]

lemma LW_worst_alloc (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (i : Fin n) :
    LW (worstGame M s i) (M.alloc s) =
      ENNReal.ofReal ((∑ k ∈ Finset.univ.erase i, M.pay s k) + lam M s i * M.alloc s i) := by
  unfold LW
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have h1 : ∀ k ∈ Finset.univ.erase i,
      min (ENNReal.ofReal ((worstGame M s i).v k (M.alloc s k))) ((worstGame M s i).c k) =
        ENNReal.ofReal (M.pay s k) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hn : 0 ≤ lam M s k * M.alloc s k :=
      mul_nonneg (lam_nonneg hM hs k) ((hM.alloc_mem s hs.1).1 k)
    simp only [worstGame, hki, if_false]
    rw [min_eq_right]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hn : 0 ≤ lam M s i * M.alloc s i :=
    mul_nonneg (lam_nonneg hM hs i) ((hM.alloc_mem s hs.1).1 i)
  rw [Finset.sum_congr rfl h1,
    ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => hM.pay_nonneg s hs.1 k) hn,
    ENNReal.ofReal_sum_of_nonneg fun k _ => hM.pay_nonneg s hs.1 k, add_comm]
  simp [worstGame]

lemma optLW_le (hM : IsRAMechanism M) {G : RAGame n} (hG : G.IsAdmissible)
    {s : Fin n → ℝ} (hs : InX s) (heq : IsEquilibrium M G s) :
    ∃ j, optLW G / LW G (M.alloc s) ≤ ratio M s j := by
  obtain ⟨j, hj⟩ := main_exists hM hG hs heq
  refine ⟨j, ENNReal.div_le_of_le_mul ?_⟩
  exact iSup₂_le fun d hd => hj d hd


lemma equilibrium_worst (hM : IsRAMechanism M) (hC : InClassC M) {s : Fin n → ℝ}
    (hs : InX s) (j : Fin n) : IsEquilibrium M (worstGame M s j) s := by
  have hsig := hs.1
  refine ⟨hsig, fun i => ⟨?_, ?_⟩⟩
  · by_cases h : i = j
    · simp [Affordable, worstGame, h]
    · simp [Affordable, worstGame, h]
  · intro y hy _
    obtain ⟨hAc, hPc⟩ := hC s hsig i (exists_other hs i)
    obtain ⟨hdA, hdP⟩ := hM.diff s hsig i (exists_other hs i)
    have hmem : s i ∈ Ici (0:ℝ) := hsig i
    have hymem : y ∈ Ici (0:ℝ) := hy
    have hA := (hdA (s i) hmem).hasDerivWithinAt
    have hP := (hdP (s i) hmem).hasDerivWithinAt
    have hApos : 0 < derivWithin (allocIn M s i) (Ici 0) (s i) := hM.deriv_pos s hs i
    have hlam : lam M s i = (derivWithin (allocIn M s i) (Ici 0) (s i))⁻¹ *
        derivWithin (payIn M s i) (Ici 0) (s i) := rfl
    have hlam0 := lam_nonneg hM hs i
    set A' := derivWithin (allocIn M s i) (Ici 0) (s i)
    set P' := derivWithin (payIn M s i) (Ici 0) (s i)
    have h1 := tangent_concave hAc hmem hymem hA
    have h2 := tangent_convex hPc hmem hymem hP
    have hlA : lam M s i * A' = P' := by
      rw [hlam, mul_comm, ← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul]
    have h3 := mul_le_mul_of_nonneg_left (sub_nonneg.2 h1) hlam0
    have key : lam M s i * (allocIn M s i y - allocIn M s i (s i)) ≤
        payIn M s i y - payIn M s i (s i) := by
      have : lam M s i * (allocIn M s i y - allocIn M s i (s i)) ≤ lam M s i * (A' * (y - s i)) := by
        have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.2 (by linarith : allocIn M s i y ≤ allocIn M s i (s i) + A' * (y - s i))) hlam0
        linarith
      have h4 : lam M s i * (A' * (y - s i)) = P' * (y - s i) := by rw [← mul_assoc, hlA]
      linarith
    have hu1 : utility M (worstGame M s j) (Function.update s i y) i =
        lam M s i * allocIn M s i y + (if i = j then 0 else M.pay s i) - payIn M s i y := by
      simp [utility, worstGame, allocIn, payIn]
    have hu2 : utility M (worstGame M s j) s i =
        lam M s i * allocIn M s i (s i) + (if i = j then 0 else M.pay s i) - payIn M s i (s i) := by
      simp [utility, worstGame, allocIn, payIn]
    rw [hu1, hu2]
    linarith


lemma update_comp_swap (s : Fin n → ℝ) (j0 i : Fin n) (y : ℝ) :
    Function.update (s ∘ Equiv.swap j0 i) j0 y = Function.update s i y ∘ Equiv.swap j0 i := by
  funext k
  by_cases hk : k = j0
  · subst hk; simp
  · have : Equiv.swap j0 i k ≠ i := by
      intro h
      apply hk
      have := congrArg (Equiv.swap j0 i) h
      simpa using this
    simp [Function.update_of_ne hk, Function.update_of_ne this]

lemma ratio_swap (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (j0 i : Fin n) :
    InX (s ∘ Equiv.swap j0 i) ∧ ratio M (s ∘ Equiv.swap j0 i) j0 = ratio M s i := by
  set σ := Equiv.swap j0 i with hσ
  have hsig := hs.1
  have hsig' : IsSignal (s ∘ σ) := fun k => hsig (σ k)
  have hσi : σ j0 = i := by simp [hσ]
  refine ⟨?_, ?_⟩
  · obtain ⟨_, a, b, hab, ha, hb⟩ := id hs
    refine ⟨hsig', σ a, σ b, fun h => hab (σ.injective h), ?_, ?_⟩
    · simpa [hσ] using ha
    · simpa [hσ] using hb
  · have hpay := hM.anon_pay σ s hsig
    have halloc := hM.anon_alloc σ s hsig
    have hA : EqOn (allocIn M (s ∘ σ) j0) (allocIn M s i) (Ici 0) := by
      intro y hy
      have h := congrFun (hM.anon_alloc σ (Function.update s i y)
        (isSignal_update hsig hy i)) j0
      simp only [allocIn]
      rw [update_comp_swap, h]
      simp [hσi]
    have hP : EqOn (payIn M (s ∘ σ) j0) (payIn M s i) (Ici 0) := by
      intro y hy
      have h := congrFun (hM.anon_pay σ (Function.update s i y)
        (isSignal_update hsig hy i)) j0
      simp only [payIn]
      rw [update_comp_swap, h]
      simp [hσi]
    have hpt : (s ∘ σ) j0 = s i := by simp [hσi]
    have hmem : s i ∈ Ici (0:ℝ) := hsig i
    have hlam : lam M (s ∘ σ) j0 = lam M s i := by
      unfold lam
      rw [hpt, derivWithin_congr hA (hA hmem), derivWithin_congr hP (hP hmem)]
    have hsum : ∑ k ∈ Finset.univ.erase j0, M.pay (s ∘ σ) k =
        ∑ k ∈ Finset.univ.erase i, M.pay s k := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_erase_eq_sub (Finset.mem_univ _),
        hpay]
      simp only [Function.comp]
      rw [Equiv.sum_comp σ (fun k => M.pay s k), hσi]
    have hal : M.alloc (s ∘ σ) j0 = M.alloc s i := by
      rw [halloc]; simp [hσi]
    unfold ratio
    rw [hlam, hsum, hal]

lemma ratio_le_sup (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (j0 i : Fin n) :
    ratio M s i ≤ ⨆ (t : Fin n → ℝ) (_ : InX t), ratio M t j0 := by
  obtain ⟨h1, h2⟩ := ratio_swap hM hs j0 i
  rw [← h2]
  exact le_iSup₂ (f := fun (t : Fin n → ℝ) (_ : InX t) => ratio M t j0) _ h1


lemma eq_zero_or_X (hM : IsRAMechanism M) {G : RAGame n} {s : Fin n → ℝ}
    (heq : IsEquilibrium M G s) : InX s ∨ ∀ i, s i = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hX, i, hi⟩ := hcon
  have hsig := heq.1
  have hpos : 0 < s i := lt_of_le_of_ne (hsig i) (Ne.symm hi)
  have hother : ∀ j, j ≠ i → s j = 0 := by
    intro j hj
    by_contra hne
    have hjpos : 0 < s j := lt_of_le_of_ne (hsig j) (Ne.symm hne)
    exact hX ⟨hsig, i, j, fun h => hj h.symm, hpos, hjpos⟩
  have hs_eq : s = Function.update (0 : Fin n → ℝ) i (s i) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk, hother k hk]
  have hy : 0 < s i / 2 := by linarith
  have halone1 := hM.alone i (s i) hpos
  have halone2 := hM.alone i (s i / 2) hy
  have hupd : Function.update s i (s i / 2) = Function.update (0 : Fin n → ℝ) i (s i / 2) := by
    rw [hs_eq]; simp
  have hpayinc : M.pay (Function.update s i (s i / 2)) i < M.pay s i := by
    have := hM.pay_incr s hsig i (show s i / 2 ∈ Ici (0:ℝ) from hy.le) (hsig i)
      (by linarith)
    simpa [payIn] using this
  have hafford : Affordable M G (Function.update s i (s i / 2)) i := by
    unfold Affordable
    exact le_trans (ENNReal.ofReal_le_ofReal hpayinc.le) (heq.2 i).1
  have hdev := (heq.2 i).2 (s i / 2) hy.le hafford
  have hA1 : M.alloc s i = 1 := by rw [hs_eq]; simpa using halone1
  have hA2 : M.alloc (Function.update s i (s i / 2)) i = 1 := by rw [hupd]; exact halone2
  simp only [utility, hA1, hA2] at hdev
  linarith

lemma zero_eq_bound (hM : IsRAMechanism M) {G : RAGame n} (hG : G.IsAdmissible)
    (heq : IsEquilibrium M G 0) : optLW G / LW G (M.alloc 0) ≤ 1 := by
  have hsig : IsSignal (0 : Fin n → ℝ) := fun _ => le_rfl
  have hterm : ∀ d, IsAllocation d → ∀ i, min (ENNReal.ofReal (G.v i (d i))) (G.c i) ≤
      min (ENNReal.ofReal (G.v i (M.alloc 0 i))) (G.c i) := by
    intro d hd i
    have ha0 : M.alloc 0 i = 0 := (hM.zero_sig 0 hsig i rfl).1
    have hp0 : M.pay 0 i = 0 := (hM.zero_sig 0 hsig i rfl).2
    rw [ha0]
    by_cases hc0 : G.c i = 0
    · rw [hc0]; simp
    · have hc : 0 < G.c i := pos_iff_ne_zero.2 hc0
      have hv1 : G.v i 1 ≤ G.v i 0 := by
        apply le_of_forall_pos_le_add
        intro ε hε
        have hcont := hM.pay_cont_zero i
        have hp00 : payIn M 0 i 0 = 0 := payIn_zero hM hsig i
        have hev1 := eventually_afford hcont (by rw [hp00]; simpa using hc)
        have hev2 : ∀ᶠ y in nhdsWithin (0:ℝ) (Ici 0), payIn M 0 i y < ε := by
          have := hcont.eventually (Iio_mem_nhds (show payIn M 0 i 0 < ε by rw [hp00]; exact hε))
          exact this
        have hev3 := (hev1.and hev2)
        have hev4 : ∀ᶠ y in nhdsWithin (0:ℝ) (Ioi 0), ENNReal.ofReal (payIn M 0 i y) ≤ G.c i ∧
            payIn M 0 i y < ε := nhdsWithin_mono 0 Ioi_subset_Ici_self hev3
        obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := (hev4.and self_mem_nhdsWithin).exists
        have hy3' : (0:ℝ) < y := hy3
        have hdev := (heq.2 i).2 y hy3'.le hy1
        have halone := hM.alone i y hy3'
        simp only [utility, payIn] at hdev hy2
        rw [halone, hp0, ha0] at hdev
        simp at hdev
        linarith
      have hd1 := isAlloc_mem hd i
      have hmono := hG.mono i hd1 ⟨zero_le_one, le_rfl⟩ hd1.2
      exact min_le_min (ENNReal.ofReal_le_ofReal (le_trans hmono hv1)) le_rfl
  have hopt : optLW G ≤ LW G (M.alloc 0) :=
    iSup₂_le fun d hd => Finset.sum_le_sum fun i _ => hterm d hd i
  exact ENNReal.div_le_of_le_mul (by simpa using hopt)


lemma worst_admissible (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s) (j : Fin n) :
    (worstGame M s j).IsAdmissible := by
  have hconst : ∀ i, 0 ≤ (if i = j then (0:ℝ) else M.pay s i) := fun i => by
    split_ifs
    · exact le_rfl
    · exact hM.pay_nonneg s hs.1 i
  refine ⟨fun i x hx => ?_, fun i x hx y hy hxy => ?_, fun i => ?_, fun i => ?_⟩
  · simp only [worstGame]
    exact add_nonneg (mul_nonneg (lam_nonneg hM hs i) hx.1) (hconst i)
  · simp only [worstGame]
    nlinarith [lam_nonneg hM hs i]
  · refine ⟨convex_Icc 0 1, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [worstGame, smul_eq_mul]
    have : b = 1 - a := by linarith
    subst this
    apply le_of_eq
    ring
  · intro x _
    simp only [worstGame]
    fun_prop

lemma isAllocation_unit (j : Fin n) : IsAllocation (unitAlloc j) := by
  refine ⟨fun k => ?_, Or.inl ?_⟩
  · unfold unitAlloc
    rw [Pi.single_apply]; split_ifs <;> norm_num
  · simp [unitAlloc]

lemma ratio_le_lpoa (hM : IsRAMechanism M) {s : Fin n → ℝ} (hs : InX s)
    (j : Fin n) (heq : IsEquilibrium M (worstGame M s j) s) : ratio M s j ≤ lpoa M := by
  have hadm := worst_admissible hM hs j
  have h1 : ratio M s j ≤ optLW (worstGame M s j) / LW (worstGame M s j) (M.alloc s) := by
    have : LW (worstGame M s j) (unitAlloc j) ≤ optLW (worstGame M s j) :=
      le_iSup₂ (f := fun (d : Fin n → ℝ) (_ : IsAllocation d) => LW (worstGame M s j) d)
        (unitAlloc j) (isAllocation_unit j)
    calc ratio M s j = LW (worstGame M s j) (unitAlloc j) / LW (worstGame M s j) (M.alloc s) := by
          rw [LW_worst_unit hM hs, LW_worst_alloc hM hs]; rfl
      _ ≤ _ := ENNReal.div_le_div_right this _
  calc ratio M s j ≤ _ := h1
    _ ≤ gameLPoA M (worstGame M s j) :=
        le_iSup₂ (f := fun (t : Fin n → ℝ) (_ : IsEquilibrium M (worstGame M s j) t) =>
          optLW (worstGame M s j) / LW (worstGame M s j) (M.alloc t)) s heq
    _ ≤ lpoa M :=
        le_iSup₂ (f := fun (G : RAGame n) (_ : G.IsAdmissible) => gameLPoA M G)
          (worstGame M s j) hadm

lemma lpoa_le_sup (hM : IsRAMechanism M) (j0 : Fin n) (h1 : ∃ s : Fin n → ℝ, InX s) :
    lpoa M ≤ ⨆ (s : Fin n → ℝ) (_ : InX s), ratio M s j0 := by
  refine iSup₂_le fun G hG => iSup₂_le fun s heq => ?_
  rcases eq_zero_or_X hM heq with hX | h0
  · obtain ⟨j, hj⟩ := optLW_le hM hG hX heq
    exact hj.trans (ratio_le_sup hM hX j0 j)
  · have : s = 0 := funext h0
    subst this
    refine (zero_eq_bound hM hG heq).trans ?_
    obtain ⟨t, ht⟩ := h1
    exact (one_le_ratio hM ht j0).trans (le_iSup₂ (f := fun (t : Fin n → ℝ) (_ : InX t) =>
      ratio M t j0) t ht)


section KellyAux

lemma kelly_sum_update (n : ℕ) (s : Fin n → ℝ) (i : Fin n) (y : ℝ) :
    ∑ j, Function.update s i y j = y + ∑ j ∈ Finset.univ.erase i, s j := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma kelly_allocIn (n : ℕ) (s : Fin n → ℝ) (i : Fin n) :
    allocIn (kelly n) s i = fun y => y / (y + ∑ j ∈ Finset.univ.erase i, s j) := by
  funext y
  simp [allocIn, kelly, kelly_sum_update]

lemma kelly_payIn (n : ℕ) (s : Fin n → ℝ) (i : Fin n) :
    payIn (kelly n) s i = fun y => y := by
  funext y
  simp [payIn, kelly]

lemma kelly_c_pos {n : ℕ} {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n)
    (h : ∃ j, j ≠ i ∧ 0 < s j) : 0 < ∑ j ∈ Finset.univ.erase i, s j := by
  obtain ⟨j, hj, hjpos⟩ := h
  have : s j ≤ ∑ j ∈ Finset.univ.erase i, s j :=
    Finset.single_le_sum (f := s) (fun k _ => hs k) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
  linarith

lemma kelly_c_nonneg {n : ℕ} {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n) :
    0 ≤ ∑ j ∈ Finset.univ.erase i, s j := Finset.sum_nonneg fun k _ => hs k

lemma kelly_hasDeriv (c y : ℝ) (hc : 0 ≤ c) (hy : 0 < y + c) :
    HasDerivAt (fun y => y / (y + c)) (c / (y + c) ^ 2) y := by
  have h : HasDerivAt (fun y => y / (y + c)) ((1 * (y + c) - y * 1) / (y + c) ^ 2) y :=
    (hasDerivAt_id' y).div ((hasDerivAt_id' y).add_const c) hy.ne'
  exact h.congr_deriv (by ring)

lemma kelly_deriv_alloc {n : ℕ} {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n)
    (h0 : 0 < s i + ∑ j ∈ Finset.univ.erase i, s j) :
    derivWithin (allocIn (kelly n) s i) (Ici 0) (s i) =
      (∑ j ∈ Finset.univ.erase i, s j) / (s i + ∑ j ∈ Finset.univ.erase i, s j) ^ 2 := by
  rw [kelly_allocIn]
  have hc := kelly_c_nonneg hs i
  exact ((kelly_hasDeriv _ _ hc h0).hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Ici 0 _ (hs i))

lemma kelly_deriv_pay {n : ℕ} {s : Fin n → ℝ} (hs : IsSignal s) (i : Fin n) :
    derivWithin (payIn (kelly n) s i) (Ici 0) (s i) = 1 := by
  rw [kelly_payIn]
  exact ((hasDerivAt_id (s i)).hasDerivWithinAt).derivWithin (uniqueDiffOn_Ici 0 _ (hs i))


lemma kelly_strictMono (c : ℝ) (hc : 0 < c) :
    StrictMonoOn (fun y : ℝ => y / (y + c)) (Ici 0) := by
  intro x hx y hy hxy
  have hx' : 0 ≤ x := hx
  have hy' : 0 ≤ y := hy
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma kelly_concave (c : ℝ) (hc : 0 < c) :
    ConcaveOn ℝ (Ici 0) (fun y : ℝ => y / (y + c)) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : 0 ≤ x := hx
  have hy' : 0 ≤ y := hy
  simp only [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  have h1 : 0 < x + c := by linarith
  have h2 : 0 < y + c := by linarith
  have h3 : 0 < a * x + (1 - a) * y + c := by nlinarith
  have e : a * (x / (x + c)) + (1 - a) * (y / (y + c)) =
      (a * x * (y + c) + (1 - a) * y * (x + c)) / ((x + c) * (y + c)) := by
    field_simp
  rw [e, div_le_div_iff₀ (mul_pos h1 h2) h3]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc.le) (sq_nonneg (x - y))]

lemma kelly_isRA (n : ℕ) : IsRAMechanism (kelly n) where
  alloc_mem s hs := by
    refine ⟨fun i => div_nonneg (hs i) (Finset.sum_nonneg fun j _ => hs j), ?_⟩
    by_cases h : ∑ j, s j = 0
    · right; intro i; simp [kelly, h]
    · left; simp only [kelly]; rw [← Finset.sum_div, div_self h]
  pay_nonneg s hs i := hs i
  anon_alloc σ s hs := by
    funext i
    simp only [kelly, Function.comp]
    rw [Equiv.sum_comp σ s]
  anon_pay σ s hs := rfl
  zero_sig s hs i h := by simp [kelly, h]
  alone i y hy := by
    simp [kelly, kelly_sum_update, hy.ne']
  alloc_incr s hs i h := by
    rw [kelly_allocIn]; exact kelly_strictMono _ (kelly_c_pos hs i h)
  pay_incr s hs i := by rw [kelly_payIn]; exact strictMonoOn_id
  pay_cont_zero i := by rw [kelly_payIn]; exact continuousWithinAt_id
  diff s hs i h := by
    rw [kelly_allocIn, kelly_payIn]
    have hc := kelly_c_pos hs i h
    constructor
    · intro y hy
      have : (0:ℝ) ≤ y := hy
      exact (kelly_hasDeriv _ _ hc.le (by linarith)).differentiableAt.differentiableWithinAt
    · exact differentiableOn_id
  diff_alone s hs i h := by
    rw [kelly_allocIn, kelly_payIn]
    have hc := kelly_c_nonneg hs i
    constructor
    · intro y hy
      have : (0:ℝ) < y := hy
      exact (kelly_hasDeriv _ _ hc (by linarith)).differentiableAt.differentiableWithinAt
    · exact differentiableOn_id
  deriv_pos s hs i := by
    have hc := kelly_c_pos hs.1 i (exists_other hs i)
    have := hs.1 i
    rw [kelly_deriv_alloc hs.1 i (by linarith)]
    exact div_pos hc (pow_pos (by linarith) 2)

lemma kelly_inC (n : ℕ) : InClassC (kelly n) := by
  intro s hs i h
  rw [kelly_allocIn, kelly_payIn]
  exact ⟨kelly_concave _ (kelly_c_pos hs i h), convexOn_id (convex_Ici 0)⟩


lemma kelly_ratio {n : ℕ} {s : Fin n → ℝ} (hs : InX s) (j : Fin n) :
    ratio (kelly n) s j = ENNReal.ofReal
      (((∑ k ∈ Finset.univ.erase j, s k) ^ 2 +
          (s j + ∑ k ∈ Finset.univ.erase j, s k) ^ 2) /
        ((∑ k ∈ Finset.univ.erase j, s k) ^ 2 +
          (s j + ∑ k ∈ Finset.univ.erase j, s k) * s j)) := by
  have hc := kelly_c_pos hs.1 j (exists_other hs j)
  have hsj := hs.1 j
  set c := ∑ k ∈ Finset.univ.erase j, s k with hcdef
  have hsum : ∑ k, s k = s j + c := (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  rw [ratio_eq (kelly_isRA n) hs j]
  congr 1
  have hlam : lam (kelly n) s j = (s j + c) ^ 2 / c := by
    unfold lam
    rw [kelly_deriv_alloc hs.1 j (by linarith), kelly_deriv_pay hs.1 j, ← hcdef]
    field_simp
  have hal : (kelly n).alloc s j = s j / (s j + c) := by
    simp only [kelly]; rw [hsum]
  have hpay : ∑ k ∈ Finset.univ.erase j, (kelly n).pay s k = c := rfl
  rw [hpay, hlam, hal]
  have : 0 < s j + c := by linarith
  have hD : 0 < c ^ 2 + (s j + c) * s j := by positivity
  field_simp

lemma kelly_ratio_le_two {n : ℕ} {s : Fin n → ℝ} (hs : InX s) (j : Fin n) :
    ratio (kelly n) s j ≤ 2 := by
  have hc := kelly_c_pos hs.1 j (exists_other hs j)
  have hsj := hs.1 j
  rw [kelly_ratio hs j, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (s j)]

lemma real_ineq (c ε δ : ℝ) (hc : 0 < c) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : ε ^ 2 ≤ δ * c ^ 2) :
    2 - δ ≤ (c ^ 2 + (ε + c) ^ 2) / (c ^ 2 + (ε + c) * ε) := by
  have hD : 0 < c ^ 2 + (ε + c) * ε := by positivity
  rw [le_div_iff₀ hD]
  nlinarith [mul_nonneg hδ (mul_nonneg (by linarith : 0 ≤ ε + c) hε)]

lemma kelly_sup_ge (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℝ≥0∞) ≤ ⨆ (s : Fin n → ℝ) (_ : InX s), ratio (kelly n) s (⟨0, by omega⟩ : Fin n) := by
  set j0 : Fin n := ⟨0, by omega⟩ with hj0
  refine le_of_forall_lt fun c hc => ?_
  have hcne : c ≠ ⊤ := ne_top_of_lt hc
  set r := c.toReal with hr
  have hcr : c = ENNReal.ofReal r := (ENNReal.ofReal_toReal hcne).symm
  have hr2 : r < 2 := by
    have := (ENNReal.toReal_lt_toReal hcne (by simp)).2 hc
    simpa [hr] using this
  set δ := min 1 ((2 - r) / 2) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ (2 - r) / 2 := min_le_right _ _
  set c0 : ℝ := ((n - 1 : ℕ) : ℝ) with hc0
  have hc0pos : 0 < c0 := Nat.cast_pos.2 (by omega)
  set ε := δ * c0 / 2 with hε
  have hεpos : 0 < ε := by positivity
  let s : Fin n → ℝ := fun k => if k = j0 then ε else 1
  have hsX : InX s := by
    refine ⟨fun k => ?_, j0, ⟨1, by omega⟩, ?_, ?_, ?_⟩
    · simp only [s]; split_ifs
      · exact hεpos.le
      · exact zero_le_one
    · intro h; have := congrArg Fin.val h; simp [hj0] at this
    · simp [s, hεpos]
    · have : (⟨1, by omega⟩ : Fin n) ≠ j0 := by
        intro h; have := congrArg Fin.val h; simp [hj0] at this
      simp [s, this]
  have hsum : ∑ k ∈ Finset.univ.erase j0, s k = c0 := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun k hk => by
      simp [s, Finset.ne_of_mem_erase hk])]
    simp [Finset.card_erase_of_mem, hc0]
  have hsj0 : s j0 = ε := by simp [s]
  have hratio : ENNReal.ofReal (2 - δ) ≤ ratio (kelly n) s j0 := by
    rw [kelly_ratio hsX j0, hsum, hsj0]
    apply ENNReal.ofReal_le_ofReal
    apply real_ineq c0 ε δ hc0pos hεpos.le hδpos.le
    rw [hε]
    nlinarith [mul_pos hδpos (sq_pos_of_pos hc0pos)]
  calc c = ENNReal.ofReal r := hcr
    _ < ENNReal.ofReal (2 - δ) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]; linarith
    _ ≤ ratio (kelly n) s j0 := hratio
    _ ≤ _ := le_iSup₂ (f := fun (t : Fin n → ℝ) (_ : InX t) => ratio (kelly n) t j0) s hsX

end KellyAux

end Aux

end LiquidPoA.Kelly

open LiquidPoA.Kelly

/-- Theorem 5.1, p. 14: the full liquid price of anarchy of Kelly is exactly two. -/
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    lpoa (kelly n) = 2 := by
  have hM := kelly_isRA n
  have hC := kelly_inC n
  have hex : ∃ s : Fin n → ℝ, InX s :=
    ⟨fun _ => 1, fun _ => zero_le_one, ⟨0, by omega⟩, ⟨1, by omega⟩,
      fun h => by simpa using congrArg Fin.val h, zero_lt_one, zero_lt_one⟩
  have hle := lpoa_le_sup hM (⟨0, by omega⟩ : Fin n) hex
  have hge : (⨆ (s : Fin n → ℝ) (_ : InX s), ratio (kelly n) s (⟨0, by omega⟩ : Fin n)) ≤
      lpoa (kelly n) :=
    iSup₂_le fun s hs => ratio_le_lpoa hM hs _ (equilibrium_worst hM hC hs _)
  have hsup : (⨆ (s : Fin n → ℝ) (_ : InX s), ratio (kelly n) s (⟨0, by omega⟩ : Fin n)) = 2 :=
    le_antisymm (iSup₂_le fun s hs => kelly_ratio_le_two hs _) (kelly_sup_ge n hn)
  rw [hsup] at hle hge
  exact le_antisymm hle hge
