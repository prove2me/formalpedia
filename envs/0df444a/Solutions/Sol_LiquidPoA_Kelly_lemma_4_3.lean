-- Prove2me | solution 1 for LiquidPoA.Kelly.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:57:35.025008+00:00
-- url     : https://prove2.me/submissions/ef1dab4b-3b66-46e3-bd5d-89454bf84b44

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

end Aux

end LiquidPoA.Kelly

open LiquidPoA.Kelly

/-- Lemma 4.3, p. 14: every vector in `𝕏ₙ` is an equilibrium of its affine game for a class-`𝒞` mechanism. -/
theorem solution {n : ℕ} (hn : 2 ≤ n) (M : Mechanism n)
    (hM : IsRAMechanism M) (hC : InClassC M)
    (s : Fin n → ℝ) (hs : InX s) :
    IsEquilibrium M (worstGame M s (⟨0, by omega⟩ : Fin n)) s :=
  equilibrium_worst hM hC hs _
