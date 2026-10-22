-- Prove2me | solution 1 for HolisticService.Effort.foc_iff_deltahat
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:56:47.37892+00:00
-- url     : https://prove2.me/submissions/fa52857e-5330-4d8d-96e7-0c587f3932c8

import Mathlib
import Definitions.Def_HolisticService_Effort_Model


open HolisticService.Effort Finset Filter Topology

namespace HSAux

variable {n : ℕ}

lemma quad_sum (P : Matrix (Fin n) (Fin n) ℝ) (hPs : P.IsSymm) (hPd : ∀ i, P i i = 1)
    (s : Fin n → ℝ) :
    ∑ i, s i ^ 2 + 2 * ∑ i, ∑ j, (if i < j then P i j * s i * s j else 0)
      = ∑ i, ∑ j, P i j * s i * s j := by
  have h1 : ∀ i j, P i j * s i * s j = (if i < j then P i j * s i * s j else 0)
      + (if j < i then P i j * s i * s j else 0) + (if i = j then s i ^ 2 else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp [hPd]; ring
    · simp [h, h.ne', not_lt.mpr h.le]
  have h2 : ∑ i, ∑ j, (if j < i then P i j * s i * s j else 0)
      = ∑ i, ∑ j, (if i < j then P i j * s i * s j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [hPs.apply]; ring
    · rfl
  have h3 : ∑ i, ∑ j, (if i = j then s i ^ 2 else 0) = ∑ i, s i ^ 2 := by
    simp
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j]
  simp only [Finset.sum_add_distrib]
  rw [h2, h3]; ring

lemma utilde_eq (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPs : M.P.IsSymm)
    (hPd : ∀ i, M.P i i = 1) (δ : Fin n → ℝ) :
    Utilde M δ = ∑ j, (1 - ctil M j) * Vval M δ j - M.π0
      - M.r / 2 * ∑ i, ∑ j, M.P i j * sig M δ i * sig M δ j := by
  have hcal : ∑ i, calV M δ i = ∑ j, (1 + ∑ m ∈ univ.erase j, M.β j m) * Vval M δ j := by
    unfold calV
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hβd]
  have hlin : ∑ j, (1 - ctil M j) * Vval M δ j
      = ∑ j, (1 + ∑ m ∈ univ.erase j, M.β j m) * Vval M δ j - ∑ j, Vval M δ j * M.c j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold ctil; ring
  unfold Utilde utility πtil
  rw [quad_sum M.P hPs hPd, hcal, hlin]
  ring

lemma inv_apply_eq (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    P⁻¹ i j = P.adjugate i j / P.det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [Matrix.smul_apply, div_eq_inv_mul]

lemma sig_hat (M : Params n) (hr : M.r ≠ 0) (hd : ∀ k, M.sH k - M.sL k ≠ 0) (i : Fin n) :
    sig M (δhat M) i = ∑ j, (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j))
      * M.P⁻¹ i j := by
  unfold sig δhat
  have hX : ∑ j, (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH i - M.sL i) * (M.sH j - M.sL j))
        * M.P⁻¹ i j
      = (∑ j, (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j)
        / (M.sH i - M.sL i) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    generalize M.sH i - M.sL i = a
    generalize M.sH j - M.sL j = b
    ring
  rw [hX]
  generalize (∑ j, (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j) = Y
  have hdi := hd i
  field_simp
  ring

lemma P_sig_hat (M : Params n) (hr : M.r ≠ 0) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hdet : IsUnit M.P.det) (i : Fin n) :
    ∑ j, M.P i j * sig M (δhat M) j
      = (1 - ctil M i) * (M.VH i - M.VL i) / (M.r * (M.sH i - M.sL i)) := by
  set w : Fin n → ℝ := fun j => (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j))
  have hs : sig M (δhat M) = Matrix.mulVec M.P⁻¹ w := by
    funext k
    rw [sig_hat M hr hd k]
    simp only [Matrix.mulVec, dotProduct, w]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have : Matrix.mulVec M.P (sig M (δhat M)) = w := by
    rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h2 := congrFun this i
  simp only [Matrix.mulVec, dotProduct] at h2
  rw [h2]

lemma utilde_diff (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPs : M.P.IsSymm)
    (hPd : ∀ i, M.P i i = 1) (hr : M.r ≠ 0) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hdet : IsUnit M.P.det) (δ : Fin n → ℝ) :
    Utilde M δ = Utilde M (δhat M) - M.r / 2 * ∑ i, ∑ j, M.P i j
      * ((δ i - δhat M i) * (M.sH i - M.sL i)) * ((δ j - δhat M j) * (M.sH j - M.sL j)) := by
  rw [utilde_eq M hβd hPs hPd δ, utilde_eq M hβd hPs hPd (δhat M)]
  set e : Fin n → ℝ := fun i => (δ i - δhat M i) * (M.sH i - M.sL i) with he
  set sh : Fin n → ℝ := sig M (δhat M) with hsh
  have hs : ∀ i, sig M δ i = sh i + e i := by
    intro i; simp only [hsh, he]; unfold sig; ring
  have hA : ∑ i, ∑ j, M.P i j * sh i * e j = ∑ i, ∑ j, M.P i j * e i * sh j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hPs.apply]; ring
  have hB : ∑ i, ∑ j, M.P i j * e i * sh j = ∑ i, e i * ∑ j, M.P i j * sh j := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hC : ∑ i, e i * ∑ j, M.P i j * sh j
      = (∑ i, (1 - ctil M i) * (M.VH i - M.VL i) * (δ i - δhat M i)) / M.r := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsh, P_sig_hat M hr hd hdet i]
    have hdi := hd i
    simp only [he]
    field_simp
  have hQ : ∑ i, ∑ j, M.P i j * sig M δ i * sig M δ j
      = ∑ i, ∑ j, M.P i j * sh i * sh j + 2 * (∑ i, e i * ∑ j, M.P i j * sh j)
        + ∑ i, ∑ j, M.P i j * e i * e j := by
    simp_rw [hs]
    have : ∀ i j, M.P i j * (sh i + e i) * (sh j + e j)
        = M.P i j * sh i * sh j + M.P i j * sh i * e j + M.P i j * e i * sh j
          + M.P i j * e i * e j := by intro i j; ring
    simp_rw [this, Finset.sum_add_distrib]
    rw [hA, hB]; ring
  have hL : ∑ j, (1 - ctil M j) * Vval M δ j
      = ∑ j, (1 - ctil M j) * Vval M (δhat M) j
        + ∑ i, (1 - ctil M i) * (M.VH i - M.VL i) * (δ i - δhat M i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Vval; ring
  rw [hQ, hC, hL]
  simp only [he]
  generalize (∑ i, (1 - ctil M i) * (M.VH i - M.VL i) * (δ i - δhat M i)) = X
  have hX : M.r / 2 * (2 * (X / M.r)) = X := by field_simp
  linear_combination -hX

lemma quad_pos (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (e : Fin n → ℝ) (he : e ≠ 0) :
    0 < ∑ i, ∑ j, P i j * e i * e j := by
  have := hP.dotProduct_mulVec_pos he
  rw [show (∑ i, ∑ j, P i j * e i * e j) = ∑ i, e i * ∑ j, P i j * e j from by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring]
  simpa [dotProduct, Matrix.mulVec] using this

lemma quad_nonneg (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (e : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, P i j * e i * e j := by
  by_cases he : e = 0
  · subst he; simp
  · exact (quad_pos P hP e he).le

/-- The core of Proposition 1: if the closed form lies in the box, it is the unique optimal effort. -/
theorem opt_core (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPd : ∀ i, M.P i i = 1)
    (hr : 0 < M.r) (hP : M.P.PosDef) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hbox : ∀ k, 0 ≤ δhat M k ∧ δhat M k ≤ 1) :
    IsOptimalDesign M (δhat M) (πtil M (δhat M)) ∧
      ∀ (δ : Fin n → ℝ) (π : ℝ), IsOptimalDesign M δ π → δ = δhat M := by
  have hPs : M.P.IsSymm := hP.isHermitian
  have hdet : IsUnit M.P.det := (hP.det_pos).ne'.isUnit
  have hdiff := utilde_diff M hβd hPs hPd hr.ne' hd hdet
  have hup : ∀ δ π, Feasible M δ π → utility M δ π ≤ Utilde M δ := by
    intro δ π hF
    have h2 := hF.2
    unfold Utilde utility πtil at *
    linarith
  have hopt : IsOptimalDesign M (δhat M) (πtil M (δhat M)) := by
    refine ⟨⟨hbox, ?_⟩, ?_⟩
    · unfold πtil; linarith
    · intro δ' π' hF
      have h1 := hup δ' π' hF
      have h2 := hdiff δ'
      have h3 := quad_nonneg M.P hP (fun i => (δ' i - δhat M i) * (M.sH i - M.sL i))
      show utility M δ' π' ≤ Utilde M (δhat M)
      nlinarith
  refine ⟨hopt, ?_⟩
  intro δ π hδ
  have h1 := hup δ π hδ.1
  have h2 := hδ.2 _ _ hopt.1
  have h3 := hdiff δ
  change utility M (δhat M) (πtil M (δhat M)) ≤ utility M δ π at h2
  have h4 : utility M (δhat M) (πtil M (δhat M)) = Utilde M (δhat M) := rfl
  by_contra hne
  have hne' : (fun i => (δ i - δhat M i) * (M.sH i - M.sL i)) ≠ 0 := by
    intro h0
    apply hne
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply, mul_eq_zero] at this
    rcases this with h | h
    · linarith
    · exact absurd h (hd i)
  have h5 := quad_pos M.P hP _ hne'
  nlinarith

theorem optEffort_eq (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPd : ∀ i, M.P i i = 1)
    (hr : 0 < M.r) (hP : M.P.PosDef) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hbox : ∀ k, 0 ≤ δhat M k ∧ δhat M k ≤ 1) :
    optEffort M = δhat M := by
  obtain ⟨hopt, huniq⟩ := opt_core M hβd hPd hr hP hd hbox
  have hex : ∃ δ, IsOptimalEffort M δ := ⟨δhat M, _, hopt⟩
  unfold optEffort
  rw [dif_pos hex]
  obtain ⟨π, hπ⟩ := Classical.choose_spec hex
  exact huniq _ _ hπ

end HSAux

open HolisticService.Effort Finset Filter Topology

namespace HSAux

variable {n : ℕ}

lemma interior_box (M : Params n) (hr : 0 < M.r) (hP : M.P.PosDef)
    (hd : ∀ k, M.sH k - M.sL k ≠ 0) (hc : ∀ k, 0 < 1 - ctil M k) (hI : Interior M) :
    ∀ i, 0 < δhat M i ∧ δhat M i < 1 := by
  intro i
  have hD : 0 < M.P.det := hP.det_pos
  have hpii : 0 < M.P⁻¹ i i := hP.inv.diag_pos
  rw [inv_apply_eq] at hpii
  have ha : 0 < M.P.adjugate i i := by
    have := mul_pos hpii hD
    rwa [div_mul_cancel₀ _ hD.ne'] at this
  set S := ∑ j ∈ Finset.univ.erase i,
      (1 - ctil M j) * (M.VH j - M.VL j) * M.P.adjugate i j / (M.r * (M.sH j - M.sL j) * M.P.det)
    with hS
  have hsplit : δhat M i = (1 - ctil M i) * (M.VH i - M.VL i)
      / (M.r * (M.sH i - M.sL i) * (M.sH i - M.sL i)) * (M.P.adjugate i i / M.P.det)
      + S / (M.sH i - M.sL i) - M.sL i / (M.sH i - M.sL i) := by
    unfold δhat
    simp_rw [inv_apply_eq]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hS, Finset.sum_div]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    generalize M.sH i - M.sL i = a
    generalize M.sH j - M.sL j = b
    ring
  obtain ⟨hlo, hhi⟩ := hI i
  unfold ΔVlo at hlo
  unfold ΔVhi at hhi
  rw [← hS] at hlo hhi
  rw [hsplit]
  have hdi := hd i
  have hci := hc i
  generalize hdd : M.sH i - M.sL i = d at *
  have hsH : M.sH i = d + M.sL i := by linarith
  rw [hsH] at hhi
  generalize 1 - ctil M i = g at *
  generalize M.VH i - M.VL i = V at *
  generalize M.P.adjugate i i = a at *
  generalize M.P.det = D at *
  have hκ : 0 < g * a / (M.r * d ^ 2 * D) := by positivity
  have key1 : g * V / (M.r * d * d) * (a / D) + S / d - M.sL i / d
      = g * a / (M.r * d ^ 2 * D) * (V - M.r * d * D / (g * a) * (M.sL i - S)) := by
    field_simp; ring
  have key2 : g * V / (M.r * d * d) * (a / D) + S / d - M.sL i / d - 1
      = g * a / (M.r * d ^ 2 * D) * (V - M.r * d * D / (g * a) * (d + M.sL i - S)) := by
    field_simp; ring
  constructor
  · rw [key1]; exact mul_pos hκ (by linarith)
  · have : g * a / (M.r * d ^ 2 * D) * (V - M.r * d * D / (g * a) * (d + M.sL i - S)) < 0 :=
      mul_neg_of_pos_of_neg hκ (by linarith)
    linarith

/-! ### One-parameter families -/

lemma withC_self (M : Params n) (i : Fin n) : withC M i (M.c i) = M := by
  simp [withC]

lemma withVH_self (M : Params n) (i : Fin n) : withVH M i (M.VH i) = M := by
  simp [withVH]

lemma withSH_self (M : Params n) (i : Fin n) : withSH M i (M.sH i) = M := by
  simp [withSH]

lemma δhat_withC (M : Params n) (i k : Fin n) (t : ℝ) :
    δhat (withC M i t) k = δhat M k + (t - M.c i) * (-(M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i) := by
  unfold δhat
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∀ j ∈ Finset.univ.erase i, ctil (withC M i t) j = ctil M j := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [ctil, withC, Function.update_of_ne hji]
  rw [Finset.sum_congr rfl fun j hj => by rw [hrest j hj]]
  have hi : ctil (withC M i t) i = ctil M i + (t - M.c i) := by
    simp [ctil, withC]; try ring
  simp only [hi]
  simp only [withC]
  generalize M.sH k - M.sL k = a
  generalize M.sH i - M.sL i = b
  ring

lemma δhat_withVH (M : Params n) (i k : Fin n) (t : ℝ) :
    δhat (withVH M i t) k = δhat M k + (t - M.VH i) * ((1 - ctil M i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i) := by
  unfold δhat
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hct : ∀ j, ctil (withVH M i t) j = ctil M j := by
    intro j; simp [ctil, withVH]
  have hrest : ∀ j ∈ Finset.univ.erase i, (withVH M i t).VH j = M.VH j := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [withVH, Function.update_of_ne hji]
  simp only [hct]
  rw [Finset.sum_congr rfl fun j hj => by rw [hrest j hj]]
  simp only [withVH, Function.update_self]
  generalize M.sH k - M.sL k = a
  generalize M.sH i - M.sL i = b
  ring

lemma δhat_withSH_ne (M : Params n) (i k : Fin n) (hki : k ≠ i) (t : ℝ) :
    δhat (withSH M i t) k = δhat M k + (1 - ctil M i) * (M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k)) * M.P⁻¹ k i * ((t - M.sL i)⁻¹ - (M.sH i - M.sL i)⁻¹) := by
  unfold δhat
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hct : ∀ j, ctil (withSH M i t) j = ctil M j := by
    intro j; simp [ctil, withSH]
  have hrest : ∀ j ∈ Finset.univ.erase i, (withSH M i t).sH j = M.sH j := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [withSH, Function.update_of_ne hji]
  have hk : (withSH M i t).sH k = M.sH k := by simp [withSH, Function.update_of_ne hki]
  simp only [hct]
  rw [Finset.sum_congr rfl fun j hj => by rw [hrest j hj]]
  simp only [hk]
  simp only [withSH, Function.update_self]
  generalize M.sH k - M.sL k = a
  generalize M.sH i - M.sL i = b
  generalize t - M.sL i = c
  ring

lemma δhat_withSH_self (M : Params n) (i : Fin n) (t : ℝ) :
    δhat (withSH M i t) i =
      (1 - ctil M i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i * ((t - M.sL i)⁻¹) ^ 2
      + ((∑ j ∈ Finset.univ.erase i,
          (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j)
        - M.sL i) * (t - M.sL i)⁻¹ := by
  unfold δhat
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hct : ∀ j, ctil (withSH M i t) j = ctil M j := by
    intro j; simp [ctil, withSH]
  have hrest : ∀ j ∈ Finset.univ.erase i, (withSH M i t).sH j = M.sH j := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [withSH, Function.update_of_ne hji]
  simp only [hct]
  rw [Finset.sum_congr rfl fun j hj => by rw [hrest j hj]]
  have hi : (withSH M i t).sH i = t := by simp [withSH]
  simp only [hi]
  simp only [withSH]
  have : ∀ j ∈ Finset.univ.erase i,
      (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (t - M.sL i) * (M.sH j - M.sL j)) * M.P⁻¹ i j
        = (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j
          * (t - M.sL i)⁻¹ := by
    intro j _
    generalize M.sH j - M.sL j = b
    generalize t - M.sL i = c
    ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
  generalize (∑ j ∈ Finset.univ.erase i,
          (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j) = B
  generalize t - M.sL i = c
  ring

/-! ### Derivatives of the closed form along the families -/

lemma hasDerivAt_δhat_withC (M : Params n) (i k : Fin n) :
    HasDerivAt (fun t => δhat (withC M i t) k) (-(M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i) (M.c i) := by
  simp_rw [δhat_withC]
  have := (((hasDerivAt_id (M.c i)).sub_const (M.c i)).mul_const (-(M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i)).const_add (δhat M k)
  simpa using this

lemma hasDerivAt_δhat_withVH (M : Params n) (i k : Fin n) :
    HasDerivAt (fun t => δhat (withVH M i t) k) ((1 - ctil M i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i) (M.VH i) := by
  simp_rw [δhat_withVH]
  have := (((hasDerivAt_id (M.VH i)).sub_const (M.VH i)).mul_const ((1 - ctil M i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i)).const_add (δhat M k)
  simpa using this

lemma hasDerivAt_δhat_withSH_ne (M : Params n) (i k : Fin n) (hki : k ≠ i)
    (hdi : M.sH i - M.sL i ≠ 0) :
    HasDerivAt (fun t => δhat (withSH M i t) k) ((1 - ctil M i) * (M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k)) * M.P⁻¹ k i * (-1 / (M.sH i - M.sL i) ^ 2)) (M.sH i) := by
  simp_rw [δhat_withSH_ne M i k hki]
  have h1 : HasDerivAt (fun t => (t - M.sL i)⁻¹) (-1 / (M.sH i - M.sL i) ^ 2) (M.sH i) := by
    have h0 : HasDerivAt (fun t : ℝ => t - M.sL i) 1 (M.sH i) :=
      (hasDerivAt_id' (M.sH i)).sub_const _
    exact h0.fun_inv hdi
  have := ((h1.sub_const ((M.sH i - M.sL i)⁻¹)).const_mul ((1 - ctil M i) * (M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k)) * M.P⁻¹ k i)).const_add (δhat M k)
  simpa using this

lemma hasDerivAt_δhat_withSH_self (M : Params n) (i : Fin n) (hdi : M.sH i - M.sL i ≠ 0) :
    HasDerivAt (fun t => δhat (withSH M i t) i)
      ((1 - ctil M i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i
          * (2 * (M.sH i - M.sL i)⁻¹ * (-1 / (M.sH i - M.sL i) ^ 2))
        + ((∑ j ∈ Finset.univ.erase i,
          (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j)
          - M.sL i) * (-1 / (M.sH i - M.sL i) ^ 2)) (M.sH i) := by
  simp_rw [δhat_withSH_self M i]
  have h1 : HasDerivAt (fun t => (t - M.sL i)⁻¹) (-1 / (M.sH i - M.sL i) ^ 2) (M.sH i) := by
    have h0 : HasDerivAt (fun t : ℝ => t - M.sL i) 1 (M.sH i) :=
      (hasDerivAt_id' (M.sH i)).sub_const _
    exact h0.fun_inv hdi
  have h2 := h1.fun_pow 2
  have := (h2.const_mul ((1 - ctil M i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i)).fun_add
    (h1.const_mul ((∑ j ∈ Finset.univ.erase i,
          (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j)
          - M.sL i))
  refine this.congr_deriv ?_
  push_cast
  ring

/-! ### Transfer to the optimal effort -/

lemma eventually_optEffort {F : ℝ → Params n} {t0 : ℝ}
    (hcont : ∀ k, ContinuousAt (fun t => δhat (F t) k) t0)
    (hbox0 : ∀ k, 0 < δhat (F t0) k ∧ δhat (F t0) k < 1)
    (hgood : ∀ᶠ t in 𝓝 t0, (∀ i, (F t).β i i = 1) ∧ (∀ i, (F t).P i i = 1) ∧ 0 < (F t).r ∧
      (F t).P.PosDef ∧ ∀ k, (F t).sH k - (F t).sL k ≠ 0) :
    ∀ᶠ t in 𝓝 t0, optEffort (F t) = δhat (F t) := by
  have hb : ∀ᶠ t in 𝓝 t0, ∀ k, 0 < δhat (F t) k ∧ δhat (F t) k < 1 := by
    rw [Filter.eventually_all]
    intro k
    exact (hcont k).eventually_mem (Ioo_mem_nhds (hbox0 k).1 (hbox0 k).2)
  filter_upwards [hb, hgood] with t h1 h2
  exact optEffort_eq (F t) h2.1 h2.2.1 h2.2.2.1 h2.2.2.2.1 h2.2.2.2.2
    (fun k => ⟨(h1 k).1.le, (h1 k).2.le⟩)

end HSAux

open HolisticService.Effort Finset Filter Topology

namespace HSAux

variable {n : ℕ}

lemma inv_symm (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (a b : Fin n) :
    P⁻¹ a b = P⁻¹ b a := by
  have := hP.inv.isHermitian.apply a b
  simp only [star_trivial] at this
  exact this.symm

lemma optEffort_withC (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPd : ∀ i, M.P i i = 1)
    (hr : 0 < M.r) (hP : M.P.PosDef) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hc : ∀ k, 0 < 1 - ctil M k) (hI : Interior M) (i k : Fin n) :
    HasDerivAt (fun t => optEffort (withC M i t) k) (-(M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i) (M.c i) := by
  have hbox := interior_box M hr hP hd hc hI
  have hev := eventually_optEffort (F := withC M i) (t0 := M.c i)
    (fun k => (hasDerivAt_δhat_withC M i k).continuousAt) (by rw [withC_self]; exact hbox)
    (Eventually.of_forall fun t => ⟨hβd, hPd, hr, hP, hd⟩)
  exact (hasDerivAt_δhat_withC M i k).congr_of_eventuallyEq (hev.mono fun t ht => congrFun ht k)

lemma optEffort_withVH (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPd : ∀ i, M.P i i = 1)
    (hr : 0 < M.r) (hP : M.P.PosDef) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hc : ∀ k, 0 < 1 - ctil M k) (hI : Interior M) (i k : Fin n) :
    HasDerivAt (fun t => optEffort (withVH M i t) k) ((1 - ctil M i)
      / (M.r * (M.sH k - M.sL k) * (M.sH i - M.sL i)) * M.P⁻¹ k i) (M.VH i) := by
  have hbox := interior_box M hr hP hd hc hI
  have hev := eventually_optEffort (F := withVH M i) (t0 := M.VH i)
    (fun k => (hasDerivAt_δhat_withVH M i k).continuousAt) (by rw [withVH_self]; exact hbox)
    (Eventually.of_forall fun t => ⟨hβd, hPd, hr, hP, hd⟩)
  exact (hasDerivAt_δhat_withVH M i k).congr_of_eventuallyEq (hev.mono fun t ht => congrFun ht k)

lemma eventually_withSH (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPd : ∀ i, M.P i i = 1)
    (hr : 0 < M.r) (hP : M.P.PosDef) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hc : ∀ k, 0 < 1 - ctil M k) (hI : Interior M) (i : Fin n) :
    ∀ᶠ t in 𝓝 (M.sH i), optEffort (withSH M i t) = δhat (withSH M i t) := by
  have hbox := interior_box M hr hP hd hc hI
  have hne : ∀ᶠ t in 𝓝 (M.sH i), t - M.sL i ≠ 0 :=
    (continuous_sub_right (M.sL i)).continuousAt.eventually_ne (hd i)
  refine eventually_optEffort (F := withSH M i) (t0 := M.sH i) ?_ (by rw [withSH_self]; exact hbox) ?_
  · intro k
    by_cases hki : k = i
    · subst hki; exact (hasDerivAt_δhat_withSH_self M k (hd k)).continuousAt
    · exact (hasDerivAt_δhat_withSH_ne M i k hki (hd i)).continuousAt
  · filter_upwards [hne] with t ht
    refine ⟨hβd, hPd, hr, hP, ?_⟩
    intro k
    by_cases hki : k = i
    · subst hki; simpa [withSH] using ht
    · simpa [withSH, Function.update_of_ne hki] using hd k

lemma optEffort_withSH_ne (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPd : ∀ i, M.P i i = 1)
    (hr : 0 < M.r) (hP : M.P.PosDef) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hc : ∀ k, 0 < 1 - ctil M k) (hI : Interior M) (i k : Fin n) (hki : k ≠ i) :
    HasDerivAt (fun t => optEffort (withSH M i t) k) ((1 - ctil M i) * (M.VH i - M.VL i)
      / (M.r * (M.sH k - M.sL k)) * M.P⁻¹ k i * (-1 / (M.sH i - M.sL i) ^ 2)) (M.sH i) := by
  have hev := eventually_withSH M hβd hPd hr hP hd hc hI i
  exact (hasDerivAt_δhat_withSH_ne M i k hki (hd i)).congr_of_eventuallyEq
    (hev.mono fun t ht => congrFun ht k)

lemma optEffort_withSH_self (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPd : ∀ i, M.P i i = 1)
    (hr : 0 < M.r) (hP : M.P.PosDef) (hd : ∀ k, M.sH k - M.sL k ≠ 0)
    (hc : ∀ k, 0 < 1 - ctil M k) (hI : Interior M) (i : Fin n) :
    HasDerivAt (fun t => optEffort (withSH M i t) i)
      ((1 - ctil M i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i
          * (2 * (M.sH i - M.sL i)⁻¹ * (-1 / (M.sH i - M.sL i) ^ 2))
        + ((∑ j ∈ Finset.univ.erase i,
          (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ i j)
          - M.sL i) * (-1 / (M.sH i - M.sL i) ^ 2)) (M.sH i) := by
  have hev := eventually_withSH M hβd hPd hr hP hd hc hI i
  exact (hasDerivAt_δhat_withSH_self M i (hd i)).congr_of_eventuallyEq
    (hev.mono fun t ht => congrFun ht i)

/-- Facts extracted from the standing assumptions. -/
lemma standing_facts (M : Params n) (hS : M.Standing) :
    (∀ i, M.β i i = 1) ∧ (∀ i, M.P i i = 1) ∧ 0 < M.r ∧ M.P.PosDef ∧
      (∀ k, M.sH k - M.sL k ≠ 0) ∧ (∀ k, 0 < 1 - ctil M k) ∧ (∀ k, 0 < M.VH k - M.VL k) ∧
      (∀ k, M.c k < 1) := by
  obtain ⟨hV, hβd, _, hβsum, hcS, _, hr, _, hne, _, hPd, _, hP⟩ := hS
  refine ⟨hβd, hPd, hr, hP, fun k => sub_ne_zero.mpr (hne k), ?_, fun k => by
    linarith [(hV k).2], fun k => (hcS k).2⟩
  intro k
  unfold ctil
  linarith [(hβsum k).1, (hcS k).2]

lemma ctil_eq_c (M : Params n) (hβ : NoTechCoupling M) (j : Fin n) : ctil M j = M.c j := by
  unfold ctil
  rw [Finset.sum_eq_zero fun m hm => hβ j m (Finset.ne_of_mem_erase hm).symm]
  ring

end HSAux

open HolisticService.Effort Finset Filter Topology

namespace HSAux

variable {n : ℕ}

/-- The threshold identities behind `Interior ↔ δ̂ ∈ (0,1)^n`. -/
lemma thr_key (M : Params n) (hr : 0 < M.r) (hP : M.P.PosDef)
    (hd : ∀ k, M.sH k - M.sL k ≠ 0) (hc : ∀ k, 0 < 1 - ctil M k) (i : Fin n) :
    0 < (1 - ctil M i) * M.P.adjugate i i / (M.r * (M.sH i - M.sL i) ^ 2 * M.P.det) ∧
    δhat M i = (1 - ctil M i) * M.P.adjugate i i / (M.r * (M.sH i - M.sL i) ^ 2 * M.P.det)
      * ((M.VH i - M.VL i) - ΔVlo M i) ∧
    δhat M i - 1 = (1 - ctil M i) * M.P.adjugate i i / (M.r * (M.sH i - M.sL i) ^ 2 * M.P.det)
      * ((M.VH i - M.VL i) - ΔVhi M i) ∧
    ΔVhi M i - ΔVlo M i
      = M.r * (M.sH i - M.sL i) ^ 2 * M.P.det / ((1 - ctil M i) * M.P.adjugate i i) := by
  have hD : 0 < M.P.det := hP.det_pos
  have hpii : 0 < M.P⁻¹ i i := hP.inv.diag_pos
  rw [inv_apply_eq] at hpii
  have ha : 0 < M.P.adjugate i i := by
    have := mul_pos hpii hD
    rwa [div_mul_cancel₀ _ hD.ne'] at this
  set S := ∑ j ∈ Finset.univ.erase i,
      (1 - ctil M j) * (M.VH j - M.VL j) * M.P.adjugate i j / (M.r * (M.sH j - M.sL j) * M.P.det)
    with hS
  have hsplit : δhat M i = (1 - ctil M i) * (M.VH i - M.VL i)
      / (M.r * (M.sH i - M.sL i) * (M.sH i - M.sL i)) * (M.P.adjugate i i / M.P.det)
      + S / (M.sH i - M.sL i) - M.sL i / (M.sH i - M.sL i) := by
    unfold δhat
    simp_rw [inv_apply_eq]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hS, Finset.sum_div]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    generalize M.sH i - M.sL i = a
    generalize M.sH j - M.sL j = b
    ring
  unfold ΔVlo ΔVhi
  rw [← hS, hsplit]
  have hdi := hd i
  have hci := hc i
  generalize hdd : M.sH i - M.sL i = d at *
  have hsH : M.sH i = d + M.sL i := by linarith
  rw [hsH]
  generalize 1 - ctil M i = g at *
  generalize M.VH i - M.VL i = V at *
  generalize M.P.adjugate i i = a at *
  generalize M.P.det = D at *
  have hga : g * a ≠ 0 := (mul_pos hci ha).ne'
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring

/-- `Σ_j (δ_j(σ^H_j − σ^L_j) + σ^L_j) ρ_{i,j} = Σ_j ρ_{i,j} σ_j(δ)`. -/
lemma gradU_eq (M : Params n) (δ : Fin n → ℝ) (i : Fin n) :
    gradU M δ i = (1 - ctil M i) * (M.VH i - M.VL i)
      - M.r * (M.sH i - M.sL i) * ∑ j, M.P i j * sig M δ j := by
  unfold gradU sig
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma update_eq_add (δ : Fin n → ℝ) (i : Fin n) (t : ℝ) (j : Fin n) :
    Function.update δ i t j = δ j + if j = i then t - δ i else 0 := by
  by_cases h : j = i
  · subst h; simp
  · simp [h, Function.update_of_ne h]

/-- Expansion of `Ũ` along the `i`-th coordinate. -/
lemma utilde_update (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPs : M.P.IsSymm)
    (hPd : ∀ i, M.P i i = 1) (δ : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    Utilde M (Function.update δ i t) = Utilde M δ + (t - δ i) * gradU M δ i
      - M.r / 2 * (t - δ i) ^ 2 * (M.sH i - M.sL i) ^ 2 := by
  rw [utilde_eq M hβd hPs hPd, utilde_eq M hβd hPs hPd, gradU_eq]
  set h := t - δ i
  have hs : ∀ j, sig M (Function.update δ i t) j
      = sig M δ j + if j = i then h * (M.sH i - M.sL i) else 0 := by
    intro j
    unfold sig
    rw [update_eq_add]
    split_ifs with hj
    · subst hj; ring
    · ring
  have hv : ∀ j, Vval M (Function.update δ i t) j
      = Vval M δ j + if j = i then h * (M.VH i - M.VL i) else 0 := by
    intro j
    unfold Vval
    rw [update_eq_add]
    split_ifs with hj
    · subst hj; ring
    · ring
  simp_rw [hs, hv]
  have hL : ∑ j, (1 - ctil M j) * (Vval M δ j + if j = i then h * (M.VH i - M.VL i) else 0)
      = ∑ j, (1 - ctil M j) * Vval M δ j + (1 - ctil M i) * (h * (M.VH i - M.VL i)) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hQ : ∑ a, ∑ b, M.P a b * (sig M δ a + if a = i then h * (M.sH i - M.sL i) else 0)
        * (sig M δ b + if b = i then h * (M.sH i - M.sL i) else 0)
      = ∑ a, ∑ b, M.P a b * sig M δ a * sig M δ b
        + 2 * (h * (M.sH i - M.sL i)) * ∑ b, M.P i b * sig M δ b
        + (h * (M.sH i - M.sL i)) ^ 2 := by
    have e : ∀ a b, M.P a b * (sig M δ a + if a = i then h * (M.sH i - M.sL i) else 0)
        * (sig M δ b + if b = i then h * (M.sH i - M.sL i) else 0)
        = M.P a b * sig M δ a * sig M δ b
          + (if a = i then h * (M.sH i - M.sL i) * (M.P i b * sig M δ b) else 0)
          + (if b = i then h * (M.sH i - M.sL i) * (M.P i a * sig M δ a) else 0)
          + (if a = i then (if b = i then (h * (M.sH i - M.sL i)) ^ 2 else 0) else 0) := by
      intro a b
      by_cases ha : a = i <;> by_cases hb : b = i
      · subst ha; subst hb; simp [hPd]; ring
      · subst ha; simp [hb]; ring
      · subst hb; simp [ha, hPs.apply]; ring
      · simp [ha, hb]
    simp_rw [e, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
      Finset.sum_const_zero]
    rw [← Finset.mul_sum]
    ring
  rw [hL, hQ]
  ring

lemma utilde_hasDerivAt' (M : Params n) (hβd : ∀ i, M.β i i = 1) (hPs : M.P.IsSymm)
    (hPd : ∀ i, M.P i i = 1) (δ : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t => Utilde M (Function.update δ i t)) (gradU M δ i) (δ i) := by
  simp_rw [utilde_update M hβd hPs hPd δ i]
  have h1 : HasDerivAt (fun t : ℝ => t - δ i) 1 (δ i) := (hasDerivAt_id' _).sub_const _
  have := ((h1.mul_const (gradU M δ i)).const_add (Utilde M δ)).sub
    (((h1.fun_pow 2).const_mul (M.r / 2)).mul_const ((M.sH i - M.sL i) ^ 2))
  refine this.congr_deriv ?_
  simp

lemma gradU_update (M : Params n) (δ : Fin n → ℝ) (i j : Fin n) (s : ℝ) :
    gradU M (Function.update δ j s) i
      = gradU M δ i - M.r * (M.sH i - M.sL i) * (M.sH j - M.sL j) * M.P i j * (s - δ j) := by
  unfold gradU
  simp_rw [update_eq_add δ j s]
  have : ∀ m, ((δ m + if m = j then s - δ j else 0) * (M.sH m - M.sL m) + M.sL m) * M.P i m
      = (δ m * (M.sH m - M.sL m) + M.sL m) * M.P i m
        + if m = j then (s - δ j) * (M.sH j - M.sL j) * M.P i j else 0 := by
    intro m
    split_ifs with hm
    · subst hm; ring
    · ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end HSAux

open HolisticService.Effort in
theorem solution {n : ℕ} (M : Params n) (hS : M.Standing) (δ : Fin n → ℝ) :
    (∀ i, gradU M δ i = 0) ↔ δ = δhat M := by
  obtain ⟨-, -, hr, hP, hd, -, -, -⟩ := HSAux.standing_facts M hS
  have hdet : IsUnit M.P.det := (hP.det_pos).ne'.isUnit
  have hPs := HSAux.P_sig_hat M hr.ne' hd hdet
  constructor
  · intro h
    have hv : Matrix.mulVec M.P (sig M δ) = Matrix.mulVec M.P (sig M (δhat M)) := by
      funext i
      have h1 := h i
      rw [HSAux.gradU_eq] at h1
      simp only [Matrix.mulVec, dotProduct]
      rw [hPs i]
      have hdi := hd i
      field_simp
      linarith
    have hv2 : sig M δ = sig M (δhat M) := by
      have := congrArg (Matrix.mulVec M.P⁻¹) hv
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec, Matrix.one_mulVec] at this
    funext k
    have := congrFun hv2 k
    unfold sig at this
    have hdk := hd k
    have : (δ k - δhat M k) * (M.sH k - M.sL k) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hdk
  · rintro rfl i
    rw [HSAux.gradU_eq, hPs i]
    have hdi := hd i
    field_simp
    ring
