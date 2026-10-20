-- Prove2me | solution 1 for MFGPlanning.Penalized.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T02:16:40.124262+00:00
-- url     : https://prove2.me/submissions/565ef608-cefc-47ee-b770-072b8cddf6a6

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme

set_option autoImplicit false

open Finset

namespace MFGPlanning.Penalized
namespace P1U

variable (d : Data)

lemma sum_shift1 (f : Pt d → ℝ) (c : ZMod d.Nh) : ∑ p : Pt d, f (p.1 + c, p.2) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.addRight c).prodCongr (Equiv.refl _)) _ _ (fun _ => rfl)

lemma sum_shift1' (f : Pt d → ℝ) (c : ZMod d.Nh) : ∑ p : Pt d, f (p.1 - c, p.2) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.subRight c).prodCongr (Equiv.refl _)) _ _ (fun _ => rfl)

lemma sum_shift2 (f : Pt d → ℝ) (c : ZMod d.Nh) : ∑ p : Pt d, f (p.1, p.2 + c) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.refl _).prodCongr (Equiv.addRight c)) _ _ (fun _ => rfl)

lemma sum_shift2' (f : Pt d → ℝ) (c : ZMod d.Nh) : ∑ p : Pt d, f (p.1, p.2 - c) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.refl _).prodCongr (Equiv.subRight c)) _ _ (fun _ => rfl)

lemma sh_a (A B : Pt d → ℝ) :
    ∑ p : Pt d, A p * B (p.1 + 1, p.2) = ∑ p : Pt d, B p * A (p.1 - 1, p.2) := by
  rw [← sum_shift1 d (fun p => B p * A (p.1 - 1, p.2)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sh_b (A B : Pt d → ℝ) :
    ∑ p : Pt d, A p * B (p.1 - 1, p.2) = ∑ p : Pt d, B p * A (p.1 + 1, p.2) := by
  rw [← sum_shift1' d (fun p => B p * A (p.1 + 1, p.2)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sh_c (A B : Pt d → ℝ) :
    ∑ p : Pt d, A p * B (p.1, p.2 + 1) = ∑ p : Pt d, B p * A (p.1, p.2 - 1) := by
  rw [← sum_shift2 d (fun p => B p * A (p.1, p.2 - 1)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sh_d (A B : Pt d → ℝ) :
    ∑ p : Pt d, A p * B (p.1, p.2 - 1) = ∑ p : Pt d, B p * A (p.1, p.2 + 1) := by
  rw [← sum_shift2' d (fun p => B p * A (p.1, p.2 + 1)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sum_mul_lap (M V : Pt d → ℝ) : ∑ p, M p * lap d V p = ∑ p, V p * lap d M p := by
  have e : ∀ A B : Pt d → ℝ, ∑ p, A p * lap d B p =
      -(1 / d.h ^ 2) * (4 * ∑ p, A p * B p - ∑ p, A p * B (p.1 + 1, p.2)
        - ∑ p, A p * B (p.1 - 1, p.2) - ∑ p, A p * B (p.1, p.2 + 1)
        - ∑ p, A p * B (p.1, p.2 - 1)) := by
    intro A B
    simp only [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    unfold lap; ring
  rw [e, e, sh_a d M V, sh_b d M V, sh_c d M V, sh_d d M V]
  have : ∑ p, M p * V p = ∑ p, V p * M p := sum_congr rfl fun p _ => mul_comm _ _
  rw [this]; ring

lemma Dh0 (V : Pt d → ℝ) (p : Pt d) : Dh d V p 0 = D1 d V p := rfl
lemma Dh1 (V : Pt d → ℝ) (p : Pt d) : Dh d V p 1 = D1 d V (p.1 - 1, p.2) := rfl
lemma Dh2 (V : Pt d → ℝ) (p : Pt d) : Dh d V p 2 = D2 d V p := rfl
lemma Dh3 (V : Pt d → ℝ) (p : Pt d) : Dh d V p 3 = D2 d V (p.1, p.2 - 1) := rfl

lemma sum_Z_Dh (Z : Pt d → Fin 4 → ℝ) (V : Pt d → ℝ) :
    ∑ p, ∑ l, Z p l * Dh d V p l = -∑ p, V p * divh d Z p := by
  have e1 : ∑ p, ∑ l, Z p l * Dh d V p l =
      (1 / d.h) * ((∑ p, (fun q => Z q 0) p * V (p.1 + 1, p.2) - ∑ p, Z p 0 * V p)
        + (∑ p, Z p 1 * V p - ∑ p, (fun q => Z q 1) p * V (p.1 - 1, p.2))
        + (∑ p, (fun q => Z q 2) p * V (p.1, p.2 + 1) - ∑ p, Z p 2 * V p)
        + (∑ p, Z p 3 * V p - ∑ p, (fun q => Z q 3) p * V (p.1, p.2 - 1))) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    simp only [Fin.sum_univ_four, Dh0, Dh1, Dh2, Dh3, D1, D2, sub_add_cancel]
    field_simp
    try ring
  have e2 : ∑ p, V p * divh d Z p =
      (1 / d.h) * ((∑ p, V p * Z p 0 - ∑ p, V p * (fun q => Z q 0) (p.1 - 1, p.2))
        + (∑ p, V p * (fun q => Z q 1) (p.1 + 1, p.2) - ∑ p, V p * Z p 1)
        + (∑ p, V p * Z p 2 - ∑ p, V p * (fun q => Z q 2) (p.1, p.2 - 1))
        + (∑ p, V p * (fun q => Z q 3) (p.1, p.2 + 1) - ∑ p, V p * Z p 3)) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    unfold divh; ring
  rw [e1, e2, sh_a d (fun q => Z q 0) V, sh_b d (fun q => Z q 1) V, sh_c d (fun q => Z q 2) V,
    sh_d d (fun q => Z q 3) V]
  beta_reduce
  have c : ∀ l : Fin 4, ∑ p, Z p l * V p = ∑ p, V p * Z p l :=
    fun l => sum_congr rfl fun p _ => mul_comm _ _
  rw [c 0, c 1, c 2, c 3]
  ring

lemma single_eq_smul (q : Fin 4 → ℝ) (l : Fin 4) :
    (Pi.single l (q l) : Fin 4 → ℝ) = q l • (Pi.single l (1 : ℝ) : Fin 4 → ℝ) := by
  ext j
  by_cases h : j = l
  · subst h; simp
  · simp [h]

lemma fderiv_expand (L : (Fin 4 → ℝ) →L[ℝ] ℝ) (q : Fin 4 → ℝ) :
    L q = ∑ l, q l * L (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single q]
  rw [map_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [single_eq_smul, map_smul, smul_eq_mul]

/-- tangent-plane bound at an arbitrary base point. -/
lemma tangent_le (f : (Fin 4 → ℝ) → ℝ) (hc : ConvexOn ℝ Set.univ f) (x : Fin 4 → ℝ)
    (hd : DifferentiableAt ℝ f x) (q : Fin 4 → ℝ) :
    f x + ∑ l, (q l - x l) * fderiv ℝ f x (Pi.single l 1) ≤ f q := by
  set φ : ℝ → ℝ := fun t => f (x + t • (q - x)) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    have h1 := hc.translate_right x
    rw [Set.preimage_univ] at h1
    have h := h1.comp_linearMap (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (q - x))
    rw [Set.preimage_univ] at h
    exact h
  have hφd : HasDerivAt φ (fderiv ℝ f x (q - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • (q - x)) ((1 : ℝ) • (q - x)) 0 :=
      ((hasDerivAt_id 0).smul_const (q - x)).const_add x
    have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (q - x)) := by
      simpa using hd.hasFDerivAt
    have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
    rw [one_smul] at h3
    exact h3
  have := hφc.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφd.differentiableAt
  rw [hφd.deriv, slope_def_field] at this
  simp only [hφ, one_smul, zero_smul, add_zero, sub_zero, div_one, add_sub_cancel] at this
  rw [fderiv_expand] at this
  simp only [Pi.sub_apply] at this
  linarith

/-- equality in the tangent-plane bound forces the base point under strict convexity. -/
lemma tangent_eq (f : (Fin 4 → ℝ) → ℝ) (hs : StrictConvexOn ℝ Set.univ f) (x : Fin 4 → ℝ)
    (hd : DifferentiableAt ℝ f x) (q : Fin 4 → ℝ)
    (h : f q ≤ f x + ∑ l, (q l - x l) * fderiv ℝ f x (Pi.single l 1)) : q = x := by
  by_contra hne
  have h1 := hs.2 (Set.mem_univ q) (Set.mem_univ x) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have h2 := tangent_le f hs.convexOn x hd ((1 / 2 : ℝ) • q + (1 / 2 : ℝ) • x)
  have e : ∀ l, ((1 / 2 : ℝ) • q + (1 / 2 : ℝ) • x) l - x l = (1 / 2) * (q l - x l) := by
    intro l; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [e] at h2
  simp only [smul_eq_mul] at h1
  rw [Fin.sum_univ_four] at h h2
  linarith

lemma dg_sign (hG1 : G1 d) (hG3 : G3 d) (p : Pt d) (q : Fin 4 → ℝ) :
    dg d p q 0 ≤ 0 ∧ 0 ≤ dg d p q 1 ∧ dg d p q 2 ≤ 0 ∧ 0 ≤ dg d p q 3 := by
  have hd : ∀ l : Fin 4, HasDerivAt (fun t : ℝ => d.g p (q + t • (Pi.single l 1 : Fin 4 → ℝ)))
      (dg d p q l) 0 := by
    intro l
    have h1 : HasDerivAt (fun t : ℝ => q + t • (Pi.single l 1 : Fin 4 → ℝ))
        (Pi.single l 1 : Fin 4 → ℝ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin 4 → ℝ)).const_add q
    have h2 : HasFDerivAt (d.g p) (fderiv ℝ (d.g p) q)
        (q + (0 : ℝ) • (Pi.single l 1 : Fin 4 → ℝ)) := by
      simpa using ((hG3 p).differentiable (by norm_num) q).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have ev : ∀ (l j : Fin 4) (t : ℝ),
      (q + t • (Pi.single l 1 : Fin 4 → ℝ)) j = q j + if j = l then t else 0 := by
    intro l j t; by_cases h : j = l <;> simp [Pi.single_apply, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← (hd 0).deriv]
    apply Antitone.deriv_nonpos
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith
  · rw [← (hd 1).deriv]
    apply Monotone.deriv_nonneg
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith
  · rw [← (hd 2).deriv]
    apply Antitone.deriv_nonpos
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith
  · rw [← (hd 3).deriv]
    apply Monotone.deriv_nonneg
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith

lemma B_eq_divh (U M : Pt d → ℝ) (p : Pt d) :
    B d U M p = divh d (fun q l => M q * dg d q (Dh d U q) l) p := by
  unfold B divh; dsimp only; ring

lemma h_pos : 0 < d.h := by
  unfold Data.h; exact inv_pos.2 (Nat.cast_pos.2 d.hNh)

lemma dt_pos : 0 < d.Δt := by
  unfold Data.Δt; exact div_pos d.hT (Nat.cast_pos.2 d.hNT)

/-- a zero of the density at time `n` propagates forward (and, with viscosity, to the
neighbours). -/
lemma zero_step (hG1 : G1 d) (hG3 : G3 d) (Mt : Fin (d.NT + 1) → Pt d → ℝ)
    (U : Fin (d.NT + 1) → Pt d → ℝ) (hnn : ∀ j p, 0 ≤ Mt j p)
    (hFP : ∀ (n : Fin d.NT) (p : Pt d), (Mt n.succ p - Mt n.castSucc p) / d.Δt
      + d.ν * lap d (Mt n.castSucc) p + B d (U n.succ) (Mt n.castSucc) p = 0)
    (n : Fin d.NT) (p : Pt d) (h0 : Mt n.castSucc p = 0) :
    Mt n.succ p = 0 ∧ (0 < d.ν → Mt n.castSucc (p.1 + 1, p.2) = 0 ∧
      Mt n.castSucc (p.1, p.2 + 1) = 0) := by
  have hh := h_pos d
  have hdt := dt_pos d
  set m := Mt n.castSucc with hm
  have e := hFP n p
  rw [← hm] at e
  have hlap : lap d m p = (1 / d.h ^ 2) * (m (p.1 + 1, p.2) + m (p.1 - 1, p.2)
      + m (p.1, p.2 + 1) + m (p.1, p.2 - 1)) := by
    unfold lap; rw [h0]; ring
  have s1 := dg_sign d hG1 hG3 (p.1 - 1, p.2) (Dh d (U n.succ) (p.1 - 1, p.2))
  have s2 := dg_sign d hG1 hG3 (p.1 + 1, p.2) (Dh d (U n.succ) (p.1 + 1, p.2))
  have s3 := dg_sign d hG1 hG3 (p.1, p.2 - 1) (Dh d (U n.succ) (p.1, p.2 - 1))
  have s4 := dg_sign d hG1 hG3 (p.1, p.2 + 1) (Dh d (U n.succ) (p.1, p.2 + 1))
  have f1 := mul_nonpos_of_nonneg_of_nonpos (hnn n.castSucc (p.1 - 1, p.2)) s1.1
  have f2 := mul_nonneg (hnn n.castSucc (p.1 + 1, p.2)) s2.2.1
  have f3 := mul_nonpos_of_nonneg_of_nonpos (hnn n.castSucc (p.1, p.2 - 1)) s3.2.2.1
  have f4 := mul_nonneg (hnn n.castSucc (p.1, p.2 + 1)) s4.2.2.2
  have hB : 0 ≤ B d (U n.succ) m p := by
    unfold B
    dsimp only
    rw [h0]
    apply mul_nonneg (by positivity)
    simp only [zero_mul, zero_sub, sub_zero]
    linarith
  have hL : 0 ≤ lap d m p := by
    rw [hlap]
    have := hnn n.castSucc (p.1 + 1, p.2); have := hnn n.castSucc (p.1 - 1, p.2)
    have := hnn n.castSucc (p.1, p.2 + 1); have := hnn n.castSucc (p.1, p.2 - 1)
    apply mul_nonneg (by positivity)
    linarith
  have hT : 0 ≤ (Mt n.succ p - m p) / d.Δt := by
    rw [h0, sub_zero]; exact div_nonneg (hnn _ _) hdt.le
  have hνL : 0 ≤ d.ν * lap d m p := mul_nonneg d.hν hL
  have z1 : (Mt n.succ p - m p) / d.Δt = 0 := by linarith
  have z2 : d.ν * lap d m p = 0 := by linarith
  refine ⟨?_, fun hν => ?_⟩
  · rw [h0, sub_zero, div_eq_zero_iff] at z1
    exact z1.resolve_right hdt.ne'
  · have hl0 : lap d m p = 0 := (mul_eq_zero.mp z2).resolve_left hν.ne'
    rw [hlap] at hl0
    have hs : m (p.1 + 1, p.2) + m (p.1 - 1, p.2) + m (p.1, p.2 + 1) + m (p.1, p.2 - 1) = 0 :=
      (mul_eq_zero.mp hl0).resolve_left (by positivity)
    have := hnn n.castSucc (p.1 + 1, p.2); have := hnn n.castSucc (p.1 - 1, p.2)
    have := hnn n.castSucc (p.1, p.2 + 1); have := hnn n.castSucc (p.1, p.2 - 1)
    constructor <;> linarith

/-- the densities are positive before the final time. -/
theorem positivity_of_FP (hG1 : G1 d) (hG3 : G3 d) (Mt : Fin (d.NT + 1) → Pt d → ℝ)
    (U : Fin (d.NT + 1) → Pt d → ℝ) (hnn : ∀ j p, 0 ≤ Mt j p)
    (hFP : ∀ (n : Fin d.NT) (p : Pt d), (Mt n.succ p - Mt n.castSucc p) / d.Δt
      + d.ν * lap d (Mt n.castSucc) p + B d (U n.succ) (Mt n.castSucc) p = 0)
    (hlast : Mt (Fin.last d.NT) = d.mT) (hmT : InK d d.mT)
    (hν : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∀ (n : Fin d.NT) (p : Pt d), 0 < Mt n.castSucc p := by
  intro n p
  rcases (hnn n.castSucc p).lt_or_eq with h | h
  · exact h
  exfalso
  have step := zero_step d hG1 hG3 Mt U hnn hFP
  have cs : ∀ (j : ℕ) (hj : j < d.NT), (Fin.castSucc (⟨j, hj⟩ : Fin d.NT)) = ⟨j, by omega⟩ :=
    fun _ _ => rfl
  have sc : ∀ (j : ℕ) (hj : j < d.NT), (Fin.succ (⟨j, hj⟩ : Fin d.NT)) = ⟨j + 1, by omega⟩ :=
    fun _ _ => rfl
  rcases hν with hν | ⟨hν0, hmTp⟩
  · have hall : ∀ q, Mt n.castSucc q = 0 := by
      have hz1 : ∀ q, Mt n.castSucc q = 0 → Mt n.castSucc (q.1 + 1, q.2) = 0 :=
        fun q hq => ((step n q hq).2 hν).1
      have hz2 : ∀ q, Mt n.castSucc q = 0 → Mt n.castSucc (q.1, q.2 + 1) = 0 :=
        fun q hq => ((step n q hq).2 hν).2
      have r1 : ∀ k : ℕ, Mt n.castSucc (p.1 + k, p.2) = 0 := by
        intro k; induction k with
        | zero => simpa using h.symm
        | succ k ih => have := hz1 _ ih; simpa [add_assoc] using this
      have r2 : ∀ (k j : ℕ), Mt n.castSucc (p.1 + k, p.2 + j) = 0 := by
        intro k j; induction j with
        | zero => simpa using r1 k
        | succ j ih => have := hz2 _ ih; simpa [add_assoc] using this
      intro q
      have := r2 (q.1 - p.1).val (q.2 - p.2).val
      simpa [ZMod.natCast_zmod_val] using this
    have prop : ∀ j : ℕ, (n : ℕ) ≤ j → ∀ (hj : j < d.NT + 1) q, Mt ⟨j, hj⟩ q = 0 := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro hj q; exact hall q
      | succ j hnj ih =>
        intro hj q
        have hjl : j < d.NT := by omega
        have := (step ⟨j, hjl⟩ q (by rw [cs]; exact ih (by omega) q)).1
        rwa [sc] at this
    have hT := prop d.NT (by omega) (by omega)
    have e : (⟨d.NT, by omega⟩ : Fin (d.NT + 1)) = Fin.last d.NT := rfl
    have hz : ∀ q, d.mT q = 0 := fun q => by rw [← hlast, ← e]; exact hT q
    have := hmT.1
    simp [hz] at this
  · have prop : ∀ j : ℕ, (n : ℕ) ≤ j → ∀ (hj : j < d.NT + 1), Mt ⟨j, hj⟩ p = 0 := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro hj; exact h.symm
      | succ j hnj ih =>
        intro hj
        have hjl : j < d.NT := by omega
        have := (step ⟨j, hjl⟩ p (by rw [cs]; exact ih (by omega))).1
        rwa [sc] at this
    have hT := prop d.NT (by omega) (by omega)
    have e : (⟨d.NT, by omega⟩ : Fin (d.NT + 1)) = Fin.last d.NT := rfl
    rw [e, hlast] at hT
    exact absurd hT (hmTp p).ne'

lemma cyc_const (N : ℕ) [NeZero N] (w : ZMod N → ℝ) (hw : ∀ x, w (x + 1) = w x) :
    ∀ x, w x = w 0 := by
  have : ∀ k : ℕ, w (k : ZMod N) = w 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, hw, ih]
  intro x
  rw [← ZMod.natCast_zmod_val x]
  exact this _

lemma torus_const (U : Pt d → ℝ) (h1 : ∀ p : Pt d, U (p.1 + 1, p.2) = U p)
    (h2 : ∀ p : Pt d, U (p.1, p.2 + 1) = U p) : ∀ p, U p = U (0, 0) := by
  intro p
  have a := cyc_const d.Nh (fun i => U (i, p.2)) (fun i => h1 (i, p.2)) p.1
  have b := cyc_const d.Nh (fun j => U (0, j)) (fun j => h2 (0, j)) p.2
  rw [a, b]

/-! ### New lemmas for the uniqueness argument -/

lemma lap_sub (A C : Pt d → ℝ) (p : Pt d) :
    lap d (fun q => A q - C q) p = lap d A p - lap d C p := by
  unfold lap; ring

lemma Dh_sub (A C : Pt d → ℝ) (p : Pt d) (l : Fin 4) :
    Dh d (fun q => A q - C q) p l = Dh d A p l - Dh d C p l := by
  fin_cases l <;> simp [Dh, D1, D2] <;> ring

lemma sumB (U M w : Pt d → ℝ) :
    ∑ p, B d U M p * w p = -∑ p, M p * ∑ l, dg d p (Dh d U p) l * Dh d w p l := by
  have h := sum_Z_Dh d (fun q l => M q * dg d q (Dh d U q) l) w
  calc ∑ p, B d U M p * w p
      = ∑ p, w p * divh d (fun q l => M q * dg d q (Dh d U q) l) p :=
        sum_congr rfl fun p _ => by rw [B_eq_divh]; ring
    _ = -∑ p, ∑ l, M p * dg d p (Dh d U p) l * Dh d w p l := by rw [h]; ring
    _ = -∑ p, M p * ∑ l, dg d p (Dh d U p) l * Dh d w p l := by
        congr 1
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun l _ => ?_
        ring

lemma fin_tele (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc, Fin.castSucc_zero] at this
    simp only [Fin.succ_castSucc, this, Fin.succ_last]
    ring

/-- the one-step Lasry–Lions energy identity. -/
lemma step_id (u0 u1 u0' u1' m0 m1 m0' m1' : Pt d → ℝ)
    (hH : ∀ p, (u1 p - u0 p) / d.Δt - d.ν * lap d u1 p + d.g p (Dh d u1 p) = d.V (m0 p))
    (hH' : ∀ p, (u1' p - u0' p) / d.Δt - d.ν * lap d u1' p + d.g p (Dh d u1' p) = d.V (m0' p))
    (hF : ∀ p, (m1 p - m0 p) / d.Δt + d.ν * lap d m0 p + B d u1 m0 p = 0)
    (hF' : ∀ p, (m1' p - m0' p) / d.Δt + d.ν * lap d m0' p + B d u1' m0' p = 0) :
    ∑ p, ((d.V (m0 p) - d.V (m0' p)) * (m0 p - m0' p)
      + (m0 p * (d.g p (Dh d u1' p) - d.g p (Dh d u1 p)
          - ∑ l, (Dh d u1' p l - Dh d u1 p l) * dg d p (Dh d u1 p) l)
        + m0' p * (d.g p (Dh d u1 p) - d.g p (Dh d u1' p)
          - ∑ l, (Dh d u1 p l - Dh d u1' p l) * dg d p (Dh d u1' p) l)))
    = ∑ p, ((u1 p - u1' p) * (m1 p - m1' p) - (u0 p - u0' p) * (m0 p - m0' p)) / d.Δt := by
  have eL := sum_mul_lap d (fun q => m0 q - m0' q) (fun q => u1 q - u1' q)
  simp only [lap_sub] at eL
  have eB1 := sumB d u1 m0 (fun q => u1 q - u1' q)
  have eB2 := sumB d u1' m0' (fun q => u1 q - u1' q)
  simp only [Dh_sub] at eB1 eB2
  have pt : ∀ p, ((d.V (m0 p) - d.V (m0' p)) * (m0 p - m0' p)
      + (m0 p * (d.g p (Dh d u1' p) - d.g p (Dh d u1 p)
          - ∑ l, (Dh d u1' p l - Dh d u1 p l) * dg d p (Dh d u1 p) l)
        + m0' p * (d.g p (Dh d u1 p) - d.g p (Dh d u1' p)
          - ∑ l, (Dh d u1 p l - Dh d u1' p l) * dg d p (Dh d u1' p) l)))
      - ((u1 p - u1' p) * (m1 p - m1' p) - (u0 p - u0' p) * (m0 p - m0' p)) / d.Δt
      = d.ν * ((u1 p - u1' p) * (lap d m0 p - lap d m0' p)
          - (m0 p - m0' p) * (lap d u1 p - lap d u1' p))
        + (B d u1 m0 p * (u1 p - u1' p) - B d u1' m0' p * (u1 p - u1' p))
        + (m0 p * ∑ l, dg d p (Dh d u1 p) l * (Dh d u1 p l - Dh d u1' p l)
          - m0' p * ∑ l, dg d p (Dh d u1' p) l * (Dh d u1 p l - Dh d u1' p l)) := by
    intro p
    rw [← hH p, ← hH' p]
    have b1 : B d u1 m0 p = -((m1 p - m0 p) / d.Δt + d.ν * lap d m0 p) := by linarith [hF p]
    have b2 : B d u1' m0' p = -((m1' p - m0' p) / d.Δt + d.ν * lap d m0' p) := by
      linarith [hF' p]
    rw [b1, b2]
    simp only [Fin.sum_univ_four]
    ring
  rw [← sub_eq_zero, ← sum_sub_distrib, sum_congr rfl (fun p _ => pt p)]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_sub_distrib,
    sum_sub_distrib, eB1, eB2]
  have eL' : ∑ p, (u1 p - u1' p) * (lap d m0 p - lap d m0' p)
      = ∑ p, (m0 p - m0' p) * (lap d u1 p - lap d u1' p) := eL.symm
  rw [eL', sub_self, mul_zero]
  ring

lemma V_strict (hW : HypW d) (x y : ℝ) (hxy : x ≠ y) : 0 < (d.V x - d.V y) * (x - y) := by
  have hm : StrictMonoOn (deriv d.W) Set.univ :=
    hW.2.1.strictMonoOn_deriv (fun z _ => (hW.1.differentiable (by norm_num)).differentiableAt)
  have hV : d.V = deriv d.W := rfl
  rw [hV]
  rcases lt_or_gt_of_ne hxy with h | h
  · have := hm (Set.mem_univ x) (Set.mem_univ y) h
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have := hm (Set.mem_univ y) (Set.mem_univ x) h
    exact mul_pos (by linarith) (by linarith)

lemma V_nonneg (hW : HypW d) (x y : ℝ) : 0 ≤ (d.V x - d.V y) * (x - y) := by
  by_cases h : x = y
  · subst h; simp
  · exact (V_strict d hW x y h).le

theorem main (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∀ U M U' M' : Fin (d.NT + 1) → Pt d → ℝ, IsPlanningSol d U M → IsPlanningSol d U' M' →
      M = M' ∧
        ((∀ p, StrictConvexOn ℝ Set.univ (d.g p)) → ∑ p, U 0 p = 0 → ∑ p, U' 0 p = 0 →
          U = U') := by
  intro U M U' M' hS hS'
  obtain ⟨hH, hF, hK, hT, h0⟩ := hS
  obtain ⟨hH', hF', hK', hT', h0'⟩ := hS'
  have hdt := dt_pos d
  have hdiff : ∀ p (q : Fin 4 → ℝ), DifferentiableAt ℝ (d.g p) q :=
    fun p q => ((hG3 p).differentiable (by norm_num)) q
  -- tangent gaps
  have tg : ∀ p (a b : Fin 4 → ℝ), 0 ≤ d.g p b - d.g p a - ∑ l, (b l - a l) * dg d p a l := by
    intro p a b
    have := tangent_le (d.g p) (hG4 p) a (hdiff p a) b
    unfold dg
    linarith
  -- the summand of the energy identity
  obtain ⟨vt, hvt⟩ : ∃ f : Fin d.NT → Pt d → ℝ, ∀ n p, f n p =
      (d.V (M n.castSucc p) - d.V (M' n.castSucc p)) * (M n.castSucc p - M' n.castSucc p) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨gp, hgp⟩ : ∃ f : Fin d.NT → Pt d → ℝ, ∀ n p, f n p =
      M n.castSucc p * (d.g p (Dh d (U' n.succ) p) - d.g p (Dh d (U n.succ) p)
          - ∑ l, (Dh d (U' n.succ) p l - Dh d (U n.succ) p l) * dg d p (Dh d (U n.succ) p) l)
        + M' n.castSucc p * (d.g p (Dh d (U n.succ) p) - d.g p (Dh d (U' n.succ) p)
          - ∑ l, (Dh d (U n.succ) p l - Dh d (U' n.succ) p l) * dg d p (Dh d (U' n.succ) p) l) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ f : Fin (d.NT + 1) → ℝ, ∀ k, f k =
      ∑ p, (U k p - U' k p) * (M k p - M' k p) := ⟨_, fun _ => rfl⟩
  have vt_nn : ∀ n p, 0 ≤ vt n p := fun n p => by rw [hvt]; exact V_nonneg d hW _ _
  have gp1_nn : ∀ (n : Fin d.NT) (p : Pt d), 0 ≤ M n.castSucc p * (d.g p (Dh d (U' n.succ) p) - d.g p (Dh d (U n.succ) p)
          - ∑ l, (Dh d (U' n.succ) p l - Dh d (U n.succ) p l) * dg d p (Dh d (U n.succ) p) l) :=
    fun n p => mul_nonneg ((hK _).2 p) (tg _ _ _)
  have gp2_nn : ∀ (n : Fin d.NT) (p : Pt d), 0 ≤ M' n.castSucc p * (d.g p (Dh d (U n.succ) p) - d.g p (Dh d (U' n.succ) p)
          - ∑ l, (Dh d (U n.succ) p l - Dh d (U' n.succ) p l) * dg d p (Dh d (U' n.succ) p) l) :=
    fun n p => mul_nonneg ((hK' _).2 p) (tg _ _ _)
  have gp_nn : ∀ n p, 0 ≤ gp n p := fun n p => by rw [hgp]; exact add_nonneg (gp1_nn n p) (gp2_nn n p)
  have step : ∀ n : Fin d.NT, ∑ p, (vt n p + gp n p) = (P n.succ - P n.castSucc) / d.Δt := by
    intro n
    have := step_id d (U n.castSucc) (U n.succ) (U' n.castSucc) (U' n.succ) (M n.castSucc)
      (M n.succ) (M' n.castSucc) (M' n.succ) (hH n) (hH' n) (hF n) (hF' n)
    rw [hP, hP, ← sum_sub_distrib, sum_div]
    rw [← this]
    refine sum_congr rfl fun p _ => ?_
    rw [hvt, hgp]
  have total : ∑ n : Fin d.NT, ∑ p, (vt n p + gp n p) = 0 := by
    rw [sum_congr rfl (fun n _ => step n), ← sum_div, fin_tele d.NT P, hP, hP, hT, hT', h0, h0']
    simp
  have each : ∀ n p, vt n p + gp n p = 0 := by
    intro n p
    have h1 := (sum_eq_zero_iff_of_nonneg (fun n _ => sum_nonneg
      (fun p _ => add_nonneg (vt_nn n p) (gp_nn n p)))).1 total n (mem_univ _)
    exact (sum_eq_zero_iff_of_nonneg (fun p _ => add_nonneg (vt_nn n p) (gp_nn n p))).1 h1 p
      (mem_univ _)
  have vt0 : ∀ n p, vt n p = 0 := fun n p => by
    have := each n p; have := vt_nn n p; have := gp_nn n p; linarith
  have gp0 : ∀ n p, gp n p = 0 := fun n p => by
    have := each n p; have := vt_nn n p; have := gp_nn n p; linarith
  have hMM : M = M' := by
    funext k p
    induction k using Fin.lastCases with
    | last => rw [hT, hT']
    | cast n =>
      by_contra hne
      have := V_strict d hW _ _ hne
      rw [← hvt, vt0] at this
      exact lt_irrefl _ this
  refine ⟨hMM, fun hsc hU0 hU0' => ?_⟩
  have hpos := positivity_of_FP d hG1 hG3 M U (fun j p => (hK j).2 p) hF hT hmT hνmT
  -- the discrete gradients agree after time 0
  have hDh : ∀ (n : Fin d.NT) p, Dh d (U' n.succ) p = Dh d (U n.succ) p := by
    intro n p
    have g1 := gp1_nn n p
    have g2 := gp2_nn n p
    have g0 := gp0 n p
    rw [hgp] at g0
    have z : M n.castSucc p * (d.g p (Dh d (U' n.succ) p) - d.g p (Dh d (U n.succ) p)
          - ∑ l, (Dh d (U' n.succ) p l - Dh d (U n.succ) p l) * dg d p (Dh d (U n.succ) p) l)
          = 0 := by linarith
    have z' := (mul_eq_zero.mp z).resolve_left (hpos n p).ne'
    apply tangent_eq (d.g p) (hsc p) _ (hdiff p _)
    unfold dg at z'
    linarith
  -- the difference at positive times is spatially constant and equal to the previous one
  obtain ⟨δ, hδ⟩ : ∃ f : Fin (d.NT + 1) → Pt d → ℝ, ∀ k p, f k p = U k p - U' k p :=
    ⟨_, fun _ _ => rfl⟩
  have hconst : ∀ (n : Fin d.NT) p, δ n.succ p = δ n.succ (0, 0) := by
    intro n
    have hz : ∀ p l, Dh d (fun q => U n.succ q - U' n.succ q) p l = 0 := by
      intro p l; rw [Dh_sub, hDh]; ring
    have hh := h_pos d
    apply torus_const d (δ n.succ)
    · intro p
      have := hz p 0
      rw [Dh0] at this
      unfold D1 at this
      rw [div_eq_zero_iff] at this
      rw [hδ, hδ]; linarith [this.resolve_right hh.ne']
    · intro p
      have := hz p 2
      rw [Dh2] at this
      unfold D2 at this
      rw [div_eq_zero_iff] at this
      rw [hδ, hδ]; linarith [this.resolve_right hh.ne']
  have hstep : ∀ (n : Fin d.NT) p, δ n.castSucc p = δ n.succ p := by
    intro n p
    have e1 := hH n p
    have e2 := hH' n p
    rw [hMM] at e1
    rw [← hDh n p] at e1
    have hl : lap d (U n.succ) p = lap d (U' n.succ) p := by
      have c := hconst n
      have : lap d (fun q => U n.succ q - U' n.succ q) p = 0 := by
        unfold lap; beta_reduce
        have c1 := c (p.1 + 1, p.2); have c2 := c (p.1 - 1, p.2)
        have c3 := c (p.1, p.2 + 1); have c4 := c (p.1, p.2 - 1); have c5 := c p
        simp only [hδ] at c1 c2 c3 c4 c5
        rw [c1, c2, c3, c4, c5]; ring
      rw [lap_sub] at this; linarith
    rw [hl] at e1
    have e3 : (U n.succ p - U n.castSucc p) / d.Δt = (U' n.succ p - U' n.castSucc p) / d.Δt := by
      linarith
    rw [div_left_inj' hdt.ne'] at e3
    rw [hδ, hδ]; linarith
  have hall : ∀ (k : ℕ) (hk : k < d.NT + 1) p, δ ⟨k, hk⟩ p = δ 0 p := by
    intro k
    induction k with
    | zero => intro hk p; rfl
    | succ k ih =>
      intro hk p
      have hkl : k < d.NT := by omega
      have := hstep ⟨k, hkl⟩ p
      have e1 : (Fin.castSucc (⟨k, hkl⟩ : Fin d.NT)) = ⟨k, by omega⟩ := rfl
      have e2 : (Fin.succ (⟨k, hkl⟩ : Fin d.NT)) = ⟨k + 1, hk⟩ := rfl
      rw [e1, e2] at this
      rw [← this, ih]
  have h0c : ∀ p, δ 0 p = δ 0 (0, 0) := by
    intro p
    have e1 : (Fin.castSucc (⟨0, d.hNT⟩ : Fin d.NT)) = 0 := by ext; simp
    have a1 := hstep ⟨0, d.hNT⟩ p
    have a2 := hstep ⟨0, d.hNT⟩ (0, 0)
    have a3 := hconst ⟨0, d.hNT⟩ p
    rw [e1] at a1 a2
    rw [a1, a2, a3]
  have hsum : ∑ p, δ 0 p = 0 := by
    simp only [hδ, sum_sub_distrib, hU0, hU0', sub_zero]
  have hc : δ 0 (0, 0) = 0 := by
    rw [sum_congr rfl (fun p _ => h0c p), sum_const, card_univ, nsmul_eq_mul] at hsum
    have hcard : (0 : ℝ) < (Fintype.card (Pt d) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
    exact (mul_eq_zero.mp hsum).resolve_left hcard.ne'
  funext k p
  have := hall k.1 k.2 p
  rw [h0c, hc, hδ] at this
  have hk : (⟨k.1, k.2⟩ : Fin (d.NT + 1)) = k := rfl
  rw [hk] at this
  linarith

end P1U
end MFGPlanning.Penalized

open MFGPlanning.Penalized in
theorem solution (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∀ U M U' M' : Fin (d.NT + 1) → Pt d → ℝ, IsPlanningSol d U M → IsPlanningSol d U' M' →
      M = M' ∧
        ((∀ p, StrictConvexOn ℝ Set.univ (d.g p)) → ∑ p, U 0 p = 0 → ∑ p, U' 0 p = 0 →
          U = U') := by
  exact MFGPlanning.Penalized.P1U.main d hG1 hG3 hG4 hG5 hW hm0 hmT hm0pos hνmT
