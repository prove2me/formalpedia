-- Prove2me | solution 1 for KalaiKleitman92.Diameter.ball_radius_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:12:26.789553+00:00
-- url     : https://prove2.me/submissions/820c3802-7476-4f51-98b9-f06a7ec1986b

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_relaxation_vertex
import Theorems.Thm_Hirsch_relaxation_no_new_neighbours

namespace Aux_KK92_ball_radius_le

open scoped RealInnerProductSpace
open Hirsch

abbrev Walk {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (L : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w L = v ∧ ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))

lemma walk_zero {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (u : E) : Walk P 0 u u :=
  ⟨fun _ => u, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

lemma walk_succ {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (L : ℕ) (u v : E)
    (h : Walk P L u v) : Walk P (L + 1) u v := by
  classical
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun j => if j ≤ L then w j else v, by simpa using h0, by simp, ?_⟩
  intro j hj
  rcases lt_or_ge j L with h1 | h1
  · have hj1 : j + 1 ≤ L := h1
    simp only [if_pos h1.le, if_pos hj1]
    exact hstep j h1
  · have hjL : j = L := by omega
    subst hjL
    left
    simp [hL]

lemma walk_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {L L' : ℕ}
    (hLL : L ≤ L') {u v : E} (h : Walk P L u v) : Walk P L' u v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hLL
  clear hLL
  induction m with
  | zero => simpa using h
  | succ m ih => exact (Nat.add_succ L m) ▸ walk_succ P _ u v ih

lemma walk_one_of_adj {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {u v : E}
    (h : Adj P u v) : Walk P 1 u v := by
  classical
  refine ⟨fun j => if j = 0 then u else v, by simp, by simp, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  exact Or.inr (by simpa using h)

lemma walk_trans {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {L₁ L₂ : ℕ} {u x v : E}
    (h₁ : Walk P L₁ u x) (h₂ : Walk P L₂ x v) : Walk P (L₁ + L₂) u v := by
  classical
  obtain ⟨w₁, a1, b1, s1⟩ := h₁
  obtain ⟨w₂, a2, b2, s2⟩ := h₂
  refine ⟨fun j => if j ≤ L₁ then w₁ j else w₂ (j - L₁), by simpa using a1, ?_, ?_⟩
  · dsimp only
    by_cases hc : L₁ + L₂ ≤ L₁
    · have hz : L₂ = 0 := by omega
      subst hz
      rw [if_pos hc]
      simpa using b1.trans (by rw [← a2, ← b2])
    · rw [if_neg hc]
      have : L₁ + L₂ - L₁ = L₂ := by omega
      rw [this]
      exact b2
  · intro j hj
    dsimp only
    by_cases hc : j ≤ L₁
    · by_cases hc1 : j + 1 ≤ L₁
      · rw [if_pos hc, if_pos hc1]
        exact s1 j (by omega)
      · have hjL : j = L₁ := by omega
        subst hjL
        rw [if_pos hc, if_neg hc1]
        have : j + 1 - j = 1 := by omega
        rw [this, b1, ← a2]
        exact s2 0 (by omega)
    · rw [if_neg hc, if_neg (by omega : ¬(j + 1 ≤ L₁))]
      have : j + 1 - L₁ = (j - L₁) + 1 := by omega
      rw [this]
      exact s2 _ (by omega)

lemma adj_right_mem_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E}
    {a b : E} (h : Adj P a b) : b ∈ Set.extremePoints ℝ P := by
  have hb : b ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    refine ⟨right_mem_segment ℝ a b, ?_⟩
    rintro x hx y hy ⟨p, q, hp, hq, hpq, hxy⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h.1)
    rw [segment_eq_image'] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hb' : b = a + (1 : ℝ) • (b - a) := by module
    have hcomb : p • (a + s • (b - a)) + q • (a + t • (b - a))
        = a + (p * s + q * t) • (b - a) := by
      calc p • (a + s • (b - a)) + q • (a + t • (b - a))
          = (p + q) • a + (p * s + q * t) • (b - a) := by module
        _ = a + (p * s + q * t) • (b - a) := by rw [hpq]; module
    have hb2 : a + (p * s + q * t) • (b - a) = b := by rw [← hcomb]; exact hxy
    have hco : p * s + q * t = 1 := by
      have h3 : ((p * s + q * t) - 1) • (b - a) = 0 := by
        have e1 : ((p * s + q * t) - 1) • (b - a)
            = (a + (p * s + q * t) • (b - a)) - (a + (1 : ℝ) • (b - a)) := by module
        rw [e1, hb2, ← hb', sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith [sub_eq_zero.mp h4]
      · exact absurd h4 hba
    have hs1 : s = 1 := by
      nlinarith [hs.1, hs.2, ht.1, ht.2]
    rw [hs1]
    module
  have hex := h.2.extremePoints_eq (𝕜 := ℝ)
  rw [hex] at hb
  exact hb.2

lemma hpoly_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy s t hs ht hst i
  have h1 := hx i
  have h2 := hy i
  have hexp : ⟪a i, s • x + t • y⟫ = s * ⟪a i, x⟫ + t * ⟪a i, y⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hexp]
  have e1 : s * ⟪a i, x⟫ ≤ s * b i := mul_le_mul_of_nonneg_left h1 hs
  have e2 : t * ⟪a i, y⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht
  have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

lemma subset_relax {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) :
    Hpoly a b ⊆ Hpoly (fun i => if i ∈ F then a i else 0) (fun i => if i ∈ F then b i else 1) := by
  intro x hx i
  by_cases hi : i ∈ F
  · simpa [hi] using hx i
  · simp [hi]

lemma isExtreme_inter {E : Type*} [AddCommGroup E] [Module ℝ E] {Q T S : Set E}
    (h : IsExtreme ℝ Q T) (hSQ : S ⊆ Q) : IsExtreme ℝ S (S ∩ T) := by
  constructor
  · exact Set.inter_subset_left
  · intro x1 h1 x2 h2 z hz hsg
    exact ⟨h1, h.2 (hSQ h1) (hSQ h2) hz.2 hsg⟩

lemma adj_of_relax_adj {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) {x y : EuclideanSpace ℝ (Fin d)} (hxP : x ∈ Hpoly a b)
    (hyP : y ∈ Hpoly a b)
    (hadj : Adj (Hpoly (fun i => if i ∈ F then a i else 0) (fun i => if i ∈ F then b i else 1)) x y) :
    Adj (Hpoly a b) x y := by
  refine ⟨hadj.1, ?_⟩
  have h := isExtreme_inter hadj.2 (subset_relax a b F)
  have heq : Hpoly a b ∩ segment ℝ x y = segment ℝ x y :=
    Set.inter_eq_right.mpr ((hpoly_convex a b).segment_subset hxP hyP)
  rwa [heq] at h

end Aux_KK92_ball_radius_le

open scoped RealInnerProductSpace
open Hirsch Aux_KK92_ball_radius_le

theorem solution (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) (k B : ℕ) (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hball : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = v ∧ w k = x ∧
        ∀ j < k, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) →
      ∀ i, ⟪a i, x⟫ = b i → i ∈ F)
    (hQ : DiamLE (Hpoly (fun i => if i ∈ F then a i else 0)
      (fun i => if i ∈ F then b i else 1)) B)
    (ω : EuclideanSpace ℝ (Fin d)) (hω : ω ∈ Set.extremePoints ℝ (Hpoly a b))
    (hωk : ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = v ∧ w k = ω ∧
      ∀ j < k, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = v ∧ w B = ω ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  rcases le_or_gt k B with hkB | hBk
  · exact walk_mono (Hpoly a b) hkB hωk
  · set Q : Set (EuclideanSpace ℝ (Fin d)) :=
      Hpoly (fun i => if i ∈ F then a i else 0) (fun i => if i ∈ F then b i else 1) with hQdef
    have hPQ : Hpoly a b ⊆ Q := subset_relax a b F
    have hQF : ∀ z ∈ Q, ∀ j ∈ F, ⟪a j, z⟫ ≤ b j := by
      intro z hz j hj
      have hzj := hz j
      simpa [hQdef, hj] using hzj
    have hv_walk : Walk (Hpoly a b) k v v := walk_mono (Hpoly a b) (Nat.zero_le k) (walk_zero _ v)
    have hvQ : v ∈ Set.extremePoints ℝ Q :=
      Hirsch.relaxation_vertex d n a b F Q hQF v hv (hPQ hv.1) (hball v hv hv_walk)
    have hωQ : ω ∈ Set.extremePoints ℝ Q :=
      Hirsch.relaxation_vertex d n a b F Q hQF ω hω (hPQ hω.1) (hball ω hω hωk)
    obtain ⟨w, hw0, hwB, hwstep⟩ := hQ v hvQ ω hωQ
    have key : ∀ j ≤ B, Walk (Hpoly a b) j v (w j) ∧ w j ∈ Set.extremePoints ℝ (Hpoly a b) := by
      intro j
      induction j with
      | zero =>
          intro _
          exact ⟨by rw [hw0]; exact walk_zero _ v, by rw [hw0]; exact hv⟩
      | succ j ih =>
          intro hjB
          obtain ⟨hrj, hvj⟩ := ih (by omega)
          have hFj : ∀ i, ⟪a i, w j⟫ = b i → i ∈ F :=
            hball (w j) hvj (walk_mono (Hpoly a b) (by omega : j ≤ k) hrj)
          rcases hwstep j (by omega) with heq | hadjQ
          · exact ⟨by rw [← heq]; exact walk_succ _ _ _ _ hrj, by rw [← heq]; exact hvj⟩
          · have hwj1P : w (j + 1) ∈ Hpoly a b := by
              refine Hirsch.relaxation_no_new_neighbours d n a b F (w j) (w (j + 1)) hvj hFj hadjQ ?_
              intro u hu
              have hu_ext : u ∈ Set.extremePoints ℝ (Hpoly a b) := adj_right_mem_extremePoints hu
              have hu_walk : Walk (Hpoly a b) k v u :=
                walk_mono (Hpoly a b) (by omega : j + 1 ≤ k)
                  (walk_trans (Hpoly a b) hrj (walk_one_of_adj (Hpoly a b) hu))
              exact hball u hu_ext hu_walk
            have hadjP : Adj (Hpoly a b) (w j) (w (j + 1)) :=
              adj_of_relax_adj a b F hvj.1 hwj1P hadjQ
            exact ⟨walk_trans (Hpoly a b) hrj (walk_one_of_adj (Hpoly a b) hadjP),
              adj_right_mem_extremePoints hadjP⟩
    have hfin := (key B (le_refl B)).1
    rwa [hwB] at hfin
