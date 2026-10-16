-- Prove2me | solution 1 for LogBarrierIPM.Iterations.theorem_30
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T15:13:09.408194+00:00
-- url     : https://prove2.me/submissions/36238e26-4783-45b8-8725-d84e6a38b75f

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_SlackLP
import Definitions.Def_LogBarrierIPM_Iterations_LW
import Definitions.Def_LogBarrierIPM_Iterations_TropicalLW

set_option autoImplicit false
open Matrix


namespace K3

/-- A function affine on the cell `[i, i+1]` (from the interpolation hypothesis). -/
lemma aff (G : ℝ → ℝ) (i : ℕ)
    (h : ∀ a ∈ Set.Icc (0 : ℝ) 1, G (i + a) = (1 - a) * G i + a * G (i + 1)) :
    ∃ α β : ℝ, ∀ x ∈ Set.Icc (i : ℝ) (i + 1), G x = α + β * x := by
  refine ⟨G i - (G (i + 1) - G i) * i, G (i + 1) - G i, ?_⟩
  intro x hx
  have h1 := h (x - i) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have : (i : ℝ) + (x - i) = x := by ring
  rw [this] at h1
  rw [h1]; ring

lemma three (α β x y z : ℝ) (hxy : x < y) (hyz : y < z)
    (h1 : (α + β * x) * (α + β * y) < 0) (h2 : (α + β * y) * (α + β * z) < 0) : False := by
  rcases le_or_gt 0 β with hβ | hβ
  · have a1 : α + β * x ≤ α + β * y := by nlinarith
    have a2 : α + β * y ≤ α + β * z := by nlinarith
    rcases lt_or_gt_of_ne (show α + β * y ≠ 0 by
      intro h; rw [h] at h1; simp at h1) with hy | hy
    · -- y negative: then x negative too, product positive
      nlinarith
    · nlinarith
  · have a1 : α + β * y ≤ α + β * x := by nlinarith
    have a2 : α + β * z ≤ α + β * y := by nlinarith
    rcases lt_or_gt_of_ne (show α + β * y ≠ 0 by
      intro h; rw [h] at h1; simp at h1) with hy | hy
    · nlinarith
    · nlinarith

lemma left (α β w x y : ℝ) (hwx : w ≤ x) (hxy : x < y)
    (h : (α + β * x) * (α + β * y) < 0) : 0 < (α + β * w) * (α + β * x) := by
  rcases le_or_gt 0 β with hβ | hβ
  · have a1 : α + β * x ≤ α + β * y := by nlinarith
    have a2 : α + β * w ≤ α + β * x := by nlinarith
    have hx : α + β * x < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith
  · have a1 : α + β * y ≤ α + β * x := by nlinarith
    have a2 : α + β * x ≤ α + β * w := by nlinarith
    have hx : 0 < α + β * x := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith

lemma mono_of_step (m : ℕ) (s : ℕ → ℝ) (hs : ∀ k, k < m → s k < s (k + 1)) :
    ∀ a b, a < b → b ≤ m → s a < s b := by
  intro a b hab hb
  induction b, hab using Nat.le_induction with
  | base => exact hs a (by omega)
  | succ b hb' ih => exact lt_trans (ih (by omega)) (hs b (by omega))

lemma aux (p : ℕ) : ∀ (G : ℝ → ℝ),
    (∀ i : ℕ, i < p → ∀ a ∈ Set.Icc (0 : ℝ) 1, G (i + a) = (1 - a) * G i + a * G (i + 1)) →
    ∀ (m : ℕ) (s : ℕ → ℝ), (∀ k, k ≤ m → 0 ≤ s k ∧ s k ≤ p) →
      (∀ k, k < m → s k < s (k + 1)) → (∀ k, k < m → G (s k) * G (s (k + 1)) < 0) → m ≤ p := by
  induction p with
  | zero =>
    intro G _ m s hb hs _
    by_contra hm
    have h0 := hb 0 (by omega)
    have h1 := hb 1 (by omega)
    have := hs 0 (by omega)
    simp at h0 h1
    linarith [h0.1, h0.2, h1.1, h1.2]
  | succ p ih =>
    intro G hG m s hb hs hprod
    have hmono := mono_of_step m s hs
    by_cases hall : ∀ k, k ≤ m → s k ≤ p
    · have := ih G (fun i hi => hG i (by omega)) m s (fun k hk => ⟨(hb k hk).1, hall k hk⟩) hs hprod
      omega
    · push_neg at hall
      classical
      have hex : ∃ k, k ≤ m ∧ (p : ℝ) < s k := hall
      obtain ⟨ks, hks, hlt⟩ : ∃ ks, (ks ≤ m ∧ (p : ℝ) < s ks) ∧ ∀ k, k < ks → s k ≤ p := by
        refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
        intro k hk
        have := Nat.find_min hex hk
        push_neg at this
        exact this (by have := (Nat.find_spec hex).1; omega)
      -- the affine cell [p, p+1]
      obtain ⟨α, β, hab⟩ := aff G p (hG p (by omega))
      have hcell : ∀ k, ks ≤ k → k ≤ m → (p : ℝ) ≤ s k ∧ s k ≤ p + 1 := by
        intro k hk1 hk2
        have h1 : s ks ≤ s k := by
          rcases eq_or_lt_of_le hk1 with h | h
          · rw [h]
          · exact le_of_lt (hmono ks k h hk2)
        have h2 := (hb k hk2).2
        push_cast at h2
        exact ⟨by linarith [hks.2], h2⟩
      have hm : m ≤ ks + 1 := by
        by_contra hcon
        have c0 := hcell ks le_rfl hks.1
        have c1 := hcell (ks + 1) (by omega) (by omega)
        have c2 := hcell (ks + 2) (by omega) (by omega)
        have e0 := hab _ ⟨c0.1, c0.2⟩
        have e1 := hab _ ⟨c1.1, c1.2⟩
        have e2 := hab _ ⟨c2.1, c2.2⟩
        have p0 := hprod ks (by omega)
        have p1 := hprod (ks + 1) (by omega)
        rw [e0, e1] at p0
        rw [e1] at p1
        rw [e2] at p1
        exact three α β _ _ _ (hs ks (by omega)) (hs (ks + 1) (by omega)) p0 p1
      rcases Nat.lt_or_ge ks 1 with hk0 | hk1
      · -- ks = 0: m ≤ 1
        omega
      · rcases (show m = ks ∨ m = ks + 1 by omega) with hmk | hmk
        · -- m = ks
          have := ih G (fun i hi => hG i (by omega)) (m - 1) s
            (fun k hk => ⟨(hb k (by omega)).1, hlt k (by omega)⟩)
            (fun k hk => hs k (by omega)) (fun k hk => hprod k (by omega))
          omega
        · -- m = ks + 1
          obtain ⟨j, hj⟩ : ∃ j, ks = j + 1 := ⟨ks - 1, by omega⟩
          have hsj : s j ≤ p := hlt j (by omega)
          have c0 := hcell ks le_rfl hks.1
          have c1 := hcell (ks + 1) (by omega) (by omega)
          have e0 := hab _ ⟨c0.1, c0.2⟩
          have e1 := hab _ ⟨c1.1, c1.2⟩
          have p1 := hprod ks (by omega)
          rw [e0, e1] at p1
          have hpj : s j < p := by
            rcases eq_or_lt_of_le hsj with h | h
            · exfalso
              have ej := hab (s j) ⟨by rw [h], by rw [h]; linarith⟩
              have p0 : G (s j) * G (s ks) < 0 := by
                have := hprod j (by omega)
                rwa [← hj] at this
              rw [ej, e0] at p0
              exact three α β (s j) (s ks) (s (ks + 1)) (hmono j ks (by omega) hks.1)
                (hs ks (by omega)) p0 p1
            · exact h
          have hGp : 0 < G p * G (s ks) := by
            have ep := hab (p : ℝ) ⟨le_rfl, by linarith⟩
            rw [ep, e0]
            exact left α β _ _ _ c0.1 (hs ks (by omega)) p1
          let s' : ℕ → ℝ := fun k => if k = ks then (p : ℝ) else s k
          have hprodj : G (s j) * G (s ks) < 0 := by
            have := hprod j (by omega)
            rwa [← hj] at this
          have hprod' : G (s j) * G p < 0 := by
            by_contra hcon
            push_neg at hcon
            have : 0 ≤ (G (s j) * G p) * (G (s ks)) ^ 2 := by positivity
            nlinarith [sq_nonneg (G (s ks))]
          have := ih G (fun i hi => hG i (by omega)) ks s'
            (by
              intro k hk
              by_cases hkk : k = ks
              · simp [s', hkk]
              · have hk' : k < ks := by omega
                simp [s', hkk]
                exact ⟨(hb k (by omega)).1, hlt k hk'⟩)
            (by
              intro k hk
              by_cases hkk : k + 1 = ks
              · have hkj : k = j := by omega
                subst hkj
                simp [s', hkk]
                have : k ≠ ks := by omega
                simp [this]
                exact hpj
              · have : k ≠ ks := by omega
                simp [s', hkk, this]
                exact hs k (by omega))
            (by
              intro k hk
              by_cases hkk : k + 1 = ks
              · have hkj : k = j := by omega
                subst hkj
                simp [s', hkk]
                have : k ≠ ks := by omega
                simp [this]
                exact hprod'
              · have : k ≠ ks := by omega
                simp [s', hkk, this]
                exact hprod k (by omega))
          omega

theorem alternations_le_pieces (p m : ℕ) (G : ℝ → ℝ)
    (hG : ∀ i : ℕ, i < p → ∀ a ∈ Set.Icc (0 : ℝ) 1,
      G (i + a) = (1 - a) * G i + a * G (i + 1))
    (s : Fin (m + 1) → ℝ) (hs : StrictMono s) (hs0 : ∀ k, 0 ≤ s k) (hsp : ∀ k, s k ≤ p)
    (halt : ∀ k : Fin m, G (s k.castSucc) * G (s k.succ) < 0) :
    m ≤ p := by
  classical
  let s' : ℕ → ℝ := fun k => if h : k < m + 1 then s ⟨k, h⟩ else 0
  refine aux p G hG m s' ?_ ?_ ?_
  · intro k hk
    have : k < m + 1 := by omega
    simp only [s', this, dif_pos]
    exact ⟨hs0 _, hsp _⟩
  · intro k hk
    have h1 : k < m + 1 := by omega
    have h2 : k + 1 < m + 1 := by omega
    simp only [s', h1, h2, dif_pos]
    exact hs (by simp [Fin.lt_def])
  · intro k hk
    have h1 : k < m + 1 := by omega
    have h2 : k + 1 < m + 1 := by omega
    simp only [s', h1, h2, dif_pos]
    exact halt ⟨k, hk⟩

end K3

namespace T30

section Poly
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- Piecewise-linear interpolation of `z 0, …, z p` (hat-function sum). -/
noncomputable def poly (p : ℕ) (z : Fin (p + 1) → E) (s : ℝ) : E :=
  ∑ i : Fin (p + 1), max 0 (1 - |s - ((i : ℕ) : ℝ)|) • z i

lemma poly_cont (p : ℕ) (z : Fin (p + 1) → E) : Continuous (poly p z) := by
  unfold poly
  refine continuous_finsetSum _ fun i _ => ?_
  exact (by fun_prop : Continuous fun s : ℝ => max 0 (1 - |s - ((i : ℕ) : ℝ)|)).smul continuous_const

lemma poly_cell (p : ℕ) (z : Fin (p + 1) → E) (j : Fin p) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    poly p z (((j : ℕ) : ℝ) + a) = (1 - a) • z j.castSucc + a • z j.succ := by
  unfold poly
  have hne : j.castSucc ≠ j.succ := by simp [Fin.ext_iff]
  rw [← Finset.sum_subset (Finset.subset_univ {j.castSucc, j.succ})]
  · rw [Finset.sum_pair hne]
    have e1 : max 0 (1 - |((j : ℕ) : ℝ) + a - (((j.castSucc : Fin (p + 1)) : ℕ) : ℝ)|) = 1 - a := by
      simp only [Fin.val_castSucc]
      rw [show ((j : ℕ) : ℝ) + a - ((j : ℕ) : ℝ) = a by ring, abs_of_nonneg ha.1]
      exact max_eq_right (by linarith [ha.2])
    have e2 : max 0 (1 - |((j : ℕ) : ℝ) + a - (((j.succ : Fin (p + 1)) : ℕ) : ℝ)|) = a := by
      simp only [Fin.val_succ]
      push_cast
      rw [show ((j : ℕ) : ℝ) + a - (((j : ℕ) : ℝ) + 1) = -(1 - a) by ring, abs_neg,
        abs_of_nonneg (by linarith [ha.2])]
      rw [max_eq_right (by linarith [ha.1])]; ring
    rw [e1, e2]
  · intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have h1 : (i : ℕ) ≠ j := fun h => hi.1 (Fin.ext (by simpa using h))
    have h2 : (i : ℕ) ≠ j + 1 := fun h => hi.2 (Fin.ext (by simpa using h))
    have : 1 ≤ |((j : ℕ) : ℝ) + a - ((i : ℕ) : ℝ)| := by
      rcases Nat.lt_or_gt_of_ne h1 with h | h
      · have : (i : ℕ) + 1 ≤ j := h
        have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast this
        rw [abs_of_nonneg (by linarith [ha.1])]; linarith [ha.1]
      · have : (j : ℕ) + 2 ≤ i := by omega
        have : ((j : ℕ) : ℝ) + 2 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast this
        rw [abs_of_nonpos (by linarith [ha.2])]; linarith [ha.2]
    rw [max_eq_left (by linarith)]
    simp

lemma exists_cell (p : ℕ) (hp : 1 ≤ p) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) p) :
    ∃ j : Fin p, ∃ a ∈ Set.Icc (0 : ℝ) 1, s = ((j : ℕ) : ℝ) + a := by
  refine ⟨⟨min ⌊s⌋₊ (p - 1), by omega⟩, s - (min ⌊s⌋₊ (p - 1) : ℕ), ⟨?_, ?_⟩, by simp⟩
  · have : ((min ⌊s⌋₊ (p - 1) : ℕ) : ℝ) ≤ s :=
      le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le hs.1)
    linarith
  · rcases le_total ⌊s⌋₊ (p - 1) with h | h
    · rw [min_eq_left h]
      have := Nat.lt_floor_add_one s
      linarith
    · rw [min_eq_right h]
      have : ((p - 1 : ℕ) : ℝ) + 1 = p := by
        rw [Nat.cast_sub hp]; push_cast; ring
      linarith [hs.2]

end Poly

end T30

namespace LogBarrierIPM.Iterations

/-- Duality identity: `x·s + w·y = c·x + b·y` on primal-dual feasible points. -/
lemma duality_identity {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : PDPoint n m) (h1 : A *ᵥ z.1 + z.2.1 = b) (h2 : z.2.2.1 - Aᵀ *ᵥ z.2.2.2 = c) :
    z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2 = c ⬝ᵥ z.1 + b ⬝ᵥ z.2.2.2 := by
  have hs : z.2.2.1 = c + Aᵀ *ᵥ z.2.2.2 := by rw [← h2]; abel
  have hw : z.2.1 = b - A *ᵥ z.1 := by rw [← h1]; abel
  rw [hs, hw, dotProduct_add, sub_dotProduct, dotProduct_comm z.1 c, dotProduct_mulVec,
    vecMul_transpose]
  ring

/-- Indicator sum with three distinct nonzero entries. -/
lemma sum_ind3 (n : ℕ) (f : Fin n → ℝ) (a b c : ℕ) (ha : a < n) (hb : b < n) (hc : c < n)
    (u v w : ℝ) :
    ∑ k : Fin n, ((if k.val = a then u else 0) + (if k.val = b then v else 0) +
        (if k.val = c then w else 0)) * f k =
      u * f ⟨a, ha⟩ + v * f ⟨b, hb⟩ + w * f ⟨c, hc⟩ := by
  have e : ∀ (d : ℕ) (hd : d < n) (k : Fin n), (k.val = d) ↔ (k = ⟨d, hd⟩) := by
    intro d hd k; simp [Fin.ext_iff]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [e a ha, e b hb, e c hc, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma lw_rowsum (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (i : Fin (3 * r - 1)) :
    (lwA r t *ᵥ x) i = ∑ k : Fin (2 * r), lwEntry t (i.val + 1) (k.val + 1) * x k := by
  simp [lwA, mulVec, dotProduct]

lemma lw_row_a (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    (lwA r t *ᵥ x) ⟨3 * j - 1, by omega⟩ =
      x ⟨2 * j, by omega⟩ - t * x ⟨2 * j - 2, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (3 * j - 1 + 1) (k.val + 1) =
      (if k.val = 2 * j then 1 else 0) + (if k.val = 2 * j - 2 then -t else 0) +
        (if k.val = 0 then 0 else 0) := by
    intro k
    have h3 : 3 * j - 1 + 1 = 3 * j := by omega
    have hd : 3 * j / 3 = j := by omega
    have hm : 3 * j % 3 = 0 := by omega
    simp only [lwEntry, h3, hd, hm]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x (2 * j) (2 * j - 2) 0 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_b (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    (lwA r t *ᵥ x) ⟨3 * j, by omega⟩ =
      x ⟨2 * j, by omega⟩ - t * x ⟨2 * j - 1, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (3 * j + 1) (k.val + 1) =
      (if k.val = 2 * j then 1 else 0) + (if k.val = 2 * j - 1 then -t else 0) +
        (if k.val = 0 then 0 else 0) := by
    intro k
    have hd : (3 * j + 1) / 3 = j := by omega
    have hm : (3 * j + 1) % 3 = 1 := by omega
    simp only [lwEntry, hd, hm]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x (2 * j) (2 * j - 1) 0 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_c (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    (lwA r t *ᵥ x) ⟨3 * j + 1, by omega⟩ =
      x ⟨2 * j + 1, by omega⟩ - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨2 * j - 2, by omega⟩
        - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨2 * j - 1, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (3 * j + 1 + 1) (k.val + 1) =
      (if k.val = 2 * j + 1 then 1 else 0) +
        (if k.val = 2 * j - 2 then -(t ^ ((1 : ℝ) - 1 / 2 ^ j)) else 0) +
        (if k.val = 2 * j - 1 then -(t ^ ((1 : ℝ) - 1 / 2 ^ j)) else 0) := by
    intro k
    have hd : (3 * j + 1 + 1) / 3 = j := by omega
    have hm : (3 * j + 1 + 1) % 3 = 2 := by omega
    simp only [lwEntry, hd, hm]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x (2 * j + 1) (2 * j - 2) (2 * j - 1) (by omega) (by omega) (by omega)]
  ring

lemma lw_row_0 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (x : Fin (2 * r) → ℝ) :
    (lwA r t *ᵥ x) ⟨0, by omega⟩ = x ⟨0, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (0 + 1) (k.val + 1) =
      (if k.val = 0 then 1 else 0) + (if k.val = 0 then 0 else 0) +
        (if k.val = 0 then 0 else 0) := by
    intro k
    simp only [lwEntry]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x 0 0 0 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_1 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (x : Fin (2 * r) → ℝ) :
    (lwA r t *ᵥ x) ⟨1, by omega⟩ = x ⟨1, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (1 + 1) (k.val + 1) =
      (if k.val = 1 then 1 else 0) + (if k.val = 1 then 0 else 0) +
        (if k.val = 1 then 0 else 0) := by
    intro k
    simp only [lwEntry]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x 1 1 1 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_a' (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j i p q : ℕ) (hj1 : 1 ≤ j) (hjr : j < r)
    (hi : i = 3 * j - 1) (hp : p = 2 * j) (hq : q = 2 * j - 2)
    (hi' : i < 3 * r - 1) (hp' : p < 2 * r) (hq' : q < 2 * r) :
    (lwA r t *ᵥ x) ⟨i, hi'⟩ = x ⟨p, hp'⟩ - t * x ⟨q, hq'⟩ := by
  subst hi hp hq; exact lw_row_a r t x j hj1 hjr

lemma lw_row_b' (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j i p q : ℕ) (hj1 : 1 ≤ j) (hjr : j < r)
    (hi : i = 3 * j) (hp : p = 2 * j) (hq : q = 2 * j - 1)
    (hi' : i < 3 * r - 1) (hp' : p < 2 * r) (hq' : q < 2 * r) :
    (lwA r t *ᵥ x) ⟨i, hi'⟩ = x ⟨p, hp'⟩ - t * x ⟨q, hq'⟩ := by
  subst hi hp hq; exact lw_row_b r t x j hj1 hjr

lemma lw_row_c' (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j i p q1 q2 : ℕ) (hj1 : 1 ≤ j) (hjr : j < r)
    (hi : i = 3 * j + 1) (hp : p = 2 * j + 1) (hq1 : q1 = 2 * j - 2) (hq2 : q2 = 2 * j - 1)
    (hi' : i < 3 * r - 1) (hp' : p < 2 * r) (hq1' : q1 < 2 * r) (hq2' : q2 < 2 * r) :
    (lwA r t *ᵥ x) ⟨i, hi'⟩ =
      x ⟨p, hp'⟩ - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨q1, hq1'⟩
        - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨q2, hq2'⟩ := by
  subst hi hp hq1 hq2; exact lw_row_c r t x j hj1 hjr


lemma xcongr {n : ℕ} (x : Fin n → ℝ) (a b : ℕ) (ha : a < n) (hb : b < n) (h : a = b) :
    x ⟨a, ha⟩ = x ⟨b, hb⟩ := by subst h; rfl

lemma lw_x0 (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) :
    z.1 ⟨0, by omega⟩ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z ∧
      z.1 ⟨0, by omega⟩ < t ^ 2 := by
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hN : (0 : ℝ) < ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 0 < 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  constructor
  · have hid := duality_identity _ _ _ z h1 h2
    have hmu : ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z =
        z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2 := by
      unfold dualityMeasure
      field_simp
    have hc : lwC r ⬝ᵥ z.1 = z.1 ⟨0, by omega⟩ := by
      simp only [dotProduct, lwC]
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro k _ hk
        have : k.val ≠ 0 := fun h => hk (Fin.ext h)
        simp [this]
      · simp
    have hb : 0 ≤ lwB r t ⬝ᵥ z.2.2.2 := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg _ (hy i).le
      unfold lwB
      split_ifs <;> positivity
    rw [hmu, hid, hc]
    linarith
  · have e := congrFun h1 ⟨0, by omega⟩
    rw [Pi.add_apply, lw_row_0 r t hr] at e
    simp only [lwB] at e
    simp at e
    have := hw ⟨0, by omega⟩
    linarith

lemma lw_step (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) (j : ℕ) (hj : j + 1 < r) :
    z.1 ⟨2 * (j + 1), by omega⟩ < t * z.1 ⟨2 * j, by omega⟩ ∧
    z.1 ⟨2 * (j + 1), by omega⟩ < t * z.1 ⟨2 * j + 1, by omega⟩ ∧
    z.1 ⟨2 * (j + 1) + 1, by omega⟩ <
      t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * (z.1 ⟨2 * j, by omega⟩ + z.1 ⟨2 * j + 1, by omega⟩) := by
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hb0 : ∀ i : Fin (3 * r - 1), 2 ≤ i.val → lwB r t i = 0 := by
    intro i hi; simp only [lwB]; rw [if_neg (by omega), if_neg (by omega)]
  have ea := congrFun h1 ⟨3 * j + 2, by omega⟩
  have ra := lw_row_a' r t z.1 (j + 1) (3 * j + 2) (2 * (j + 1)) (2 * j) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [Pi.add_apply, ra] at ea
  have eb := congrFun h1 ⟨3 * j + 3, by omega⟩
  have rb := lw_row_b' r t z.1 (j + 1) (3 * j + 3) (2 * (j + 1)) (2 * j + 1) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [Pi.add_apply, rb] at eb
  have ec := congrFun h1 ⟨3 * j + 4, by omega⟩
  have rc := lw_row_c' r t z.1 (j + 1) (3 * j + 4) (2 * (j + 1) + 1) (2 * j) (2 * j + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  rw [Pi.add_apply, rc] at ec
  have wa := hw ⟨3 * j + 2, by omega⟩
  have wb := hw ⟨3 * j + 3, by omega⟩
  have wc := hw ⟨3 * j + 4, by omega⟩
  rw [hb0 ⟨3 * j + 2, by omega⟩ (by simp)] at ea
  rw [hb0 ⟨3 * j + 3, by omega⟩ (by simp)] at eb
  rw [hb0 ⟨3 * j + 4, by omega⟩ (by simp)] at ec
  refine ⟨by linarith, by linarith, by linarith⟩

/-- elementary upper bounds along the chain -/
theorem lw_upper (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) (lam : ℝ)
    (hμ : dualityMeasure z ≤ t ^ lam) :
    ∀ j : ℕ, ∀ hj : j < r,
      z.1 ⟨2 * j, by omega⟩ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ j * t ^ (xPair lam j).1 ∧
      z.1 ⟨2 * j + 1, by omega⟩ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ j * t ^ (xPair lam j).2 := by
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  intro j
  induction j with
  | zero =>
    intro hj
    obtain ⟨h0a, h0b⟩ := lw_x0 r hr t ht1 z hfeas
    obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
    simp only [xPair, pow_zero, mul_one, Nat.mul_zero, Nat.zero_add]
    refine ⟨?_, ?_⟩
    · rcases le_total lam 2 with hl | hl
      · rw [min_eq_left hl]
        calc z.1 ⟨0, by omega⟩ ≤ _ := h0a
          _ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * t ^ lam :=
            mul_le_mul_of_nonneg_left hμ (by linarith)
      · rw [min_eq_right hl]
        calc z.1 ⟨0, by omega⟩ ≤ t ^ 2 := h0b.le
          _ = t ^ (2 : ℝ) := by norm_num
          _ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * t ^ (2 : ℝ) :=
            le_mul_of_one_le_left (by positivity) hN1
    · have e := congrFun h1 ⟨1, by omega⟩
      rw [Pi.add_apply, lw_row_1 r t hr] at e
      simp only [lwB] at e
      simp at e
      have := hw ⟨1, by omega⟩
      rw [Real.rpow_one]
      calc z.1 ⟨1, by omega⟩ ≤ t := by linarith
        _ ≤ _ := le_mul_of_one_le_left ht0.le hN1
  | succ j ih =>
    intro hj
    obtain ⟨ihA, ihB⟩ := ih (by omega)
    obtain ⟨sa, sb, sc⟩ := lw_step r hr t z hfeas j hj
    set X := z.1 ⟨2 * j, by omega⟩ with hX
    set Y := z.1 ⟨2 * j + 1, by omega⟩ with hY
    set P := z.1 ⟨2 * (j + 1), by omega⟩ with hP
    set Q := z.1 ⟨2 * (j + 1) + 1, by omega⟩ with hQ
    set C : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ j with hC
    have hC0 : 0 ≤ C := by positivity
    set α := (xPair lam j).1 with hα
    set β := (xPair lam j).2 with hβ
    have hxp : xPair lam (j + 1) = (1 + min α β, (1 - 1 / 2 ^ (j + 1)) + max α β) := by
      rw [xPair]
    have hpow : ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ (j + 1) = 2 * C := by
      rw [hC]; ring
    rw [hxp, hpow]
    simp only
    have hmono : ∀ a b : ℝ, a ≤ b → t ^ a ≤ t ^ b :=
      fun a b h => Real.rpow_le_rpow_of_exponent_le ht1.le h
    refine ⟨?_, ?_⟩
    · rw [Real.rpow_add ht0, Real.rpow_one]
      rcases le_total α β with h | h
      · rw [min_eq_left h]
        have : P ≤ t * (C * t ^ α) := by nlinarith
        have h2 : 0 ≤ C * (t * t ^ α) := by positivity
        nlinarith
      · rw [min_eq_right h]
        have : P ≤ t * (C * t ^ β) := by nlinarith
        have h2 : 0 ≤ C * (t * t ^ β) := by positivity
        nlinarith
    · rw [Real.rpow_add ht0]
      have hτ : 0 < t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) := by positivity
      have hXb : X ≤ C * t ^ max α β := ihA.trans (mul_le_mul_of_nonneg_left (hmono _ _ (le_max_left _ _)) hC0)
      have hYb : Y ≤ C * t ^ max α β := ihB.trans (mul_le_mul_of_nonneg_left (hmono _ _ (le_max_right _ _)) hC0)
      have : Q ≤ t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * (2 * (C * t ^ max α β)) := by
        calc Q ≤ _ := sc.le
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hτ.le
      calc Q ≤ _ := this
        _ = _ := by ring


/-- extension by zero of a `Fin n` vector to `ℕ` -/
noncomputable def fext {n : ℕ} (f : Fin n → ℝ) (a : ℕ) : ℝ := if h : a < n then f ⟨a, h⟩ else 0

lemma sum_ind (n : ℕ) (f : Fin n → ℝ) (a : ℕ) (u : ℝ) :
    ∑ k : Fin n, (if k.val = a then u else 0) * f k = u * fext f a := by
  unfold fext
  by_cases h : a < n
  · have e : ∀ k : Fin n, (k.val = a) ↔ (k = ⟨a, h⟩) := fun k => by simp [Fin.ext_iff]
    simp only [e, dif_pos h, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have e : ∀ k : Fin n, ¬ (k.val = a) := fun k hk => h (hk ▸ k.isLt)
    simp [e, h]

lemma lw_colsum (r : ℕ) (t : ℝ) (y : Fin (3 * r - 1) → ℝ) (k : Fin (2 * r)) :
    ((lwA r t)ᵀ *ᵥ y) k = ∑ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (k.val + 1) * y i := by
  simp [lwA, mulVec, dotProduct, Matrix.transpose_apply]

lemma lw_col_a (r : ℕ) (t : ℝ) (y : Fin (3 * r - 1) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    ((lwA r t)ᵀ *ᵥ y) ⟨2 * j, by omega⟩ =
      fext y (3 * j - 1) + fext y (3 * j) - t * fext y (3 * j + 2)
        - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext y (3 * j + 4) := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (2 * j + 1) =
      (if i.val = 3 * j - 1 then 1 else 0) + (if i.val = 3 * j then 1 else 0) +
      (if i.val = 3 * j + 2 then -t else 0) +
      (if i.val = 3 * j + 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1))) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = j + 1 by omega]; simp; done)
  simp only [hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring


lemma lw_col_a0 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (y : Fin (3 * r - 1) → ℝ) :
    ((lwA r t)ᵀ *ᵥ y) ⟨0, by omega⟩ =
      fext y 0 - t * fext y 2 - t ^ ((1 : ℝ) - 1 / 2 ^ 1) * fext y 4 := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (0 + 1) =
      (if i.val = 0 then 1 else 0) + (if i.val = 2 then -t else 0) +
      (if i.val = 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ 1)) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = 1 by omega]; simp; done)
  simp only [Fin.val_mk, hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring

lemma lw_col_b0 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (y : Fin (3 * r - 1) → ℝ) :
    ((lwA r t)ᵀ *ᵥ y) ⟨1, by omega⟩ =
      fext y 1 - t * fext y 3 - t ^ ((1 : ℝ) - 1 / 2 ^ 1) * fext y 4 := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (1 + 1) =
      (if i.val = 1 then 1 else 0) + (if i.val = 3 then -t else 0) +
      (if i.val = 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ 1)) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = 1 by omega]; simp; done)
  simp only [Fin.val_mk, hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring

lemma lw_col_b (r : ℕ) (t : ℝ) (y : Fin (3 * r - 1) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    ((lwA r t)ᵀ *ᵥ y) ⟨2 * j + 1, by omega⟩ =
      fext y (3 * j + 1) - t * fext y (3 * j + 3)
        - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext y (3 * j + 4) := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (2 * j + 1 + 1) =
      (if i.val = 3 * j + 1 then 1 else 0) + (if i.val = 3 * j + 3 then -t else 0) +
      (if i.val = 3 * j + 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1))) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = j + 1 by omega]; simp; done)
  simp only [hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring


lemma fext_nonneg {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (a : ℕ) : 0 ≤ fext f a := by
  unfold fext; split_ifs with h
  · exact hf _
  · exact le_rfl

lemma fext_pos {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) (a : ℕ) (ha : a < n) : 0 < fext f a := by
  unfold fext; rw [dif_pos ha]; exact hf _

/-- `F_a(j)`: inflow at the `a`-column of pair `j`. -/
noncomputable def Fa {r : ℕ} (y : Fin (3 * r - 1) → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 + fext y 0 else fext y (3 * j - 1) + fext y (3 * j)

/-- `F_b(j)`: inflow at the `b`-column of pair `j`. -/
noncomputable def Fb {r : ℕ} (y : Fin (3 * r - 1) → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then fext y 1 else fext y (3 * j + 1)

lemma lw_s_a (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (z : PDPoint (2 * r) (3 * r - 1))
    (h2 : z.2.2.1 - (lwA r t)ᵀ *ᵥ z.2.2.2 = lwC r) (j : ℕ) (hj : j < r) :
    z.2.2.1 ⟨2 * j, by omega⟩ = Fa z.2.2.2 j - t * fext z.2.2.2 (3 * j + 2)
      - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext z.2.2.2 (3 * j + 4) := by
  have hk := congrFun h2 ⟨2 * j, by omega⟩
  rw [Pi.sub_apply] at hk
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have := lw_col_a0 r t hr z.2.2.2
    simp only [Nat.mul_zero] at hk ⊢
    rw [this] at hk
    simp only [lwC] at hk
    simp only [Fa, if_true]
    simp at hk ⊢
    linarith
  · rw [lw_col_a r t z.2.2.2 j hpos hj] at hk
    simp only [lwC] at hk
    rw [if_neg (by omega)] at hk
    simp only [Fa, if_neg (show j ≠ 0 by omega)]
    linarith

lemma lw_s_b (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (z : PDPoint (2 * r) (3 * r - 1))
    (h2 : z.2.2.1 - (lwA r t)ᵀ *ᵥ z.2.2.2 = lwC r) (j : ℕ) (hj : j < r) :
    z.2.2.1 ⟨2 * j + 1, by omega⟩ = Fb z.2.2.2 j - t * fext z.2.2.2 (3 * j + 3)
      - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext z.2.2.2 (3 * j + 4) := by
  have hk := congrFun h2 ⟨2 * j + 1, by omega⟩
  rw [Pi.sub_apply] at hk
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have := lw_col_b0 r t hr z.2.2.2
    simp only [Nat.mul_zero, Nat.zero_add] at hk ⊢
    rw [this] at hk
    simp only [lwC] at hk
    simp only [Fb, if_true]
    simp at hk ⊢
    linarith
  · rw [lw_col_b r t z.2.2.2 j hpos hj] at hk
    simp only [lwC] at hk
    rw [if_neg (by omega)] at hk
    simp only [Fb, if_neg (show j ≠ 0 by omega)]
    linarith


lemma lw_dual_base (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) :
    t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 ≤
      ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z := by
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hN : (0 : ℝ) < ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 0 < 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  have hid := duality_identity _ _ _ z h1 h2
  have hmu : ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z =
      z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2 := by
    unfold dualityMeasure
    field_simp
  have hc : lwC r ⬝ᵥ z.1 = z.1 ⟨0, by omega⟩ := by
    simp only [dotProduct, lwC]
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp
    · intro k _ hk
      have : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [this]
    · simp
  have hb : lwB r t ⬝ᵥ z.2.2.2 = t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 := by
    simp only [dotProduct]
    have hpt : ∀ i : Fin (3 * r - 1), lwB r t i = (if i.val = 0 then t ^ 2 else 0) +
        (if i.val = 1 then t else 0) := by
      intro i; unfold lwB; split_ifs <;> first | omega | simp
    simp only [hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  rw [hmu, hid, hc, hb]
  have := hx ⟨0, by omega⟩
  linarith

lemma flow_step (t : ℝ) (ht1 : 1 < t) (lam A B c D Fa Fb ya yb yc : ℝ) (hD : 0 ≤ D)
    (hFa : Fa ≤ D * t ^ (lam - A)) (hFb : Fb ≤ D * t ^ (lam - B))
    (hya : 0 ≤ ya) (hyb : 0 ≤ yb) (hyc : 0 ≤ yc)
    (h1 : t * ya ≤ Fa) (h2 : t * yb ≤ Fb)
    (h3 : t ^ ((1 : ℝ) - c) * yc ≤ Fa) (h4 : t ^ ((1 : ℝ) - c) * yc ≤ Fb) :
    ya + yb ≤ 2 * D * t ^ (lam - (1 + min A B)) ∧
    yc ≤ 2 * D * t ^ (lam - ((1 - c) + max A B)) := by
  have ht0 : 0 < t := by linarith
  have hmono : ∀ a b : ℝ, a ≤ b → t ^ a ≤ t ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le ht1.le h
  constructor
  · have e : t ^ (lam - min A B) = t ^ (lam - (1 + min A B)) * t := by
      rw [show lam - min A B = (lam - (1 + min A B)) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
    have hA : t ^ (lam - A) ≤ t ^ (lam - min A B) := hmono _ _ (by linarith [min_le_left A B])
    have hB : t ^ (lam - B) ≤ t ^ (lam - min A B) := hmono _ _ (by linarith [min_le_right A B])
    have key : t * (ya + yb) ≤ t * (2 * D * t ^ (lam - (1 + min A B))) := by
      calc t * (ya + yb) = t * ya + t * yb := by ring
        _ ≤ Fa + Fb := add_le_add h1 h2
        _ ≤ D * t ^ (lam - min A B) + D * t ^ (lam - min A B) :=
            add_le_add (hFa.trans (mul_le_mul_of_nonneg_left hA hD))
              (hFb.trans (mul_le_mul_of_nonneg_left hB hD))
        _ = t * (2 * D * t ^ (lam - (1 + min A B))) := by rw [e]; ring
    exact le_of_mul_le_mul_left key ht0
  · set τ : ℝ := t ^ ((1 : ℝ) - c) with hτ
    have hτ0 : 0 < τ := by positivity
    have e : t ^ (lam - max A B) = t ^ (lam - ((1 - c) + max A B)) * τ := by
      rw [hτ, ← Real.rpow_add ht0]; congr 1; ring
    have hbound : τ * yc ≤ D * t ^ (lam - max A B) := by
      rcases le_total A B with h | h
      · rw [max_eq_right h]; exact h4.trans hFb
      · rw [max_eq_left h]; exact h3.trans hFa
    have hnn : 0 ≤ D * t ^ (lam - ((1 - c) + max A B)) := by positivity
    have : τ * yc ≤ τ * (D * t ^ (lam - ((1 - c) + max A B))) := by
      calc τ * yc ≤ D * t ^ (lam - max A B) := hbound
        _ = τ * (D * t ^ (lam - ((1 - c) + max A B))) := by rw [e]; ring
    have := le_of_mul_le_mul_left this hτ0
    nlinarith


theorem lw_dual_bound (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) (lam : ℝ)
    (hμ : dualityMeasure z = t ^ lam) :
    ∀ j : ℕ, j < r →
      Fa z.2.2.2 j ≤ (((2 * r + (3 * r - 1) : ℕ) : ℝ) + 1) * 2 ^ j * t ^ (lam - (xPair lam j).1) ∧
      Fb z.2.2.2 j ≤ (((2 * r + (3 * r - 1) : ℕ) : ℝ) + 1) * 2 ^ j * t ^ (lam - (xPair lam j).2) := by
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  have hbase := lw_dual_base r hr t ht1 z hfeas
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hy0 : 0 ≤ fext z.2.2.2 0 := fext_nonneg _ (fun i => (hy i).le) 0
  have hy1 : 0 ≤ fext z.2.2.2 1 := fext_nonneg _ (fun i => (hy i).le) 1
  intro j
  induction j with
  | zero =>
    intro hj
    rw [hμ] at hbase
    set N : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) with hNdef
    have e2 : t ^ lam = t ^ (lam - 2) * t ^ 2 := by
      rw [show lam = (lam - 2) + (2 : ℕ) by push_cast; ring, Real.rpow_add ht0, Real.rpow_natCast]
      simp
    have e1 : t ^ lam = t ^ (lam - 1) * t := by
      rw [show lam = (lam - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
      simp
    have hT2 : fext z.2.2.2 0 ≤ N * t ^ (lam - 2) := by
      have : t ^ 2 * fext z.2.2.2 0 ≤ t ^ 2 * (N * t ^ (lam - 2)) := by
        calc t ^ 2 * fext z.2.2.2 0 ≤ t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 := by
              have : 0 ≤ t * fext z.2.2.2 1 := by positivity
              linarith
          _ ≤ N * t ^ lam := hbase
          _ = t ^ 2 * (N * t ^ (lam - 2)) := by rw [e2]; ring
      exact le_of_mul_le_mul_left this (by positivity)
    have hT1 : fext z.2.2.2 1 ≤ N * t ^ (lam - 1) := by
      have : t * fext z.2.2.2 1 ≤ t * (N * t ^ (lam - 1)) := by
        calc t * fext z.2.2.2 1 ≤ t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 := by
              have : 0 ≤ t ^ 2 * fext z.2.2.2 0 := by positivity
              linarith
          _ ≤ N * t ^ lam := hbase
          _ = t * (N * t ^ (lam - 1)) := by rw [e1]; ring
      exact le_of_mul_le_mul_left this ht0
    simp only [xPair, pow_zero, mul_one, Fa, Fb, if_true]
    refine ⟨?_, ?_⟩
    · rcases le_total lam 2 with hl | hl
      · rw [min_eq_left hl, sub_self, Real.rpow_zero]
        have : t ^ (lam - 2) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
        nlinarith
      · rw [min_eq_right hl]
        have : 1 ≤ t ^ (lam - 2) := Real.one_le_rpow ht1.le (by linarith)
        nlinarith
    · have : 0 ≤ t ^ (lam - 1) := by positivity
      nlinarith
  | succ j ih =>
    intro hj
    obtain ⟨ihA, ihB⟩ := ih (by omega)
    set N : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) with hNdef
    have sa := lw_s_a r hr t z h2 j (by omega)
    have sb := lw_s_b r hr t z h2 j (by omega)
    have pa := hs ⟨2 * j, by omega⟩
    have pb := hs ⟨2 * j + 1, by omega⟩
    set τ : ℝ := t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) with hτ
    have hτ0 : 0 < τ := by positivity
    set ya := fext z.2.2.2 (3 * j + 2) with hya
    set yb := fext z.2.2.2 (3 * j + 3) with hyb
    set yc := fext z.2.2.2 (3 * j + 4) with hyc
    have ya0 : 0 ≤ ya := fext_nonneg _ (fun i => (hy i).le) _
    have yb0 : 0 ≤ yb := fext_nonneg _ (fun i => (hy i).le) _
    have yc0 : 0 ≤ yc := fext_nonneg _ (fun i => (hy i).le) _
    rw [sa] at pa
    rw [sb] at pb
    have hty : 0 ≤ τ * yc := by positivity
    have hta : 0 ≤ t * ya := by positivity
    have htb : 0 ≤ t * yb := by positivity
    have key := flow_step t ht1 lam (xPair lam j).1 (xPair lam j).2 (1 / 2 ^ (j + 1))
      ((N + 1) * 2 ^ j) (Fa z.2.2.2 j) (Fb z.2.2.2 j) ya yb yc (by positivity) ihA ihB ya0 yb0 yc0
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hxp : xPair lam (j + 1) = (1 + min (xPair lam j).1 (xPair lam j).2,
        (1 - 1 / 2 ^ (j + 1)) + max (xPair lam j).1 (xPair lam j).2) := by
      rw [xPair]
    have eFa : Fa z.2.2.2 (j + 1) = ya + yb := by
      simp only [Fa]
      rw [if_neg (by omega), hya, hyb]
      congr 2 <;> omega
    have eFb : Fb z.2.2.2 (j + 1) = yc := by
      simp only [Fb]
      rw [if_neg (by omega), hyc]
      congr 1
    rw [hxp, eFa, eFb]
    simp only
    have e2 : (N + 1) * 2 ^ (j + 1) = 2 * ((N + 1) * 2 ^ j) := by ring
    rw [e2]
    exact ⟨key.1, key.2⟩


lemma log_sandwich (t : ℝ) (ht1 : 1 < t) (x A ρ U D θ : ℝ) (hx : 0 < x) (hθ : θ < 1)
    (hD : 0 < D) (hup : x ≤ U * t ^ A) (hlow : (1 - θ) * t ^ A ≤ x * D)
    (hU : U ≤ t ^ ρ) (hDθ : D / (1 - θ) ≤ t ^ ρ) (hU0 : 0 ≤ U) :
    |Real.logb t x - A| ≤ ρ := by
  have ht0 : 0 < t := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  rw [abs_le]
  constructor
  · -- A - ρ ≤ logb x
    rw [show -ρ ≤ Real.logb t x - A ↔ A - ρ ≤ Real.logb t x by constructor <;> intro h <;> linarith]
    rw [Real.le_logb_iff_rpow_le ht1 hx, Real.rpow_sub ht0]
    have hA : 0 < t ^ A := by positivity
    have hρ : 0 < t ^ ρ := by positivity
    rw [div_le_iff₀ hρ]
    have h2 : t ^ A ≤ x * (D / (1 - θ)) := by
      rw [mul_div_assoc', le_div_iff₀ h1θ]; linarith
    calc t ^ A ≤ x * (D / (1 - θ)) := h2
      _ ≤ x * t ^ ρ := mul_le_mul_of_nonneg_left hDθ hx.le
  · rw [sub_le_iff_le_add, add_comm, Real.logb_le_iff_le_rpow ht1 hx, Real.rpow_add ht0]
    calc x ≤ U * t ^ A := hup
      _ ≤ t ^ ρ * t ^ A := mul_le_mul_of_nonneg_right hU (by positivity)
      _ = t ^ A * t ^ ρ := mul_comm _ _

lemma lower_coord (t : ℝ) (ht1 : 1 < t) (x s Fcap D θ lam A : ℝ) (hx : 0 < x)
    (hxs : (1 - θ) * t ^ lam ≤ x * s) (hs : s ≤ Fcap) (hF : Fcap ≤ D * t ^ (lam - A)) :
    (1 - θ) * t ^ A ≤ x * D := by
  have ht0 : 0 < t := by linarith
  have e : t ^ lam = t ^ A * t ^ (lam - A) := by
    rw [← Real.rpow_add ht0]; congr 1; ring
  have hp : 0 < t ^ (lam - A) := by positivity
  have h1 : (1 - θ) * t ^ A * t ^ (lam - A) ≤ x * D * t ^ (lam - A) := by
    calc (1 - θ) * t ^ A * t ^ (lam - A) = (1 - θ) * t ^ lam := by rw [e]; ring
      _ ≤ x * s := hxs
      _ ≤ x * (D * t ^ (lam - A)) := mul_le_mul_of_nonneg_left (hs.trans hF) hx.le
      _ = x * D * t ^ (lam - A) := by ring
  exact le_of_mul_le_mul_right h1 hp

lemma two_pow_le_factorial (n : ℕ) : 2 ^ n ≤ (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.factorial_succ (n + 1)]
    have : 2 ≤ n + 1 + 1 := by omega
    calc 2 ^ n * 2 ≤ (n + 1).factorial * (n + 1 + 1) := Nat.mul_le_mul ih this
      _ = (n + 1 + 1) * (n + 1).factorial := by ring

lemma const_sq_le (r j : ℕ) (hr : 1 ≤ r) (hj : j < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (5 * (r : ℝ) * 2 ^ j / (1 - θ)) ^ 2 ≤
      max (Nat.factorial (10 * r - 2) : ℝ) ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3) := by
  refine le_trans ?_ (le_max_right _ _)
  have h1θ : 0 < 1 - θ := by linarith
  have h1θ1 : 1 - θ ≤ 1 := by linarith
  set F : ℕ := Nat.factorial (10 * r - 1) with hF
  have hF1 : 1 ≤ F := Nat.factorial_pos _
  have h5 : 5 * r ≤ F := le_trans (by omega) (Nat.self_le_factorial (10 * r - 1))
  have h2 : 2 ^ j ≤ F := by
    calc 2 ^ j ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (r - 1 + 1).factorial := two_pow_le_factorial _
      _ ≤ F := Nat.factorial_le (by omega)
  have h3 : 5 * r * 2 ^ j ≤ F * F := Nat.mul_le_mul h5 h2
  have h3' : (5 * (r : ℝ) * 2 ^ j) ≤ (F : ℝ) * F := by exact_mod_cast h3
  have hF1' : (1 : ℝ) ≤ F := by exact_mod_cast hF1
  have h5' : (0 : ℝ) ≤ 5 * (r : ℝ) * 2 ^ j := by positivity
  rw [div_pow]
  have h4 : (5 * (r : ℝ) * 2 ^ j) ^ 2 ≤ (F : ℝ) ^ 24 := by
    calc (5 * (r : ℝ) * 2 ^ j) ^ 2 ≤ ((F : ℝ) * F) ^ 2 := pow_le_pow_left₀ h5' h3' 2
      _ = (F : ℝ) ^ 4 := by ring
      _ ≤ (F : ℝ) ^ 24 := pow_le_pow_right₀ hF1' (by norm_num)
  have h6 : (1 - θ) ^ 3 ≤ (1 - θ) ^ 2 := pow_le_pow_of_le_one h1θ.le h1θ1 (by norm_num)
  have h7 : 0 < (1 - θ) ^ 3 := by positivity
  rw [div_le_div_iff₀ (by positivity) h7]
  calc (5 * (r : ℝ) * 2 ^ j) ^ 2 * (1 - θ) ^ 3 ≤ (F : ℝ) ^ 24 * (1 - θ) ^ 3 :=
        mul_le_mul_of_nonneg_right h4 h7.le
    _ ≤ (F : ℝ) ^ 24 * (1 - θ) ^ 2 := mul_le_mul_of_nonneg_left h6 (by positivity)


theorem nbhd_log_close (r : ℕ) (hr : 1 ≤ r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (t : ℝ)
    (ht : (max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) ^ (2 ^ (r - 1)) < t)
    (z : PDPoint (2 * r) (3 * r - 1)) (hz : z ∈ lwWideNeighborhood r θ t)
    (h0 : 1 ≤ dualityMeasure z) (h2 : dualityMeasure z ≤ t ^ 2) (j : ℕ) (hj : j < r) :
    |Real.logb t (z.1 ⟨2 * j, by omega⟩) - (xPair (Real.logb t (dualityMeasure z)) j).1| ≤
        Real.logb t (max (Nat.factorial (10 * r - 2) : ℝ)
          ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) / 2 ∧
    |Real.logb t (z.1 ⟨2 * j + 1, by omega⟩) - (xPair (Real.logb t (dualityMeasure z)) j).2| ≤
        Real.logb t (max (Nat.factorial (10 * r - 2) : ℝ)
          ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) / 2 := by
  set M : ℝ := max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3) with hM
  have hM1 : (1 : ℝ) ≤ M :=
    le_max_of_le_left (by exact_mod_cast Nat.factorial_pos _)
  have hMpos : 0 < M := by linarith
  have ht1 : 1 < t := lt_of_le_of_lt (one_le_pow₀ hM1) ht
  have ht0 : 0 < t := by linarith
  have hz' : z ∈ wideNeighborhood (lwA r t) (lwB r t) (lwC r) θ := hz
  obtain ⟨hfeas, hxs, hwy⟩ := hz'
  have hμpos : 0 < dualityMeasure z := by linarith
  set lam : ℝ := Real.logb t (dualityMeasure z) with hlam
  have hμ : dualityMeasure z = t ^ lam := (Real.rpow_logb ht0 ht1.ne' hμpos).symm
  have hup := lw_upper r hr t ht1 z hfeas lam (le_of_eq hμ) j hj
  have hdual := lw_dual_bound r hr t ht1 z hfeas lam hμ j hj
  have hsa := lw_s_a r hr t z hfeas.2.1 j hj
  have hsb := lw_s_b r hr t z hfeas.2.1 j hj
  obtain ⟨hfe1, hfe2, hx, hw, hs, hy⟩ := hfeas
  set N : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) with hNdef
  have hN5 : N + 1 = 5 * (r : ℝ) := by
    have : 2 * r + (3 * r - 1) + 1 = 5 * r := by omega
    rw [hNdef]
    exact_mod_cast this
  have hN0 : 0 ≤ N := by positivity
  set ρ : ℝ := Real.logb t M / 2 with hρ
  have hρ2 : (t ^ ρ) ^ 2 = M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
      show ρ * ((2 : ℕ) : ℝ) = Real.logb t M by rw [hρ]; push_cast; ring,
      Real.rpow_logb ht0 ht1.ne' hMpos]
  set D : ℝ := (N + 1) * 2 ^ j with hD
  set U : ℝ := N * 2 ^ j with hU
  have hD0 : 0 < D := by rw [hD]; positivity
  have hUD : U ≤ D := by rw [hU, hD]; nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) j]
  have hC : D / (1 - θ) ≤ t ^ ρ := by
    have hsq := const_sq_le r j hr hj θ hθ0 hθ1
    have hDC : D / (1 - θ) = 5 * (r : ℝ) * 2 ^ j / (1 - θ) := by rw [hD, hN5]
    rw [hDC]
    have htρ : 0 < t ^ ρ := by positivity
    by_contra hcon
    push_neg at hcon
    have : (t ^ ρ) ^ 2 < (5 * (r : ℝ) * 2 ^ j / (1 - θ)) ^ 2 := by
      apply pow_lt_pow_left₀ hcon htρ.le (by norm_num)
    rw [hρ2] at this
    linarith
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hUρ : U ≤ t ^ ρ := by
    refine hUD.trans (le_trans ?_ hC)
    rw [le_div_iff₀ (by linarith : 0 < 1 - θ)]
    nlinarith
  have main : ∀ (x s Fc A : ℝ), 0 < x → (1 - θ) * dualityMeasure z ≤ x * s → s ≤ Fc →
      Fc ≤ D * t ^ (lam - A) → x ≤ U * t ^ A → |Real.logb t x - A| ≤ ρ := by
    intro x s Fc A hx hxs' hs' hF hup'
    exact log_sandwich t ht1 x A ρ U D θ hx hθ1 hD0 hup'
      (lower_coord t ht1 x s Fc D θ lam A hx (by rw [← hμ]; exact hxs') hs' hF) hUρ hC hU0
  have ya0 := fext_nonneg z.2.2.2 (fun i => (hy i).le) (3 * j + 2)
  have yb0 := fext_nonneg z.2.2.2 (fun i => (hy i).le) (3 * j + 3)
  have yc0 := fext_nonneg z.2.2.2 (fun i => (hy i).le) (3 * j + 4)
  have hτ0 : 0 < t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) := by positivity
  constructor
  · refine main _ (z.2.2.1 ⟨2 * j, by omega⟩) (Fa z.2.2.2 j) _ (hx _) (hxs _) ?_ ?_ hup.1
    · rw [hsa]
      have := mul_nonneg ht0.le ya0
      have := mul_nonneg hτ0.le yc0
      linarith
    · exact hdual.1
  · refine main _ (z.2.2.1 ⟨2 * j + 1, by omega⟩) (Fb z.2.2.2 j) _ (hx _) (hxs _) ?_ ?_ hup.2
    · rw [hsb]
      have := mul_nonneg ht0.le yb0
      have := mul_nonneg hτ0.le yc0
      linarith
    · exact hdual.2



lemma xPair_delta_succ (lam : ℝ) (j : ℕ) :
    (xPair lam (j + 1)).1 - (xPair lam (j + 1)).2 =
      1 / 2 ^ (j + 1) - |(xPair lam j).1 - (xPair lam j).2| := by
  have h : (xPair lam (j + 1)) = (1 + min (xPair lam j).1 (xPair lam j).2,
      (1 - 1 / 2 ^ (j + 1)) + max (xPair lam j).1 (xPair lam j).2) := by
    rw [xPair]
  rw [h]
  simp only
  rcases le_total (xPair lam j).1 (xPair lam j).2 with hle | hle
  · rw [min_eq_left hle, max_eq_right hle, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right hle, max_eq_left hle, abs_of_nonneg (by linarith)]; ring

lemma xPair_cell (n : ℕ) : ∀ (k : ℕ), k < 2 ^ n → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
    (xPair (2 * ((k : ℝ) + u) / 2 ^ n) n).1 - (xPair (2 * ((k : ℝ) + u) / 2 ^ n) n).2
      = (-1) ^ (k + 1) * (1 - 2 * u) / 2 ^ n := by
  induction n with
  | zero =>
    intro k hk u hu0 hu1
    have : k = 0 := by simpa using hk
    subst this
    simp only [xPair, pow_zero, Nat.cast_zero, zero_add, div_one]
    rw [min_eq_left (by linarith)]
    ring
  | succ n ih =>
    intro k hk u hu0 hu1
    obtain ⟨k0, e, he, hk0⟩ : ∃ k0 e : ℕ, e < 2 ∧ k = 2 * k0 + e := ⟨k / 2, k % 2, by omega, by omega⟩
    have hk0' : k0 < 2 ^ n := by rw [pow_succ] at hk; omega
    have hlam : 2 * ((k : ℝ) + u) / 2 ^ (n + 1) = 2 * ((k0 : ℝ) + (e + u) / 2) / 2 ^ n := by
      rw [hk0]; push_cast; rw [pow_succ]; field_simp; ring
    rw [xPair_delta_succ, hlam]
    have := ih k0 hk0' ((e + u) / 2) (by positivity) (by interval_cases e <;> simp <;> linarith)
    rw [this]
    interval_cases e
    · simp only [hk0]
      have : (-1 : ℝ) ^ (2 * k0 + 0 + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [this, pow_succ]
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos]
      simp only [abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg (by linarith)]
      field_simp
      ring
    · simp only [hk0]
      have : (-1 : ℝ) ^ (2 * k0 + 1 + 1) = 1 := by rw [show 2 * k0 + 1 + 1 = 2 * (k0 + 1) by ring, pow_mul]; norm_num
      rw [this, pow_succ]
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos]
      simp only [abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonpos (by linarith)]
      field_simp
      ring

theorem xPair_zigzag (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ 2 ^ (r - 1)) :
    (xPair (2 * (k : ℝ) / 2 ^ (r - 1)) (r - 1)).1 - (xPair (2 * (k : ℝ) / 2 ^ (r - 1)) (r - 1)).2
      = (-1) ^ (k + 1) / 2 ^ (r - 1) := by
  rcases Nat.lt_or_ge k (2 ^ (r - 1)) with h | h
  · have := xPair_cell (r - 1) k h 0 le_rfl zero_le_one
    simp only [add_zero, mul_zero, sub_zero, mul_one] at this
    rw [this]
  · have hk' : k = 2 ^ (r - 1) := le_antisymm hk h
    have hpos : 0 < 2 ^ (r - 1) := by positivity
    have := xPair_cell (r - 1) (k - 1) (by omega) 1 zero_le_one le_rfl
    have hc : ((k - 1 : ℕ) : ℝ) + 1 = k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at this
    rw [this]
    have : (-1 : ℝ) ^ (k - 1 + 1) = (-1) ^ k := by rw [Nat.sub_add_cancel (by omega)]
    rw [this, pow_succ]
    ring


lemma continuous_dualityMeasure (n m : ℕ) : Continuous (dualityMeasure : PDPoint n m → ℝ) := by
  unfold dualityMeasure
  simp only [dotProduct]
  fun_prop


/-- helper: sign extraction from logs -/
lemma sign_of_close (L1 L2 Xa Xb ρ : ℝ) (q : ℝ) (hq : 0 < q) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (h1 : |L1 - Xa| ≤ ρ) (h2 : |L2 - Xb| ≤ ρ) (hX : Xa - Xb = s / q) (hρ : 2 * ρ < 1 / q) :
    0 < s * (L1 - L2) := by
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have hsq : s * (s / q) = 1 / q := by
    rcases hs with rfl | rfl <;> ring
  have key : s * (L1 - L2) = s * (Xa - Xb) + s * ((L1 - Xa) - (L2 - Xb)) := by ring
  rw [key, hX, hsq]
  have : -(2 * ρ) ≤ s * ((L1 - Xa) - (L2 - Xb)) := by
    rcases hs with rfl | rfl <;> nlinarith [a1.1, a1.2, a2.1, a2.2]
  linarith

theorem nbhd_sign (r : ℕ) (hr : 1 ≤ r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (t : ℝ)
    (ht : (max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) ^ (2 ^ (r - 1)) < t)
    (k : ℕ) (hk : k ≤ 2 ^ (r - 1)) (z : PDPoint (2 * r) (3 * r - 1))
    (hz : z ∈ lwWideNeighborhood r θ t)
    (hμ : dualityMeasure z = t ^ (2 * (k : ℝ) / 2 ^ (r - 1))) :
    0 < (-1) ^ (k + 1) *
      (z.1 ⟨2 * r - 2, by omega⟩ - z.1 ⟨2 * r - 1, by omega⟩) := by
  set M : ℝ := max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3) with hM
  have hM1 : (1 : ℝ) ≤ M :=
    le_max_of_le_left (by exact_mod_cast Nat.factorial_pos _)
  have ht1 : 1 < t := lt_of_le_of_lt (one_le_pow₀ hM1) ht
  have hq : (0 : ℝ) < 2 ^ (r - 1) := by positivity
  have hlam0 : 0 ≤ 2 * (k : ℝ) / 2 ^ (r - 1) := by positivity
  have hlam2 : 2 * (k : ℝ) / 2 ^ (r - 1) ≤ 2 := by
    rw [div_le_iff₀ hq]
    have : (k : ℝ) ≤ 2 ^ (r - 1) := by exact_mod_cast hk
    linarith
  have h0 : 1 ≤ dualityMeasure z := by
    rw [hμ]; exact Real.one_le_rpow ht1.le hlam0
  have h2 : dualityMeasure z ≤ t ^ 2 := by
    rw [hμ]
    calc t ^ (2 * (k : ℝ) / 2 ^ (r - 1)) ≤ t ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1.le hlam2
      _ = t ^ 2 := by norm_num
  have hlog : Real.logb t (dualityMeasure z) = 2 * (k : ℝ) / 2 ^ (r - 1) := by
    rw [hμ, Real.logb_rpow (by linarith) ht1.ne']
  obtain ⟨c1, c2⟩ := nbhd_log_close r hr θ hθ0 hθ1 t ht z hz h0 h2 (r - 1) (by omega)
  rw [hlog] at c1 c2
  have i1 : (⟨2 * (r - 1), by omega⟩ : Fin (2 * r)) = ⟨2 * r - 2, by omega⟩ :=
    Fin.ext (by simp; omega)
  have i2 : (⟨2 * (r - 1) + 1, by omega⟩ : Fin (2 * r)) = ⟨2 * r - 1, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [i1] at c1
  rw [i2] at c2
  have hpos : ∀ j, 0 < z.1 j := hz.1.2.2.1
  have hx1 := hpos ⟨2 * r - 2, by omega⟩
  have hx2 := hpos ⟨2 * r - 1, by omega⟩
  -- the radius is small
  have hρ : 2 * (Real.logb t M / 2) < 1 / 2 ^ (r - 1) := by
    have hMpos : 0 < M := by linarith
    have h1 : Real.logb t (M ^ (2 ^ (r - 1))) < 1 := by
      have := Real.logb_lt_logb ht1 (by positivity) ht
      rwa [Real.logb_self_eq_one ht1] at this
    rw [Real.logb_pow] at h1
    rw [lt_div_iff₀ hq]
    push_cast at h1
    nlinarith
  have hz2 := xPair_zigzag r k hr hk
  have hsgn : (-1 : ℝ) ^ (k + 1) = 1 ∨ (-1 : ℝ) ^ (k + 1) = -1 := by
    rcases neg_one_pow_eq_or ℝ (k + 1) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hfin := sign_of_close _ _ _ _ _ _ hq _ hsgn c1 c2 hz2 hρ
  -- transfer from logs to values
  rcases hsgn with h | h
  · rw [h] at hfin ⊢
    have := (Real.logb_lt_logb_iff ht1 hx2 hx1).mp (by linarith)
    linarith
  · rw [h] at hfin ⊢
    have := (Real.logb_lt_logb_iff ht1 hx1 hx2).mp (by linarith)
    linarith


end LogBarrierIPM.Iterations

open LogBarrierIPM.Iterations in
theorem solution (r : ℕ) (hr : 1 ≤ r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (t : ℝ)
    (ht : (max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) ^ (2 ^ (r - 1)) < t)
    (p : ℕ) (z : Fin (p + 1) → PDPoint (2 * r) (3 * r - 1))
    (hseg : ∀ i : Fin p, segment ℝ (z i.castSucc) (z i.succ) ⊆ lwWideNeighborhood r θ t)
    (hstart : dualityMeasure (z 0) ≤ 1)
    (hend : t ^ 2 ≤ dualityMeasure (z (Fin.last p))) :
    2 ^ (r - 1) ≤ p := by
  have hM1 : (1 : ℝ) ≤ max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3) :=
    le_max_of_le_left (by exact_mod_cast Nat.factorial_pos _)
  have ht1 : 1 < t := lt_of_le_of_lt (one_le_pow₀ hM1) ht
  have hp : 1 ≤ p := by
    by_contra h
    obtain rfl : p = 0 := by omega
    have h0 : (Fin.last 0 : Fin (0 + 1)) = 0 := rfl
    rw [h0] at hend
    nlinarith
  set m : ℕ := 2 ^ (r - 1) with hm
  have hmpos : (0 : ℝ) < 2 ^ (r - 1) := by positivity
  -- the polygon
  set γ : ℝ → PDPoint (2 * r) (3 * r - 1) := T30.poly p z with hγ
  have hγc : Continuous γ := T30.poly_cont p z
  set φ : ℝ → ℝ := fun s => dualityMeasure (γ s) with hφ
  have hφc : Continuous φ := (continuous_dualityMeasure _ _).comp hγc
  have hγ0 : γ 0 = z 0 := by
    have := T30.poly_cell p z ⟨0, hp⟩ 0 ⟨le_rfl, zero_le_one⟩
    simpa using this
  have hγp : γ p = z (Fin.last p) := by
    have := T30.poly_cell p z ⟨p - 1, by omega⟩ 1 ⟨zero_le_one, le_rfl⟩
    have e : ((p - 1 : ℕ) : ℝ) + 1 = p := by rw [Nat.cast_sub hp]; push_cast; ring
    have e2 : (⟨p - 1, by omega⟩ : Fin p).succ = Fin.last p := Fin.ext (by simp; omega)
    simp only [e, e2] at this
    simpa using this
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) p, γ s ∈ lwWideNeighborhood r θ t := by
    intro s hs
    obtain ⟨j, a, ha, hsa⟩ := T30.exists_cell p hp s hs
    have := T30.poly_cell p z j a ha
    rw [hsa]
    show T30.poly p z _ ∈ _
    rw [this]
    exact hseg j ⟨1 - a, a, by linarith [ha.2], ha.1, by ring, rfl⟩
  -- levels
  set c : ℕ → ℝ := fun k => t ^ (2 * (k : ℝ) / 2 ^ (r - 1)) with hc
  have hc_mono : ∀ k, c k < c (k + 1) := by
    intro k
    simp only [hc]
    apply Real.rpow_lt_rpow_of_exponent_lt ht1
    rw [div_lt_div_iff_of_pos_right hmpos]
    push_cast; linarith
  have hc_ge : ∀ k, 1 ≤ c k := by
    intro k
    exact Real.one_le_rpow ht1.le (by positivity)
  have hc_le : ∀ k, k ≤ m → c k ≤ t ^ 2 := by
    intro k hk
    have h1 : 2 * (k : ℝ) / 2 ^ (r - 1) ≤ 2 := by
      rw [div_le_iff₀ hmpos]
      have : (k : ℝ) ≤ 2 ^ (r - 1) := by exact_mod_cast hk
      linarith
    calc c k ≤ t ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1.le h1
      _ = t ^ 2 := by norm_num
  -- thresholds
  let S : ℕ → Set ℝ := fun k => {s | s ∈ Set.Icc (0 : ℝ) p ∧ c k ≤ φ s}
  have hSne : ∀ k, k ≤ m → (S k).Nonempty := by
    intro k hk
    refine ⟨p, ⟨by positivity, le_rfl⟩, ?_⟩
    have : φ p = dualityMeasure (z (Fin.last p)) := by simp only [hφ, hγp]
    rw [this]
    exact le_trans (hc_le k hk) hend
  have hSclosed : ∀ k, IsClosed (S k) := fun k =>
    isClosed_Icc.inter (isClosed_le continuous_const hφc)
  have hSbdd : ∀ k, BddBelow (S k) := fun k => ⟨0, fun s hs => hs.1.1⟩
  set sv : ℕ → ℝ := fun k => sInf (S k) with hsv
  have hsvmem : ∀ k, k ≤ m → sv k ∈ S k := fun k hk =>
    (hSclosed k).csInf_mem (hSne k hk) (hSbdd k)
  have hφeq : ∀ k, k ≤ m → φ (sv k) = c k := by
    intro k hk
    have hm1 := hsvmem k hk
    refine le_antisymm ?_ hm1.2
    rcases eq_or_lt_of_le hm1.1.1 with h0 | hpos
    · have : φ (sv k) = dualityMeasure (z 0) := by rw [← h0]; simp only [hφ, hγ0]
      rw [this]
      exact le_trans hstart (hc_ge k)
    · have hsub : Set.Ico (0 : ℝ) (sv k) ⊆ {s | φ s ≤ c k} := by
        intro s hs
        by_contra hcon
        have hcon' : c k ≤ φ s := le_of_lt (not_le.mp hcon)
        have hsS : s ∈ S k := ⟨⟨hs.1, le_trans hs.2.le hm1.1.2⟩, hcon'⟩
        have := csInf_le (hSbdd k) hsS
        exact absurd hs.2 (not_lt.mpr this)
      have hcl : IsClosed {s | φ s ≤ c k} := isClosed_le hφc continuous_const
      have := hcl.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt hpos)] at this
      exact this ⟨hm1.1.1, le_rfl⟩
  have hstrict : ∀ k, k < m → sv k < sv (k + 1) := by
    intro k hk
    have hle : sv k ≤ sv (k + 1) := by
      apply csInf_le_csInf (hSbdd k) (hSne (k + 1) hk)
      intro s hs
      exact ⟨hs.1, le_trans (hc_mono k).le hs.2⟩
    refine lt_of_le_of_ne hle ?_
    intro h
    have h1 := hφeq k hk.le
    have h2 := hφeq (k + 1) hk
    rw [h] at h1
    have := hc_mono k
    linarith
  -- sign function
  set G : ℝ → ℝ := fun s => (γ s).1 ⟨2 * r - 2, by omega⟩ - (γ s).1 ⟨2 * r - 1, by omega⟩ with hG
  have hGsign : ∀ k, k ≤ m → 0 < (-1 : ℝ) ^ (k + 1) * G (sv k) := by
    intro k hk
    have hm1 := hsvmem k hk
    exact nbhd_sign r hr θ hθ0 hθ1 t ht k hk (γ (sv k)) (hmem _ hm1.1) (hφeq k hk)
  have hGaff : ∀ i : ℕ, i < p → ∀ a ∈ Set.Icc (0 : ℝ) 1,
      G (i + a) = (1 - a) * G i + a * G (i + 1) := by
    intro i hi a ha
    have h1 := T30.poly_cell p z ⟨i, hi⟩ a ha
    have h0 := T30.poly_cell p z ⟨i, hi⟩ 0 ⟨le_rfl, zero_le_one⟩
    have h2 := T30.poly_cell p z ⟨i, hi⟩ 1 ⟨zero_le_one, le_rfl⟩
    simp only [hG, hγ]
    simp only [add_zero] at h0
    rw [h1, show (i : ℝ) + 1 = (i : ℝ) + 1 from rfl, h2, h0]
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key := K3.alternations_le_pieces p m G hGaff (fun k => sv k.val)
    (by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      exact hstrict i.val i.isLt)
    (fun k => (hsvmem k.val (by omega)).1.1)
    (fun k => (hsvmem k.val (by omega)).1.2)
    (by
      intro k
      have h1 := hGsign k.val (by omega)
      have h2 := hGsign (k.val + 1) (by omega)
      simp only [Fin.val_castSucc, Fin.val_succ]
      have e : ((-1 : ℝ) ^ (k.val + 1)) * ((-1 : ℝ) ^ (k.val + 1 + 1)) = -1 := by
        rw [← pow_add, show k.val + 1 + (k.val + 1 + 1) = 2 * (k.val + 1) + 1 by ring, pow_succ,
          pow_mul]
        norm_num
      have := mul_pos h1 h2
      nlinarith [this, e])
  exact key

