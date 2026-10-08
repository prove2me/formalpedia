-- Prove2me | solution 1 for HooftDimReduction.staircase_determines_all
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:02:59.498066+00:00
-- url     : https://prove2.me/submissions/8a2eaeb1-71d1-4d08-b96d-84719e6aa218

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

set_option autoImplicit false

open HooftDimReduction in
theorem hooftb0c6_uniq {p : ℕ} {g : (Fin 4 → ZMod p) → ZMod p} (hg : IsPlaquetteRule g)
    (i : Fin 4) (v w : Fin 4 → ZMod p) (h : ∀ j, j ≠ i → v j = w j)
    (hv : g v = 0) (hw : g w = 0) : v i = w i := by
  obtain ⟨a, _, huniq⟩ := hg i v
  have h1 : v i = a := huniq _ (by
    show g (Function.update v i (v i)) = 0
    rw [Function.update_eq_self]; exact hv)
  have h2 : w i = a := by
    apply huniq
    show g (Function.update v i (w i)) = 0
    have : Function.update v i (w i) = w := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact h j hj
    rw [this]; exact hw
  rw [h1, h2]

/-- Combinatorial core: propagation of agreement from the staircase. -/
theorem hooftb0c6_comb (A : ℤ → ℤ → ℤ → Prop)
    (h13_1 : ∀ i j k, A i j k → A (i+1) j (k+1) → A i j (k+1) → A (i+1) j k)
    (h12_2 : ∀ i j k, A i j k → A (i+1) j k → A i (j+1) k → A (i+1) (j+1) k)
    (h13_3 : ∀ i j k, A i j k → A (i+1) j k → A (i+1) j (k+1) → A i j (k+1))
    (h12_0 : ∀ i j k, A (i+1) j k → A (i+1) (j+1) k → A i (j+1) k → A i j k)
    (h23_2 : ∀ i j k, A i j k → A i (j+1) k → A i j (k+1) → A i (j+1) (k+1))
    (h23_0 : ∀ i j k, A i (j+1) k → A i (j+1) (k+1) → A i j (k+1) → A i j k)
    (hst : ∀ m, A m (-m) m ∧ A (m+1) (-m) m ∧ A (m+1) (-m-1) m) :
    ∀ i j k, A i j k := by
  let R : ℤ → Prop := fun a => ∀ i j k, j + k = -1 → i - k = a → A i j k
  let S : ℤ → Prop := fun a => ∀ i j k, j + k = 0 → i - k = a → A i j k
  have S0 : S 0 := by
    intro i j k h1 h2
    obtain rfl : i = k := by omega
    obtain rfl : j = -i := by omega
    exact (hst i).1
  have S1 : S 1 := by
    intro i j k h1 h2
    obtain rfl : i = k + 1 := by omega
    obtain rfl : j = -k := by omega
    exact (hst k).2.1
  have R1 : R 1 := by
    intro i j k h1 h2
    obtain rfl : i = k + 1 := by omega
    obtain rfl : j = -k - 1 := by omega
    exact (hst k).2.2
  -- upward step
  have up : ∀ a, R a → S a → S (a-1) → R (a+1) ∧ S (a+1) ∧ S a := by
    intro a hR hS hS'
    have hR1 : R (a+1) := by
      intro i j k h1 h2
      have := h13_1 (i-1) j k (hR _ _ _ (by omega) (by omega))
        (hS _ _ _ (by omega) (by omega)) (hS' _ _ _ (by omega) (by omega))
      simpa using this
    refine ⟨hR1, ?_, hS⟩
    intro i j k h1 h2
    have := h12_2 (i-1) (j-1) k (hR _ _ _ (by omega) (by omega))
      (hR1 _ _ _ (by omega) (by omega)) (hS _ _ _ (by omega) (by omega))
    simpa using this
  -- downward step
  have down : ∀ a, R a → R (a+1) → S a → R (a-1) ∧ R a ∧ S (a-1) := by
    intro a hR hR1 hS
    have hS' : S (a-1) := by
      intro i j k h1 h2
      have := h13_3 i j (k-1) (hR _ _ _ (by omega) (by omega))
        (hR1 _ _ _ (by omega) (by omega)) (hS _ _ _ (by omega) (by omega))
      simpa using this
    refine ⟨?_, hR, hS'⟩
    intro i j k h1 h2
    exact h12_0 i j k (hR _ _ _ (by omega) (by omega))
      (hS _ _ _ (by omega) (by omega)) (hS' _ _ _ (by omega) (by omega))
  have R0 : R 0 := by
    intro i j k h1 h2
    exact h12_0 i j k (R1 _ _ _ (by omega) (by omega))
      (S1 _ _ _ (by omega) (by omega)) (S0 _ _ _ (by omega) (by omega))
  have UP : ∀ n : ℕ, R (1 + n) ∧ S (1 + n) ∧ S n := by
    intro n
    induction n with
    | zero => simpa using ⟨R1, S1, S0⟩
    | succ n ih =>
      have := up _ ih.1 ih.2.1 (by simpa using ih.2.2)
      push_cast
      refine ⟨by simpa [add_assoc] using this.1, by simpa [add_assoc] using this.2.1,
        by simpa [add_comm] using this.2.2⟩
  have DN : ∀ n : ℕ, R (-n) ∧ R (-n + 1) ∧ S (-n) := by
    intro n
    induction n with
    | zero => simpa using ⟨R0, R1, S0⟩
    | succ n ih =>
      have := down _ ih.1 ih.2.1 ih.2.2
      push_cast
      refine ⟨by simpa [sub_eq_add_neg, add_comm] using this.1, ?_, ?_⟩
      · have h := this.2.1
        have e : -((n:ℤ) + 1) + 1 = -(n:ℤ) := by ring
        rw [e]; exact h
      · simpa [sub_eq_add_neg, add_comm] using this.2.2
  have Rall : ∀ a, R a := by
    intro a
    rcases le_or_gt 1 a with h | h
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n:ℤ) = a - 1 := ⟨(a-1).toNat, by omega⟩
      have := (UP n).1
      rw [hn] at this; simpa using this
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n:ℤ) = -a := ⟨(-a).toNat, by omega⟩
      have := (DN n).1
      rw [hn] at this; simpa using this
  have Sall : ∀ a, S a := by
    intro a
    rcases le_or_gt 0 a with h | h
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n:ℤ) = a := ⟨a.toNat, by omega⟩
      have := (UP n).2.2
      rw [hn] at this; exact this
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n:ℤ) = -a := ⟨(-a).toNat, by omega⟩
      have := (DN n).2.2
      rw [hn] at this; simpa using this
  -- stage 3: levels
  let P : ℤ → Prop := fun t => ∀ i j k, j + k = t → A i j k
  have Pm1 : P (-1) := fun i j k h => Rall (i - k) i j k h rfl
  have P0 : P 0 := fun i j k h => Sall (i - k) i j k h rfl
  have pup : ∀ t, P t → P (t+1) → P (t+2) := by
    intro t h0 h1 i j k h
    have := h23_2 i (j-1) (k-1) (h0 _ _ _ (by omega)) (h1 _ _ _ (by omega))
      (h1 _ _ _ (by omega))
    simpa using this
  have pdn : ∀ t, P t → P (t+1) → P (t-1) := by
    intro t h0 h1 i j k h
    exact h23_0 i j k (h0 _ _ _ (by omega)) (h1 _ _ _ (by omega)) (h0 _ _ _ (by omega))
  have PU : ∀ n : ℕ, P (n - 1) ∧ P n := by
    intro n
    induction n with
    | zero => simpa using ⟨Pm1, P0⟩
    | succ n ih =>
      have := pup _ ih.1 (by simpa using ih.2)
      push_cast
      refine ⟨by simpa using ih.2, ?_⟩
      have e : (n:ℤ) - 1 + 2 = n + 1 := by ring
      rw [e] at this; exact this
  have PD : ∀ n : ℕ, P (-n - 1) ∧ P (-n) := by
    intro n
    induction n with
    | zero => simpa using ⟨Pm1, P0⟩
    | succ n ih =>
      have := pdn _ ih.1 (by simpa using ih.2)
      push_cast
      refine ⟨?_, ?_⟩
      · have e : -(n:ℤ) - 1 - 1 = -((n:ℤ) + 1) - 1 := by ring
        rw [e] at this; exact this
      · have e : -(n:ℤ) - 1 = -((n:ℤ) + 1) := by ring
        rw [← e]; exact ih.1
  intro i j k
  rcases le_or_gt 0 (j + k) with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n:ℤ) = j + k := ⟨(j+k).toNat, by omega⟩
    exact (PU n).2 i j k hn.symm
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n:ℤ) = -(j + k) := ⟨(-(j+k)).toNat, by omega⟩
    exact (PD n).2 i j k (by omega)

open HooftDimReduction in
theorem hooftb0c6_stair (x₀ : Site) (m : ℤ) :
    staircase x₀ (3*m) = x₀ + (m, -m, m) ∧
    staircase x₀ (3*m+1) = x₀ + (m+1, -m, m) ∧
    staircase x₀ (3*m+2) = x₀ + (m+1, -m-1, m) := by
  have a0 : (3*m)/3 = m := by omega
  have a1 : (3*m+1)/3 = m := by omega
  have a2 : (3*m+2)/3 = m := by omega
  have b0 : (3*m)%3 = 0 := by omega
  have b1 : (3*m+1)%3 = 1 := by omega
  have b2 : (3*m+2)%3 = 2 := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [staircase, a0, a1, a2, b0, b1, b2, e1, e2, e3] <;>
    ext <;> simp <;> ring

open HooftDimReduction in
theorem hooftb0c6_corner (x₀ : Site) (i j k : ℤ) :
    plaquette (x₀ + (i, j, k)) .p12 =
      ![x₀ + (i, j, k), x₀ + (i+1, j, k), x₀ + (i+1, j+1, k), x₀ + (i, j+1, k)] ∧
    plaquette (x₀ + (i, j, k)) .p13 =
      ![x₀ + (i, j, k), x₀ + (i+1, j, k), x₀ + (i+1, j, k+1), x₀ + (i, j, k+1)] ∧
    plaquette (x₀ + (i, j, k)) .p23 =
      ![x₀ + (i, j, k), x₀ + (i, j+1, k), x₀ + (i, j+1, k+1), x₀ + (i, j, k+1)] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext m <;> fin_cases m <;>
    simp [plaquette, Plane.dirs, e1, e2, e3, add_assoc]

open HooftDimReduction in
theorem solution (p : ℕ) (g : Site → Plane → (Fin 4 → ZMod p) → ZMod p)
    (hg : ∀ x P, IsPlaquetteRule (g x P)) (x₀ : Site) (f f' : Site → ZMod p)
    (hf : SatisfiesRules g f) (hf' : SatisfiesRules g f')
    (hstair : ∀ n : ℤ, f (staircase x₀ n) = f' (staircase x₀ n)) :
    f = f' := by
  have key : ∀ (x : Site) (P : Plane) (i : Fin 4),
      (∀ j, j ≠ i → f (plaquette x P j) = f' (plaquette x P j)) →
        f (plaquette x P i) = f' (plaquette x P i) := fun x P i h =>
    hooftb0c6_uniq (hg x P) i (fun j => f (plaquette x P j)) (fun j => f' (plaquette x P j))
      h (hf x P) (hf' x P)
  have hA := hooftb0c6_comb (fun i j k => f (x₀ + (i, j, k)) = f' (x₀ + (i, j, k)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext y
    have := hA (y.1 - x₀.1) (y.2.1 - x₀.2.1) (y.2.2 - x₀.2.2)
    have e : x₀ + (y.1 - x₀.1, y.2.1 - x₀.2.1, y.2.2 - x₀.2.2) = y := by
      ext <;> simp
    simp only [e] at this
    exact this
  · intro i j k h0 h2 h3
    have hc := (hooftb0c6_corner x₀ i j k).2.1
    have := key (x₀ + (i, j, k)) .p13 1 (by intro m hm; fin_cases m <;> simp_all)
    simpa [hc] using this
  · intro i j k h0 h1 h3
    have hc := (hooftb0c6_corner x₀ i j k).1
    have := key (x₀ + (i, j, k)) .p12 2 (by intro m hm; fin_cases m <;> simp_all)
    simpa [hc] using this
  · intro i j k h0 h1 h2
    have hc := (hooftb0c6_corner x₀ i j k).2.1
    have := key (x₀ + (i, j, k)) .p13 3 (by intro m hm; fin_cases m <;> simp_all)
    simpa [hc] using this
  · intro i j k h1 h2 h3
    have hc := (hooftb0c6_corner x₀ i j k).1
    have := key (x₀ + (i, j, k)) .p12 0 (by intro m hm; fin_cases m <;> simp_all)
    simpa [hc] using this
  · intro i j k h0 h1 h3
    have hc := (hooftb0c6_corner x₀ i j k).2.2
    have := key (x₀ + (i, j, k)) .p23 2 (by intro m hm; fin_cases m <;> simp_all)
    simpa [hc] using this
  · intro i j k h1 h2 h3
    have hc := (hooftb0c6_corner x₀ i j k).2.2
    have := key (x₀ + (i, j, k)) .p23 0 (by intro m hm; fin_cases m <;> simp_all)
    simpa [hc] using this
  · intro m
    have hs := hooftb0c6_stair x₀ m
    refine ⟨?_, ?_, ?_⟩
    · have := hstair (3*m); rw [hs.1] at this; exact this
    · have := hstair (3*m+1); rw [hs.2.1] at this; exact this
    · have := hstair (3*m+2); rw [hs.2.2] at this; exact this
