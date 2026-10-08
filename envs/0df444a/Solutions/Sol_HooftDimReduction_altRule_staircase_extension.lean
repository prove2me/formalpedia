-- Prove2me | solution 1 for HooftDimReduction.altRule_staircase_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:37:37.063457+00:00
-- url     : https://prove2.me/submissions/bd0aaa5a-0412-4b32-aa66-70ceb5dd5cee

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

set_option autoImplicit false

namespace HooftAltAux
open HooftDimReduction

/-- A partial-sum function on `ℤ`: `psum d 0 = 0`, `psum d (k+1) = psum d k + d k`. -/
def psum {G : Type*} [AddCommGroup G] (d : ℤ → G) : ℤ → G
  | Int.ofNat n => ∑ i ∈ Finset.range n, d (i : ℤ)
  | Int.negSucc n => -∑ i ∈ Finset.range (n + 1), d (-((i : ℤ) + 1))

lemma psum_zero {G : Type*} [AddCommGroup G] (d : ℤ → G) : psum d 0 = 0 := by
  show psum d (Int.ofNat 0) = 0
  simp [psum]

lemma psum_succ {G : Type*} [AddCommGroup G] (d : ℤ → G) (k : ℤ) :
    psum d (k + 1) = psum d k + d k := by
  rcases k with n | n
  · show psum d (Int.ofNat (n + 1)) = psum d (Int.ofNat n) + d (Int.ofNat n)
    simp only [psum, Finset.sum_range_succ]
    rfl
  · rcases n with _ | m
    · show psum d (Int.ofNat 0) = psum d (Int.negSucc 0) + d (Int.negSucc 0)
      simp [psum, Int.negSucc_eq]
    · show psum d (Int.negSucc m) = psum d (Int.negSucc (m + 1)) + d (Int.negSucc (m + 1))
      simp only [psum]
      rw [Finset.sum_range_succ (n := m + 1), Int.negSucc_eq]
      push_cast
      abel

lemma const_of_succ {G : Type*} (F : ℤ → G) (h : ∀ t, F (t + 1) = F t) :
    ∀ t, F t = F 0 := by
  intro t
  refine Int.induction_on t rfl ?_ ?_
  · intro i ih
    rw [h, ih]
  · intro i ih
    rw [← ih, ← h (-(i : ℤ) - 1)]
    congr 1
    ring

lemma const_of_succ' {G : Type*} (F : ℤ → G) (h : ∀ t, F (t + 1) = F t) (s t : ℤ) :
    F s = F t := by
  rw [const_of_succ F h s, const_of_succ F h t]

lemma st0 (a0 b0 c0 m : ℤ) :
    staircase (a0, b0, c0) (3 * m) = (a0 + m, b0 - m, c0 + m) := by
  have h1 : (3 * m) / 3 = m := by omega
  have h2 : (3 * m) % 3 = 0 := by omega
  simp only [staircase, h1, h2, if_true, e1, e2, e3]
  ext <;> simp <;> ring

lemma st1 (a0 b0 c0 m : ℤ) :
    staircase (a0, b0, c0) (3 * m + 1) = (a0 + m + 1, b0 - m, c0 + m) := by
  have h1 : (3 * m + 1) / 3 = m := by omega
  have h2 : (3 * m + 1) % 3 = 1 := by omega
  simp only [staircase, h1, h2, e1, e2, e3]
  ext <;> simp <;> ring

lemma st2 (a0 b0 c0 m : ℤ) :
    staircase (a0, b0, c0) (3 * m + 2) = (a0 + m + 1, b0 - m - 1, c0 + m) := by
  have h1 : (3 * m + 2) / 3 = m := by omega
  have h2 : (3 * m + 2) % 3 = 2 := by omega
  simp only [staircase, h1, h2, e1, e2, e3]
  ext <;> simp <;> ring

lemma rules_iff {p : ℕ} (f : Site → ZMod p) :
    SatisfiesRules (fun _ _ => altRule) f ↔
      ∀ a b c : ℤ,
        f (a, b, c) - f (a + 1, b, c) + f (a + 1, b + 1, c) - f (a, b + 1, c) = 0 ∧
        f (a, b, c) - f (a + 1, b, c) + f (a + 1, b, c + 1) - f (a, b, c + 1) = 0 ∧
        f (a, b, c) - f (a, b + 1, c) + f (a, b + 1, c + 1) - f (a, b, c + 1) = 0 := by
  constructor
  · intro h a b c
    refine ⟨?_, ?_, ?_⟩
    · have := h (a, b, c) .p12
      simpa [altRule, plaquette, Plane.dirs, e1, e2, e3] using this
    · have := h (a, b, c) .p13
      simpa [altRule, plaquette, Plane.dirs, e1, e2, e3] using this
    · have := h (a, b, c) .p23
      simpa [altRule, plaquette, Plane.dirs, e1, e2, e3] using this
  · intro h x P
    obtain ⟨a, b, c⟩ := x
    obtain ⟨h1, h2, h3⟩ := h a b c
    cases P
    · simpa [altRule, plaquette, Plane.dirs, e1, e2, e3] using h1
    · simpa [altRule, plaquette, Plane.dirs, e1, e2, e3] using h2
    · simpa [altRule, plaquette, Plane.dirs, e1, e2, e3] using h3

lemma unique_zero {p : ℕ} (a0 b0 c0 : ℤ) (h : Site → ZMod p)
    (hr : SatisfiesRules (fun _ _ => altRule) h)
    (hs : ∀ n : ℤ, h (staircase (a0, b0, c0) n) = 0) : ∀ y, h y = 0 := by
  rw [rules_iff] at hr
  -- staircase values
  have s0 : ∀ m, h (a0 + m, b0 - m, c0 + m) = 0 := fun m => by
    rw [← st0]; exact hs _
  have s1 : ∀ m, h (a0 + m + 1, b0 - m, c0 + m) = 0 := fun m => by
    rw [← st1]; exact hs _
  have s2 : ∀ m, h (a0 + m + 1, b0 - m - 1, c0 + m) = 0 := fun m => by
    rw [← st2]; exact hs _
  have s3 : ∀ m, h (a0 + m + 1, b0 - m - 1, c0 + m + 1) = 0 := fun m => by
    have := s0 (m + 1)
    have e : (a0 + (m + 1), b0 - (m + 1), c0 + (m + 1)) =
        (a0 + m + 1, b0 - m - 1, c0 + m + 1) := by ext <;> simp <;> ring
    rw [e] at this; exact this
  -- D1 = 0
  have D1 : ∀ a b c, h (a + 1, b, c) = h (a, b, c) := by
    intro a b c
    have inv : ∀ b c b' c', h (a + 1, b, c) - h (a, b, c) = h (a + 1, b', c') - h (a, b', c') := by
      intro b c b' c'
      have hb : ∀ c, ∀ b b', h (a + 1, b, c) - h (a, b, c) = h (a + 1, b', c) - h (a, b', c) :=
        fun c => const_of_succ' (fun b => h (a + 1, b, c) - h (a, b, c)) (fun t => by
          have := (hr a t c).1
          linear_combination this)
      have hc : ∀ b, ∀ c c', h (a + 1, b, c) - h (a, b, c) = h (a + 1, b, c') - h (a, b, c') :=
        fun b => const_of_succ' (fun c => h (a + 1, b, c) - h (a, b, c)) (fun t => by
          have := (hr a b t).2.1
          linear_combination this)
      rw [hb c b b', hc b' c c']
    have := inv b c (b0 - (a - a0)) (c0 + (a - a0))
    have e1' := s0 (a - a0)
    have e2' := s1 (a - a0)
    have ea : a0 + (a - a0) = a := by ring
    rw [ea] at e1' e2'
    rw [← sub_eq_zero, this, e1', e2', sub_zero]
  have D2 : ∀ a b c, h (a, b + 1, c) = h (a, b, c) := by
    intro a b c
    have hb : ∀ c, ∀ a a', h (a, b + 1, c) - h (a, b, c) = h (a', b + 1, c) - h (a', b, c) :=
      fun c => const_of_succ' (fun a => h (a, b + 1, c) - h (a, b, c)) (fun t => by
        have := (hr t b c).1
        linear_combination this)
    have hc : ∀ a, ∀ c c', h (a, b + 1, c) - h (a, b, c) = h (a, b + 1, c') - h (a, b, c') :=
      fun a => const_of_succ' (fun c => h (a, b + 1, c) - h (a, b, c)) (fun t => by
        have := (hr a b t).2.2
        linear_combination this)
    have m := b0 - b - 1
    have e1' := s1 (b0 - b - 1)
    have e2' := s2 (b0 - b - 1)
    have eb1 : b0 - (b0 - b - 1) = b + 1 := by ring
    have eb2 : b0 - (b0 - b - 1) - 1 = b := by ring
    rw [eb1] at e1'
    rw [eb2] at e2'
    rw [← sub_eq_zero, hb c a (a0 + (b0 - b - 1) + 1), hc _ c (c0 + (b0 - b - 1)), e1', e2',
      sub_zero]
  have D3 : ∀ a b c, h (a, b, c + 1) = h (a, b, c) := by
    intro a b c
    have hb : ∀ b, ∀ a a', h (a, b, c + 1) - h (a, b, c) = h (a', b, c + 1) - h (a', b, c) :=
      fun b => const_of_succ' (fun a => h (a, b, c + 1) - h (a, b, c)) (fun t => by
        have := (hr t b c).2.1
        linear_combination this)
    have hc : ∀ a, ∀ b b', h (a, b, c + 1) - h (a, b, c) = h (a, b', c + 1) - h (a, b', c) :=
      fun a => const_of_succ' (fun b => h (a, b, c + 1) - h (a, b, c)) (fun t => by
        have := (hr a t c).2.2
        linear_combination this)
    have e1' := s2 (c - c0)
    have e2' := s3 (c - c0)
    have ec : c0 + (c - c0) = c := by ring
    rw [ec] at e1' e2'
    rw [← sub_eq_zero, hb b a (a0 + (c - c0) + 1), hc _ b (b0 - (c - c0) - 1), e1', e2',
      sub_zero]
  intro y
  obtain ⟨a, b, c⟩ := y
  have ha := const_of_succ' (fun a => h (a, b, c)) (fun t => D1 t b c) a a0
  have hb := const_of_succ' (fun b => h (a0, b, c)) (fun t => D2 a0 t c) b b0
  have hc := const_of_succ' (fun c => h (a0, b0, c)) (fun t => D3 a0 b0 t) c c0
  have h0 := s0 0
  simp only [add_zero, sub_zero] at h0
  rw [ha, hb, hc, h0]

end HooftAltAux

open HooftDimReduction in
theorem solution (p : ℕ) (x₀ : Site) (φ : ℤ → ZMod p) :
    ∃! f : Site → ZMod p,
      SatisfiesRules (fun _ _ => altRule) f ∧ ∀ n : ℤ, f (staircase x₀ n) = φ n := by
  obtain ⟨a0, b0, c0⟩ := x₀
  set P1 := HooftAltAux.psum (fun m => φ (3 * m + 1) - φ (3 * m)) with hP1
  set P2 := HooftAltAux.psum (fun m => φ (3 * m + 2) - φ (3 * m + 1)) with hP2
  set P3 := HooftAltAux.psum (fun m => φ (3 * m + 3) - φ (3 * m + 2)) with hP3
  have Q : ∀ m, φ 0 + P1 m + P2 m + P3 m = φ (3 * m) := by
    have := HooftAltAux.const_of_succ (fun m => φ 0 + P1 m + P2 m + P3 m - φ (3 * m)) (by
      intro t
      simp only [hP1, hP2, hP3, HooftAltAux.psum_succ]
      have : (3 * (t + 1)) = 3 * t + 3 := by ring
      rw [this]
      ring)
    intro m
    have hm := this m
    simp only [hP1, hP2, hP3, HooftAltAux.psum_zero, mul_zero] at hm
    rw [← sub_eq_zero, hm]
    ring
  have hFs : ∀ n : ℤ, (fun y : Site => φ 0 + P1 (y.1 - a0) + P2 (b0 - y.2.1) + P3 (y.2.2 - c0))
      (staircase (a0, b0, c0) n) = φ n := by
    intro n
    have hn : n = 3 * (n / 3) + n % 3 := by omega
    have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    set m := n / 3
    rcases hr with hr | hr | hr
    · rw [hr, add_zero] at hn
      rw [hn, HooftAltAux.st0]
      simp only
      rw [← Q m]
      ring_nf
    · rw [hr] at hn
      rw [hn, HooftAltAux.st1]
      simp only
      have e1 : a0 + m + 1 - a0 = m + 1 := by ring
      have e2 : b0 - (b0 - m) = m := by ring
      have e3 : c0 + m - c0 = m := by ring
      rw [e1, e2, e3, hP1, HooftAltAux.psum_succ, ← hP1, ← Q m]
      ring
    · rw [hr] at hn
      rw [hn, HooftAltAux.st2]
      simp only
      have e1 : a0 + m + 1 - a0 = m + 1 := by ring
      have e2 : b0 - (b0 - m - 1) = m + 1 := by ring
      have e3 : c0 + m - c0 = m := by ring
      rw [e1, e2, e3, hP1, HooftAltAux.psum_succ, ← hP1, hP2, HooftAltAux.psum_succ, ← hP2,
        ← Q m]
      ring
  refine ⟨fun y => φ 0 + P1 (y.1 - a0) + P2 (b0 - y.2.1) + P3 (y.2.2 - c0), ⟨?_, hFs⟩, ?_⟩
  · rw [HooftAltAux.rules_iff]
    intro a b c
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · rintro g ⟨hg, hgs⟩
    have hd := HooftAltAux.unique_zero a0 b0 c0
      (fun y => g y - (φ 0 + P1 (y.1 - a0) + P2 (b0 - y.2.1) + P3 (y.2.2 - c0))) ?_ ?_
    · funext y
      have := hd y
      exact sub_eq_zero.mp this
    · rw [HooftAltAux.rules_iff] at hg ⊢
      intro a b c
      obtain ⟨h1, h2, h3⟩ := hg a b c
      refine ⟨?_, ?_, ?_⟩
      · simp only; linear_combination h1
      · simp only; linear_combination h2
      · simp only; linear_combination h3
    · intro n
      rw [hgs n, ← hFs n, sub_self]
