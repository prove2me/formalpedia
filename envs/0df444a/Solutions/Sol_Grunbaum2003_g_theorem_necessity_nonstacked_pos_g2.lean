-- Prove2me | solution 1 for Grunbaum2003.g_theorem_necessity_nonstacked_pos_g2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T09:45:35.422789+00:00
-- url     : https://prove2.me/submissions/e2ba7273-67d6-40fa-a864-5b829c52c93f

import Mathlib
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix

-- ==== from f9336347_c1b.lean
set_option autoImplicit false
open scoped BigOperators

namespace GF93M

/-! ### Macaulay shadow function `Phi` and the arithmetic step (function form of `MacArith`).
`Phi (k+1) x` is the shadow value of the `(k+1)`-binomial (Macaulay) expansion of `x`;
`Phi 0 = 0`. -/

theorem lt_choose_bound (x j : ℕ) : x < Nat.choose (x + j + 1) (j + 1) := by
  induction x with
  | zero => simp
  | succ x ih =>
    have h1 : 0 < Nat.choose (x + j + 1) j := Nat.choose_pos (by omega)
    have h2 : Nat.choose (x + 1 + j + 1) (j + 1) =
        Nat.choose (x + j + 1) j + Nat.choose (x + j + 1) (j + 1) := by
      rw [show x + 1 + j + 1 = (x + j + 1) + 1 by ring]; exact Nat.choose_succ_succ' _ _
    omega

/-- `top j x`: the greatest `a` with `C(a, j+1) ≤ x`. -/
def top (j x : ℕ) : ℕ := Nat.findGreatest (fun a => Nat.choose a (j + 1) ≤ x) (x + j + 1)

theorem top_spec (j x : ℕ) :
    Nat.choose (top j x) (j + 1) ≤ x ∧ x < Nat.choose (top j x + 1) (j + 1) := by
  have hP : Nat.choose (top j x) (j + 1) ≤ x :=
    Nat.findGreatest_spec (P := fun a => Nat.choose a (j + 1) ≤ x) (Nat.zero_le _) (by simp)
  refine ⟨hP, ?_⟩
  by_contra h
  push_neg at h
  have hle : top j x ≤ x + j + 1 := Nat.findGreatest_le _
  rcases Nat.lt_or_ge (top j x) (x + j + 1) with hlt | hge
  · exact Nat.findGreatest_is_greatest (P := fun a => Nat.choose a (j + 1) ≤ x)
      (n := x + j + 1) (k := top j x + 1) (Nat.lt_succ_self _) (by omega) h
  · have : top j x = x + j + 1 := le_antisymm hle hge
    rw [this] at hP
    have := lt_choose_bound x j
    omega

theorem top_eq (j x a : ℕ) (h1 : Nat.choose a (j + 1) ≤ x) (h2 : x < Nat.choose (a + 1) (j + 1)) :
    top j x = a := by
  obtain ⟨t1, t2⟩ := top_spec j x
  rcases lt_trichotomy (top j x) a with h | h | h
  · have := Nat.choose_le_choose (j + 1) (show top j x + 1 ≤ a by omega); omega
  · exact h
  · have := Nat.choose_le_choose (j + 1) (show a + 1 ≤ top j x by omega); omega

theorem top_ge (j x : ℕ) (hx : 0 < x) : j + 1 ≤ top j x := by
  obtain ⟨-, t2⟩ := top_spec j x
  by_contra h
  push_neg at h
  rcases Nat.lt_or_ge (top j x + 1) (j + 1) with h' | h'
  · rw [Nat.choose_eq_zero_of_lt h'] at t2; omega
  · have : top j x + 1 = j + 1 := by omega
    rw [this, Nat.choose_self] at t2; omega

def Phi : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, x => if x = 0 then 0 else
      Nat.choose (top j x - 1) j + Phi j (x - Nat.choose (top j x) (j + 1))

theorem Phi_zero (j : ℕ) : Phi j 0 = 0 := by cases j <;> simp [Phi]

theorem Phi_succ (j x : ℕ) (hx : x ≠ 0) :
    Phi (j + 1) x = Nat.choose (top j x - 1) j + Phi j (x - Nat.choose (top j x) (j + 1)) := by
  rw [Phi, if_neg hx]

theorem Phi_rep (j x : ℕ) (hx : 0 < x) : ∃ c r, x = Nat.choose (c + 1) (j + 1) + r ∧
    r < Nat.choose (c + 1) j ∧ j ≤ c ∧ Phi (j + 1) x = Nat.choose c j + Phi j r := by
  obtain ⟨t1, t2⟩ := top_spec j x
  have ha := top_ge j x hx
  refine ⟨top j x - 1, x - Nat.choose (top j x) (j + 1), ?_, ?_, by omega, ?_⟩
  · rw [Nat.sub_add_cancel (by omega : 1 ≤ top j x)]; omega
  · rw [Nat.sub_add_cancel (by omega : 1 ≤ top j x)]
    have := Nat.choose_succ_succ' (top j x) j; omega
  · exact Phi_succ j x (by omega)

theorem Phi_decomp (j c z : ℕ) (hz : z < Nat.choose (c + 1) j)
    (hpos : 0 < Nat.choose (c + 1) (j + 1) + z) :
    Phi (j + 1) (Nat.choose (c + 1) (j + 1) + z) = Nat.choose c j + Phi j z := by
  have hc : Nat.choose (c + 1 + 1) (j + 1) = Nat.choose (c + 1) j + Nat.choose (c + 1) (j + 1) :=
    Nat.choose_succ_succ' (c + 1) j
  have ht : top j (Nat.choose (c + 1) (j + 1) + z) = c + 1 :=
    top_eq j _ (c + 1) (Nat.le_add_right _ _) (by omega)
  rw [Phi_succ j _ (by omega), ht, Nat.add_sub_cancel, Nat.add_sub_cancel_left]

theorem Phi_choose (j c : ℕ) (hc : j ≤ c) :
    Phi (j + 1) (Nat.choose (c + 1) (j + 1)) = Nat.choose c j := by
  have h1 : 0 < Nat.choose (c + 1) j := Nat.choose_pos (by omega)
  have h2 : 0 < Nat.choose (c + 1) (j + 1) := Nat.choose_pos (by omega)
  have := Phi_decomp j c 0 h1 (by omega)
  rwa [Nat.add_zero, Phi_zero, Nat.add_zero] at this

theorem sub_bound (j : ℕ) (hmono : ∀ x x', x ≤ x' → Phi j x ≤ Phi j x') (c r : ℕ) (hc : j ≤ c)
    (hr : r < Nat.choose (c + 1) j) : Nat.choose c j + Phi j r ≤ Nat.choose (c + 1) j := by
  cases j with
  | zero => simp [Phi]
  | succ j =>
    have h1 := hmono r (Nat.choose (c + 1) (j + 1)) hr.le
    rw [Phi_choose j c (by omega)] at h1
    have h2 := Nat.choose_succ_succ' c j
    omega

theorem Phi_mono (j : ℕ) : ∀ x x', x ≤ x' → Phi j x ≤ Phi j x' := by
  induction j with
  | zero => intro x x' _; simp [Phi]
  | succ j ih =>
    intro x x' hxx
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx; simp [Phi_zero]
    obtain ⟨c, r, hxr, hr, hjc, hP⟩ := Phi_rep j x hx
    obtain ⟨c', r', hxr', hr', hjc', hP'⟩ := Phi_rep j x' (by omega)
    rw [hP, hP']
    have pc' := Nat.choose_succ_succ' (c' + 1) j
    have hle : c ≤ c' := by
      by_contra h; push_neg at h
      have := Nat.choose_le_choose (j + 1) (show c' + 1 + 1 ≤ c + 1 by omega); omega
    rcases Nat.lt_or_ge c c' with hlt | hge
    · have hb := sub_bound j ih c r hjc hr
      have hm : Nat.choose (c + 1) j ≤ Nat.choose c' j := Nat.choose_le_choose j (by omega)
      omega
    · have heq : c = c' := le_antisymm hle hge
      subst heq
      have := ih r r' (by omega)
      omega

theorem Phi_le (j x : ℕ) : Phi j x ≤ x := by
  induction j generalizing x with
  | zero => simp [Phi]
  | succ j ih =>
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx; simp [Phi_zero]
    obtain ⟨c, r, hxr, hr, hjc, hP⟩ := Phi_rep j x hx
    have := ih r
    have pc := Nat.choose_succ_succ' c j
    omega

theorem Phi_pos (j x : ℕ) (hx : 0 < x) : 0 < Phi (j + 1) x := by
  obtain ⟨c, r, -, -, hjc, hP⟩ := Phi_rep j x hx
  have := Nat.choose_pos hjc
  omega

theorem gap (j : ℕ) : ∀ c w, j ≤ c → w < Nat.choose (c + 1) j → w < Nat.choose c j + Phi j w := by
  induction j with
  | zero =>
    intro c w _ hw
    simp only [Nat.choose_zero_right] at hw ⊢
    omega
  | succ j ih =>
    intro c w hc hw
    have pc := Nat.choose_succ_succ' c j
    rcases Nat.lt_or_ge w (Nat.choose c (j + 1)) with h | h
    · omega
    · obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
      obtain ⟨w', rfl⟩ := Nat.exists_eq_add_of_le h
      have hw' : w' < Nat.choose (e + 1) j := by omega
      have hpos : 0 < Nat.choose (e + 1) (j + 1) := Nat.choose_pos (by omega)
      rw [Phi_decomp j e w' hw' (by omega)]
      have := ih e w' (by omega) hw'
      omega

theorem macStep (k : ℕ)
    (ih : ∀ k', k = k' + 1 → ∀ x0 y, Phi (k' + 1) x0 + Phi k' y ≤ y → Phi (k' + 1) (x0 + y) ≤ y)
    (x0 y : ℕ) (h : Phi (k + 1) x0 + Phi k y ≤ y) : Phi (k + 1) (x0 + y) ≤ y := by
  by_contra hgt
  push_neg at hgt
  have hx : 0 < x0 + y := by
    rcases Nat.eq_zero_or_pos (x0 + y) with h0 | h0
    · rw [h0, Phi_zero] at hgt; omega
    · exact h0
  obtain ⟨c, r, hxr, hr, hkc, hP⟩ := Phi_rep k (x0 + y) hx
  rw [hP] at hgt
  have pc := Nat.choose_succ_succ' c k
  rcases Nat.lt_or_ge y (Nat.choose c k) with hy | hy
  · rcases Nat.lt_or_ge k c with hkc' | hkc'
    · obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      have h1 := Phi_mono (k + 1) (Nat.choose (d + 1) (k + 1)) x0 (by omega)
      rw [Phi_choose k d (by omega)] at h1
      have h2 := gap k d y (by omega) hy
      omega
    · have hck : c = k := le_antisymm hkc' hkc
      have hy0 : y = 0 := by rw [hck, Nat.choose_self] at hy; omega
      have := Phi_pos k x0 (by omega)
      omega
  · have hsb := sub_bound k (Phi_mono k) c r hkc hr
    have hle3 := Phi_le k r
    cases k with
    | zero =>
      simp only [Phi, Nat.choose_zero_right] at hgt hy
      omega
    | succ k =>
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      have pk := Nat.choose_succ_succ' (d + 1) k
      have pd := Nat.choose_succ_succ' d k
      obtain ⟨y', rfl⟩ := Nat.exists_eq_add_of_le hy
      have hy'lt : y' < Nat.choose (d + 1) k := by omega
      have hpos : 0 < Nat.choose (d + 1) (k + 1) := Nat.choose_pos (by omega)
      rw [Phi_decomp k d y' hy'lt (by omega)] at h
      rcases Nat.lt_or_ge (r - y') (Nat.choose (d + 1) (k + 1)) with hz | hz
      · have hx0 : x0 = Nat.choose (d + 1) (k + 1 + 1) + (r - y') := by omega
        rw [hx0, Phi_decomp (k + 1) d (r - y') hz (by omega)] at h
        have hih := ih k rfl (r - y') y'
        have hr' : r - y' + y' = r := by omega
        rw [hr'] at hih
        have hih2 : ¬ (Phi (k + 1) (r - y') + Phi k y' ≤ y') := fun hh => absurd (hih hh) (by omega)
        omega
      · have h1 := Phi_mono (k + 1 + 1) (Nat.choose (d + 1 + 1) (k + 1 + 1)) x0 (by omega)
        rw [Phi_choose (k + 1) (d + 1) (by omega)] at h1
        have h2 := gap k d y' (by omega) hy'lt
        omega

/-- Function form of the arithmetic step `MacArith`. -/
theorem macPhi (k : ℕ) : ∀ x0 y, Phi (k + 1) x0 + Phi k y ≤ y → Phi (k + 1) (x0 + y) ≤ y := by
  induction k with
  | zero => exact macStep 0 (fun k' h => absurd h (by omega))
  | succ k ih =>
    exact macStep (k + 1) (fun k' h => by
      obtain rfl : k = k' := by omega
      exact ih)

end GF93M

set_option autoImplicit false
open scoped BigOperators

namespace GF93M

open Finsupp

/-- (duplicate of the def in f9336347_mac.lean; drop on merge) -/
noncomputable def lowerShadow {n : ℕ} (T : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  T.biUnion fun μ => (Finset.univ.filter fun v => 0 < μ v).image fun v => μ - Finsupp.single v 1

theorem mem_lowerShadow {n : ℕ} (T : Finset (Fin n →₀ ℕ)) (ν : Fin n →₀ ℕ) :
    ν ∈ lowerShadow T ↔ ∃ v, ν + single v 1 ∈ T := by
  simp only [lowerShadow, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨μ, hμ, v, hv, rfl⟩
    refine ⟨v, ?_⟩
    have hle : single v 1 ≤ μ := by rw [Finsupp.single_le_iff]; exact hv
    rwa [tsub_add_cancel_of_le hle]
  · rintro ⟨v, hv⟩
    exact ⟨_, hv, v, by simp, by simp⟩

/-- Support in the variables with index `≥ m`. -/
def Supp {n : ℕ} (m : ℕ) (T : Finset (Fin n →₀ ℕ)) : Prop :=
  ∀ μ ∈ T, ∀ v : Fin n, 0 < μ v → m ≤ v.val

/-- Strongly stable (Borel-fixed) with respect to the variables of index `≥ m`. -/
def SStab {n : ℕ} (m : ℕ) (T : Finset (Fin n →₀ ℕ)) : Prop :=
  ∀ μ ∈ T, ∀ i j : Fin n, m ≤ i.val → i < j → 0 < μ j → μ - single j 1 + single i 1 ∈ T

/-- The quotient `T : x_{v0}`. -/
noncomputable def quot {n : ℕ} (v0 : Fin n) (T : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  (T.filter fun μ => 0 < μ v0).image fun μ => μ - single v0 1

theorem mem_quot {n : ℕ} (v0 : Fin n) (T : Finset (Fin n →₀ ℕ)) (ν : Fin n →₀ ℕ) :
    ν ∈ quot v0 T ↔ ν + single v0 1 ∈ T := by
  simp only [quot, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨μ, ⟨hμ, hv⟩, rfl⟩
    have hle : single v0 1 ≤ μ := by rw [Finsupp.single_le_iff]; exact hv
    rwa [tsub_add_cancel_of_le hle]
  · intro h; exact ⟨_, ⟨h, by simp⟩, by simp⟩

theorem card_quot {n : ℕ} (v0 : Fin n) (T : Finset (Fin n →₀ ℕ)) :
    (quot v0 T).card = (T.filter fun μ => 0 < μ v0).card := by
  apply Finset.card_image_of_injOn
  intro μ hμ μ' hμ' h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hμ hμ'
  have h1 : single v0 1 ≤ μ := by rw [Finsupp.single_le_iff]; exact hμ.2
  have h2 : single v0 1 ≤ μ' := by rw [Finsupp.single_le_iff]; exact hμ'.2
  have := congrArg (· + single v0 1) h
  simp only [tsub_add_cancel_of_le h1, tsub_add_cancel_of_le h2] at this
  exact this

/-- For a strongly stable set, the lower shadow is the quotient by the first variable. -/
theorem shadow_eq_quot {n m : ℕ} (T : Finset (Fin n →₀ ℕ)) (v0 : Fin n) (hv0 : v0.val = m)
    (hsupp : Supp m T) (hss : SStab m T) : lowerShadow T = quot v0 T := by
  ext ν
  rw [mem_lowerShadow, mem_quot]
  constructor
  · rintro ⟨v, hv⟩
    by_cases hvv : v = v0
    · subst hvv; exact hv
    · have hm : m ≤ v.val := hsupp _ hv v (by simp)
      have hlt : v0 < v := by
        rw [Fin.lt_def]
        have : v.val ≠ v0.val := fun h => hvv (Fin.ext h)
        omega
      have := hss _ hv v0 v (by omega) hlt (by simp)
      simpa [add_tsub_cancel_right] using this
  · intro h; exact ⟨v0, h⟩

theorem supp_quot {n m : ℕ} (T : Finset (Fin n →₀ ℕ)) (v0 : Fin n)
    (hsupp : Supp m T) : Supp m (quot v0 T) := by
  intro ν hν v hv
  rw [mem_quot] at hν
  exact hsupp _ hν v (by simp only [Finsupp.coe_add, Pi.add_apply]; omega)

theorem sstab_quot {n m : ℕ} (T : Finset (Fin n →₀ ℕ)) (v0 : Fin n)
    (hss : SStab m T) : SStab m (quot v0 T) := by
  intro ν hν i j hi hij hj
  rw [mem_quot] at hν ⊢
  have := hss _ hν i j hi hij (by simp only [Finsupp.coe_add, Pi.add_apply]; omega)
  convert this using 1
  ext w
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> omega

theorem supp_low {n m : ℕ} (T : Finset (Fin n →₀ ℕ)) (v0 : Fin n) (hv0 : v0.val = m)
    (hsupp : Supp m T) : Supp (m + 1) (T.filter fun μ => ¬ 0 < μ v0) := by
  intro μ hμ v hv
  rw [Finset.mem_filter] at hμ
  have h1 := hsupp _ hμ.1 v hv
  have h2 : v ≠ v0 := by rintro rfl; exact hμ.2 hv
  have : v.val ≠ v0.val := fun h => h2 (Fin.ext h)
  omega

theorem sstab_low {n m : ℕ} (T : Finset (Fin n →₀ ℕ)) (v0 : Fin n) (hv0 : v0.val = m)
    (hss : SStab m T) : SStab (m + 1) (T.filter fun μ => ¬ 0 < μ v0) := by
  intro μ hμ i j hi hij hj
  rw [Finset.mem_filter] at hμ ⊢
  refine ⟨hss _ hμ.1 i j (by omega) hij hj, ?_⟩
  have hi0 : i ≠ v0 := by
    intro h; rw [h] at hi; omega
  have hj0 : j ≠ v0 := by
    intro h; rw [h] at hj; exact hμ.2 hj
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply, if_neg hi0, if_neg hj0]
  omega

theorem shadow_low_sub {n m : ℕ} (T : Finset (Fin n →₀ ℕ)) (v0 : Fin n) (hv0 : v0.val = m)
    (hsupp : Supp m T) (hss : SStab m T) :
    lowerShadow (T.filter fun μ => ¬ 0 < μ v0) ⊆
      (quot v0 T).filter fun ν => ¬ 0 < ν v0 := by
  intro ν hν
  rw [mem_lowerShadow] at hν
  obtain ⟨v, hv⟩ := hν
  rw [Finset.mem_filter] at hv ⊢
  have hT : ν ∈ lowerShadow T := (mem_lowerShadow T ν).mpr ⟨v, hv.1⟩
  rw [shadow_eq_quot T v0 hv0 hsupp hss] at hT
  refine ⟨hT, ?_⟩
  have := hv.2
  simp only [Finsupp.coe_add, Pi.add_apply] at this
  omega

theorem deg_quot {n : ℕ} (v0 : Fin n) (T : Finset (Fin n →₀ ℕ)) (k : ℕ)
    (hdeg : ∀ μ ∈ T, Finsupp.degree μ = k + 1) : ∀ ν ∈ quot v0 T, Finsupp.degree ν = k := by
  intro ν hν
  rw [mem_quot] at hν
  have := hdeg _ hν
  rw [map_add, Finsupp.degree_single] at this
  omega

/-- The numerical Macaulay lower-shadow bound, stated for every admissible expansion. -/
def LB (k x s : ℕ) : Prop :=
  ∀ (i : ℕ) (a : ℕ → ℕ), 0 < i → i ≤ k + 1 → i ≤ a i →
    (∀ r t : ℕ, i ≤ r → r < t → t ≤ k + 1 → a r < a t) →
    x = ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r →
    (∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r - 1) (r - 1)) ≤ s

/-- The arithmetic step of the Green/Macaulay induction (checked numerically for k ≤ 5, x0, y < 150). -/
def MacArith : Prop :=
  ∀ (k x0 y s0 s1 : ℕ), LB k x0 s0 → (k = 0 ∨ LB (k - 1) y s1) → s0 + s1 ≤ y →
    LB k (x0 + y) y

theorem LB_zero (k s : ℕ) : LB k 0 s := by
  intro i a hi hik hia _ hx
  exfalso
  have hpos : 0 < Nat.choose (a i) i := Nat.choose_pos hia
  have hle : Nat.choose (a i) i ≤ ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r :=
    Finset.single_le_sum (f := fun r => Nat.choose (a r) r) (fun _ _ => Nat.zero_le _)
      (Finset.mem_Icc.mpr ⟨le_rfl, hik⟩)
  omega

/-- Macaulay's bound for strongly stable sets, from the arithmetic step. -/
theorem sstab_bound (hA : MacArith) (k : ℕ) : ∀ (n : ℕ) (T : Finset (Fin n →₀ ℕ)) (m : ℕ),
    Supp m T → SStab m T → (∀ μ ∈ T, Finsupp.degree μ = k + 1) →
    LB k T.card (lowerShadow T).card := by
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro n
  suffices H : ∀ (j m : ℕ) (T : Finset (Fin n →₀ ℕ)), n - m = j → Supp m T → SStab m T →
      (∀ μ ∈ T, Finsupp.degree μ = k + 1) → LB k T.card (lowerShadow T).card by
    intro T m h1 h2 h3; exact H _ m T rfl h1 h2 h3
  intro j
  induction j with
  | zero =>
    intro m T hj hsupp _ hdeg
    have hT : T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro μ hμ
      have hne : μ ≠ 0 := by
        intro h; have := hdeg μ hμ; rw [h, map_zero] at this; omega
      obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp hne
      have hv' : 0 < μ v := by simp only [Finsupp.coe_zero, Pi.zero_apply] at hv; omega
      have := hsupp μ hμ v hv'
      have := v.isLt
      omega
    subst hT
    simpa using LB_zero k _
  | succ j ihj =>
    intro m T hj hsupp hss hdeg
    have hmn : m < n := by omega
    set v0 : Fin n := ⟨m, hmn⟩ with hv0def
    have hv0 : v0.val = m := rfl
    set T0 := T.filter fun μ => ¬ 0 < μ v0 with hT0
    set U := quot v0 T with hUdef
    have h0 : LB k T0.card (lowerShadow T0).card :=
      ihj (m + 1) T0 (by omega) (supp_low T v0 hv0 hsupp) (sstab_low T v0 hv0 hss)
        (fun μ hμ => hdeg μ (Finset.mem_filter.mp hμ).1)
    have h1 : k = 0 ∨ LB (k - 1) U.card (lowerShadow U).card := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact Or.inl hk
      · right
        refine ihk (k - 1) (by omega) n U m (supp_quot T v0 hsupp) (sstab_quot T v0 hss) ?_
        intro ν hν
        have := deg_quot v0 T k hdeg ν hν
        omega
    have hcardT : T.card = T0.card + U.card := by
      rw [hUdef, card_quot, add_comm]
      exact (Finset.card_filter_add_card_filter_not _).symm
    have hshU : lowerShadow U = quot v0 U :=
      shadow_eq_quot U v0 hv0 (supp_quot T v0 hsupp) (sstab_quot T v0 hss)
    have hineq : (lowerShadow T0).card + (lowerShadow U).card ≤ U.card := by
      have e1 : (lowerShadow T0).card ≤ (U.filter fun ν => ¬ 0 < ν v0).card :=
        Finset.card_le_card (shadow_low_sub T v0 hv0 hsupp hss)
      rw [hshU, card_quot]
      have e2 := Finset.card_filter_add_card_filter_not (s := U) (fun ν => 0 < ν v0)
      omega
    rw [hcardT, shadow_eq_quot T v0 hv0 hsupp hss]
    exact hA k _ _ _ _ h0 h1 hineq

/-! ### Two-variable slice compression (Clements–Lindström) -/

section Comp

variable {n : ℕ}

/-- The part of `μ` outside the coordinates `i, j`. -/
noncomputable def keyOf (i j : Fin n) (μ : Fin n →₀ ℕ) : Fin n →₀ ℕ := (μ.erase i).erase j

theorem keyOf_apply (i j : Fin n) (μ : Fin n →₀ ℕ) (w : Fin n) :
    keyOf i j μ w = if w = j then 0 else if w = i then 0 else μ w := by
  simp only [keyOf, Finsupp.erase_apply]

theorem key_eq_iff (i j : Fin n) (μ ν : Fin n →₀ ℕ) :
    keyOf i j μ = keyOf i j ν ↔ ∀ w, w ≠ i → w ≠ j → μ w = ν w := by
  constructor
  · intro h w hi hj
    have := DFunLike.congr_fun h w
    simpa [keyOf_apply, hi, hj] using this
  · intro h
    ext w
    simp only [keyOf_apply]
    split_ifs with h1 h2
    · rfl
    · rfl
    · exact h w h2 h1

theorem ext_ij (i j : Fin n) (μ ν : Fin n →₀ ℕ) (hk : ∀ w, w ≠ i → w ≠ j → μ w = ν w)
    (hi : μ i = ν i) (hj : μ j = ν j) : μ = ν := by
  ext w
  by_cases h1 : w = i
  · rw [h1]; exact hi
  by_cases h2 : w = j
  · rw [h2]; exact hj
  exact hk w h1 h2

theorem single_off (i w : Fin n) (c : ℕ) (h : w ≠ i) : (single i c) w = 0 :=
  Finsupp.single_eq_of_ne h

/-- The monomial with the key of `κ` and exponents `a` at `i`, `b` at `j`. -/
noncomputable def mk (i j : Fin n) (κ : Fin n →₀ ℕ) (a b : ℕ) : Fin n →₀ ℕ :=
  keyOf i j κ + single i a + single j b

theorem mk_i (i j : Fin n) (hij : i ≠ j) (κ : Fin n →₀ ℕ) (a b : ℕ) : mk i j κ a b i = a := by
  simp [mk, keyOf_apply, hij, single_off j i b hij]

theorem mk_j (i j : Fin n) (hij : i ≠ j) (κ : Fin n →₀ ℕ) (a b : ℕ) : mk i j κ a b j = b := by
  simp [mk, keyOf_apply, single_off i j a (Ne.symm hij)]

theorem mk_w (i j : Fin n) (κ : Fin n →₀ ℕ) (a b : ℕ) (w : Fin n) (hi : w ≠ i) (hj : w ≠ j) :
    mk i j κ a b w = κ w := by
  simp [mk, keyOf_apply, hi, hj, single_off i w a hi, single_off j w b hj]

/-- Size of the `(i,j)`-slice of `ν` in `T`. -/
noncomputable def cnt (i j : Fin n) (T : Finset (Fin n →₀ ℕ)) (ν : Fin n →₀ ℕ) : ℕ :=
  (T.filter fun μ => keyOf i j μ = keyOf i j ν ∧ μ i + μ j = ν i + ν j).card

/-- The `(i,j)`-compression: every slice is replaced by its initial segment in the `j`-exponent. -/
noncomputable def comp (i j : Fin n) (T : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  (T.biUnion fun μ => (Finset.range (μ i + μ j + 1)).image fun t =>
      mk i j μ (μ i + μ j - t) t).filter fun ν => ν j < cnt i j T ν

theorem mem_comp (i j : Fin n) (hij : i ≠ j) (T : Finset (Fin n →₀ ℕ)) (ν : Fin n →₀ ℕ) :
    ν ∈ comp i j T ↔ ν j < cnt i j T ν := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    have hpos : 0 < cnt i j T ν := by omega
    obtain ⟨μ, hμ⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hμ
    obtain ⟨hμT, hk, hs⟩ := hμ
    refine Finset.mem_biUnion.mpr ⟨μ, hμT, Finset.mem_image.mpr
      ⟨ν j, Finset.mem_range.mpr (by omega), ?_⟩⟩
    rw [key_eq_iff] at hk
    apply ext_ij i j
    · intro w hi hj; rw [mk_w i j _ _ _ w hi hj]; exact hk w hi hj
    · rw [mk_i i j hij]; omega
    · rw [mk_j i j hij]

/-- One-dimensional shadow bound inside a slice. -/
theorem oneD (s : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.range (s + 2)) :
    min A.card (s + 1) ≤ (A.filter (· ≤ s) ∪ (A.filter (1 ≤ ·)).image (· - 1)).card := by
  by_cases hs : s + 1 ∈ A
  · by_cases hfull : Finset.range (s + 1) ⊆ A
    · calc min A.card (s + 1) ≤ s + 1 := min_le_right _ _
        _ = (Finset.range (s + 1)).card := (Finset.card_range _).symm
        _ ≤ _ := Finset.card_le_card (fun t ht => Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hfull ht, by rw [Finset.mem_range] at ht; omega⟩))
    · obtain ⟨t0, ht0r, ht0A⟩ := Finset.not_subset.mp hfull
      set G := (Finset.range (s + 1)).filter (· ∉ A) with hGdef
      have hGne : G.Nonempty := ⟨t0, Finset.mem_filter.mpr ⟨ht0r, ht0A⟩⟩
      set t := G.max' hGne with htdef
      have htG : t ∈ G := G.max'_mem hGne
      rw [hGdef, Finset.mem_filter, Finset.mem_range] at htG
      have ht1 : t + 1 ∈ A := by
        by_contra hc
        rcases Nat.lt_or_ge (t + 1) (s + 1) with h | h
        · have : t + 1 ≤ t := G.le_max' (t + 1) (by
            rw [hGdef, Finset.mem_filter, Finset.mem_range]; exact ⟨h, hc⟩)
          omega
        · have : t + 1 = s + 1 := by omega
          rw [this] at hc; exact hc hs
      have hsub : insert t (A.filter (· ≤ s)) ⊆
          A.filter (· ≤ s) ∪ (A.filter (1 ≤ ·)).image (· - 1) := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨t + 1, Finset.mem_filter.mpr ⟨ht1, by omega⟩, by omega⟩)
        · exact Finset.mem_union_left _ hx
      have hnot : t ∉ A.filter (· ≤ s) := fun h => htG.2 (Finset.mem_filter.mp h).1
      have hcard : (A.filter (· ≤ s)).card + 1 = A.card := by
        have := Finset.card_filter_add_card_filter_not (s := A) (fun x => x ≤ s)
        have h2 : (A.filter fun x => ¬ x ≤ s) = {s + 1} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, hx'⟩; have := Finset.mem_range.mp (hA hx); omega
          · rintro rfl; exact ⟨hs, by omega⟩
        rw [h2, Finset.card_singleton] at this
        omega
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at this
      omega
  · have hf : A.filter (· ≤ s) = A := by
      apply Finset.filter_true_of_mem
      intro x hx
      have h1 := Finset.mem_range.mp (hA hx)
      have h2 : x ≠ s + 1 := fun h => hs (h ▸ hx)
      omega
    calc min A.card (s + 1) ≤ A.card := min_le_left _ _
      _ = (A.filter (· ≤ s)).card := by rw [hf]
      _ ≤ _ := Finset.card_le_card Finset.subset_union_left

/-- Compression does not create new shadow: `∂ C(T) ⊆ C(∂ T)`. -/
theorem shadow_comp_sub (i j : Fin n) (hij : i ≠ j) (T : Finset (Fin n →₀ ℕ)) :
    lowerShadow (comp i j T) ⊆ comp i j (lowerShadow T) := by
  intro ν hν
  rw [mem_lowerShadow] at hν
  obtain ⟨v, hv⟩ := hν
  rw [mem_comp i j hij] at hv ⊢
  have hρw : ∀ w, ((ν + single v 1 : Fin n →₀ ℕ) w) = ν w + if v = w then 1 else 0 := fun w => by
    simp [Finsupp.single_apply]
  by_cases hvij : v = i ∨ v = j
  · set s := ν i + ν j with hsdef
    set ρ := ν + single v 1 with hρ
    have hsum : ρ i + ρ j = s + 1 := by
      rw [hρw, hρw]
      rcases hvij with h | h <;> subst h <;> simp [hij, Ne.symm hij] <;> omega
    have hkey : ∀ w, w ≠ i → w ≠ j → ρ w = ν w := by
      intro w hi hj
      rw [hρw]
      have : v ≠ w := by rcases hvij with h | h <;> subst h <;> [exact Ne.symm hi; exact Ne.symm hj]
      simp [this]
    have hρj : ν j ≤ ρ j := by rw [hρw]; omega
    have hρj' : v = j → ν j + 1 = ρ j := by
      intro h; subst h; rw [hρw]; simp
    set G := T.filter fun μ => keyOf i j μ = keyOf i j ρ ∧ μ i + μ j = ρ i + ρ j with hG
    have hmemG : ∀ μ ∈ G, μ ∈ T ∧ (∀ w, w ≠ i → w ≠ j → μ w = ν w) ∧ μ i + μ j = s + 1 := by
      intro μ hμ
      rw [hG, Finset.mem_filter, key_eq_iff] at hμ
      refine ⟨hμ.1, fun w hi hj => (hμ.2.1 w hi hj).trans (hkey w hi hj), hμ.2.2.trans hsum⟩
    set A := G.image fun μ => μ j with hA
    have hAcard : A.card = G.card := by
      apply Finset.card_image_of_injOn
      intro μ hμ μ' hμ' h
      obtain ⟨-, hk, hs1⟩ := hmemG μ hμ
      obtain ⟨-, hk', hs1'⟩ := hmemG μ' hμ'
      simp only at h
      apply ext_ij i j
      · intro w hi hj; rw [hk w hi hj, hk' w hi hj]
      · omega
      · exact h
    have hAsub : A ⊆ Finset.range (s + 2) := by
      intro t ht
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨-, -, hs1⟩ := hmemG μ hμ
      rw [Finset.mem_range]; omega
    have hlt : ν j < min A.card (s + 1) := by
      have hc : ρ j < G.card := hv
      rw [hAcard]
      rcases hvij with h | h
      · have : ρ j = ν j := by
          rw [hρw]; have : v ≠ j := by rw [h]; exact hij
          simp [this]
        omega
      · have := hρj' h; omega
    refine lt_of_lt_of_le hlt (le_trans (oneD s A hAsub) ?_)
    apply Finset.card_le_card_of_injOn (fun t => mk i j ν (s - t) t)
    · intro t ht
      rw [Finset.mem_coe] at ht ⊢
      have htle : t ≤ s := by
        rcases Finset.mem_union.mp ht with h | h
        · exact (Finset.mem_filter.mp h).2
        · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h
          obtain ⟨ht'A, -⟩ := Finset.mem_filter.mp ht'
          have := Finset.mem_range.mp (hAsub ht'A); omega
      rw [Finset.mem_filter]
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_lowerShadow]
        rcases Finset.mem_union.mp ht with h | h
        · obtain ⟨htA, -⟩ := Finset.mem_filter.mp h
          obtain ⟨μ, hμG, hμt⟩ := Finset.mem_image.mp htA
          obtain ⟨hμT, hk, hs1⟩ := hmemG μ hμG
          refine ⟨i, ?_⟩
          convert hμT using 1
          apply ext_ij i j
          · intro w hi hj
            simp only [Finsupp.coe_add, Pi.add_apply]
            rw [mk_w i j _ _ _ w hi hj, single_off i w 1 hi, hk w hi hj]; rfl
          · simp only [Finsupp.coe_add, Pi.add_apply]
            rw [mk_i i j hij]; simp; omega
          · simp only [Finsupp.coe_add, Pi.add_apply]
            rw [mk_j i j hij, single_off i j 1 (Ne.symm hij)]; omega
        · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h
          obtain ⟨ht'A, ht'1⟩ := Finset.mem_filter.mp ht'
          obtain ⟨μ, hμG, hμt⟩ := Finset.mem_image.mp ht'A
          obtain ⟨hμT, hk, hs1⟩ := hmemG μ hμG
          refine ⟨j, ?_⟩
          convert hμT using 1
          apply ext_ij i j
          · intro w hi hj
            simp only [Finsupp.coe_add, Pi.add_apply]
            rw [mk_w i j _ _ _ w hi hj, single_off j w 1 hj, hk w hi hj]; rfl
          · simp only [Finsupp.coe_add, Pi.add_apply]
            rw [mk_i i j hij, single_off j i 1 hij]; omega
          · simp only [Finsupp.coe_add, Pi.add_apply]
            rw [mk_j i j hij]; simp; omega
      · rw [key_eq_iff]
        intro w hi hj
        exact mk_w i j _ _ _ w hi hj
      · rw [mk_i i j hij, mk_j i j hij]; omega
    · intro t1 _ t2 _ h
      have := DFunLike.congr_fun h j
      simp only [mk_j i j hij] at this
      exact this
  · simp only [not_or] at hvij
    obtain ⟨hvi, hvj⟩ := hvij
    have hρj : ((ν + single v 1 : Fin n →₀ ℕ) j) = ν j := by rw [hρw]; simp [hvj]
    rw [hρj] at hv
    refine lt_of_lt_of_le hv ?_
    apply Finset.card_le_card_of_injOn (fun μ => μ - single v 1)
    · intro μ hμ
      rw [Finset.mem_coe, Finset.mem_filter, key_eq_iff] at hμ
      rw [Finset.mem_coe, Finset.mem_filter, key_eq_iff]
      obtain ⟨hμT, hk, hs1⟩ := hμ
      have hμv : μ v = ν v + 1 := by
        rw [hk v (Ne.symm (Ne.symm hvi)) hvj, hρw]; simp
      have hle : single v 1 ≤ μ := by rw [Finsupp.single_le_iff]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_lowerShadow]
        exact ⟨v, by rw [tsub_add_cancel_of_le hle]; exact hμT⟩
      · intro w hi hj
        simp only [Finsupp.coe_tsub, Pi.sub_apply]
        rw [hk w hi hj, hρw, Finsupp.single_apply]
        split_ifs <;> omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply]
        rw [single_off v i 1 (Ne.symm hvi), single_off v j 1 (Ne.symm hvj)]
        rw [hρw, hρw] at hs1
        simp [hvi, hvj] at hs1
        omega
    · intro μ hμ μ' hμ' h
      rw [Finset.mem_coe, Finset.mem_filter, key_eq_iff] at hμ hμ'
      have h1 : μ v = ν v + 1 := by rw [hμ.2.1 v (Ne.symm (Ne.symm hvi)) hvj, hρw]; simp
      have h2 : μ' v = ν v + 1 := by rw [hμ'.2.1 v (Ne.symm (Ne.symm hvi)) hvj, hρw]; simp
      have hle : single v 1 ≤ μ := by rw [Finsupp.single_le_iff]; omega
      have hle' : single v 1 ≤ μ' := by rw [Finsupp.single_le_iff]; omega
      have := congrArg (· + single v 1) h
      simp only [tsub_add_cancel_of_le hle, tsub_add_cancel_of_le hle'] at this
      exact this

end Comp


/-! ### Session 4: cardinality, degree and potential of the compression; reduction to `MacArith` -/

section Comp2

variable {n : ℕ}

/-- The slice signature of `μ`: its key outside `i, j` and its total exponent on `i, j`. -/
noncomputable def sig (i j : Fin n) (μ : Fin n →₀ ℕ) : (Fin n →₀ ℕ) × ℕ := (keyOf i j μ, μ i + μ j)

theorem cnt_eq (i j : Fin n) (T : Finset (Fin n →₀ ℕ)) (ν : Fin n →₀ ℕ) :
    cnt i j T ν = (T.filter fun μ => sig i j μ = sig i j ν).card := by
  simp only [cnt, sig, Prod.mk.injEq]

theorem cnt_congr (i j : Fin n) (T : Finset (Fin n →₀ ℕ)) (ν ν' : Fin n →₀ ℕ)
    (h : sig i j ν = sig i j ν') : cnt i j T ν = cnt i j T ν' := by
  rw [cnt_eq, cnt_eq, h]

theorem mk_self (i j : Fin n) (hij : i ≠ j) (μ : Fin n →₀ ℕ) : mk i j μ (μ i) (μ j) = μ :=
  ext_ij i j _ _ (fun w hi hj => mk_w i j _ _ _ w hi hj) (mk_i i j hij _ _ _) (mk_j i j hij _ _ _)

theorem keyOf_mk (i j : Fin n) (κ : Fin n →₀ ℕ) (a b : ℕ) :
    keyOf i j (mk i j κ a b) = keyOf i j κ := by
  rw [key_eq_iff]; intro w hi hj; exact mk_w i j _ _ _ w hi hj

theorem sig_mk (i j : Fin n) (hij : i ≠ j) (κ : Fin n →₀ ℕ) (a b : ℕ) :
    sig i j (mk i j κ a b) = (keyOf i j κ, a + b) := by
  simp only [sig, keyOf_mk, mk_i i j hij, mk_j i j hij]

theorem sig_mk_sub (i j : Fin n) (hij : i ≠ j) (μ0 : Fin n →₀ ℕ) (t : ℕ) (ht : t ≤ μ0 i + μ0 j) :
    sig i j (mk i j μ0 (μ0 i + μ0 j - t) t) = sig i j μ0 := by
  rw [sig_mk i j hij, sig]
  congr 1
  omega

theorem degree_mk (i j : Fin n) (κ : Fin n →₀ ℕ) (a b : ℕ) :
    Finsupp.degree (mk i j κ a b) = Finsupp.degree (keyOf i j κ) + a + b := by
  simp only [mk, map_add, Finsupp.degree_single]

theorem degree_split (i j : Fin n) (hij : i ≠ j) (μ : Fin n →₀ ℕ) :
    Finsupp.degree μ = Finsupp.degree (keyOf i j μ) + μ i + μ j := by
  have := degree_mk i j μ (μ i) (μ j)
  rwa [mk_self i j hij] at this

theorem cnt_le (i j : Fin n) (hij : i ≠ j) (T : Finset (Fin n →₀ ℕ)) (ν : Fin n →₀ ℕ) :
    cnt i j T ν ≤ ν i + ν j + 1 := by
  unfold cnt
  calc _ ≤ (Finset.range (ν i + ν j + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun μ => μ j)
        · intro μ hμ
          rw [Finset.mem_coe, Finset.mem_filter] at hμ
          obtain ⟨-, -, hs⟩ := hμ
          rw [Finset.mem_coe, Finset.mem_range]; show μ j < _; omega
        · intro μ hμ μ' hμ' h
          rw [Finset.mem_coe, Finset.mem_filter, key_eq_iff] at hμ hμ'
          obtain ⟨-, hk, hs⟩ := hμ
          obtain ⟨-, hk', hs'⟩ := hμ'
          simp only at h
          apply ext_ij i j
          · intro w hi hj; rw [hk w hi hj, hk' w hi hj]
          · omega
          · exact h
    _ = _ := Finset.card_range _

theorem fiber_comp (i j : Fin n) (hij : i ≠ j) (T : Finset (Fin n →₀ ℕ)) (μ0 : Fin n →₀ ℕ) :
    (comp i j T).filter (fun ν => sig i j ν = sig i j μ0) =
      (Finset.range (cnt i j T μ0)).image fun t => mk i j μ0 (μ0 i + μ0 j - t) t := by
  ext ν
  rw [Finset.mem_filter, mem_comp i j hij, Finset.mem_image]
  constructor
  · rintro ⟨hc, hs⟩
    rw [cnt_congr i j T ν μ0 hs] at hc
    refine ⟨ν j, Finset.mem_range.mpr hc, ?_⟩
    simp only [sig, Prod.mk.injEq, key_eq_iff] at hs
    obtain ⟨hk, hs2⟩ := hs
    apply ext_ij i j
    · intro w hi hj; rw [mk_w i j _ _ _ w hi hj]; exact (hk w hi hj).symm
    · rw [mk_i i j hij]; omega
    · rw [mk_j i j hij]
  · rintro ⟨t, ht, rfl⟩
    rw [Finset.mem_range] at ht
    have hle := cnt_le i j hij T μ0
    have hsig := sig_mk_sub i j hij μ0 t (by omega)
    refine ⟨?_, hsig⟩
    rw [cnt_congr i j T _ μ0 hsig, mk_j i j hij]; exact ht

theorem sig_comp_mem (i j : Fin n) (hij : i ≠ j) (T : Finset (Fin n →₀ ℕ)) :
    ∀ ν ∈ comp i j T, sig i j ν ∈ T.image (sig i j) := by
  intro ν hν
  obtain ⟨μ, hμ, hν'⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hν).1
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hν'
  rw [Finset.mem_range] at ht
  exact Finset.mem_image.mpr ⟨μ, hμ, (sig_mk_sub i j hij μ t (by omega)).symm⟩

/-- (S2) Compression preserves cardinality. -/
theorem card_comp (i j : Fin n) (hij : i ≠ j) (T : Finset (Fin n →₀ ℕ)) :
    (comp i j T).card = T.card := by
  rw [Finset.card_eq_sum_card_fiberwise (sig_comp_mem i j hij T),
    Finset.card_eq_sum_card_fiberwise (fun μ hμ => Finset.mem_image_of_mem (sig i j) hμ)]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨μ0, -, rfl⟩ := Finset.mem_image.mp hb
  rw [fiber_comp i j hij, Finset.card_image_of_injective _ ?_, Finset.card_range, cnt_eq]
  intro t1 t2 h
  have := DFunLike.congr_fun h j
  simpa only [mk_j i j hij] using this

/-- (S3) Compression preserves degrees. -/
theorem deg_comp (i j : Fin n) (hij : i ≠ j) (T : Finset (Fin n →₀ ℕ)) (d : ℕ)
    (hdeg : ∀ μ ∈ T, Finsupp.degree μ = d) : ∀ ν ∈ comp i j T, Finsupp.degree ν = d := by
  intro ν hν
  obtain ⟨μ, hμ, hν'⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hν).1
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hν'
  rw [Finset.mem_range] at ht
  rw [degree_mk, ← hdeg μ hμ, degree_split i j hij μ]
  omega

/-! Potential: sum over the set of the index-weighted degree. -/

def wt (μ : Fin n →₀ ℕ) : ℕ := ∑ v : Fin n, v.val * μ v

theorem wt_add (μ ν : Fin n →₀ ℕ) : wt (μ + ν) = wt μ + wt ν := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem wt_single (i : Fin n) (a : ℕ) : wt (single i a) = i.val * a := by
  simp [wt, Finsupp.single_apply]

theorem wt_mk (i j : Fin n) (κ : Fin n →₀ ℕ) (a b : ℕ) :
    wt (mk i j κ a b) = wt (keyOf i j κ) + i.val * a + j.val * b := by
  simp only [mk, wt_add, wt_single]

theorem wt_split (i j : Fin n) (hij : i ≠ j) (μ : Fin n →₀ ℕ) :
    wt μ = wt (keyOf i j μ) + i.val * μ i + j.val * μ j := by
  have := wt_mk i j μ (μ i) (μ j)
  rwa [mk_self i j hij] at this

theorem lin (i j s t : ℕ) (hij : i ≤ j) (hts : t ≤ s) :
    i * (s - t) + j * t = i * s + (j - i) * t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hts
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]; ring

theorem wt_fiber (i j : Fin n) (hij : i.val < j.val) (μ μ0 : Fin n →₀ ℕ)
    (h : sig i j μ = sig i j μ0) :
    wt μ = wt (keyOf i j μ0) + i.val * (μ0 i + μ0 j) + (j.val - i.val) * μ j := by
  have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
  simp only [sig, Prod.mk.injEq] at h
  have h3 := wt_split i j hne μ
  rw [h.1] at h3
  have h4 := lin i.val j.val (μ i + μ j) (μ j) hij.le (by omega)
  rw [Nat.add_sub_cancel] at h4
  rw [h3, ← h.2]
  linarith

theorem range_sum (A : Finset ℕ) : ∑ t ∈ Finset.range A.card, t ≤ ∑ t ∈ A, t ∧
    (∑ t ∈ A, t ≤ ∑ t ∈ Finset.range A.card, t → A = Finset.range A.card) := by
  refine Finset.induction_on_max A ?_ ?_
  · simp
  · intro a s ha ih
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcs : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (ha x hx)
      simpa using Finset.card_le_card this
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has, Finset.sum_range_succ]
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by omega, fun h => ?_⟩
    have ha' : a = s.card := by omega
    have hs : s = Finset.range s.card := ih2 (by omega)
    rw [Finset.range_add_one, ← hs, ha']

theorem sum_lin_le (A : Finset ℕ) (D c : ℕ) :
    ∑ x ∈ Finset.range A.card, (D + c * x) ≤ ∑ x ∈ A, (D + c * x) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_range, ← Finset.mul_sum, ← Finset.mul_sum]
  exact Nat.add_le_add_left (Nat.mul_le_mul le_rfl (range_sum A).1) _

theorem sum_lin_lt (A : Finset ℕ) (D c : ℕ) (hc : 0 < c) (hA : A ≠ Finset.range A.card) :
    ∑ x ∈ Finset.range A.card, (D + c * x) < ∑ x ∈ A, (D + c * x) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_range, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := range_sum A
  have h2 : ∑ t ∈ Finset.range A.card, t < ∑ t ∈ A, t := by
    by_contra h; exact hA (h1.2 (not_lt.mp h))
  exact Nat.add_lt_add_left (mul_lt_mul_of_pos_left h2 hc) _

theorem slice_inj (i j : Fin n) (T : Finset (Fin n →₀ ℕ)) (μ0 : Fin n →₀ ℕ) :
    Set.InjOn (fun μ : Fin n →₀ ℕ => μ j)
      ↑(T.filter fun μ => sig i j μ = sig i j μ0) := by
  intro μ hμ μ' hμ' h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, sig, Prod.mk.injEq, key_eq_iff] at hμ hμ'
  obtain ⟨-, hk, hs⟩ := hμ
  obtain ⟨-, hk', hs'⟩ := hμ'
  simp only at h
  apply ext_ij i j
  · intro w hi hj; rw [hk w hi hj, hk' w hi hj]
  · omega
  · exact h

theorem slice_card (i j : Fin n) (T : Finset (Fin n →₀ ℕ)) (μ0 : Fin n →₀ ℕ) :
    ((T.filter fun μ => sig i j μ = sig i j μ0).image fun μ => μ j).card = cnt i j T μ0 := by
  rw [Finset.card_image_of_injOn (slice_inj i j T μ0), cnt_eq]

theorem slice_sum (i j : Fin n) (hij : i.val < j.val) (T : Finset (Fin n →₀ ℕ))
    (μ0 : Fin n →₀ ℕ) :
    ∑ μ ∈ T.filter (fun μ => sig i j μ = sig i j μ0), wt μ =
      ∑ x ∈ (T.filter fun μ => sig i j μ = sig i j μ0).image (fun μ => μ j),
        (wt (keyOf i j μ0) + i.val * (μ0 i + μ0 j) + (j.val - i.val) * x) := by
  rw [Finset.sum_image (by intro μ hμ μ' hμ' h; exact slice_inj i j T μ0 hμ hμ' h)]
  apply Finset.sum_congr rfl
  intro μ hμ
  exact wt_fiber i j hij μ μ0 (Finset.mem_filter.mp hμ).2

theorem comp_slice_sum (i j : Fin n) (hij : i.val < j.val) (T : Finset (Fin n →₀ ℕ))
    (μ0 : Fin n →₀ ℕ) :
    ∑ ν ∈ (comp i j T).filter (fun ν => sig i j ν = sig i j μ0), wt ν =
      ∑ x ∈ Finset.range (cnt i j T μ0),
        (wt (keyOf i j μ0) + i.val * (μ0 i + μ0 j) + (j.val - i.val) * x) := by
  have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
  rw [fiber_comp i j hne, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    have hle := cnt_le i j hne T μ0
    rw [wt_fiber i j hij _ μ0 (sig_mk_sub i j hne μ0 t (by omega)), mk_j i j hne]
  · intro t1 _ t2 _ h
    have := DFunLike.congr_fun h j
    simpa only [mk_j i j hne] using this

noncomputable def pot (T : Finset (Fin n →₀ ℕ)) : ℕ := ∑ μ ∈ T, wt μ

/-- (S5a) Compression never increases the potential, and strictly decreases it when the set
is not stable under the move `x_j → x_i`. -/
theorem pot_comp (i j : Fin n) (hij : i.val < j.val) (T : Finset (Fin n →₀ ℕ)) :
    pot (comp i j T) ≤ pot T ∧ (∀ μ ∈ T, 0 < μ j → μ - single j 1 + single i 1 ∉ T →
      pot (comp i j T) < pot T) := by
  have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
  unfold pot
  rw [← Finset.sum_fiberwise_of_maps_to (sig_comp_mem i j hne T) wt,
    ← Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem (sig i j) hμ) wt]
  have key : ∀ b ∈ T.image (sig i j),
      ∑ ν ∈ (comp i j T).filter (fun ν => sig i j ν = b), wt ν ≤
        ∑ ν ∈ T.filter (fun ν => sig i j ν = b), wt ν := by
    intro b hb
    obtain ⟨μ0, -, rfl⟩ := Finset.mem_image.mp hb
    rw [comp_slice_sum i j hij T μ0, slice_sum i j hij T μ0, ← slice_card i j T μ0]
    exact sum_lin_le _ _ _
  refine ⟨Finset.sum_le_sum key, ?_⟩
  intro μ hμ hj hnot
  apply Finset.sum_lt_sum key
  refine ⟨sig i j μ, Finset.mem_image_of_mem _ hμ, ?_⟩
  rw [comp_slice_sum i j hij T μ, slice_sum i j hij T μ, ← slice_card i j T μ]
  apply sum_lin_lt _ _ _ (by omega)
  intro hA
  have hmA : μ j ∈ (T.filter fun ν => sig i j ν = sig i j μ).image (fun ν => ν j) :=
    Finset.mem_image.mpr ⟨μ, Finset.mem_filter.mpr ⟨hμ, rfl⟩, rfl⟩
  have hm1 : μ j - 1 ∈ (T.filter fun ν => sig i j ν = sig i j μ).image (fun ν => ν j) := by
    rw [hA] at hmA ⊢; rw [Finset.mem_range] at hmA ⊢; omega
  obtain ⟨μ', hμ', hμ'j⟩ := Finset.mem_image.mp hm1
  rw [Finset.mem_filter] at hμ'
  obtain ⟨hμ'T, hsg⟩ := hμ'
  simp only [sig, Prod.mk.injEq, key_eq_iff] at hsg
  obtain ⟨hk, hs⟩ := hsg
  apply hnot
  convert hμ'T using 1
  apply ext_ij i j
  · intro w hi hj'
    simp [Finsupp.single_apply, Ne.symm hi, Ne.symm hj', hk w hi hj']
  · simp [Finsupp.single_apply, hne, Ne.symm hne]
    omega
  · simp [Finsupp.single_apply, hne, Ne.symm hne]
    omega

/-- (S5) Repeated compression reaches a strongly stable set with no larger shadow. -/
theorem exists_sstab (k : ℕ) : ∀ (p : ℕ) (T : Finset (Fin n →₀ ℕ)), pot T = p →
    (∀ μ ∈ T, Finsupp.degree μ = k + 1) →
    ∃ T' : Finset (Fin n →₀ ℕ), T'.card = T.card ∧ (∀ μ ∈ T', Finsupp.degree μ = k + 1) ∧
      (lowerShadow T').card ≤ (lowerShadow T).card ∧ SStab 0 T' := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro T hp hdeg
  by_cases hs : SStab 0 T
  · exact ⟨T, rfl, hdeg, le_rfl, hs⟩
  · unfold SStab at hs
    push_neg at hs
    obtain ⟨μ, hμ, i, j, -, hij, hj, hnot⟩ := hs
    have hij' : i.val < j.val := hij
    have hne : i ≠ j := ne_of_lt hij
    have hlt := (pot_comp i j hij' T).2 μ hμ hj hnot
    obtain ⟨T', h1, h2, h3, h4⟩ :=
      ih _ (by rw [← hp]; exact hlt) (comp i j T) rfl (deg_comp i j hne T _ hdeg)
    refine ⟨T', h1.trans (card_comp i j hne T), h2, h3.trans ?_, h4⟩
    calc (lowerShadow (comp i j T)).card ≤ (comp i j (lowerShadow T)).card :=
          Finset.card_le_card (shadow_comp_sub i j hne T)
      _ = _ := card_comp i j hne _

/-- The Macaulay shadow bound for every degree-`(k+1)` set, given the arithmetic step. -/
theorem shadow_LB (hA : MacArith) (k : ℕ) (T : Finset (Fin n →₀ ℕ))
    (hdeg : ∀ μ ∈ T, Finsupp.degree μ = k + 1) : LB k T.card (lowerShadow T).card := by
  obtain ⟨T', h1, h2, h3, h4⟩ := exists_sstab k _ T rfl hdeg
  have := sstab_bound hA k n T' 0 (fun _ _ _ _ => Nat.zero_le _) h4 h2
  rw [h1] at this
  intro i a hi hik hia hmono hx
  exact (this i a hi hik hia hmono hx).trans h3

end Comp2

end GF93M

set_option autoImplicit false
open scoped BigOperators

namespace GF93M

open Grunbaum2003

/-- Existence of the (k+1)-binomial (Macaulay) expansion, with a bound on the top entry. -/
theorem exists_expansion : ∀ (k x b : ℕ), 0 < x → x < Nat.choose b (k + 1) →
    ∃ (i : ℕ) (a : ℕ → ℕ), 0 < i ∧ i ≤ k + 1 ∧ i ≤ a i ∧
      (∀ r s : ℕ, i ≤ r → r < s → s ≤ k + 1 → a r < a s) ∧ a (k + 1) < b ∧
      x = ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r := by
  intro k
  induction k with
  | zero =>
    intro x b hx hxb
    refine ⟨1, fun _ => x, Nat.one_pos, le_refl _, hx, fun r s h1 h2 h3 => by omega, ?_, ?_⟩
    · simpa using hxb
    · simp
  | succ k ih =>
    intro x b hx hxb
    have hex : ∃ c, x < Nat.choose (c + 1) (k + 2) := ⟨b - 1, by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; simp at hxb
      · rwa [Nat.sub_add_cancel hb]⟩
    set c := Nat.find hex with hc
    have hc1 : x < Nat.choose (c + 1) (k + 2) := Nat.find_spec hex
    have hc2 : Nat.choose c (k + 2) ≤ x := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0]; simp
      · have := Nat.find_min hex (show c - 1 < c by omega)
        rw [Nat.sub_add_cancel h0] at this
        omega
    have hcb : c < b := by
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with hb | hb
        · subst hb; simp at hxb
        · exact hb
      have : c ≤ b - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel hb])
      omega
    have hkc : k + 2 ≤ c := by
      by_contra hlt
      have : Nat.choose (c + 1) (k + 2) ≤ 1 := by
        rcases Nat.lt_or_ge (c + 1) (k + 2) with h | h
        · rw [Nat.choose_eq_zero_of_lt h]; omega
        · have : c + 1 = k + 2 := by omega
          rw [this, Nat.choose_self]
      omega
    have hpas : Nat.choose (c + 1) (k + 2) = Nat.choose c (k + 1) + Nat.choose c (k + 2) :=
      Nat.choose_succ_succ c (k + 1)
    set y := x - Nat.choose c (k + 2) with hy
    rcases Nat.eq_zero_or_pos y with hy0 | hy0
    · refine ⟨k + 2, fun _ => c, by omega, le_refl _, hkc, fun r s h1 h2 h3 => by omega, hcb, ?_⟩
      simp only [Finset.Icc_self, Finset.sum_singleton]
      omega
    · obtain ⟨i, a, hi0, hik, hia, hmono, hak, hsum⟩ := ih y c hy0 (by omega)
      refine ⟨i, fun r => if r = k + 2 then c else a r, hi0, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [show i ≠ k + 2 by omega, if_false]; exact hia
      · intro r s h1 h2 h3
        have hr : r ≠ k + 2 := by omega
        simp only [hr, if_false]
        by_cases hs : s = k + 2
        · simp only [hs, if_true]
          rcases Nat.eq_or_lt_of_le (show r ≤ k + 1 by omega) with h | h
          · rw [h]; exact hak
          · exact lt_trans (hmono r (k + 1) h1 h le_rfl) hak
        · simp only [hs, if_false]; exact hmono r s h1 h2 (by omega)
      · simp only [if_true]; exact hcb
      · rw [Finset.sum_Icc_succ_top (show i ≤ k + 1 + 1 by omega)]
        have hs : ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (if r = k + 2 then c else a r) r =
            ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r :=
          Finset.sum_congr rfl (fun r hr => by
            have : r ≠ k + 2 := by have := (Finset.mem_Icc.mp hr).2; omega
            simp only [this, if_false])
        show x = ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (if r = k + 2 then c else a r) r +
          Nat.choose (if k + 2 = k + 2 then c else a (k + 2)) (k + 2)
        rw [hs, if_pos rfl]
        omega


/-- Macaulay's lower-shadow bound for multisets (Clements-Lindstrom): the core combinatorial step. -/
def ShadowBound : Prop :=
  ∀ (n k : ℕ) (T : Finset (Fin n →₀ ℕ)), (∀ μ ∈ T, μ.sum (fun _ e => e) = k + 1) →
    ∀ (i : ℕ) (a : ℕ → ℕ), 0 < i → i ≤ k + 1 → i ≤ a i →
      (∀ r s : ℕ, i ≤ r → r < s → s ≤ k + 1 → a r < a s) →
      T.card = ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r →
      (∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r - 1) (r - 1)) ≤ (lowerShadow T).card

theorem deg_eq (n : ℕ) (μ : Fin n →₀ ℕ) : μ.sum (fun _ e => e) = Finsupp.degree μ := rfl

theorem deg_sub_single {n : ℕ} (μ : Fin n →₀ ℕ) (v : Fin n) (hv : 0 < μ v) :
    Finsupp.degree (μ - Finsupp.single v 1) + 1 = Finsupp.degree μ := by
  have hle : Finsupp.single v 1 ≤ μ := by
    rw [Finsupp.single_le_iff]; omega
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

theorem lt_choose_self_add (x : ℕ) : ∀ j : ℕ, x < Nat.choose (x + (j + 1)) (j + 1) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show x + (j + 1 + 1) = (x + (j + 1)) + 1 by omega, Nat.choose_succ_succ]
    omega

/-- Reduction: Macaulay's theorem for order ideals follows from the shadow bound. -/
theorem macaulay_of_shadow (hSB : ShadowBound) (n m : ℕ) (S : Finset (Fin n →₀ ℕ))
    (h0 : (0 : Fin n →₀ ℕ) ∈ S) (hS : ∀ μ ∈ S, ∀ ν : Fin n →₀ ℕ, ν ≤ μ → ν ∈ S) :
    IsMSequence m (fun k => (S.filter (fun μ => μ.sum (fun _ e => e) = k)).card) := by
  refine ⟨?_, ?_⟩
  · simp only [deg_eq]
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext μ
    simp only [Finset.mem_filter, Finset.mem_singleton, Finsupp.degree_eq_zero_iff]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro rfl; exact ⟨h0, rfl⟩
  · intro k hk _hkm
    set x := (S.filter (fun μ => μ.sum (fun _ e => e) = k)).card with hx
    rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · exact Or.inl hx0
    · right
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      obtain ⟨i, a, hi0, hik, hia, hmono, _hab, hsum⟩ :=
        exists_expansion j x (x + (j + 1)) hx0 (lt_choose_self_add x j)
      refine ⟨i, a, hi0, hik, hia, hmono, hsum, ?_⟩
      have hT : ∀ μ ∈ S.filter (fun μ => μ.sum (fun _ e => e) = j + 1),
          μ.sum (fun _ e => e) = j + 1 := fun μ hμ => (Finset.mem_filter.mp hμ).2
      refine le_trans (hSB n j _ hT i a hi0 hik hia hmono hsum) (Finset.card_le_card ?_)
      intro ν hν
      simp only [lowerShadow, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and] at hν
      obtain ⟨μ, ⟨hμS, hμd⟩, v, hv, rfl⟩ := hν
      refine Finset.mem_filter.mpr ⟨hS μ hμS _ tsub_le_self, ?_⟩
      have := deg_sub_single μ v hv
      rw [deg_eq] at hμd ⊢
      show _ = j + 1 - 1
      omega

end GF93M

/-! ### Session 5: bridge `LB` <-> `Phi`, hence `MacArith`, `ShadowBound`, `MacaulayOrderIdeal`. -/
namespace GF93M

theorem hockey (a : ℕ → ℕ) (i : ℕ) (hi : 0 < i) (hia : i ≤ a i) : ∀ m : ℕ, i ≤ m →
    (∀ r s : ℕ, i ≤ r → r < s → s ≤ m → a r < a s) →
    ∑ r ∈ Finset.Icc i m, Nat.choose (a r) r < Nat.choose (a m + 1) m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro him hmono
    rcases Nat.eq_or_lt_of_le him with heq | hlt
    · subst heq
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h1 := Nat.choose_succ_succ' (a (m + 1)) m
      have h2 : 0 < Nat.choose (a (m + 1)) m := Nat.choose_pos (by omega)
      omega
    · rw [Finset.sum_Icc_succ_top (by omega : i ≤ m + 1)]
      have h1 := ih (by omega) (fun r s h1 h2 h3 => hmono r s h1 h2 (by omega))
      have hlt' : a m < a (m + 1) := hmono m (m + 1) (by omega) (by omega) le_rfl
      have h2 : Nat.choose (a m + 1) m ≤ Nat.choose (a (m + 1)) m := Nat.choose_le_choose m (by omega)
      have h3 := Nat.choose_succ_succ' (a (m + 1)) m
      omega

theorem eval_top (k : ℕ) (a : ℕ → ℕ) (h : k + 1 ≤ a (k + 1)) :
    Nat.choose (a (k + 1) - 1) (k + 1 - 1) = Phi (k + 1) (Nat.choose (a (k + 1)) (k + 1)) := by
  obtain ⟨c, hc⟩ : ∃ c, a (k + 1) = c + 1 := ⟨a (k + 1) - 1, by omega⟩
  rw [hc, Phi_choose k c (by omega)]
  simp

theorem eval (k : ℕ) : ∀ (i : ℕ) (a : ℕ → ℕ), 0 < i → i ≤ k + 1 → i ≤ a i →
    (∀ r s : ℕ, i ≤ r → r < s → s ≤ k + 1 → a r < a s) →
    ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r - 1) (r - 1) =
      Phi (k + 1) (∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r) := by
  induction k with
  | zero =>
    intro i a hi hik hia _
    obtain rfl : i = 1 := by omega
    rw [Finset.Icc_self, Finset.sum_singleton, Finset.sum_singleton]
    exact eval_top 0 a hia
  | succ k ih =>
    intro i a hi hik hia hmono
    rcases Nat.eq_or_lt_of_le hik with heq | hlt
    · subst heq
      rw [Finset.Icc_self, Finset.sum_singleton, Finset.sum_singleton]
      exact eval_top (k + 1) a hia
    · rw [Finset.sum_Icc_succ_top (by omega : i ≤ k + 1 + 1),
        Finset.sum_Icc_succ_top (by omega : i ≤ k + 1 + 1)]
      have hmono' : ∀ r s : ℕ, i ≤ r → r < s → s ≤ k + 1 → a r < a s :=
        fun r s h1 h2 h3 => hmono r s h1 h2 (by omega)
      have hIH := ih i a hi (by omega) hia hmono'
      have hz := hockey a i hi hia (k + 1) (by omega) hmono'
      have hlt' : a (k + 1) < a (k + 1 + 1) := hmono _ _ (by omega) (by omega) le_rfl
      obtain ⟨c, hc⟩ : ∃ c, a (k + 1 + 1) = c + 1 := ⟨a (k + 1 + 1) - 1, by omega⟩
      have hle : Nat.choose (a (k + 1) + 1) (k + 1) ≤ Nat.choose (c + 1) (k + 1) :=
        Nat.choose_le_choose (k + 1) (by omega)
      set z := ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r with hzdef
      have hzpos : 0 < z := by
        have hp : 0 < Nat.choose (a i) i := Nat.choose_pos hia
        have : Nat.choose (a i) i ≤ z :=
          Finset.single_le_sum (f := fun r => Nat.choose (a r) r) (fun _ _ => Nat.zero_le _)
            (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
        omega
      have hd := Phi_decomp (k + 1) c z (by omega) (by omega)
      rw [hc, add_comm z, hd, ← hIH]
      simp only [Nat.add_sub_cancel]
      omega

theorem LB_of_Phi (k x s : ℕ) (h : Phi (k + 1) x ≤ s) : LB k x s := by
  intro i a hi hik hia hmono hx
  rw [eval k i a hi hik hia hmono, ← hx]
  exact h

theorem Phi_of_LB (k x s : ℕ) (h : LB k x s) : Phi (k + 1) x ≤ s := by
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · rw [hx0, Phi_zero]; exact Nat.zero_le _
  obtain ⟨i, a, hi0, hik, hia, hmono, _hab, hsum⟩ :=
    exists_expansion k x (x + (k + 1)) hx0 (lt_choose_self_add x k)
  have := h i a hi0 hik hia hmono hsum
  rw [eval k i a hi0 hik hia hmono, ← hsum] at this
  exact this

theorem macArith : MacArith := by
  intro k x0 y s0 s1 h0 h1 hs
  apply LB_of_Phi
  apply macPhi k
  have a0 := Phi_of_LB k x0 s0 h0
  have a1 : Phi k y ≤ s1 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [Phi]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rcases h1 with h1 | h1
      · omega
      · simpa using Phi_of_LB k' y s1 (by simpa using h1)
  omega

theorem shadowBound : ShadowBound := by
  intro n k T hT i a hi hik hia hmono hcard
  exact shadow_LB macArith k T (fun μ hμ => hT μ hμ) i a hi hik hia hmono hcard

theorem macaulayOrderIdeal (n m : ℕ) (S : Finset (Fin n →₀ ℕ))
    (h0 : (0 : Fin n →₀ ℕ) ∈ S) (hS : ∀ μ ∈ S, ∀ ν : Fin n →₀ ℕ, ν ≤ μ → ν ∈ S) :
    Grunbaum2003.IsMSequence m (fun k => (S.filter (fun μ => μ.sum (fun _ e => e) = k)).card) :=
  macaulay_of_shadow shadowBound n m S h0 hS

end GF93M


namespace GF93SM

open MvPolynomial

/-- Polynomials with pairwise distinct leading exponents (for a monomial order) are linearly independent. -/
theorem linIndep_of_degree_inj {σ K ι : Type*} [Field K] (m : MonomialOrder σ)
    (p : ι → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => m.degree (p i))) : LinearIndependent K p := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i0' hi0'
  by_contra hne
  set s' := s.filter (fun i => g i ≠ 0) with hs'
  have hne' : s'.Nonempty := ⟨i0', Finset.mem_filter.mpr ⟨hi0', hne⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image s' (fun i => m.toSyn (m.degree (p i))) hne'
  obtain ⟨hi0s, hgi0⟩ := Finset.mem_filter.mp hi0
  have hc := congrArg (MvPolynomial.coeff (m.degree (p i0))) hsum
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single i0] at hc
  · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hc
    have hl : (p i0).coeff (m.degree (p i0)) ≠ 0 := by
      have := (m.leadingCoeff_ne_zero_iff (f := p i0)).mpr (hp i0)
      exact this
    exact (mul_ne_zero hgi0 hl) hc
  · intro i his hii0
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hgi : g i = 0
    · rw [hgi, zero_mul]
    · have hle := hmax i (Finset.mem_filter.mpr ⟨his, hgi⟩)
      have hneq : m.toSyn (m.degree (p i)) ≠ m.toSyn (m.degree (p i0)) := by
        intro h
        exact hii0 (hinj (m.toSyn.injective h))
      rw [m.coeff_eq_zero_of_lt (lt_of_le_of_ne hle hneq), mul_zero]
  · intro h; exact absurd hi0s h

/-- Monomials of total degree `k` in `n` variables. -/
def D (n k : ℕ) : Finset (Fin n →₀ ℕ) := Finset.finsuppAntidiag Finset.univ k

theorem sum_eq_degree {n : ℕ} (μ : Fin n →₀ ℕ) : μ.sum (fun _ e => e) = μ.degree := rfl

theorem mem_D {n k : ℕ} (μ : Fin n →₀ ℕ) : μ ∈ D n k ↔ μ.degree = k := by
  unfold D
  rw [Finset.mem_finsuppAntidiag]
  have h1 : Finset.univ.sum μ = μ.degree := by
    rw [← sum_eq_degree, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rw [h1]
  simp

theorem homog_eq (K : Type) [Field K] (n k : ℕ) :
    homogeneousSubmodule (Fin n) K k = AddMonoidAlgebra.supported K K (↑(D n k) : Set (Fin n →₀ ℕ)) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  congr 1
  ext μ
  simp [mem_D]

theorem finrank_supp (K : Type) [Field K] (n : ℕ) (s : Finset (Fin n →₀ ℕ)) :
    Module.finrank K (AddMonoidAlgebra.supported K K (↑s : Set (Fin n →₀ ℕ))) = s.card := by
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) (↑s : Set (Fin n →₀ ℕ))).finrank_eq,
    Module.finrank_finsupp_self]
  simp

theorem finite_supp (K : Type) [Field K] (n : ℕ) (s : Finset (Fin n →₀ ℕ)) :
    Module.Finite K (AddMonoidAlgebra.supported K K (↑s : Set (Fin n →₀ ℕ))) :=
  Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
    (↑s : Set (Fin n →₀ ℕ))).symm

/-- Leading exponents of nonzero homogeneous elements of `I`. -/
def L {K : Type} [Field K] {n : ℕ} (m : MonomialOrder (Fin n))
    (I : Submodule K (MvPolynomial (Fin n) K)) : Set (Fin n →₀ ℕ) :=
  {μ | ∃ p ∈ I, p.IsHomogeneous μ.degree ∧ p ≠ 0 ∧ m.degree p = μ}

section
variable {K : Type} [Field K] {n : ℕ} (m : MonomialOrder (Fin n))
    (I : Submodule K (MvPolynomial (Fin n) K))

theorem L_add_X (hX : ∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) {μ : Fin n →₀ ℕ} (hμ : μ ∈ L m I)
    (v : Fin n) : μ + Finsupp.single v 1 ∈ L m I := by
  obtain ⟨p, hpI, hph, hp0, hpd⟩ := hμ
  refine ⟨X v * p, hX p hpI v, ?_, ?_, ?_⟩
  · have := (isHomogeneous_X K v).mul hph
    convert this using 1
    rw [map_add, add_comm]
    simp
  · exact mul_ne_zero (X_ne_zero v) hp0
  · rw [m.degree_mul (X_ne_zero v) hp0, m.degree_X, hpd, add_comm]

theorem L_add_single (hX : ∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) {μ : Fin n →₀ ℕ} (hμ : μ ∈ L m I)
    (v : Fin n) (b : ℕ) : μ + Finsupp.single v b ∈ L m I := by
  induction b with
  | zero => simpa using hμ
  | succ b ih =>
    have := L_add_X m I hX ih v
    rwa [add_assoc, ← Finsupp.single_add] at this

theorem L_add (hX : ∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) (a : Fin n →₀ ℕ) :
    ∀ {μ : Fin n →₀ ℕ}, μ ∈ L m I → μ + a ∈ L m I := by
  induction a using Finsupp.induction with
  | zero => intro μ hμ; simpa using hμ
  | single_add x b f _ _ ih =>
    intro μ hμ
    have := L_add_single m I hX (ih hμ) x b
    rwa [add_assoc, add_comm f] at this

theorem zero_notMem_L (h1 : (1 : MvPolynomial (Fin n) K) ∉ I) : (0 : Fin n →₀ ℕ) ∉ L m I := by
  rintro ⟨p, hpI, -, hp0, hpd⟩
  apply h1
  have hC := (m.degree_eq_zero_iff).mp hpd
  have hl : m.leadingCoeff p ≠ 0 := (m.leadingCoeff_ne_zero_iff).mpr hp0
  generalize m.leadingCoeff p = c at hC hl
  have : (1 : MvPolynomial (Fin n) K) = c⁻¹ • p := by
    rw [hC, smul_eq_C_mul, ← C_mul, inv_mul_cancel₀ hl, C_1]
  rw [this]
  exact I.smul_mem _ hpI

end

section count
variable {K : Type} [Field K] {n : ℕ} (m : MonomialOrder (Fin n))
    (I : Submodule K (MvPolynomial (Fin n) K)) [DecidablePred (· ∈ L m I)]

theorem homog_finite (k : ℕ) : Module.Finite K (homogeneousSubmodule (Fin n) K k) := by
  rw [homog_eq]; exact finite_supp K n _

theorem finrank_homog (k : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin n) K k) = (D n k).card := by
  rw [homog_eq]; exact finrank_supp K n _

theorem card_L_le (k : ℕ) :
    ((D n k).filter (· ∈ L m I)).card ≤
      Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) := by
  set A := (I ⊓ homogeneousSubmodule (Fin n) K k : Submodule K (MvPolynomial (Fin n) K))
  have : Module.Finite K (homogeneousSubmodule (Fin n) K k) := homog_finite k
  have : Module.Finite K A := Submodule.finiteDimensional_of_le inf_le_right
  set T := (D n k).filter (· ∈ L m I) with hTdef
  have hT : ∀ μ : T, ∃ p ∈ I, p.IsHomogeneous (μ : Fin n →₀ ℕ).degree ∧ p ≠ 0 ∧
      m.degree p = μ := fun μ => (Finset.mem_filter.mp μ.2).2
  choose p hpI hph hp0 hpd using hT
  have hdeg : ∀ μ : T, (μ : Fin n →₀ ℕ).degree = k :=
    fun μ => (mem_D _).mp (Finset.mem_filter.mp μ.2).1
  let q : T → A := fun μ => ⟨p μ, hpI μ, by have h := hph μ; rw [hdeg μ] at h; exact h⟩
  have hli : LinearIndependent K (A.subtype ∘ q) := by
    apply linIndep_of_degree_inj m
    · intro μ; exact hp0 μ
    · intro a b hab
      change m.degree (p a) = m.degree (p b) at hab
      rw [hpd, hpd] at hab
      exact Subtype.ext hab
  have := (LinearIndependent.of_comp _ hli).fintype_card_le_finrank
  simpa using this

theorem finrank_add_card_N_le (k : ℕ) :
    Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) +
      ((D n k).filter (· ∉ L m I)).card ≤ (D n k).card := by
  set H := homogeneousSubmodule (Fin n) K k with hH
  set A := (I ⊓ H : Submodule K (MvPolynomial (Fin n) K))
  set N := (D n k).filter (· ∉ L m I) with hN
  set V : Submodule K (MvPolynomial (Fin n) K) := AddMonoidAlgebra.supported K K (↑N : Set (Fin n →₀ ℕ))
  have : Module.Finite K H := homog_finite k
  have : Module.Finite K A := Submodule.finiteDimensional_of_le inf_le_right
  have : Module.Finite K V := finite_supp K n N
  have hVH : V ≤ H := by
    rw [hH, homog_eq]
    exact AddMonoidAlgebra.supported_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hdisj : A ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    rw [Submodule.mem_inf, Submodule.mem_inf] at hq
    obtain ⟨⟨hqI, hqH⟩, hqV⟩ := hq
    rw [Submodule.mem_bot]
    by_contra hq0
    have hmem : m.degree q ∈ q.support := m.degree_mem_support hq0
    have hNm : m.degree q ∈ N := by
      by_contra hn
      have := (AddMonoidAlgebra.mem_supported' ..).mp hqV (m.degree q) hn
      exact (mem_support_iff.mp hmem) this
    obtain ⟨hD, hL⟩ := Finset.mem_filter.mp hNm
    apply hL
    refine ⟨q, hqI, ?_, hq0, rfl⟩
    rw [(mem_D _).mp hD]; exact hqH
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A V
  rw [hdisj, finrank_bot] at h1
  have h2 : Module.finrank K ↥(A ⊔ V) ≤ Module.finrank K H :=
    Submodule.finrank_mono (sup_le inf_le_right hVH)
  have h3 : Module.finrank K V = N.card := finrank_supp K n N
  have h4 := finrank_homog (K := K) (n := n) k
  calc Module.finrank K A + N.card = Module.finrank K A + Module.finrank K V := by rw [h3]
    _ = Module.finrank K ↥(A ⊔ V) := by omega
    _ ≤ Module.finrank K H := h2
    _ = (D n k).card := h4

end count

theorem standardMonomials' : ∀ (K : Type) [Field K] (n M : ℕ) (I : Submodule K (MvPolynomial (Fin n) K)),
    (∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) →
    (1 : MvPolynomial (Fin n) K) ∉ I →
    ∃ S : Finset (Fin n →₀ ℕ), (0 : Fin n →₀ ℕ) ∈ S ∧
      (∀ μ ∈ S, ∀ ν : Fin n →₀ ℕ, ν ≤ μ → ν ∈ S) ∧
      ∀ k ≤ M, (S.filter (fun μ => μ.sum (fun _ e => e) = k)).card +
          Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) =
        Module.finrank K (homogeneousSubmodule (Fin n) K k) := by
  intro K _ n M I hX h1
  classical
  let m : MonomialOrder (Fin n) := MonomialOrder.lex
  refine ⟨((Finset.range (M+1)).biUnion (fun k => D n k)).filter (· ∉ L m I), ?_, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨⟨0, by omega, (mem_D _).mpr (map_zero _)⟩, zero_notMem_L m I h1⟩
  · intro μ hμ ν hνμ
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range] at hμ ⊢
    obtain ⟨⟨k, hk, hkD⟩, hμL⟩ := hμ
    refine ⟨⟨ν.degree, ?_, (mem_D _).mpr rfl⟩, ?_⟩
    · have h0 := (mem_D _).mp hkD
      have h2 : μ.degree = ν.degree + (μ - ν).degree := by
        calc μ.degree = (ν + (μ - ν)).degree := by rw [add_tsub_cancel_of_le hνμ]
          _ = _ := map_add _ _ _
      omega
    · intro hνL
      apply hμL
      have := L_add m I hX (μ - ν) hνL
      rwa [add_tsub_cancel_of_le hνμ] at this
  · intro k hk
    have hfilt : (((Finset.range (M+1)).biUnion (fun k => D n k)).filter (· ∉ L m I)).filter
        (fun μ => μ.sum (fun _ e => e) = k) = (D n k).filter (· ∉ L m I) := by
      apply Finset.ext
      intro μ
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_biUnion, sum_eq_degree]
      constructor
      · rintro ⟨⟨_, h'⟩, h⟩; exact ⟨(mem_D _).mpr h, h'⟩
      · rintro ⟨h, h'⟩
        exact ⟨⟨⟨k, Finset.mem_range.mpr (by omega), h⟩, h'⟩, (mem_D _).mp h⟩
    rw [hfilt]
    have a := card_L_le m I k
    have b := finrank_add_card_N_le m I k
    have c := Finset.card_filter_add_card_filter_not (s := D n k) (p := fun μ => μ ∈ L m I)
    have d := finrank_homog (K := K) (n := n) k
    omega

end GF93SM



namespace GF93S

open MvPolynomial

/-- C1b-iii (standard monomials; Macaulay 1927, Cox-Little-O'Shea Ch.5 Prop 5.3.4 / Ch.9 Prop 9.3.3):
for a homogeneous ideal `I` (as a `K`-subspace closed under multiplication by variables and under
taking homogeneous components) with `1 ∉ I`, and any degree bound `m`, there is a finite order ideal
of monomials containing `0` whose degree-`k` count is `dim_K (K[x]_k / I_k)` for every `k ≤ m`. -/
def StandardMonomials : Prop :=
  ∀ (K : Type) [Field K] (n m : ℕ) (I : Submodule K (MvPolynomial (Fin n) K)),
    (∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) →
    (∀ p ∈ I, ∀ k : ℕ, homogeneousComponent k p ∈ I) →
    (1 : MvPolynomial (Fin n) K) ∉ I →
    ∃ S : Finset (Fin n →₀ ℕ), (0 : Fin n →₀ ℕ) ∈ S ∧
      (∀ μ ∈ S, ∀ ν : Fin n →₀ ℕ, ν ≤ μ → ν ∈ S) ∧
      ∀ k ≤ m, (S.filter (fun μ => μ.sum (fun _ e => e) = k)).card +
          Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) =
        Module.finrank K (homogeneousSubmodule (Fin n) K k)

/-- C1b-i (Stanley 1980 via hard Lefschetz; McMullen 1993 / Timorin 1999): the Dehn-Sommerville
`g`-vector of a simplicial `d`-polytope is, in degrees `≤ d/2`, the Hilbert function of a standard
graded quotient `K[x_1..x_n]/I`. Stated abstractly for a given `g`. -/
def LefschetzHilbert (m : ℕ) (g : ℕ → ℕ) : Prop :=
  ∃ (n : ℕ) (I : Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    (∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) ∧
    (∀ p ∈ I, ∀ k : ℕ, homogeneousComponent k p ∈ I) ∧
    (1 : MvPolynomial (Fin n) ℚ) ∉ I ∧
    ∀ k ≤ m, g k + Module.finrank ℚ (I ⊓ homogeneousSubmodule (Fin n) ℚ k : Submodule ℚ _) =
      Module.finrank ℚ (homogeneousSubmodule (Fin n) ℚ k)


theorem mseq_congr (m : ℕ) (f g : ℕ → ℕ) (hf : Grunbaum2003.IsMSequence m f)
    (h : ∀ k ≤ m, f k = g k) : Grunbaum2003.IsMSequence m g := by
  obtain ⟨h0, hk⟩ := hf
  refine ⟨by rw [← h 0 (Nat.zero_le _)]; exact h0, ?_⟩
  intro k hk0 hkm
  rw [← h k hkm, ← h (k - 1) (by omega)]
  exact hk k hk0 hkm

/-- C1b glue: Lefschetz Hilbert function + standard monomials + Macaulay => M-sequence. -/
theorem mseq_of_lefschetz
    (hMac : ∀ (n m : ℕ) (S : Finset (Fin n →₀ ℕ)), (0 : Fin n →₀ ℕ) ∈ S →
      (∀ μ ∈ S, ∀ ν : Fin n →₀ ℕ, ν ≤ μ → ν ∈ S) →
      Grunbaum2003.IsMSequence m (fun k => (S.filter (fun μ => μ.sum (fun _ e => e) = k)).card))
    (hSM : StandardMonomials) (m : ℕ) (g : ℕ → ℕ) (hL : LefschetzHilbert m g) :
    Grunbaum2003.IsMSequence m g := by
  obtain ⟨n, I, hX, hH, h1, hg⟩ := hL
  obtain ⟨S, hS0, hSd, hS⟩ := hSM ℚ n m I hX hH h1
  refine mseq_congr m _ g (hMac n m S hS0 hSd) ?_
  intro k hk
  have a := hS k hk
  have b := hg k hk
  omega

theorem standardMonomials_holds : StandardMonomials :=
  fun K _ n m I hX _ h1 => GF93SM.standardMonomials' K n m I hX h1

/-- C1b-i, field-general form: `g` (in degrees `≤ m`) is the Hilbert function of a standard graded
quotient `K[x_1..x_n]/I` over some field `K` (allows characteristic-2 anisotropy routes). -/
def LefschetzHilbertF (m : ℕ) (g : ℕ → ℕ) : Prop :=
  ∃ (K : Type) (inst : Field K) (n : ℕ) (I : Submodule K (MvPolynomial (Fin n) K)),
    (∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) ∧
    (1 : MvPolynomial (Fin n) K) ∉ I ∧
    ∀ k ≤ m, g k + Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) =
      Module.finrank K (homogeneousSubmodule (Fin n) K k)

/-- C1b (minus C1b-i): a Hilbert function of a standard graded algebra is an M-sequence. -/
theorem mseq_of_lefschetzHilbertF (m : ℕ) (g : ℕ → ℕ) (hL : LefschetzHilbertF m g) :
    Grunbaum2003.IsMSequence m g := by
  obtain ⟨K, inst, n, I, hX, h1, hg⟩ := hL
  obtain ⟨S, hS0, hSd, hS⟩ := GF93SM.standardMonomials' K n m I hX h1
  refine mseq_congr m _ g (GF93M.macaulayOrderIdeal n m S hS0 hSd) ?_
  intro k hk
  have a := hS k hk
  have b := hg k hk
  omega

theorem mseq_of_lefschetzHilbert (m : ℕ) (g : ℕ → ℕ) (hL : LefschetzHilbert m g) :
    Grunbaum2003.IsMSequence m g :=
  mseq_of_lefschetz GF93M.macaulayOrderIdeal standardMonomials_holds m g hL

end GF93S



-- ==== from f9336347_b3.lean
set_option autoImplicit false

/-! Layer G1 (session 7): basic face structure of a polytope `P = convexHull V`, `V` finite.
Every exposed face is the convex hull of the extreme points it contains, there are finitely
many faces, every extreme point is exposed, and `faceCount P 0 = #(extreme points)`. -/

namespace GF93G

open Grunbaum2003

variable {d : ℕ}

abbrev E (d : ℕ) := Fin d → ℝ

theorem ext_finite {V : Set (E d)} (hV : V.Finite) :
    (Set.extremePoints ℝ (convexHull ℝ V)).Finite :=
  hV.subset extremePoints_convexHull_subset

/-- An exposed face of a polytope is the convex hull of the extreme points it contains. -/
theorem face_eq_hull {V F : Set (E d)} (hV : V.Finite)
    (hF : IsExposed ℝ (convexHull ℝ V) F) :
    F = convexHull ℝ (F ∩ Set.extremePoints ℝ (convexHull ℝ V)) := by
  have hPc : IsCompact (convexHull ℝ V) := hV.isCompact_convexHull (𝕜 := ℝ)
  have hFc : IsCompact F := hF.isCompact hPc
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ V)
  have hKM := closure_convexHull_extremePoints hFc hFconv
  rw [hF.isExtreme.extremePoints_eq] at hKM
  have hfin : (F ∩ Set.extremePoints ℝ (convexHull ℝ V)).Finite :=
    (ext_finite hV).subset Set.inter_subset_right
  rw [(hfin.isClosed_convexHull (𝕜 := ℝ)).closure_eq] at hKM
  exact hKM.symm

/-- The polytope is the convex hull of its extreme points. -/
theorem hull_ext {V : Set (E d)} (hV : V.Finite) :
    convexHull ℝ V = convexHull ℝ (Set.extremePoints ℝ (convexHull ℝ V)) := by
  have hPc : IsCompact (convexHull ℝ V) := hV.isCompact_convexHull (𝕜 := ℝ)
  have hKM := closure_convexHull_extremePoints hPc (convex_convexHull ℝ V)
  rw [((ext_finite hV).isClosed_convexHull (𝕜 := ℝ)).closure_eq] at hKM
  exact hKM.symm

/-- Finitely many faces. -/
theorem faces_finite {V : Set (E d)} (hV : V.Finite) (Q : Set (E d) → Prop) :
    {F : Set (E d) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ V) F ∧ Q F}.Finite := by
  apply ((ext_finite hV).powerset.image (convexHull ℝ)).subset
  rintro F ⟨_, hF, _⟩
  exact ⟨F ∩ Set.extremePoints ℝ (convexHull ℝ V), Set.inter_subset_right,
    (face_eq_hull hV hF).symm⟩

/-- Every extreme point of a polytope is an exposed point. -/
theorem extreme_exposed {V : Set (E d)} (hV : V.Finite) {e : E d}
    (he : e ∈ Set.extremePoints ℝ (convexHull ℝ V)) :
    IsExposed ℝ (convexHull ℝ V) {e} := by
  set P := convexHull ℝ V with hPdef
  set X := Set.extremePoints ℝ P with hXdef
  have hXf : X.Finite := ext_finite hV
  have heP : e ∈ P := he.1
  have hconv : Convex ℝ (P \ {e}) :=
    ((convex_convexHull ℝ V).mem_extremePoints_iff_convex_sdiff.mp he).2
  have hsub : X \ {e} ⊆ P \ {e} := fun x hx =>
    ⟨hx.1.1, hx.2⟩
  have hnot : e ∉ convexHull ℝ (X \ {e}) := fun h =>
    (convexHull_min hsub hconv h).2 rfl
  obtain ⟨f, u, hfe, hfb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    ((hXf.subset Set.sdiff_subset).isClosed_convexHull (𝕜 := ℝ)) hnot
  intro _
  refine ⟨-f, ?_⟩
  -- every point of P has (-f) ≤ (-f) e
  have hle : ∀ y ∈ P, (-f) y ≤ (-f) e := by
    have hhalf : Convex ℝ {y : E d | (-f) y ≤ (-f) e} :=
      convex_halfSpace_le (-f).toLinearMap.isLinear _
    have hXs : X ⊆ {y : E d | (-f) y ≤ (-f) e} := by
      intro x hx
      by_cases hxe : x = e
      · subst hxe; show (-f) x ≤ (-f) x; exact le_rfl
      · have := hfb x (subset_convexHull ℝ _ ⟨hx, hxe⟩)
        simp only [Set.mem_setOf_eq, ContinuousLinearMap.neg_apply]
        linarith
    intro y hy
    have hy' : y ∈ convexHull ℝ X := by rw [hXdef, ← hull_ext hV]; exact hy
    exact convexHull_min hXs hhalf hy'
  ext x
  constructor
  · rintro rfl; exact ⟨heP, hle⟩
  · rintro hx
    -- the exposed face F = {x ∈ P | ...} is the hull of its extreme points, all equal to e
    set F := {x ∈ P | ∀ y ∈ P, (-f) y ≤ (-f) x} with hFdef
    have hFexp : IsExposed ℝ P F := fun _ => ⟨-f, rfl⟩
    have hFX : F ∩ X ⊆ {e} := by
      rintro b ⟨hbF, hbX⟩
      by_contra hbe
      have h1 := hfb b (subset_convexHull ℝ _ ⟨hbX, hbe⟩)
      have h2 := hbF.2 e heP
      simp only [ContinuousLinearMap.neg_apply] at h2
      linarith
    have := face_eq_hull hV hFexp
    have hxF : x ∈ F := hx
    rw [this] at hxF
    have := convexHull_mono hFX hxF
    rwa [convexHull_singleton] at this

theorem finrank_zero_iff {F : Set (E d)} :
    Module.finrank ℝ (affineSpan ℝ F).direction = 0 ↔ F.Subsingleton := by
  rw [direction_affineSpan, Submodule.finrank_eq_zero, vectorSpan_eq_bot_iff_subsingleton]

/-- Vertices: `faceCount P 0` is the number of extreme points. -/
theorem faceCount_zero {V : Set (E d)} (hV : V.Finite) :
    faceCount (convexHull ℝ V) 0 = (Set.extremePoints ℝ (convexHull ℝ V)).ncard := by
  unfold faceCount
  have hset : {F : Set (E d) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ V) F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = 0} =
      (fun e => ({e} : Set (E d))) '' Set.extremePoints ℝ (convexHull ℝ V) := by
    ext F
    simp only [Set.mem_setOf_eq, Set.mem_image, finrank_zero_iff]
    constructor
    · rintro ⟨⟨x, hx⟩, hF, hs⟩
      have hFx : F = {x} := hs.eq_singleton_of_mem hx
      subst hFx
      exact ⟨x, exposedPoints_subset_extremePoints
        (mem_exposedPoints_iff_exposed_singleton.mpr hF), rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨Set.singleton_nonempty e, extreme_exposed hV he, Set.subsingleton_singleton⟩
  rw [hset, Set.ncard_image_of_injective _ Set.singleton_injective]

/-- A linear bound on the extreme points holds on the whole polytope. -/
theorem halfspace_of_ext {V : Set (E d)} (hV : V.Finite) (n : StrongDual ℝ (E d)) (c : ℝ)
    (hc : ∀ w ∈ Set.extremePoints ℝ (convexHull ℝ V), n w ≤ c) :
    ∀ y ∈ convexHull ℝ V, n y ≤ c := by
  intro y hy
  have hy' : y ∈ convexHull ℝ (Set.extremePoints ℝ (convexHull ℝ V)) := by
    rw [← hull_ext hV]; exact hy
  exact convexHull_min (t := {y | n y ≤ c}) hc (convex_halfSpace_le n.toLinearMap.isLinear c) hy'

/-- The face exposed by `l` is the hull of the extreme points maximizing `l`. -/
theorem argmax_eq_hull {V : Set (E d)} (hV : V.Finite) (l : StrongDual ℝ (E d)) :
    {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} =
      convexHull ℝ {v ∈ Set.extremePoints ℝ (convexHull ℝ V) |
        ∀ w ∈ Set.extremePoints ℝ (convexHull ℝ V), l w ≤ l v} := by
  have hFexp : IsExposed ℝ (convexHull ℝ V) {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} :=
    fun _ => ⟨l, rfl⟩
  apply Set.Subset.antisymm
  · intro x hx
    rw [face_eq_hull hV hFexp] at hx
    refine convexHull_mono ?_ hx
    rintro v ⟨hvF, hvX⟩
    exact ⟨hvX, fun w hw => hvF.2 w hw.1⟩
  · apply convexHull_min _ (hFexp.convex (convex_convexHull ℝ V))
    rintro v ⟨hvX, hv⟩
    exact ⟨hvX.1, halfspace_of_ext hV l _ hv⟩

/-- For polytopes, an exposed face of an exposed face is an exposed face. -/
theorem exposed_trans {V : Set (E d)} (hV : V.Finite) {F G : Set (E d)}
    (hF : IsExposed ℝ (convexHull ℝ V) F) (hG : IsExposed ℝ F G) :
    IsExposed ℝ (convexHull ℝ V) G := by
  classical
  intro hGne
  have hGconv : Convex ℝ G := hG.convex (hF.convex (convex_convexHull ℝ V))
  have hFne : F.Nonempty := hGne.mono hG.subset
  obtain ⟨l, rfl⟩ := hF hFne
  obtain ⟨m, rfl⟩ := hG hGne
  obtain ⟨x0, hx0⟩ := hGne
  have hXf := ext_finite hV
  have hgap : ∀ v ∈ Set.extremePoints ℝ (convexHull ℝ V),
      v ∉ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} → l v < l x0 := by
    intro v hv hvF
    by_contra hlt
    have hlt := not_lt.mp hlt
    exact hvF ⟨hv.1, fun y hy => (hx0.1.2 y hy).trans hlt⟩
  obtain ⟨δ, hδ, hδv⟩ : ∃ δ > 0, ∀ v ∈ Set.extremePoints ℝ (convexHull ℝ V),
      v ∉ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} → l v + δ ≤ l x0 := by
    by_cases hS : (hXf.toFinset.filter (fun v =>
        v ∉ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x})).Nonempty
    · obtain ⟨v0, hv0, hmin⟩ := Finset.exists_min_image _ (fun v => l x0 - l v) hS
      have hv0' := Finset.mem_filter.mp hv0
      refine ⟨l x0 - l v0, by linarith [hgap v0 (hXf.mem_toFinset.mp hv0'.1) hv0'.2], ?_⟩
      intro v hv hvF
      have := hmin v (Finset.mem_filter.mpr ⟨hXf.mem_toFinset.mpr hv, hvF⟩)
      linarith
    · exact ⟨1, one_pos, fun v hv hvF =>
        absurd ⟨v, Finset.mem_filter.mpr ⟨hXf.mem_toFinset.mpr hv, hvF⟩⟩ hS⟩
  obtain ⟨K, hK0, hKv⟩ : ∃ K : ℝ, 0 ≤ K ∧
      ∀ v ∈ Set.extremePoints ℝ (convexHull ℝ V), m v - m x0 ≤ K := by
    refine ⟨∑ v ∈ hXf.toFinset, |m v| + |m x0|, by positivity, ?_⟩
    intro v hv
    have h1 : |m v| ≤ ∑ v ∈ hXf.toFinset, |m v| :=
      Finset.single_le_sum (f := fun v => |m v|) (fun _ _ => abs_nonneg _)
        (hXf.mem_toFinset.mpr hv)
    have h2 := le_abs_self (m v)
    have h3 := neg_abs_le (m x0)
    linarith
  obtain ⟨t, ht0, htδ⟩ : ∃ t : ℝ, 0 < t ∧ t * δ = K + 1 :=
    ⟨(K + 1) / δ, div_pos (by linarith) hδ, div_mul_cancel₀ _ hδ.ne'⟩
  refine ⟨m + t • l, ?_⟩
  have hn : ∀ x, (m + t • l) x = m x + t * l x := fun x => by simp
  have hout : ∀ v ∈ Set.extremePoints ℝ (convexHull ℝ V),
      v ∉ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} →
      m v + t * l v < m x0 + t * l x0 := by
    intro v hv hvF
    have h1 := mul_le_mul_of_nonneg_left (hδv v hv hvF) ht0.le
    rw [mul_add] at h1
    have h2 := hKv v hv
    linarith
  have hvert : ∀ w ∈ Set.extremePoints ℝ (convexHull ℝ V), (m + t • l) w ≤ (m + t • l) x0 := by
    intro w hw
    rw [hn, hn]
    by_cases hwF : w ∈ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}
    · have h1 := mul_le_mul_of_nonneg_left (hx0.1.2 w hw.1) ht0.le
      have h2 : m w ≤ m x0 := hx0.2 w hwF
      linarith
    · exact (hout w hw hwF).le
  have hall := halfspace_of_ext hV (m + t • l) _ hvert
  ext x
  constructor
  · rintro ⟨hxF, hxG⟩
    refine ⟨hxF.1, fun y hy => (hall y hy).trans ?_⟩
    rw [hn, hn]
    have h1 := mul_le_mul_of_nonneg_left (hxF.2 x0 hx0.1.1) ht0.le
    have h2 : m x0 ≤ m x := hxG x0 hx0.1
    linarith
  · intro hx
    rw [argmax_eq_hull hV] at hx
    refine convexHull_min ?_ hGconv hx
    rintro v ⟨hvX, hvmax⟩
    have hge : (m + t • l) x0 ≤ (m + t • l) v :=
      halfspace_of_ext hV (m + t • l) _ hvmax x0 hx0.1.1
    rw [hn, hn] at hge
    by_cases hvF : v ∈ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}
    · refine ⟨hvF, fun y hy => ?_⟩
      have heq : l v = l x0 := le_antisymm (hx0.1.2 v hvX.1) (hvF.2 x0 hx0.1.1)
      rw [heq] at hge
      have h3 : m y ≤ m x0 := hx0.2 y hy
      linarith
    · exact absurd hge (not_le.mpr (hout v hvX hvF))

/-- G2a (OPEN): every proper face of a full-dimensional polytope lies in a facet. -/
def ProperFaceInFacet : Prop :=
  ∀ (d : ℕ) (V : Set (E d)), V.Finite → affineSpan ℝ (convexHull ℝ V) = ⊤ →
    ∀ F : Set (E d), F.Nonempty → IsExposed ℝ (convexHull ℝ V) F → F ≠ convexHull ℝ V →
      ∃ G : Set (E d), IsExposed ℝ (convexHull ℝ V) G ∧ F ⊆ G ∧
        Module.finrank ℝ (affineSpan ℝ G).direction + 1 = d

/-- G2b (OPEN): for a simplicial polytope, proper k-faces are exactly the vertex sets of size k+1
of the boundary complex. -/
def SimplicialFaceCount : Prop :=
  ∀ (d : ℕ) (P : Set (E d)), IsSimplicialDPolytope P → ∀ k < d,
    faceCount P k = {S : Set (E d) | ∃ F : Set (E d), F.Nonempty ∧ IsExposed ℝ P F ∧
      F ≠ P ∧ S = F ∩ Set.extremePoints ℝ P ∧ S.ncard = k + 1}.ncard


/-! ### G2a (session 8): proper faces lie in facets, by gift wrapping. -/

theorem vspan_le_ker {A : Set (E d)} (φ : E d →ₗ[ℝ] ℝ) (c : ℝ) (h : ∀ x ∈ A, φ x = c) :
    (affineSpan ℝ A).direction ≤ LinearMap.ker φ := by
  rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  simp [LinearMap.mem_ker, h x hx, h y hy]

theorem finrank_ker_add_one (φ : E d →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) :
    Module.finrank ℝ (LinearMap.ker φ) + 1 = d := by
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : LinearMap.range φ = ⊤ := by
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h; push_neg at h; exact hφ (LinearMap.ext h)
    rw [eq_top_iff]
    intro r _
    exact ⟨(r / φ x) • x, by simp [hx]⟩
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  omega

theorem toLin_ne {l : StrongDual ℝ (E d)} (hl : l ≠ 0) : (l.toLinearMap : E d →ₗ[ℝ] ℝ) ≠ 0 := by
  intro h
  apply hl
  ext x
  simpa using LinearMap.congr_fun h x

theorem dim_lt_of_const {A : Set (E d)} (φ : E d →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (c : ℝ)
    (h : ∀ x ∈ A, φ x = c) : Module.finrank ℝ (affineSpan ℝ A).direction + 1 ≤ d := by
  have h1 := Submodule.finrank_mono (vspan_le_ker φ c h)
  have h2 := finrank_ker_add_one φ hφ
  exact (Nat.add_le_add_right h1 1).trans h2.le

theorem face_dim_lt {V : Set (E d)} (l : StrongDual ℝ (E d)) (hl : l ≠ 0)
    (hG : ({x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} : Set (E d)).Nonempty) :
    Module.finrank ℝ (affineSpan ℝ
      {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}).direction + 1 ≤ d := by
  obtain ⟨x0, hx0⟩ := hG
  have hc : ∀ x ∈ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x},
      l.toLinearMap x = l x0 :=
    fun x hx => le_antisymm (hx0.2 x hx.1) (hx.2 x0 hx0.1)
  exact dim_lt_of_const l.toLinearMap (toLin_ne hl) _ hc

set_option maxHeartbeats 1000000 in
/-- One gift-wrapping step: a face of codimension at least 2 lies in a strictly larger
proper face. -/
theorem gift_step {V : Set (E d)} (hV : V.Finite) (htop : affineSpan ℝ (convexHull ℝ V) = ⊤)
    (l : StrongDual ℝ (E d)) (hl : l ≠ 0)
    (hGne : ({x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} : Set (E d)).Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ
      {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}).direction + 2 ≤ d) :
    ∃ G' : Set (E d), G'.Nonempty ∧ IsExposed ℝ (convexHull ℝ V) G' ∧ G' ≠ convexHull ℝ V ∧
      {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} ⊆ G' ∧
      Module.finrank ℝ (affineSpan ℝ
        {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}).direction <
        Module.finrank ℝ (affineSpan ℝ G').direction := by
  classical
  obtain ⟨g0, hg0⟩ := hGne
  have hXf := ext_finite hV
  obtain ⟨W, hW⟩ : ∃ W, W = (affineSpan ℝ
      {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}).direction := ⟨_, rfl⟩
  have hlG : ∀ x ∈ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}, l x = l g0 :=
    fun x hx => le_antisymm (hg0.2 x hx.1) (hx.2 g0 hg0.1)
  have hA := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [Module.finrank_fin_fun] at hA
  have hWd : Module.finrank ℝ W + 2 ≤ d := hW ▸ hdim
  obtain ⟨L, hL⟩ : ∃ L : Module.Dual ℝ (E d), L = l.toLinearMap := ⟨_, rfl⟩
  have hL0 : L ≠ 0 := by rw [hL]; exact toLin_ne hl
  have hspan := finrank_span_singleton (K := ℝ) hL0
  obtain ⟨m0, hm0A, hm0l⟩ : ∃ m ∈ W.dualAnnihilator, m ∉ ℝ ∙ L := by
    by_contra hcon
    push_neg at hcon
    have h3 := (Submodule.finrank_mono (show W.dualAnnihilator ≤ ℝ ∙ L from hcon)).trans hspan.le
    omega
  have hconstG : ∀ (m : Module.Dual ℝ (E d)), m ∈ W.dualAnnihilator →
      ∀ x ∈ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}, m x = m g0 := by
    intro m hm x hx
    have hmem : x -ᵥ g0 ∈ W := by
      rw [hW, direction_affineSpan]; exact vsub_mem_vectorSpan ℝ hx hg0
    have := (Submodule.mem_dualAnnihilator m).mp hm _ hmem
    rw [vsub_eq_sub, map_sub] at this
    linarith
  obtain ⟨v0, hv0X, hv0⟩ : ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ V), m0 v ≠ m0 g0 := by
    by_contra hcon
    push_neg at hcon
    have hc1 := halfspace_of_ext hV (LinearMap.toContinuousLinearMap m0) (m0 g0)
      (fun w hw => by simp [hcon w hw])
    have hc2 := halfspace_of_ext hV (-LinearMap.toContinuousLinearMap m0) (-m0 g0)
      (fun w hw => by simp [hcon w hw])
    have hcP : ∀ y ∈ convexHull ℝ V, m0 y = m0 g0 := fun y hy => by
      have a := hc1 y hy
      have b := hc2 y hy
      simp at a b
      linarith
    have hker := vspan_le_ker m0 _ hcP
    rw [htop, AffineSubspace.direction_top, top_le_iff] at hker
    apply hm0l
    have : m0 = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ LinearMap.ker m0 := by rw [hker]; trivial
      simpa using this
    rw [this]; exact Submodule.zero_mem _
  obtain ⟨m, hmA, hml, v1, hv1X, hv1⟩ : ∃ m ∈ W.dualAnnihilator, m ∉ ℝ ∙ L ∧
      ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ V), m g0 < m v := by
    rcases lt_or_gt_of_ne hv0 with h | h
    · refine ⟨-m0, neg_mem hm0A, fun h' => hm0l (by simpa using neg_mem h'), v0, hv0X, ?_⟩
      simp only [LinearMap.neg_apply]; linarith
    · exact ⟨m0, hm0A, hm0l, v0, hv0X, h⟩
  have hmG := hconstG m hmA
  have hT : (hXf.toFinset.filter (fun v => m g0 < m v)).Nonempty :=
    ⟨v1, Finset.mem_filter.mpr ⟨hXf.mem_toFinset.mpr hv1X, hv1⟩⟩
  obtain ⟨vs, hvsT, hvsmin⟩ := Finset.exists_min_image _
    (fun v => (l g0 - l v) / (m v - m g0)) hT
  have hvs := Finset.mem_filter.mp hvsT
  have hvsX : vs ∈ Set.extremePoints ℝ (convexHull ℝ V) := hXf.mem_toFinset.mp hvs.1
  have hlt : ∀ v ∈ Set.extremePoints ℝ (convexHull ℝ V), m g0 < m v → l v < l g0 := by
    intro v hv hmv
    by_contra hle
    push_neg at hle
    have hvG : v ∈ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} :=
      ⟨hv.1, fun y hy => (hg0.2 y hy).trans hle⟩
    linarith [hmG v hvG]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (l g0 - l vs) / (m vs - m g0) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]; exact div_pos (by linarith [hlt vs hvsX hvs.2]) (by linarith [hvs.2])
  have hsvs : s * (m vs - m g0) = l g0 - l vs := by
    rw [hs]; exact div_mul_cancel₀ _ (sub_pos.mpr hvs.2).ne'
  obtain ⟨n, hnx⟩ : ∃ n : StrongDual ℝ (E d), ∀ x, n x = l x + s * m x :=
    ⟨l + s • LinearMap.toContinuousLinearMap m, fun x => by simp⟩
  have hvert : ∀ w ∈ Set.extremePoints ℝ (convexHull ℝ V), n w ≤ n g0 := by
    intro w hw
    rw [hnx, hnx]
    by_cases hmw : m g0 < m w
    · have h1 := hvsmin w (Finset.mem_filter.mpr ⟨hXf.mem_toFinset.mpr hw, hmw⟩)
      rw [← hs] at h1
      have h2 := (le_div_iff₀ (by linarith : (0:ℝ) < m w - m g0)).mp h1
      nlinarith
    · push_neg at hmw
      have h1 := hg0.2 w hw.1
      nlinarith [mul_le_mul_of_nonneg_left hmw hs0.le]
  have hall := halfspace_of_ext hV n _ hvert
  have hnG : ∀ x ∈ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x}, n x = n g0 :=
    fun x hx => by rw [hnx, hnx, hlG x hx, hmG x hx]
  have hnvs : n vs = n g0 := by
    rw [hnx, hnx]; linarith
  have hn0 : n ≠ 0 := by
    intro h0
    apply hml
    rw [Submodule.mem_span_singleton]
    refine ⟨-s⁻¹, ?_⟩
    refine LinearMap.ext fun x => ?_
    have hx := hnx x
    rw [h0, ContinuousLinearMap.zero_apply] at hx
    rw [hL]
    simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    rw [show l x = -(s * m x) by linarith, neg_mul_neg, ← mul_assoc, inv_mul_cancel₀ hs0.ne',
      one_mul]
  have hG'ne : ({x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, n y ≤ n x} : Set (E d)).Nonempty :=
    ⟨g0, hg0.1, hall⟩
  have hsub : affineSpan ℝ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} ≤
      affineSpan ℝ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, n y ≤ n x} :=
    affineSpan_mono ℝ (fun x hx => ⟨hx.1, fun y hy => (hall y hy).trans (hnG x hx).ge⟩)
  refine ⟨{x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, n y ≤ n x}, hG'ne, fun _ => ⟨n, rfl⟩,
    ?_, fun x hx => ⟨hx.1, fun y hy => (hall y hy).trans (hnG x hx).ge⟩, ?_⟩
  · intro hEq
    have h1 := face_dim_lt n hn0 hG'ne
    rw [hEq, htop, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at h1
    omega
  · have hvsin : vs ∈ affineSpan ℝ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, n y ≤ n x} :=
      subset_affineSpan ℝ _ ⟨hvsX.1, fun y hy => (hall y hy).trans hnvs.ge⟩
    have hvsout : vs ∉ affineSpan ℝ {x ∈ convexHull ℝ V | ∀ y ∈ convexHull ℝ V, l y ≤ l x} := by
      intro hin
      have hmem := AffineSubspace.vsub_mem_direction hin (subset_affineSpan ℝ _ hg0)
      rw [← hW] at hmem
      have := (Submodule.mem_dualAnnihilator m).mp hmA _ hmem
      rw [vsub_eq_sub, map_sub] at this
      linarith [hvs.2]
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne (AffineSubspace.direction_le hsub) ?_
    intro hdir
    exact hvsout ((AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
      ⟨g0, subset_affineSpan ℝ _ hg0⟩ hsub) ▸ hvsin)

/-- G2a PROVED: every proper face of a full-dimensional polytope lies in a facet. -/
theorem properFaceInFacet : ProperFaceInFacet := by
  intro d V hV htop F hFne hF hFP
  obtain ⟨G, ⟨hGne, hGexp, hFG, hGP⟩, hGmax⟩ := Set.exists_max_image
    {G : Set (E d) | G.Nonempty ∧ IsExposed ℝ (convexHull ℝ V) G ∧ (F ⊆ G ∧ G ≠ convexHull ℝ V)}
    (fun G => Module.finrank ℝ (affineSpan ℝ G).direction)
    (faces_finite hV (fun G => F ⊆ G ∧ G ≠ convexHull ℝ V)) ⟨F, hFne, hF, subset_rfl, hFP⟩
  refine ⟨G, hGexp, hFG, ?_⟩
  obtain ⟨l, hl⟩ := hGexp hGne
  subst hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hGP
    ext x
    simp
  have h1 := face_dim_lt l hl0 hGne
  by_contra hne
  obtain ⟨G', hG'ne, hG'exp, hG'P, hGG', hlt⟩ := gift_step hV htop l hl0 hGne (by omega)
  have h2 := hGmax G' ⟨hG'ne, hG'exp, hFG.trans hGG', hG'P⟩
  omega


/-! ### G2b (session 8): face dimensions of a simplicial polytope are vertex counts minus one. -/

theorem face_dim_card {d : ℕ} {P : Set (E d)} (hP : IsSimplicialDPolytope P) {F : Set (E d)}
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F) (hFP : F ≠ P) :
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 = (F ∩ Set.extremePoints ℝ P).ncard := by
  obtain ⟨⟨⟨V, hVf, -, rfl⟩, htop⟩, hsimp⟩ := hP
  obtain ⟨G, hG, hFG, hGd⟩ := properFaceInFacet d V hVf htop F hFne hF hFP
  obtain ⟨v, hv, hGv⟩ := hsimp G (hFne.mono hFG) hG hGd
  obtain ⟨S, hS⟩ : ∃ S, S = F ∩ Set.extremePoints ℝ (convexHull ℝ V) := ⟨_, rfl⟩
  rw [← hS]
  have hSf : S.Finite := hS ▸ (ext_finite hVf).subset Set.inter_subset_right
  have hSv : S ⊆ Set.range v := by
    rw [hS]
    rintro x ⟨hxF, hxX⟩
    have hxE : x ∈ Set.extremePoints ℝ G :=
      inter_extremePoints_subset_extremePoints_of_subset hG.subset ⟨hFG hxF, hxX⟩
    rw [hGv] at hxE
    exact extremePoints_convexHull_subset hxE
  have hSi : AffineIndependent ℝ ((↑) : S → E d) := hv.range.mono hSv
  have hFS : F = convexHull ℝ S := by rw [hS]; exact face_eq_hull hVf hF
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hFS, h, convexHull_empty] at hFne
    exact Set.not_nonempty_empty hFne
  have hpos : 0 < S.ncard := (Set.ncard_pos hSf).mpr hSne
  have := hSf.fintype
  have hcard : Fintype.card S = (S.ncard - 1) + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; omega
  have h1 := hSi.finrank_vectorSpan hcard
  rw [Subtype.range_coe] at h1
  rw [hFS, affineSpan_convexHull, direction_affineSpan, h1]
  omega

/-- G2b PROVED. -/
theorem simplicialFaceCount : SimplicialFaceCount := by
  intro d P hP k hk
  unfold faceCount
  have hdimP : ∀ F : Set (E d), F = P → Module.finrank ℝ (affineSpan ℝ F).direction = d := by
    rintro F rfl
    rw [hP.1.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  have hset : {S : Set (E d) | ∃ F : Set (E d), F.Nonempty ∧ IsExposed ℝ P F ∧
      F ≠ P ∧ S = F ∩ Set.extremePoints ℝ P ∧ S.ncard = k + 1} =
      (fun F => F ∩ Set.extremePoints ℝ P) '' {F : Set (E d) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k} := by
    ext S
    constructor
    · rintro ⟨F, hFne, hF, hFP, rfl, hc⟩
      refine ⟨F, ⟨hFne, hF, ?_⟩, rfl⟩
      have := face_dim_card hP hFne hF hFP
      omega
    · rintro ⟨F, ⟨hFne, hF, hk'⟩, rfl⟩
      have hFP : F ≠ P := fun h => by have := hdimP F h; omega
      refine ⟨F, hFne, hF, hFP, rfl, ?_⟩
      show (F ∩ Set.extremePoints ℝ P).ncard = k + 1
      have := face_dim_card hP hFne hF hFP
      omega
  rw [hset, Set.ncard_image_of_injOn]
  rintro F ⟨hFne, hF, -⟩ G ⟨hGne, hG, -⟩ hFG
  obtain ⟨⟨V, hVf, -, rfl⟩, -⟩ := hP.1
  rw [face_eq_hull hVf hF, face_eq_hull hVf hG]
  exact congrArg (convexHull ℝ) hFG

end GF93G


set_option autoImplicit false

/-! C1a-h shelling layer (session 9): the abstract line-shelling argument in polar form.
`Φ` = facets (vertex finsets), `a F` = facet normal (`a F ⬝ᵥ w = 1` on `F`, `≤ 1` on vertices),
`nb F v` = the facet adjacent to `F` across the ridge `F \ {v}`, `c` a generic direction.
Restriction set `R F = {v ∈ F | c ⬝ a F < c ⬝ a (nb F v)}`; every simplex `G` of the boundary
lies in exactly one interval `[R F, F]`. -/

namespace GF93SH

open Matrix Finset

abbrev E (d : ℕ) := Fin d → ℝ

variable {d : ℕ}

theorem eq_zero_of_dot_span {S : Set (E d)} (hspan : Submodule.span ℝ S = ⊤) (u : E d)
    (h : ∀ w ∈ S, u ⬝ᵥ w = 0) : u = 0 := by
  have hall : ∀ x : E d, u ⬝ᵥ x = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℝ S := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simp
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul r x _ hx => rw [dotProduct_smul, hx, smul_zero]
  exact dotProduct_self_eq_zero.mp (hall u)

theorem sum_dot {ι : Type*} (s : Finset ι) (f : ι → E d) (w : E d) :
    (∑ i ∈ s, f i) ⬝ᵥ w = ∑ i ∈ s, f i ⬝ᵥ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, add_dotProduct, ih]

theorem dot_sum {ι : Type*} (s : Finset ι) (f : ι → E d) (w : E d) :
    w ⬝ᵥ (∑ i ∈ s, f i) = ∑ i ∈ s, w ⬝ᵥ f i := by
  rw [dotProduct_comm, sum_dot]
  exact sum_congr rfl (fun i _ => dotProduct_comm _ _)

/-- Key inequality (local optimality ⇒ global, simplex-method style). -/
theorem shell_ineq (F G : Finset (E d)) (hspan : ∀ y : E d, (∀ w ∈ F, y ⬝ᵥ w = 0) → y = 0)
    (hGF : G ⊆ F) (aF aF' c : E d) (δ : E d → E d)
    (hF : ∀ w ∈ F, aF ⬝ᵥ w = 1) (hF' : ∀ w ∈ F, aF' ⬝ᵥ w ≤ 1) (hG : ∀ w ∈ G, aF' ⬝ᵥ w = 1)
    (hδ : ∀ v ∈ F, ∀ w ∈ F, w ≠ v → δ v ⬝ᵥ w = 1) (hδv : ∀ v ∈ F, δ v ⬝ᵥ v < 1)
    (hc : ∀ v ∈ F, v ∉ G → c ⬝ᵥ δ v < c ⬝ᵥ aF) : c ⬝ᵥ aF' ≤ c ⬝ᵥ aF := by
  classical
  set lam : E d → ℝ := fun v => (aF' ⬝ᵥ v - 1) / (δ v ⬝ᵥ v - 1) with hlam
  have hrep : aF' - aF = ∑ v ∈ F, lam v • (δ v - aF) := by
    have h0 := hspan (aF' - aF - ∑ v ∈ F, lam v • (δ v - aF)) (by
      intro w hw
      have hw' : w ∈ F := hw
      rw [sub_dotProduct, sum_dot, sub_dotProduct, hF w hw']
      rw [sum_eq_single w]
      · rw [smul_dotProduct, sub_dotProduct, hF w hw', smul_eq_mul, hlam]
        have hne : δ w ⬝ᵥ w - 1 ≠ 0 := by linarith [hδv w hw']
        field_simp
        ring
      · intro v hv hvw
        rw [smul_dotProduct, sub_dotProduct, hδ v hv w hw' (Ne.symm hvw), hF w hw']
        simp
      · intro h; exact absurd hw' h)
    exact sub_eq_zero.mp h0
  have key : c ⬝ᵥ (aF' - aF) ≤ 0 := by
    rw [hrep, dot_sum]
    apply sum_nonpos
    intro v hv
    rw [dotProduct_smul, smul_eq_mul]
    have hlam0 : 0 ≤ lam v := by
      simp only [hlam]
      exact div_nonneg_of_nonpos (by linarith [hF' v hv]) (by linarith [hδv v hv])
    by_cases hvG : v ∈ G
    · have : lam v = 0 := by simp only [hlam, hG v hvG, sub_self, zero_div]
      rw [this, zero_mul]
    · rw [dotProduct_sub]
      exact mul_nonpos_of_nonneg_of_nonpos hlam0 (by linarith [hc v hv hvG])
  rw [dotProduct_sub] at key
  linarith

/-- Restriction set of a facet for the direction `c`. -/
noncomputable def R (a : Finset (E d) → E d) (nb : Finset (E d) → E d → Finset (E d)) (c : E d)
    (F : Finset (E d)) : Finset (E d) :=
  F.filter (fun v => c ⬝ᵥ a F < c ⬝ᵥ a (nb F v))

theorem R_subset (a : Finset (E d) → E d) (nb : Finset (E d) → E d → Finset (E d)) (c : E d)
    (F : Finset (E d)) : R a nb c F ⊆ F := filter_subset _ _

/-- Shelling uniqueness: every face `G` lies in exactly one interval `[R F, F]`. -/
theorem shelling (Φ : Finset (Finset (E d))) (a : Finset (E d) → E d)
    (nb : Finset (E d) → E d → Finset (E d)) (c : E d)
    (hspan : ∀ F ∈ Φ, ∀ y : E d, (∀ w ∈ F, y ⬝ᵥ w = 0) → y = 0)
    (ha1 : ∀ F ∈ Φ, ∀ w ∈ F, a F ⬝ᵥ w = 1)
    (ha2 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w ≤ 1)
    (ha3 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w = 1 → w ∈ F')
    (hnb : ∀ F ∈ Φ, ∀ v ∈ F, nb F v ∈ Φ ∧ F.erase v ⊆ nb F v ∧ v ∉ nb F v)
    (hgen : ∀ F ∈ Φ, ∀ F' ∈ Φ, c ⬝ᵥ a F = c ⬝ᵥ a F' → F = F')
    (G : Finset (E d)) (hG : ∃ F ∈ Φ, G ⊆ F) :
    ∃! F, F ∈ Φ ∧ R a nb c F ⊆ G ∧ G ⊆ F := by
  classical
  -- local optimality at a facet satisfying R F ⊆ G
  have hloc : ∀ F ∈ Φ, R a nb c F ⊆ G → ∀ v ∈ F, v ∉ G → c ⬝ᵥ a (nb F v) < c ⬝ᵥ a F := by
    intro F hF hR v hv hvG
    have hnR : v ∉ R a nb c F := fun h => hvG (hR h)
    simp only [R, mem_filter, not_and, not_lt] at hnR
    have hle := hnR hv
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hgen _ (hnb F hF v hv).1 _ hF h
      exact (hnb F hF v hv).2.2 (by rw [this]; exact hv)
  have hcmp : ∀ F ∈ Φ, ∀ F' ∈ Φ, R a nb c F ⊆ G → G ⊆ F → G ⊆ F' →
      c ⬝ᵥ a F' ≤ c ⬝ᵥ a F := by
    intro F hF F' hF' hR hGF hGF'
    refine shell_ineq F G (hspan F hF) hGF (a F) (a F') c (fun v => a (nb F v)) (ha1 F hF)
      (ha2 F hF F' hF') (fun w hw => ha1 F' hF' w (hGF' hw)) ?_ ?_ (hloc F hF hR)
    · intro v hv w hw hwv
      exact ha1 _ (hnb F hF v hv).1 w ((hnb F hF v hv).2.1 (mem_erase.mpr ⟨hwv, hw⟩))
    · intro v hv
      have h1 := ha2 F hF _ (hnb F hF v hv).1 v hv
      rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd (ha3 F hF _ (hnb F hF v hv).1 v hv h) (hnb F hF v hv).2.2
  obtain ⟨F0, hF0, hGF0⟩ := hG
  have hne : (Φ.filter (fun F => G ⊆ F)).Nonempty := ⟨F0, mem_filter.mpr ⟨hF0, hGF0⟩⟩
  obtain ⟨F, hFm, hmax⟩ := exists_max_image _ (fun F => c ⬝ᵥ a F) hne
  rw [mem_filter] at hFm
  refine ⟨F, ⟨hFm.1, ?_, hFm.2⟩, ?_⟩
  · intro v hv
    by_contra hvG
    have hvF : v ∈ F := R_subset a nb c F hv
    have hGn : G ⊆ nb F v := fun x hx =>
      (hnb F hFm.1 v hvF).2.1 (mem_erase.mpr ⟨fun h => hvG (h ▸ hx), hFm.2 hx⟩)
    have h1 := hmax _ (mem_filter.mpr ⟨(hnb F hFm.1 v hvF).1, hGn⟩)
    simp only [R, mem_filter] at hv
    linarith [hv.2]
  · rintro F' ⟨hF', hR', hGF'⟩
    have h1 := hcmp F' hF' F hFm.1 hR' hGF' hFm.2
    have h2 := hmax F' (mem_filter.mpr ⟨hF', hGF'⟩)
    exact hgen _ hF' _ hFm.1 (le_antisymm h2 h1)

/-- Reversing the direction complements the restriction sets. -/
theorem R_neg (Φ : Finset (Finset (E d))) (a : Finset (E d) → E d)
    (nb : Finset (E d) → E d → Finset (E d)) (c : E d)
    (hnb : ∀ F ∈ Φ, ∀ v ∈ F, nb F v ∈ Φ ∧ F.erase v ⊆ nb F v ∧ v ∉ nb F v)
    (hgen : ∀ F ∈ Φ, ∀ F' ∈ Φ, c ⬝ᵥ a F = c ⬝ᵥ a F' → F = F') (F : Finset (E d)) (hF : F ∈ Φ) :
    R a nb (-c) F = F \ R a nb c F := by
  classical
  ext v
  simp only [R, mem_filter, mem_sdiff, neg_dotProduct, neg_lt_neg_iff, not_and, not_lt]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun _ => h.le⟩
  · rintro ⟨hv, h⟩
    refine ⟨hv, (h hv).lt_of_ne ?_⟩
    intro heq
    have := hgen _ (hnb F hF v hv).1 _ hF heq
    exact (hnb F hF v hv).2.2 (by rw [this]; exact hv)

/-- The relation `f_k = ∑ h_i C(d-i, d-k)` determines `h` (unitriangular). -/
theorem tri_unique (h h' : ℕ → ℤ)
    (hrel : ∀ k ≤ d, ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - k) : ℤ) =
      ∑ i ∈ range (d + 1), h' i * ((d - i).choose (d - k) : ℤ)) :
    ∀ k ≤ d, h k = h' k := by
  have hcut : ∀ (u : ℕ → ℤ) (k : ℕ), k ≤ d → ∑ i ∈ range (d + 1), u i * ((d - i).choose (d - k) : ℤ) =
      ∑ i ∈ range k, u i * ((d - i).choose (d - k) : ℤ) + u k := by
    intro u k hk
    have hsub : range (k + 1) ⊆ range (d + 1) := range_subset_range.mpr (by omega)
    rw [← sum_subset hsub (fun i hi hni => by
      have : k < i := by simp only [mem_range] at hni; omega
      rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hi; omega)]
      simp)]
    rw [sum_range_succ, Nat.choose_self]
    simp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have e := hrel k hk
    rw [hcut h k hk, hcut h' k hk] at e
    have hs : ∑ i ∈ range k, h i * ((d - i).choose (d - k) : ℤ) =
        ∑ i ∈ range k, h' i * ((d - i).choose (d - k) : ℤ) :=
      sum_congr rfl (fun i hi => by rw [ih i (mem_range.mp hi) (by simp only [mem_range] at hi; omega)])
    linarith

theorem interval_card {α : Type*} [DecidableEq α] (R F : Finset α) (hRF : R ⊆ F) (k : ℕ)
    (hk : k ≤ F.card) :
    ((F.powerset).filter (fun G => R ⊆ G ∧ G.card = k)).card =
      (F.card - R.card).choose (F.card - k) := by
  have hc : (F \ R).card + R.card = F.card := card_sdiff_add_card_eq_card hRF
  rw [show F.card - R.card = (F \ R).card by omega, ← card_powersetCard]
  apply card_nbij' (fun G => F \ G) (fun T => F \ T)
  · intro G hG
    change G ∈ F.powerset.filter (fun G => R ⊆ G ∧ G.card = k) at hG
    show F \ G ∈ powersetCard (F.card - k) (F \ R)
    simp only [mem_filter, mem_powerset, mem_powersetCard] at hG ⊢
    refine ⟨sdiff_subset_sdiff le_rfl hG.2.1, ?_⟩
    have := card_sdiff_add_card_eq_card hG.1
    omega
  · intro T hT
    change T ∈ powersetCard (F.card - k) (F \ R) at hT
    show F \ T ∈ F.powerset.filter (fun G => R ⊆ G ∧ G.card = k)
    simp only [mem_filter, mem_powerset, mem_powersetCard] at hT ⊢
    have hTF : T ⊆ F := hT.1.trans sdiff_subset
    refine ⟨sdiff_subset, ?_, ?_⟩
    · intro x hx
      refine mem_sdiff.mpr ⟨hRF hx, fun hxT => ?_⟩
      exact (mem_sdiff.mp (hT.1 hxT)).2 hx
    · have := card_sdiff_add_card_eq_card hTF
      omega
  · intro G hG
    change G ∈ F.powerset.filter (fun G => R ⊆ G ∧ G.card = k) at hG
    simp only [mem_filter, mem_powerset] at hG
    exact Finset.sdiff_sdiff_eq_self hG.1
  · intro T hT
    change T ∈ powersetCard (F.card - k) (F \ R) at hT
    simp only [mem_powersetCard] at hT
    exact Finset.sdiff_sdiff_eq_self (hT.1.trans sdiff_subset)

theorem shell_count {α : Type*} [DecidableEq α] (Φ : Finset (Finset α)) (R : Finset α → Finset α)
    (d : ℕ) (hcard : ∀ F ∈ Φ, F.card = d) (hRF : ∀ F ∈ Φ, R F ⊆ F)
    (Δ : Finset (Finset α)) (hΔ : ∀ G, G ∈ Δ ↔ ∃ F ∈ Φ, G ⊆ F)
    (huniq : ∀ G ∈ Δ, ∃! F, F ∈ Φ ∧ R F ⊆ G ∧ G ⊆ F) (k : ℕ) (hk : k ≤ d) :
    ((Δ.filter (fun G => G.card = k)).card : ℤ) =
      ∑ i ∈ range (d + 1), ((Φ.filter (fun F => (R F).card = i)).card : ℤ) *
        ((d - i).choose (d - k) : ℤ) := by
  have hset : Δ.filter (fun G => G.card = k) =
      Φ.biUnion (fun F => F.powerset.filter (fun G => R F ⊆ G ∧ G.card = k)) := by
    ext G
    simp only [mem_filter, mem_biUnion, mem_powerset]
    constructor
    · rintro ⟨hG, hGk⟩
      obtain ⟨F, ⟨hF, hRG, hGF⟩, -⟩ := huniq G hG
      exact ⟨F, hF, hGF, hRG, hGk⟩
    · rintro ⟨F, hF, hGF, hRG, hGk⟩
      exact ⟨(hΔ G).mpr ⟨F, hF, hGF⟩, hGk⟩
  have hmaps : ∀ F ∈ Φ, (R F).card ∈ range (d + 1) := by
    intro F hF
    rw [mem_range]
    have := card_le_card (hRF F hF)
    rw [hcard F hF] at this
    omega
  rw [hset, card_biUnion, Nat.cast_sum, ← sum_fiberwise_of_maps_to hmaps]
  · apply sum_congr rfl
    intro i _
    have : ∀ F ∈ Φ.filter (fun F => (R F).card = i),
        (((F.powerset.filter (fun G => R F ⊆ G ∧ G.card = k)).card : ℕ) : ℤ) =
          ((d - i).choose (d - k) : ℤ) := by
      intro F hF
      rw [mem_filter] at hF
      rw [interval_card (R F) F (hRF F hF.1) k (by rw [hcard F hF.1]; exact hk), hcard F hF.1, hF.2]
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  · intro F hF F' hF' hne
    simp only [Function.onFun, Finset.disjoint_left, mem_filter, mem_powerset]
    rintro G ⟨hGF, hRG, -⟩ ⟨hGF', hRG', -⟩
    obtain ⟨F0, -, huF⟩ := huniq G ((hΔ G).mpr ⟨F, hF, hGF⟩)
    exact hne ((huF F ⟨hF, hRG, hGF⟩).trans (huF F' ⟨hF', hRG', hGF'⟩).symm)


open scoped Classical in
/-- C1a-h from shelling data: the h-vector of a line shelling is symmetric, starts at 1, and
counts the boundary simplices. -/
theorem hvector_of_shelling (Φ : Finset (Finset (E d))) (a : Finset (E d) → E d)
    (nb : Finset (E d) → E d → Finset (E d)) (c : E d)
    (hcard : ∀ F ∈ Φ, F.card = d) (hΦ : Φ.Nonempty)
    (hspan : ∀ F ∈ Φ, ∀ y : E d, (∀ w ∈ F, y ⬝ᵥ w = 0) → y = 0)
    (ha1 : ∀ F ∈ Φ, ∀ w ∈ F, a F ⬝ᵥ w = 1)
    (ha2 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w ≤ 1)
    (ha3 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w = 1 → w ∈ F')
    (hnb : ∀ F ∈ Φ, ∀ v ∈ F, nb F v ∈ Φ ∧ F.erase v ⊆ nb F v ∧ v ∉ nb F v)
    (hgen : ∀ F ∈ Φ, ∀ F' ∈ Φ, c ⬝ᵥ a F = c ⬝ᵥ a F' → F = F') :
    ∃ h : ℕ → ℤ, h 0 = 1 ∧ (∀ i ≤ d, h i = h (d - i)) ∧
      ∀ k ≤ d, (((Φ.biUnion powerset).filter (fun G => G.card = k)).card : ℤ) =
        ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - k) : ℤ) := by
  have hΔ : ∀ G, G ∈ Φ.biUnion powerset ↔ ∃ F ∈ Φ, G ⊆ F := by
    intro G; simp only [mem_biUnion, mem_powerset]
  have hgen' : ∀ F ∈ Φ, ∀ F' ∈ Φ, (-c) ⬝ᵥ a F = (-c) ⬝ᵥ a F' → F = F' := by
    intro F hF F' hF' h
    rw [neg_dotProduct, neg_dotProduct, neg_inj] at h
    exact hgen F hF F' hF' h
  have cnt : ∀ c' : E d, (∀ F ∈ Φ, ∀ F' ∈ Φ, c' ⬝ᵥ a F = c' ⬝ᵥ a F' → F = F') → ∀ k ≤ d,
      (((Φ.biUnion powerset).filter (fun G => G.card = k)).card : ℤ) =
        ∑ i ∈ range (d + 1), ((Φ.filter (fun F => (R a nb c' F).card = i)).card : ℤ) *
          ((d - i).choose (d - k) : ℤ) := fun c' hg k hk =>
    shell_count Φ (R a nb c') d hcard (fun F _ => R_subset a nb c' F) _ hΔ
      (fun G hG => shelling Φ a nb c' hspan ha1 ha2 ha3 hnb hg G ((hΔ G).mp hG)) k hk
  have hneg : ∀ i ≤ d, ((Φ.filter (fun F => (R a nb (-c) F).card = i)).card : ℤ) =
      ((Φ.filter (fun F => (R a nb c F).card = d - i)).card : ℤ) := by
    intro i hi
    congr 2
    apply filter_congr
    intro F hF
    rw [R_neg Φ a nb c hnb hgen F hF]
    have e := card_sdiff_add_card_eq_card (R_subset a nb c F)
    rw [hcard F hF] at e
    constructor <;> intro <;> omega
  have htri := tri_unique (d := d)
    (fun i => ((Φ.filter (fun F => (R a nb c F).card = i)).card : ℤ))
    (fun i => ((Φ.filter (fun F => (R a nb (-c) F).card = i)).card : ℤ))
    (fun k hk => (cnt c hgen k hk).symm.trans (cnt (-c) hgen' k hk))
  refine ⟨fun i => ((Φ.filter (fun F => (R a nb c F).card = i)).card : ℤ), ?_, ?_,
    fun k hk => cnt c hgen k hk⟩
  · obtain ⟨F0, ⟨hF0, hR0, -⟩, huq⟩ := shelling Φ a nb c hspan ha1 ha2 ha3 hnb hgen ∅
      ⟨hΦ.choose, hΦ.choose_spec, empty_subset _⟩
    have hs : Φ.filter (fun F => (R a nb c F).card = 0) = {F0} := by
      ext F
      simp only [mem_filter, mem_singleton, card_eq_zero]
      constructor
      · rintro ⟨hF, hR⟩
        exact huq F ⟨hF, by simp [hR], empty_subset _⟩
      · rintro rfl
        exact ⟨hF0, subset_empty.mp hR0⟩
    simp only [hs, card_singleton, Nat.cast_one]
  · intro i hi
    exact (htri i hi).trans (hneg i hi)

/-- Distinct facets have distinct normals. -/
theorem a_inj (Φ : Finset (Finset (E d))) (a : Finset (E d) → E d)
    (hcard : ∀ F ∈ Φ, F.card = d) (ha1 : ∀ F ∈ Φ, ∀ w ∈ F, a F ⬝ᵥ w = 1)
    (ha3 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w = 1 → w ∈ F') :
    ∀ F ∈ Φ, ∀ F' ∈ Φ, a F = a F' → F = F' := by
  intro F hF F' hF' h
  have hsub : F ⊆ F' := fun w hw => ha3 F hF F' hF' w hw (by rw [← h]; exact ha1 F hF w hw)
  exact eq_of_subset_of_card_le hsub (by rw [hcard F hF, hcard F' hF'])

/-- A generic direction exists (moment curve `c = (t^i)`, `t` off finitely many roots). -/
theorem exists_generic (Φ : Finset (Finset (E d))) (a : Finset (E d) → E d)
    (hinj : ∀ F ∈ Φ, ∀ F' ∈ Φ, a F = a F' → F = F') :
    ∃ c : E d, ∀ F ∈ Φ, ∀ F' ∈ Φ, c ⬝ᵥ a F = c ⬝ᵥ a F' → F = F' := by
  classical
  let p : E d → Polynomial ℝ := fun u => ∑ i : Fin d, Polynomial.C (u i) * Polynomial.X ^ (i : ℕ)
  have hp0 : ∀ u : E d, u ≠ 0 → p u ≠ 0 := by
    intro u hu hpu
    apply hu
    funext i
    have := congrArg (fun q => Polynomial.coeff q (i : ℕ)) hpu
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h).symm
    · simp
  have hev : ∀ (u : E d) (t : ℝ), (p u).eval t = (fun i : Fin d => t ^ (i : ℕ)) ⬝ᵥ u := by
    intro u t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, dotProduct]
    exact sum_congr rfl (fun i _ => mul_comm _ _)
  let S := (Φ ×ˢ Φ).filter (fun q => q.1 ≠ q.2)
  let Q := ∏ q ∈ S, p (a q.1 - a q.2)
  have hQ : Q ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro q hq
    simp only [S, mem_filter, mem_product] at hq
    apply hp0
    intro h
    exact hq.2 (hinj _ hq.1.1 _ hq.1.2 (sub_eq_zero.mp h))
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset Q.roots.toFinset
  refine ⟨fun i => t ^ (i : ℕ), fun F hF F' hF' h => ?_⟩
  by_contra hne
  have hQt : Q.eval t ≠ 0 := by
    intro h0
    exact ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr h0))
  rw [Polynomial.eval_prod, prod_ne_zero_iff] at hQt
  have := hQt (F, F') (by simp only [S, mem_filter, mem_product]; exact ⟨⟨hF, hF'⟩, hne⟩)
  rw [hev, dotProduct_sub, h, sub_self] at this
  exact this rfl

/-- `T` is not contained in a hyperplane through `0` (spans the space). -/
def Full (T : Finset (E d)) : Prop := ∀ y : E d, (∀ x ∈ T, y ⬝ᵥ x = 0) → y = 0

/-- Neighbor lemma N (polar form, Bruggesser–Mani): across each ridge `F \ {v}` of a facet
`F = {x ∈ V | a ⬝ x = 1}` there is a facet `{x ∈ V | b ⬝ x = 1}` containing the ridge and not `v`.
`hI`: `0` is interior; `hS`: simpliciality (full tight sets have `d` points). -/
theorem neighbor (V : Finset (E d)) (hI : ∀ u : E d, u ≠ 0 → ∃ x ∈ V, 0 < u ⬝ᵥ x)
    (hS : ∀ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) → Full (V.filter (fun x => b ⬝ᵥ x = 1)) →
      (V.filter (fun x => b ⬝ᵥ x = 1)).card = d)
    (a : E d) (ha : ∀ x ∈ V, a ⬝ᵥ x ≤ 1) (hF : Full (V.filter (fun x => a ⬝ᵥ x = 1)))
    (v : E d) (hv : v ∈ V.filter (fun x => a ⬝ᵥ x = 1)) :
    ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧ Full (V.filter (fun x => b ⬝ᵥ x = 1)) ∧
      (V.filter (fun x => a ⬝ᵥ x = 1)).erase v ⊆ V.filter (fun x => b ⬝ᵥ x = 1) ∧
      v ∉ V.filter (fun x => b ⬝ᵥ x = 1) := by
  set F := V.filter (fun x => a ⬝ᵥ x = 1) with hFdef
  have hcardF : F.card = d := hS a ha hF
  let M : E d →ₗ[ℝ] (↥F → ℝ) :=
    { toFun := fun y w => y ⬝ᵥ (w : E d)
      map_add' := by intro y z; funext w; simp [add_dotProduct]
      map_smul' := by intro r y; funext w; simp [smul_dotProduct] }
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hF
    intro x hx
    exact congrFun hy ⟨x, hx⟩
  have hsurj : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
        hcardF])).mp hinj
  obtain ⟨u, hu⟩ := hsurj (fun w => if (w : E d) = v then -1 else 0)
  have hu' : ∀ w ∈ F, u ⬝ᵥ w = if w = v then -1 else 0 := fun w hw => congrFun hu ⟨w, hw⟩
  have huv : u ⬝ᵥ v = -1 := by rw [hu' v hv, if_pos rfl]
  have huw : ∀ w ∈ F, w ≠ v → u ⬝ᵥ w = 0 := fun w hw hne => by rw [hu' w hw, if_neg hne]
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_dotProduct] at huv
    norm_num at huv
  obtain ⟨x0, hx0V, hx0⟩ := hI u hu0
  have hXne : (V.filter (fun x => 0 < u ⬝ᵥ x)).Nonempty := ⟨x0, mem_filter.mpr ⟨hx0V, hx0⟩⟩
  obtain ⟨xs, hxsX, hmin⟩ := exists_min_image _ (fun x => (1 - a ⬝ᵥ x) / (u ⬝ᵥ x)) hXne
  rw [mem_filter] at hxsX
  have hlt : ∀ x ∈ V, 0 < u ⬝ᵥ x → a ⬝ᵥ x < 1 := by
    intro x hxV hxu
    rcases (ha x hxV).lt_or_eq with h | h
    · exact h
    · exfalso
      have hxF : x ∈ F := mem_filter.mpr ⟨hxV, h⟩
      by_cases hxv : x = v
      · rw [hxv, huv] at hxu
        norm_num at hxu
      · rw [huw x hxF hxv] at hxu
        exact lt_irrefl _ hxu
  set t := (1 - a ⬝ᵥ xs) / (u ⬝ᵥ xs) with ht
  have htpos : 0 < t := div_pos (by linarith [hlt xs hxsX.1 hxsX.2]) hxsX.2
  have hbx : ∀ x, (a + t • u) ⬝ᵥ x = a ⬝ᵥ x + t * (u ⬝ᵥ x) := fun x => by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  refine ⟨a + t • u, ?_, ?_, ?_, ?_⟩
  · intro x hxV
    rw [hbx]
    by_cases hxu : 0 < u ⬝ᵥ x
    · have h1 : t ≤ (1 - a ⬝ᵥ x) / (u ⬝ᵥ x) := hmin x (mem_filter.mpr ⟨hxV, hxu⟩)
      rw [le_div_iff₀ hxu] at h1
      linarith
    · rw [not_lt] at hxu
      have := mul_nonpos_of_nonneg_of_nonpos htpos.le hxu
      linarith [ha x hxV]
  · intro y hy
    have hyw : ∀ w ∈ F, w ≠ v → y ⬝ᵥ w = 0 := fun w hw hne =>
      hy w (mem_filter.mpr ⟨(mem_filter.mp hw).1, by
        rw [hbx, (mem_filter.mp hw).2, huw w hw hne]; ring⟩)
    have hz : y + (y ⬝ᵥ v) • u = 0 := by
      apply hF
      intro w hw
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
      by_cases hwv : w = v
      · rw [hwv, huv]; ring
      · rw [hyw w hw hwv, huw w hw hwv]; ring
    have hxs1 : (a + t • u) ⬝ᵥ xs = 1 := by
      rw [hbx, ht, div_mul_cancel₀ _ hxsX.2.ne']
      ring
    have hyxs : y ⬝ᵥ xs = 0 := hy xs (mem_filter.mpr ⟨hxsX.1, hxs1⟩)
    have hyeq : y = -(y ⬝ᵥ v) • u := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact hz
    have hprod : (y ⬝ᵥ v) * (u ⬝ᵥ xs) = 0 := by
      have h2 := hyxs
      rw [hyeq, smul_dotProduct, smul_eq_mul] at h2
      linear_combination -h2
    have hyv : y ⬝ᵥ v = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd h hxsX.2.ne'
    rw [hyeq, hyv, neg_zero, zero_smul]
  · intro w hw
    have hwF := mem_of_mem_erase hw
    refine mem_filter.mpr ⟨(mem_filter.mp hwF).1, ?_⟩
    rw [hbx, (mem_filter.mp hwF).2, huw w hwF (ne_of_mem_erase hw)]
    ring
  · intro hvb
    have h1 := (mem_filter.mp hvb).2
    rw [hbx, (mem_filter.mp hv).2, huv] at h1
    linarith

open scoped Classical in
/-- Facets of the polar data: full tight sets of normals `b` with `b ⬝ x ≤ 1` on `V`. -/
noncomputable def facets (V : Finset (E d)) : Finset (Finset (E d)) :=
  V.powerset.filter (fun T => ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧
    T = V.filter (fun x => b ⬝ᵥ x = 1) ∧ Full T)

open scoped Classical in
theorem mem_facets {V T : Finset (E d)} : T ∈ facets V ↔ ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧
    T = V.filter (fun x => b ⬝ᵥ x = 1) ∧ Full T := by
  unfold facets
  rw [mem_filter, mem_powerset]
  constructor
  · exact fun h => h.2
  · rintro ⟨b, hb, rfl, hf⟩
    exact ⟨filter_subset _ _, b, hb, rfl, hf⟩

open scoped Classical in
/-- C1a-h in polar form: a vertex set `V` with `0` interior (`hI`) and simplicial (`hS`) has a
symmetric h-vector with `h 0 = 1` counting the simplices of its boundary complex. -/
theorem polar_hvector (V : Finset (E d)) (hI : ∀ u : E d, u ≠ 0 → ∃ x ∈ V, 0 < u ⬝ᵥ x)
    (hS : ∀ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) → Full (V.filter (fun x => b ⬝ᵥ x = 1)) →
      (V.filter (fun x => b ⬝ᵥ x = 1)).card = d)
    (hne : (facets V).Nonempty) :
    ∃ h : ℕ → ℤ, h 0 = 1 ∧ (∀ i ≤ d, h i = h (d - i)) ∧
      ∀ k ≤ d, ((((facets V).biUnion powerset).filter (fun G => G.card = k)).card : ℤ) =
        ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - k) : ℤ) := by
  have hspec : ∀ T ∈ facets V, ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧
      T = V.filter (fun x => b ⬝ᵥ x = 1) ∧ Full T := fun T hT => mem_facets.mp hT
  let a : Finset (E d) → E d := fun T => if h : T ∈ facets V then (hspec T h).choose else 0
  have ha : ∀ T ∈ facets V, (∀ x ∈ V, a T ⬝ᵥ x ≤ 1) ∧
      T = V.filter (fun x => a T ⬝ᵥ x = 1) ∧ Full T := by
    intro T hT
    have e : a T = (hspec T hT).choose := dif_pos hT
    rw [e]
    exact (hspec T hT).choose_spec
  have hsub : ∀ T ∈ facets V, T ⊆ V := by
    intro T hT
    rw [(ha T hT).2.1]
    exact filter_subset _ _
  have ha1 : ∀ F ∈ facets V, ∀ w ∈ F, a F ⬝ᵥ w = 1 := by
    intro F hF w hw
    rw [(ha F hF).2.1] at hw
    exact (mem_filter.mp hw).2
  have ha2 : ∀ F ∈ facets V, ∀ F' ∈ facets V, ∀ w ∈ F, a F' ⬝ᵥ w ≤ 1 :=
    fun F hF F' hF' w hw => (ha F' hF').1 w (hsub F hF hw)
  have ha3 : ∀ F ∈ facets V, ∀ F' ∈ facets V, ∀ w ∈ F, a F' ⬝ᵥ w = 1 → w ∈ F' := by
    intro F hF F' hF' w hw h1
    rw [(ha F' hF').2.1]
    exact mem_filter.mpr ⟨hsub F hF hw, h1⟩
  have hfull : ∀ F ∈ facets V, Full (V.filter (fun x => a F ⬝ᵥ x = 1)) := by
    intro F hF
    have := (ha F hF).2.2
    rwa [(ha F hF).2.1] at this
  have hcard : ∀ F ∈ facets V, F.card = d := by
    intro F hF
    rw [(ha F hF).2.1]
    exact hS (a F) (ha F hF).1 (hfull F hF)
  let nb : Finset (E d) → E d → Finset (E d) := fun F v =>
    if h : ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧ Full (V.filter (fun x => b ⬝ᵥ x = 1)) ∧
        F.erase v ⊆ V.filter (fun x => b ⬝ᵥ x = 1) ∧ v ∉ V.filter (fun x => b ⬝ᵥ x = 1)
    then V.filter (fun x => h.choose ⬝ᵥ x = 1) else ∅
  have hnb : ∀ F ∈ facets V, ∀ v ∈ F, nb F v ∈ facets V ∧ F.erase v ⊆ nb F v ∧ v ∉ nb F v := by
    intro F hF v hv
    have hex : ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧ Full (V.filter (fun x => b ⬝ᵥ x = 1)) ∧
        F.erase v ⊆ V.filter (fun x => b ⬝ᵥ x = 1) ∧ v ∉ V.filter (fun x => b ⬝ᵥ x = 1) := by
      have hFe := (ha F hF).2.1
      have hv' : v ∈ V.filter (fun x => a F ⬝ᵥ x = 1) := by rwa [hFe] at hv
      have := neighbor V hI hS (a F) (ha F hF).1 (hfull F hF) v hv'
      rwa [← hFe] at this
    have e : nb F v = V.filter (fun x => hex.choose ⬝ᵥ x = 1) := dif_pos hex
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hex.choose_spec
    rw [e]
    exact ⟨mem_facets.mpr ⟨hex.choose, hb1, rfl, hb2⟩, hb3, hb4⟩
  obtain ⟨c, hc⟩ := exists_generic (facets V) a (a_inj (facets V) a hcard ha1 ha3)
  exact hvector_of_shelling (facets V) a nb c hcard hne (fun F hF => (ha F hF).2.2)
    ha1 ha2 ha3 hnb hc

end GF93SH


/-! Session 17: explicit shelling data (ord, R) satisfying the combinatorial shelling
`hsh` and its reversal `hrev`, as needed by `GF93LG.lefschetzHilbertF_of_shell`. -/
namespace GF93WR
open Matrix Finset GF93SH

/-- Combinatorial shelling data of a pure complex `Φ` of dimension `d - 1`. -/
def ShellData {α : Type*} [DecidableEq α] (d : ℕ) (Φ : Finset (Finset α))
    (ord : Finset α → ℕ) (R : Finset α → Finset α) : Prop :=
  (∀ F ∈ Φ, F.card = d) ∧ (∀ F ∈ Φ, R F ⊆ F) ∧ Set.InjOn ord Φ ∧
    (∀ F ∈ Φ, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Φ, G ⊆ F' → ord F' ≤ ord F)) ∧
    (∀ F ∈ Φ, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Φ, G ⊆ F' → ord F ≤ ord F'))

theorem ord_le {β : Type*} (Φ : Finset β) (s : β → ℝ) {F F' : β} (hF : F ∈ Φ) :
    (Φ.filter (fun G => s G < s F')).card ≤ (Φ.filter (fun G => s G < s F)).card ↔
      s F' ≤ s F := by
  classical
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hss : Φ.filter (fun G => s G < s F) ⊂ Φ.filter (fun G => s G < s F') := by
      refine ⟨fun G hG => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hG ⊢
        exact ⟨hG.1, hG.2.trans hlt⟩
      · have := hsub (mem_filter.mpr ⟨hF, hlt⟩)
        exact lt_irrefl _ (mem_filter.mp this).2
    exact absurd (card_lt_card hss) (not_lt.mpr h)
  · intro h
    apply card_le_card
    intro G hG
    simp only [mem_filter] at hG ⊢
    exact ⟨hG.1, lt_of_lt_of_le hG.2 h⟩

variable {d : ℕ}

theorem shelling_iff (Φ : Finset (Finset (E d))) (a : Finset (E d) → E d)
    (nb : Finset (E d) → E d → Finset (E d)) (c : E d)
    (hspan : ∀ F ∈ Φ, ∀ y : E d, (∀ w ∈ F, y ⬝ᵥ w = 0) → y = 0)
    (ha1 : ∀ F ∈ Φ, ∀ w ∈ F, a F ⬝ᵥ w = 1)
    (ha2 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w ≤ 1)
    (ha3 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w = 1 → w ∈ F')
    (hnb : ∀ F ∈ Φ, ∀ v ∈ F, nb F v ∈ Φ ∧ F.erase v ⊆ nb F v ∧ v ∉ nb F v)
    (hgen : ∀ F ∈ Φ, ∀ F' ∈ Φ, c ⬝ᵥ a F = c ⬝ᵥ a F' → F = F')
    (F : Finset (E d)) (hF : F ∈ Φ) (G : Finset (E d)) (hGF : G ⊆ F) :
    R a nb c F ⊆ G ↔ ∀ F' ∈ Φ, G ⊆ F' → c ⬝ᵥ a F' ≤ c ⬝ᵥ a F := by
  classical
  constructor
  · intro hR F' hF' hGF'
    have hloc : ∀ v ∈ F, v ∉ G → c ⬝ᵥ a (nb F v) < c ⬝ᵥ a F := by
      intro v hv hvG
      have hnR : v ∉ R a nb c F := fun h => hvG (hR h)
      simp only [R, mem_filter, not_and, not_lt] at hnR
      have hle := hnR hv
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso
        have := hgen _ (hnb F hF v hv).1 _ hF h
        exact (hnb F hF v hv).2.2 (by rw [this]; exact hv)
    refine shell_ineq F G (hspan F hF) hGF (a F) (a F') c (fun v => a (nb F v)) (ha1 F hF)
      (ha2 F hF F' hF') (fun w hw => ha1 F' hF' w (hGF' hw)) ?_ ?_ hloc
    · intro v hv w hw hwv
      exact ha1 _ (hnb F hF v hv).1 w ((hnb F hF v hv).2.1 (mem_erase.mpr ⟨hwv, hw⟩))
    · intro v hv
      have h1 := ha2 F hF _ (hnb F hF v hv).1 v hv
      rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd (ha3 F hF _ (hnb F hF v hv).1 v hv h) (hnb F hF v hv).2.2
  · intro hmax v hv
    by_contra hvG
    have hvF : v ∈ F := R_subset a nb c F hv
    have hGn : G ⊆ nb F v := fun x hx =>
      (hnb F hF v hvF).2.1 (mem_erase.mpr ⟨fun h => hvG (h ▸ hx), hGF hx⟩)
    have h1 := hmax _ (hnb F hF v hvF).1 hGn
    simp only [R, mem_filter] at hv
    linarith [hv.2]

open scoped Classical in
/-- The shelling count with explicit `h`, plus the combinatorial shelling data. -/
def HShell (d : ℕ) (Φ : Finset (Finset (E d))) (ord : Finset (E d) → ℕ)
    (R' : Finset (E d) → Finset (E d)) : Prop :=
  ShellData d Φ ord R' ∧ (Φ.filter (fun F => (R' F).card = 0)).card = 1 ∧
    (∀ i ≤ d, (Φ.filter (fun F => (R' F).card = i)).card =
      (Φ.filter (fun F => (R' F).card = d - i)).card) ∧
    ∀ k ≤ d, (((Φ.biUnion powerset).filter (fun G => G.card = k)).card : ℤ) =
      ∑ i ∈ range (d + 1), ((Φ.filter (fun F => (R' F).card = i)).card : ℤ) *
        ((d - i).choose (d - k) : ℤ)

open scoped Classical in
theorem shelled_of_data (Φ : Finset (Finset (E d))) (a : Finset (E d) → E d)
    (nb : Finset (E d) → E d → Finset (E d)) (c : E d)
    (hcard : ∀ F ∈ Φ, F.card = d) (hΦ : Φ.Nonempty)
    (hspan : ∀ F ∈ Φ, ∀ y : E d, (∀ w ∈ F, y ⬝ᵥ w = 0) → y = 0)
    (ha1 : ∀ F ∈ Φ, ∀ w ∈ F, a F ⬝ᵥ w = 1)
    (ha2 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w ≤ 1)
    (ha3 : ∀ F ∈ Φ, ∀ F' ∈ Φ, ∀ w ∈ F, a F' ⬝ᵥ w = 1 → w ∈ F')
    (hnb : ∀ F ∈ Φ, ∀ v ∈ F, nb F v ∈ Φ ∧ F.erase v ⊆ nb F v ∧ v ∉ nb F v)
    (hgen : ∀ F ∈ Φ, ∀ F' ∈ Φ, c ⬝ᵥ a F = c ⬝ᵥ a F' → F = F') :
    ∃ (ord : Finset (E d) → ℕ) (R' : Finset (E d) → Finset (E d)), HShell d Φ ord R' := by
  have hΔ : ∀ G, G ∈ Φ.biUnion powerset ↔ ∃ F ∈ Φ, G ⊆ F := by
    intro G; simp only [mem_biUnion, mem_powerset]
  have hgen' : ∀ F ∈ Φ, ∀ F' ∈ Φ, (-c) ⬝ᵥ a F = (-c) ⬝ᵥ a F' → F = F' := by
    intro F hF F' hF' h
    rw [neg_dotProduct, neg_dotProduct, neg_inj] at h
    exact hgen F hF F' hF' h
  have cnt : ∀ k ≤ d, (((Φ.biUnion powerset).filter (fun G => G.card = k)).card : ℤ) =
      ∑ i ∈ range (d + 1), ((Φ.filter (fun F => (R a nb c F).card = i)).card : ℤ) *
        ((d - i).choose (d - k) : ℤ) := fun k hk =>
    shell_count Φ (R a nb c) d hcard (fun F _ => R_subset a nb c F) _ hΔ
      (fun G hG => shelling Φ a nb c hspan ha1 ha2 ha3 hnb hgen G ((hΔ G).mp hG)) k hk
  obtain ⟨h, h0, hs, hrel⟩ := hvector_of_shelling Φ a nb c hcard hΦ hspan ha1 ha2 ha3 hnb hgen
  have htri := tri_unique (d := d)
    (fun i => ((Φ.filter (fun F => (R a nb c F).card = i)).card : ℤ)) h
    (fun k hk => (cnt k hk).symm.trans (hrel k hk))
  have hle : ∀ F ∈ Φ, ∀ F' : Finset (E d),
      (Φ.filter (fun G => c ⬝ᵥ a G < c ⬝ᵥ a F')).card ≤
        (Φ.filter (fun G => c ⬝ᵥ a G < c ⬝ᵥ a F)).card ↔ c ⬝ᵥ a F' ≤ c ⬝ᵥ a F :=
    fun F hF F' => ord_le Φ (fun G => c ⬝ᵥ a G) hF
  refine ⟨fun F => (Φ.filter (fun G => c ⬝ᵥ a G < c ⬝ᵥ a F)).card, R a nb c,
    ⟨hcard, fun F _ => R_subset a nb c F, ?_, ?_, ?_⟩, ?_, ?_, cnt⟩
  · intro F hF F' hF' heq
    exact hgen F hF F' hF' (le_antisymm ((hle F' hF' F).mp heq.le) ((hle F hF F').mp heq.ge))
  · intro F hF G hGF
    rw [shelling_iff Φ a nb c hspan ha1 ha2 ha3 hnb hgen F hF G hGF]
    exact forall₂_congr (fun F' _ => imp_congr_right (fun _ => (hle F hF F').symm))
  · intro F hF G hGF
    rw [← R_neg Φ a nb c hnb hgen F hF,
      shelling_iff Φ a nb (-c) hspan ha1 ha2 ha3 hnb hgen' F hF G hGF]
    refine forall₂_congr (fun F' hF' => imp_congr_right (fun _ => ?_))
    rw [neg_dotProduct, neg_dotProduct, neg_le_neg_iff]
    exact (hle F' hF' F).symm
  · have e := htri 0 (Nat.zero_le _)
    rw [h0] at e
    exact_mod_cast e
  · intro i hi
    have e := (htri i hi).trans ((hs i hi).trans (htri (d - i) (by omega)).symm)
    exact_mod_cast e

open scoped Classical in
/-- `polar_hvector` with explicit shelling data. -/
theorem polar_shelled (V : Finset (E d)) (hI : ∀ u : E d, u ≠ 0 → ∃ x ∈ V, 0 < u ⬝ᵥ x)
    (hS : ∀ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) → Full (V.filter (fun x => b ⬝ᵥ x = 1)) →
      (V.filter (fun x => b ⬝ᵥ x = 1)).card = d)
    (hne : (facets V).Nonempty) :
    (∀ F ∈ facets V, F ⊆ V) ∧
      ∃ (ord : Finset (E d) → ℕ) (R' : Finset (E d) → Finset (E d)), HShell d (facets V) ord R' := by
  have hspec : ∀ T ∈ facets V, ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧
      T = V.filter (fun x => b ⬝ᵥ x = 1) ∧ Full T := fun T hT => mem_facets.mp hT
  let a : Finset (E d) → E d := fun T => if h : T ∈ facets V then (hspec T h).choose else 0
  have ha : ∀ T ∈ facets V, (∀ x ∈ V, a T ⬝ᵥ x ≤ 1) ∧
      T = V.filter (fun x => a T ⬝ᵥ x = 1) ∧ Full T := by
    intro T hT
    have e : a T = (hspec T hT).choose := dif_pos hT
    rw [e]
    exact (hspec T hT).choose_spec
  have hsub : ∀ T ∈ facets V, T ⊆ V := by
    intro T hT
    rw [(ha T hT).2.1]
    exact filter_subset _ _
  have ha1 : ∀ F ∈ facets V, ∀ w ∈ F, a F ⬝ᵥ w = 1 := by
    intro F hF w hw
    rw [(ha F hF).2.1] at hw
    exact (mem_filter.mp hw).2
  have ha2 : ∀ F ∈ facets V, ∀ F' ∈ facets V, ∀ w ∈ F, a F' ⬝ᵥ w ≤ 1 :=
    fun F hF F' hF' w hw => (ha F' hF').1 w (hsub F hF hw)
  have ha3 : ∀ F ∈ facets V, ∀ F' ∈ facets V, ∀ w ∈ F, a F' ⬝ᵥ w = 1 → w ∈ F' := by
    intro F hF F' hF' w hw h1
    rw [(ha F' hF').2.1]
    exact mem_filter.mpr ⟨hsub F hF hw, h1⟩
  have hfull : ∀ F ∈ facets V, Full (V.filter (fun x => a F ⬝ᵥ x = 1)) := by
    intro F hF
    have := (ha F hF).2.2
    rwa [(ha F hF).2.1] at this
  have hcard : ∀ F ∈ facets V, F.card = d := by
    intro F hF
    rw [(ha F hF).2.1]
    exact hS (a F) (ha F hF).1 (hfull F hF)
  let nb : Finset (E d) → E d → Finset (E d) := fun F v =>
    if h : ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧ Full (V.filter (fun x => b ⬝ᵥ x = 1)) ∧
        F.erase v ⊆ V.filter (fun x => b ⬝ᵥ x = 1) ∧ v ∉ V.filter (fun x => b ⬝ᵥ x = 1)
    then V.filter (fun x => h.choose ⬝ᵥ x = 1) else ∅
  have hnb : ∀ F ∈ facets V, ∀ v ∈ F, nb F v ∈ facets V ∧ F.erase v ⊆ nb F v ∧ v ∉ nb F v := by
    intro F hF v hv
    have hex : ∃ b : E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) ∧ Full (V.filter (fun x => b ⬝ᵥ x = 1)) ∧
        F.erase v ⊆ V.filter (fun x => b ⬝ᵥ x = 1) ∧ v ∉ V.filter (fun x => b ⬝ᵥ x = 1) := by
      have hFe := (ha F hF).2.1
      have hv' : v ∈ V.filter (fun x => a F ⬝ᵥ x = 1) := by rwa [hFe] at hv
      have := neighbor V hI hS (a F) (ha F hF).1 (hfull F hF) v hv'
      rwa [← hFe] at this
    have e : nb F v = V.filter (fun x => hex.choose ⬝ᵥ x = 1) := dif_pos hex
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hex.choose_spec
    rw [e]
    exact ⟨mem_facets.mpr ⟨hex.choose, hb1, rfl, hb2⟩, hb3, hb4⟩
  obtain ⟨c, hc⟩ := exists_generic (facets V) a (a_inj (facets V) a hcard ha1 ha3)
  exact ⟨hsub, shelled_of_data (facets V) a nb c hcard hne (fun F hF => (ha F hF).2.2)
    ha1 ha2 ha3 hnb hc⟩

end GF93WR


namespace GF93WR
open Finset

/-- Transport shelling data along a map that is injective on the vertex set. -/
theorem transport {α : Type*} [DecidableEq α] {n d : ℕ} (U : Finset α) (ι : α → Fin n)
    (hι : Set.InjOn ι U) (Φ : Finset (Finset α)) (hΦU : ∀ F ∈ Φ, F ⊆ U)
    (ord : Finset α → ℕ) (R : Finset α → Finset α) (hD : ShellData d Φ ord R) :
    ∃ (Fs : Finset (Finset (Fin n))) (ordT : Finset (Fin n) → ℕ)
      (RT : Finset (Fin n) → Finset (Fin n)), ShellData d Fs ordT RT ∧
      (∀ k, (Fs.filter (fun F => (RT F).card = k)).card =
        (Φ.filter (fun F => (R F).card = k)).card) ∧ (Φ.Nonempty → Fs.Nonempty) := by
  obtain ⟨hcard, hRF, hord, hsh, hrev⟩ := hD
  let pre : Finset (Fin n) → Finset α := fun T => U.filter (fun x => ι x ∈ T)
  have k1 : ∀ F ⊆ U, pre (F.image ι) = F := by
    intro F hF
    ext x
    simp only [pre, mem_filter, mem_image]
    constructor
    · rintro ⟨hxU, y, hy, hyx⟩
      rwa [← hι (hF hy) hxU hyx]
    · intro hx
      exact ⟨hF hx, x, hx, rfl⟩
  have k2 : ∀ F ⊆ U, (F.image ι).card = F.card := fun F hF =>
    card_image_of_injOn (hι.mono (fun x hx => hF hx))
  have k3 : ∀ A ⊆ U, ∀ B ⊆ U, (A.image ι ⊆ B.image ι ↔ A ⊆ B) := by
    intro A hA B hB
    refine ⟨fun h x hx => ?_, fun h => image_subset_image h⟩
    obtain ⟨y, hy, hyx⟩ := mem_image.mp (h (mem_image_of_mem ι hx))
    rwa [← hι (hB hy) (hA hx) hyx]
  have k4 : ∀ F ⊆ U, ∀ T ⊆ F.image ι, (pre T).image ι = T ∧ pre T ⊆ F := by
    intro F hF T hT
    refine ⟨?_, ?_⟩
    · ext t
      simp only [pre, mem_image, mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩
        exact hx
      · intro ht
        obtain ⟨x, hx, rfl⟩ := mem_image.mp (hT ht)
        exact ⟨x, ⟨hF hx, ht⟩, rfl⟩
    · intro x hx
      simp only [pre, mem_filter] at hx
      obtain ⟨y, hy, hyx⟩ := mem_image.mp (hT hx.2)
      rwa [← hι (hF hy) hx.1 hyx]
  have k5 : ∀ A ⊆ U, ∀ B ⊆ U, A.image ι \ B.image ι = (A \ B).image ι := by
    intro A hA B hB
    ext t
    simp only [mem_sdiff, mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      exact ⟨x, ⟨hx, fun hxB => hn ⟨x, hxB, rfl⟩⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxB⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro ⟨y, hy, hyx⟩
      exact hxB (hι (hB hy) (hA hx) hyx ▸ hy)
  have hinj : Set.InjOn (fun F : Finset α => F.image ι) Φ := by
    intro F hF F' hF' h
    have := congrArg pre h
    simp only at this
    rwa [k1 F (hΦU F hF), k1 F' (hΦU F' hF')] at this
  refine ⟨Φ.image (fun F => F.image ι), fun T => ord (pre T), fun T => (R (pre T)).image ι,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun h => h.image _⟩
  · intro T hT
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hT
    rw [k2 F (hΦU F hF), hcard F hF]
  · intro T hT
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hT
    simp only [k1 F (hΦU F hF)]
    exact image_subset_image (hRF F hF)
  · intro T hT T' hT' h
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hT
    obtain ⟨F', hF', rfl⟩ := mem_image.mp hT'
    simp only [k1 F (hΦU F hF), k1 F' (hΦU F' hF')] at h
    rw [hord hF hF' h]
  · intro T hT G hGT
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hT
    have hU := hΦU F hF
    obtain ⟨hG1, hG2⟩ := k4 F hU G hGT
    simp only [k1 F hU]
    rw [← hG1, k3 _ ((hRF F hF).trans hU) _ (hG2.trans hU), hsh F hF _ hG2, forall_mem_image]
    refine forall₂_congr (fun F' hF' => ?_)
    rw [k3 _ (hG2.trans hU) _ (hΦU F' hF'), k1 F' (hΦU F' hF')]
  · intro T hT G hGT
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hT
    have hU := hΦU F hF
    obtain ⟨hG1, hG2⟩ := k4 F hU G hGT
    simp only [k1 F hU]
    rw [← hG1, k5 _ hU _ ((hRF F hF).trans hU), k3 _ (sdiff_subset.trans hU) _ (hG2.trans hU),
      hrev F hF _ hG2, forall_mem_image]
    refine forall₂_congr (fun F' hF' => ?_)
    rw [k3 _ (hG2.trans hU) _ (hΦU F' hF'), k1 F' (hΦU F' hF')]
  · intro k
    rw [filter_image, card_image_of_injOn (hinj.mono (fun F hF => (mem_filter.mp hF).1))]
    congr 1
    apply filter_congr
    intro F hF
    simp only [k1 F (hΦU F hF), k2 _ ((hRF F hF).trans (hΦU F hF))]

end GF93WR

namespace GF93BR

open Matrix Finset Grunbaum2003 GF93G

variable {d : ℕ}

open scoped Classical in
/-- `GF93SH.polar_hvector` as a hypothesis (proved in scratch/probe/f9336347_shell.lean). -/
def PolarHV : Prop :=
  ∀ (d : ℕ) (V : Finset (GF93SH.E d)), (∀ u : GF93SH.E d, u ≠ 0 → ∃ x ∈ V, 0 < u ⬝ᵥ x) →
    (∀ b : GF93SH.E d, (∀ x ∈ V, b ⬝ᵥ x ≤ 1) → GF93SH.Full (V.filter (fun x => b ⬝ᵥ x = 1)) →
      (V.filter (fun x => b ⬝ᵥ x = 1)).card = d) →
    (GF93SH.facets V).Nonempty →
    ∃ h : ℕ → ℤ, h 0 = 1 ∧ (∀ i ≤ d, h i = h (d - i)) ∧
      ∀ k ≤ d, ((((GF93SH.facets V).biUnion powerset).filter (fun G => G.card = k)).card : ℤ) =
        ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - k) : ℤ)

noncomputable def dlin (b : E d) : E d →ₗ[ℝ] ℝ where
  toFun x := b ⬝ᵥ x
  map_add' x y := dotProduct_add b x y
  map_smul' c x := by simp [dotProduct_smul]

@[simp] theorem dlin_apply (b x : E d) : dlin b x = b ⬝ᵥ x := rfl

noncomputable def dl (b : E d) : StrongDual ℝ (E d) := LinearMap.toContinuousLinearMap (dlin b)

@[simp] theorem dl_apply (b x : E d) : dl b x = b ⬝ᵥ x := rfl

theorem dlin_ne {b : E d} (hb : b ≠ 0) : dlin b ≠ 0 := by
  intro h
  apply hb
  apply dotProduct_self_eq_zero.mp
  have := LinearMap.congr_fun h b
  simpa using this

theorem lin_dot (l : E d →ₗ[ℝ] ℝ) (x : E d) : l x = (fun i => l (Pi.single i 1)) ⬝ᵥ x := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (Pi.single i (x i) : E d) = x i • (Pi.single i (1 : ℝ) : E d) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hs, map_smul, smul_eq_mul, mul_comm]

theorem dot_fsum {ι : Type*} (s : Finset ι) (f : ι → E d) (u : E d) :
    u ⬝ᵥ ∑ i ∈ s, f i = ∑ i ∈ s, u ⬝ᵥ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, dotProduct_add, ih]

/-- A finite set with no nonzero vector orthogonal to it spans. -/
theorem span_of_full {T : Finset (E d)} (hT : GF93SH.Full T) :
    Submodule.span ℝ (T : Set (E d)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  apply hf0
  have hy := hT (fun i => f (Pi.single i 1)) (fun x hx => by
    rw [← lin_dot]
    exact hfle (Submodule.subset_span hx))
  refine LinearMap.ext fun x => ?_
  rw [lin_dot f x, hy]
  simp

section
variable {V0 : Set (E d)} (hV0 : V0.Finite)

noncomputable def Xf : Finset (E d) := (ext_finite hV0).toFinset

theorem mem_Xf {e : E d} : e ∈ Xf hV0 ↔ e ∈ Set.extremePoints ℝ (convexHull ℝ V0) :=
  Set.Finite.mem_toFinset _

noncomputable def p0 : E d := ((Xf hV0).card : ℝ)⁻¹ • ∑ e ∈ Xf hV0, e

noncomputable def Vp : Finset (E d) := (Xf hV0).image (fun e => e - p0 hV0)

theorem mem_Vp {x : E d} :
    x ∈ Vp hV0 ↔ x + p0 hV0 ∈ Set.extremePoints ℝ (convexHull ℝ V0) := by
  unfold Vp
  rw [mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa [mem_Xf] using he
  · intro h
    exact ⟨x + p0 hV0, (mem_Xf hV0).2 h, by simp⟩

theorem Xf_nonempty (hne : V0.Nonempty) : (Xf hV0).Nonempty := by
  have hc : IsCompact (convexHull ℝ V0) := hV0.isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨e, he⟩ := hc.extremePoints_nonempty (hne.convexHull)
  exact ⟨e, (mem_Xf hV0).2 he⟩

theorem sum_centered (hne : (Xf hV0).Nonempty) (u : E d) :
    ∑ e ∈ Xf hV0, u ⬝ᵥ (e - p0 hV0) = 0 := by
  have hcard : ((Xf hV0).card : ℝ) ≠ 0 := by
    have := hne.card_pos
    positivity
  simp only [dotProduct_sub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [p0, dotProduct_smul, smul_eq_mul, dot_fsum]
  field_simp
  ring

theorem exm {e : E d} (he : e ∈ Set.extremePoints ℝ (convexHull ℝ V0)) :
    e ∈ convexHull ℝ V0 := he.1

/-- B1: `p0` is interior. -/
theorem hI (hne : V0.Nonempty) (htop : affineSpan ℝ (convexHull ℝ V0) = ⊤) (u : E d)
    (hu : u ≠ 0) : ∃ x ∈ Vp hV0, 0 < u ⬝ᵥ x := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ e ∈ Xf hV0, u ⬝ᵥ (e - p0 hV0) ≤ 0 := fun e he =>
    hcon _ ((mem_Vp hV0).2 (by simpa [mem_Xf] using he))
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hle).1 (sum_centered hV0 (Xf_nonempty hV0 hne) u)
  have h1 : ∀ e ∈ Set.extremePoints ℝ (convexHull ℝ V0), dlin u e = u ⬝ᵥ p0 hV0 := by
    intro e he
    have := hz e ((mem_Xf hV0).2 he)
    rw [dotProduct_sub, sub_eq_zero] at this
    simpa using this
  have hc : ∀ x ∈ convexHull ℝ V0, dlin u x = u ⬝ᵥ p0 hV0 := by
    intro x hx
    rw [hull_ext hV0] at hx
    exact convexHull_min (t := {x | dlin u x = u ⬝ᵥ p0 hV0}) h1
      (convex_hyperplane (dlin u).isLinear _) hx
  have := dim_lt_of_const (dlin u) (dlin_ne hu) _ hc
  rw [htop, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at this
  omega

/-- K: a polar tight set is the vertex set (translated) of a proper exposed face. -/
theorem polar_face (hne : V0.Nonempty) (htop : affineSpan ℝ (convexHull ℝ V0) = ⊤) (b : E d)
    (hb : ∀ x ∈ Vp hV0, b ⬝ᵥ x ≤ 1) (t : E d) (ht : t ∈ Vp hV0) (hbt : b ⬝ᵥ t = 1) :
    ({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} : Set (E d)).Nonempty ∧
    IsExposed ℝ (convexHull ℝ V0) {x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} ∧
    {x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} ≠ convexHull ℝ V0 ∧
    {x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} ∩
        Set.extremePoints ℝ (convexHull ℝ V0) =
      (fun x => x + p0 hV0) '' ↑((Vp hV0).filter (fun x => b ⬝ᵥ x = 1)) ∧
    (∀ x ∈ {x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x},
      dlin b x = b ⬝ᵥ p0 hV0 + 1) := by
  have hmax : ∀ y ∈ convexHull ℝ V0, dl b y ≤ b ⬝ᵥ p0 hV0 + 1 := by
    apply halfspace_of_ext hV0
    intro w hw
    have := hb (w - p0 hV0) ((mem_Vp hV0).2 (by simpa using hw))
    rw [dotProduct_sub] at this
    simp only [dl_apply]
    linarith
  have hte : t + p0 hV0 ∈ convexHull ℝ V0 := exm ((mem_Vp hV0).1 ht)
  have hbte : b ⬝ᵥ (t + p0 hV0) = b ⬝ᵥ p0 hV0 + 1 := by rw [dotProduct_add, hbt]; ring
  have memG : ∀ x, x ∈ ({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} :
      Set (E d)) ↔ x ∈ convexHull ℝ V0 ∧ b ⬝ᵥ x = b ⬝ᵥ p0 hV0 + 1 := by
    intro x
    simp only [Set.mem_setOf_eq, dl_apply]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨hx, le_antisymm (by simpa using hmax x hx) ?_⟩
      rw [← hbte]; exact hy _ hte
    · rintro ⟨hx, hbx⟩
      refine ⟨hx, fun y hy => ?_⟩
      rw [hbx]; simpa using hmax y hy
  have hb0 : b ≠ 0 := by rintro rfl; simp at hbt
  refine ⟨⟨_, (memG _).2 ⟨hte, hbte⟩⟩, fun _ => ⟨dl b, rfl⟩, ?_, ?_, ?_⟩
  · intro hGP
    obtain ⟨x, hx, hpos⟩ := hI hV0 hne htop (-b) (neg_ne_zero.mpr hb0)
    have hxP : x + p0 hV0 ∈ convexHull ℝ V0 := exm ((mem_Vp hV0).1 hx)
    rw [← hGP] at hxP
    have := ((memG _).1 hxP).2
    rw [neg_dotProduct] at hpos
    rw [dotProduct_add] at this
    linarith
  · ext e
    simp only [Set.mem_inter_iff, Set.mem_image, coe_filter]
    constructor
    · rintro ⟨hG, he⟩
      refine ⟨e - p0 hV0, ⟨(mem_Vp hV0).2 (by simpa using he), ?_⟩, by simp⟩
      have := ((memG e).1 hG).2
      rw [dotProduct_sub]; linarith
    · rintro ⟨x, ⟨hx, hbx⟩, rfl⟩
      have he := (mem_Vp hV0).1 hx
      refine ⟨(memG _).2 ⟨exm he, ?_⟩, he⟩
      rw [dotProduct_add, hbx]; ring
  · intro x hx
    simpa using ((memG x).1 hx).2

/-- K': every proper nonempty exposed face is cut out by a polar normal. -/
theorem face_polar (hne : V0.Nonempty) {F : Set (E d)} (hFne : F.Nonempty)
    (hF : IsExposed ℝ (convexHull ℝ V0) F) (hFP : F ≠ convexHull ℝ V0) :
    ∃ b : E d, (∀ x ∈ Vp hV0, b ⬝ᵥ x ≤ 1) ∧ (∃ t ∈ Vp hV0, b ⬝ᵥ t = 1) ∧
      F = {x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} := by
  obtain ⟨l, rfl⟩ := hF hFne
  set a : E d := fun i => l (Pi.single i 1) with ha
  have hla : ∀ x, l x = a ⬝ᵥ x := fun x => lin_dot l.toLinearMap x
  obtain ⟨g, hgP, hg⟩ := hFne
  set c := a ⬝ᵥ g with hc
  have hle : ∀ y ∈ convexHull ℝ V0, a ⬝ᵥ y ≤ c := fun y hy => by
    rw [← hla, hc, ← hla]; exact hg y hy
  have hext : ∀ e, e ∈ Set.extremePoints ℝ (convexHull ℝ V0) → a ⬝ᵥ e ≤ c :=
    fun e he => hle e (exm he)
  -- `a ⬝ p0 < c`
  have hlt : a ⬝ᵥ p0 hV0 < c := by
    by_contra hge
    push Not at hge
    have hle' : ∀ e ∈ Xf hV0, a ⬝ᵥ (e - p0 hV0) ≤ 0 := fun e he => by
      rw [dotProduct_sub]; linarith [hext e ((mem_Xf hV0).1 he)]
    have hz := (Finset.sum_eq_zero_iff_of_nonpos hle').1
      (sum_centered hV0 (Xf_nonempty hV0 hne) a)
    apply hFP
    apply Set.Subset.antisymm (fun x hx => hx.1)
    intro x hx
    refine ⟨hx, fun y hy => ?_⟩
    rw [hla, hla]
    have hlow : ∀ y ∈ convexHull ℝ V0, (-l) y ≤ -c := by
      apply halfspace_of_ext hV0
      intro w hw
      have := hz w ((mem_Xf hV0).2 hw)
      rw [dotProduct_sub, sub_eq_zero] at this
      simp only [ContinuousLinearMap.neg_apply, hla]
      linarith
    have := hlow x hx
    simp only [ContinuousLinearMap.neg_apply, hla] at this
    linarith [hle y hy]
  set k := (c - a ⬝ᵥ p0 hV0)⁻¹ with hk
  have hkpos : 0 < k := inv_pos.mpr (by linarith)
  refine ⟨k • a, ?_, ?_, ?_⟩
  · intro x hx
    have he := (mem_Vp hV0).1 hx
    have h1 := hext _ he
    rw [smul_dotProduct, smul_eq_mul, hk, inv_mul_le_iff₀ (by linarith)]
    rw [dotProduct_add] at h1
    linarith
  · obtain ⟨e, he⟩ : (convexHull ℝ V0 ∩ {x | ∀ y ∈ convexHull ℝ V0, l y ≤ l x} ∩
        Set.extremePoints ℝ (convexHull ℝ V0)).Nonempty := by
      have hfe := face_eq_hull hV0 (F := {x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, l y ≤ l x})
        (fun _ => ⟨l, rfl⟩)
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      have : g ∈ ({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, l y ≤ l x} : Set (E d)) :=
        ⟨hgP, hg⟩
      rw [hfe] at this
      have hem' : ({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, l y ≤ l x} : Set (E d)) ∩
          Set.extremePoints ℝ (convexHull ℝ V0) = ∅ := hem
      rw [hem', convexHull_empty] at this
      exact this
    refine ⟨e - p0 hV0, (mem_Vp hV0).2 (by simpa using he.2), ?_⟩
    have hae : a ⬝ᵥ e = c := le_antisymm (hext e he.2) (by
      have := he.1.2 g hgP
      rw [hla, hla] at this; exact this)
    rw [smul_dotProduct, smul_eq_mul, dotProduct_sub, hae, hk]
    field_simp [show c - a ⬝ᵥ p0 hV0 ≠ 0 by linarith]
  · ext x
    simp only [Set.mem_setOf_eq, dl_apply, smul_dotProduct, smul_eq_mul, hla]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, fun y hy' => mul_le_mul_of_nonneg_left (hy y hy') hkpos.le⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, fun y hy' => le_of_mul_le_mul_left (hy y hy') hkpos⟩

end

end GF93BR

namespace GF93BR

open Matrix Finset Grunbaum2003 GF93G

variable {d : ℕ}

section
variable {V0 : Set (E d)} (hV0 : V0.Finite)

theorem ncard_tr (T : Finset (E d)) :
    ((fun x => x + p0 hV0) '' (↑T : Set (E d))).ncard = T.card := by
  rw [Set.ncard_image_of_injective _ (add_left_injective _), Set.ncard_coe_finset]

/-- Kf: the polar tight set of a facet is full. -/
theorem facet_full (hne : V0.Nonempty) (htop : affineSpan ℝ (convexHull ℝ V0) = ⊤) (b : E d)
    (hb : ∀ x ∈ Vp hV0, b ⬝ᵥ x ≤ 1) (t : E d) (ht : t ∈ Vp hV0) (hbt : b ⬝ᵥ t = 1)
    (hdim : Module.finrank ℝ (affineSpan ℝ
      ({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} : Set (E d))).direction + 1
        = d) :
    GF93SH.Full ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1)) := by
  obtain ⟨hGne, hGexp, hGP, hGX, hGc⟩ := polar_face hV0 hne htop b hb t ht hbt
  have hspan : Submodule.span ℝ (((Vp hV0).filter (fun x => b ⬝ᵥ x = 1) : Finset (E d)) :
      Set (E d)) = ⊤ := by
    have hWG : (affineSpan ℝ (({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} :
        Set (E d)) ∩ Set.extremePoints ℝ (convexHull ℝ V0))).direction =
        (affineSpan ℝ ({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} :
          Set (E d))).direction := by
      rw [← affineSpan_convexHull, ← face_eq_hull hV0 hGexp]
    have hWle : (affineSpan ℝ (({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} :
        Set (E d)) ∩ Set.extremePoints ℝ (convexHull ℝ V0))).direction ≤
        Submodule.span ℝ (((Vp hV0).filter (fun x => b ⬝ᵥ x = 1) : Finset (E d)) : Set (E d)) := by
      rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [hGX] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      show (x' + p0 hV0) -ᵥ (y' + p0 hV0) ∈ _
      rw [vsub_eq_sub, add_sub_add_right_eq_sub]
      exact Submodule.sub_mem _ (Submodule.subset_span hx') (Submodule.subset_span hy')
    have htT : t ∈ (Vp hV0).filter (fun x => b ⬝ᵥ x = 1) := mem_filter.2 ⟨ht, hbt⟩
    have htW : t ∉ (affineSpan ℝ (({x ∈ convexHull ℝ V0 | ∀ y ∈ convexHull ℝ V0, dl b y ≤ dl b x} :
        Set (E d)) ∩ Set.extremePoints ℝ (convexHull ℝ V0))).direction := by
      intro htW
      have hker := vspan_le_ker (dlin b) (b ⬝ᵥ p0 hV0 + 1) (fun x hx => hGc x hx.1) htW
      simp [hbt] at hker
    have hlt := lt_of_le_of_ne hWle (fun h => htW (h ▸ Submodule.subset_span htT))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hWG] at h1
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    rw [Module.finrank_fin_fun]
    calc d = _ := hdim.symm
      _ ≤ _ := h1
  intro y hy
  exact GF93SH.eq_zero_of_dot_span hspan y hy

/-- B2 (`hS`): full polar tight sets have exactly `d` points (simpliciality). -/
theorem hS (hP : IsSimplicialDPolytope (convexHull ℝ V0)) (hne : V0.Nonempty)
    (htop : affineSpan ℝ (convexHull ℝ V0) = ⊤) (b : E d)
    (hb : ∀ x ∈ Vp hV0, b ⬝ᵥ x ≤ 1) (hF : GF93SH.Full ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1))) :
    ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1)).card = d := by
  have hge : d ≤ ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1)).card := by
    have := finrank_span_finset_le_card (R := ℝ) ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1))
    unfold Set.finrank at this
    rw [span_of_full hF, finrank_top, Module.finrank_fin_fun] at this
    exact this
  rcases ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1)).eq_empty_or_nonempty with he | ⟨t, htT⟩
  · rw [he] at hge ⊢
    simp only [card_empty] at hge ⊢
    omega
  have ht := mem_filter.1 htT
  obtain ⟨hGne, hGexp, hGP, hGX, hGc⟩ := polar_face hV0 hne htop b hb t ht.1 ht.2
  have h1 := face_dim_card hP hGne hGexp hGP
  rw [hGX, ncard_tr] at h1
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 := ht.2
    rw [zero_dotProduct] at h0
    exact zero_ne_one h0
  have h2 := dim_lt_of_const (dlin b) (dlin_ne hb0) _ hGc
  omega

/-- B3: a polar facet exists. -/
theorem facets_ne (hP : IsSimplicialDPolytope (convexHull ℝ V0)) (hne : V0.Nonempty)
    (htop : affineSpan ℝ (convexHull ℝ V0) = ⊤) (hd : 0 < d) :
    (GF93SH.facets (Vp hV0)).Nonempty := by
  classical
  obtain ⟨e, he⟩ := Xf_nonempty hV0 hne
  have he' := (mem_Xf hV0).1 he
  have hexp := extreme_exposed hV0 he'
  have hneP : ({e} : Set (E d)) ≠ convexHull ℝ V0 := by
    intro h
    have h1 : affineSpan ℝ ({e} : Set (E d)) = ⊤ := h ▸ htop
    have h2 : (affineSpan ℝ ({e} : Set (E d))).direction = ⊤ := by
      rw [h1, AffineSubspace.direction_top]
    rw [direction_affineSpan, vectorSpan_singleton] at h2
    have h3 : Module.finrank ℝ (⊤ : Submodule ℝ (E d)) = 0 := by
      rw [← h2]; exact finrank_bot ℝ (E d)
    rw [finrank_top, Module.finrank_fin_fun] at h3
    omega
  obtain ⟨G, hGexp, heG, hGd⟩ :=
    properFaceInFacet d V0 hV0 htop {e} (Set.singleton_nonempty e) hexp hneP
  have hGne : G.Nonempty := ⟨e, heG rfl⟩
  have hGP : G ≠ convexHull ℝ V0 := by
    intro h
    rw [h, htop, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at hGd
    omega
  obtain ⟨b, hb, ⟨t, ht, hbt⟩, rfl⟩ := face_polar hV0 hne hGne hGexp hGP
  refine ⟨(Vp hV0).filter (fun x => b ⬝ᵥ x = 1), ?_⟩
  unfold GF93SH.facets
  rw [mem_filter, mem_powerset]
  exact ⟨filter_subset _ _, b, hb, rfl, facet_full hV0 hne htop b hb t ht hbt hGd⟩

/-- Perturbation: every subset `U` of a polar facet `T` is itself a polar tight set. -/
theorem pert (hP : IsSimplicialDPolytope (convexHull ℝ V0)) (hne : V0.Nonempty)
    (htop : affineSpan ℝ (convexHull ℝ V0) = ⊤) {T U : Finset (E d)}
    (hT : T ∈ GF93SH.facets (Vp hV0)) (hUT : U ⊆ T) :
    ∃ b' : E d, (∀ x ∈ Vp hV0, b' ⬝ᵥ x ≤ 1) ∧ (Vp hV0).filter (fun x => b' ⬝ᵥ x = 1) = U := by
  classical
  unfold GF93SH.facets at hT
  rw [mem_filter, mem_powerset] at hT
  obtain ⟨-, b, hb, rfl, hfull⟩ := hT
  have hcard := hS hV0 hP hne htop b hb hfull
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range (Subtype.val :
      ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1) : Finset (E d)) → E d)) := by
    rw [Subtype.range_coe_subtype]
    exact (span_of_full hfull).ge
  have hli : LinearIndependent ℝ (Subtype.val :
      ((Vp hV0).filter (fun x => b ⬝ᵥ x = 1) : Finset (E d)) → E d) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by simp [hcard])
  set T := (Vp hV0).filter (fun x => b ⬝ᵥ x = 1) with hTdef
  let B := Module.Basis.mk hli hsp
  let f : E d →ₗ[ℝ] ℝ := ∑ i ∈ univ.filter (fun i : T => i.1 ∉ U), B.coord i
  have hft : ∀ t (ht : t ∈ T), f t = if t ∈ U then 0 else 1 := by
    intro t ht
    have hB : B ⟨t, ht⟩ = t := Module.Basis.mk_apply hli hsp ⟨t, ht⟩
    calc f t = f (B ⟨t, ht⟩) := by rw [hB]
      _ = ∑ i ∈ univ.filter (fun i : T => i.1 ∉ U), B.coord i (B ⟨t, ht⟩) := by
          simp only [f, LinearMap.sum_apply]
      _ = ∑ i ∈ univ.filter (fun i : T => i.1 ∉ U), if (⟨t, ht⟩ : T) = i then (1 : ℝ) else 0 := by
          refine sum_congr rfl fun i _ => ?_
          rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      _ = if t ∈ U then 0 else 1 := by
          rw [Finset.sum_ite_eq]
          by_cases h : t ∈ U <;> simp [h]
  set c : E d := -(fun i => f (Pi.single i 1)) with hc
  have hcx : ∀ x, c ⬝ᵥ x = - f x := fun x => by rw [hc, neg_dotProduct, ← lin_dot]
  have hoff : ∀ x ∈ Vp hV0, x ∉ T → b ⬝ᵥ x < 1 := fun x hx hxT =>
    lt_of_le_of_ne (hb x hx) (fun h => hxT (mem_filter.2 ⟨hx, h⟩))
  set δ : ℝ := if h : (Vp hV0 \ T).Nonempty then (Vp hV0 \ T).inf' h (fun x => 1 - b ⬝ᵥ x) else 1
    with hδdef
  have hδ : 0 < δ := by
    by_cases h : (Vp hV0 \ T).Nonempty
    · rw [hδdef, dif_pos h, Finset.lt_inf'_iff]
      intro x hx
      rw [mem_sdiff] at hx
      linarith [hoff x hx.1 hx.2]
    · rw [hδdef, dif_neg h]; norm_num
  have hδx : ∀ x ∈ Vp hV0, x ∉ T → δ ≤ 1 - b ⬝ᵥ x := by
    intro x hx hxT
    have hx' : x ∈ Vp hV0 \ T := mem_sdiff.2 ⟨hx, hxT⟩
    rw [hδdef, dif_pos ⟨x, hx'⟩]
    exact Finset.inf'_le _ hx'
  set M : ℝ := 1 + ∑ x ∈ Vp hV0, |c ⬝ᵥ x| with hMdef
  have hMx : ∀ x ∈ Vp hV0, |c ⬝ᵥ x| < M := fun x hx => by
    have := Finset.single_le_sum (f := fun x => |c ⬝ᵥ x|) (fun _ _ => abs_nonneg _) hx
    linarith
  have hM : 0 < M := by
    have : 0 ≤ ∑ x ∈ Vp hV0, |c ⬝ᵥ x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hk : 0 < δ / M := div_pos hδ hM
  have hval : ∀ x, (b + (δ / M) • c) ⬝ᵥ x = b ⬝ᵥ x + δ / M * (c ⬝ᵥ x) := fun x => by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hout : ∀ x ∈ Vp hV0, x ∉ T → (b + (δ / M) • c) ⬝ᵥ x < 1 := by
    intro x hx hxT
    rw [hval]
    have h1 : δ / M * (c ⬝ᵥ x) ≤ δ / M * |c ⬝ᵥ x| := mul_le_mul_of_nonneg_left (le_abs_self _) hk.le
    have h2 : δ / M * |c ⬝ᵥ x| < δ / M * M := mul_lt_mul_of_pos_left (hMx x hx) hk
    rw [div_mul_cancel₀ _ hM.ne'] at h2
    linarith [hδx x hx hxT]
  have hin : ∀ x ∈ T, (b + (δ / M) • c) ⬝ᵥ x = if x ∈ U then 1 else 1 - δ / M := by
    intro x hxT
    rw [hval, hcx, hft x hxT, (mem_filter.1 hxT).2]
    by_cases h : x ∈ U <;> simp [h] <;> ring
  refine ⟨b + (δ / M) • c, fun x hx => ?_, ?_⟩
  · by_cases hxT : x ∈ T
    · rw [hin x hxT]
      split_ifs <;> linarith
    · exact (hout x hx hxT).le
  · ext x
    rw [mem_filter]
    constructor
    · rintro ⟨hx, h1⟩
      by_cases hxT : x ∈ T
      · rw [hin x hxT] at h1
        by_contra hxU
        rw [if_neg hxU] at h1
        linarith
      · linarith [hout x hx hxT]
    · intro hxU
      have hxT := hUT hxU
      exact ⟨(mem_filter.1 hxT).1, by rw [hin x hxT, if_pos hxU]⟩

/-- B4: face numbers = simplex counts of the polar boundary complex. -/
theorem count (hP : IsSimplicialDPolytope (convexHull ℝ V0)) (hne : V0.Nonempty)
    (htop : affineSpan ℝ (convexHull ℝ V0) = ⊤) (j : ℕ) (hj : j < d) :
    faceCount (convexHull ℝ V0) j =
      (((GF93SH.facets (Vp hV0)).biUnion powerset).filter (fun G => G.card = j + 1)).card := by
  classical
  rw [simplicialFaceCount d _ hP j hj]
  have hinj : Function.Injective
      (fun U : Finset (E d) => (fun x => x + p0 hV0) '' (↑U : Set (E d))) := by
    intro U U' h
    exact Finset.coe_injective ((Set.image_injective.2 (add_left_injective (p0 hV0))) h)
  rw [← Set.ncard_coe_finset (((GF93SH.facets (Vp hV0)).biUnion powerset).filter
    (fun G => G.card = j + 1)), ← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext S
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, mem_filter, mem_biUnion,
    mem_powerset]
  constructor
  · rintro ⟨F, hFne, hFexp, hFP, rfl, hcard⟩
    obtain ⟨G, hGexp, hFG, hGd⟩ := properFaceInFacet d V0 hV0 htop F hFne hFexp hFP
    have hGne : G.Nonempty := hFne.mono hFG
    have hGP : G ≠ convexHull ℝ V0 := by
      intro h
      rw [h, htop, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at hGd
      omega
    obtain ⟨bF, hbF, ⟨tF, htF, hbtF⟩, hFeq⟩ := face_polar hV0 hne hFne hFexp hFP
    obtain ⟨bG, hbG, ⟨tG, htG, hbtG⟩, hGeq⟩ := face_polar hV0 hne hGne hGexp hGP
    have hFX := (polar_face hV0 hne htop bF hbF tF htF hbtF).2.2.2.1
    have hGX := (polar_face hV0 hne htop bG hbG tG htG hbtG).2.2.2.1
    rw [← hFeq] at hFX
    rw [← hGeq] at hGX
    refine ⟨(Vp hV0).filter (fun x => bF ⬝ᵥ x = 1),
      ⟨⟨(Vp hV0).filter (fun x => bG ⬝ᵥ x = 1), ?_, ?_⟩, ?_⟩, hFX.symm⟩
    · unfold GF93SH.facets
      rw [mem_filter, mem_powerset]
      refine ⟨filter_subset _ _, bG, hbG, rfl, ?_⟩
      have hGd' := hGd
      rw [hGeq] at hGd'
      exact facet_full hV0 hne htop bG hbG tG htG hbtG hGd'
    · intro x hx
      have hx' : x + p0 hV0 ∈ F ∩ Set.extremePoints ℝ (convexHull ℝ V0) := by
        rw [hFX]; exact ⟨x, hx, rfl⟩
      have hxG : x + p0 hV0 ∈ G ∩ Set.extremePoints ℝ (convexHull ℝ V0) := ⟨hFG hx'.1, hx'.2⟩
      rw [hGX] at hxG
      obtain ⟨y, hy, hyx⟩ := hxG
      have hyx' : y = x := add_right_cancel hyx
      rw [← hyx']
      exact hy
    · rw [hFX, ncard_tr] at hcard
      exact hcard
  · rintro ⟨U, ⟨⟨T, hT, hUT⟩, hUc⟩, rfl⟩
    have hUne : U.Nonempty := by
      rw [← Finset.card_pos, hUc]
      omega
    obtain ⟨b', hb', hfil⟩ := pert hV0 hP hne htop hT hUT
    obtain ⟨t, htU⟩ := hUne
    have ht : t ∈ (Vp hV0).filter (fun x => b' ⬝ᵥ x = 1) := hfil ▸ htU
    obtain ⟨hGne, hGexp, hGP, hGX, -⟩ :=
      polar_face hV0 hne htop b' hb' t (mem_filter.1 ht).1 (mem_filter.1 ht).2
    refine ⟨_, hGne, hGexp, hGP, by rw [hGX, hfil], ?_⟩
    rw [ncard_tr]
    exact hUc

end

/-- C1a-h `HVectorDS` from the polar h-vector theorem. -/
theorem hvector (hPH : PolarHV) : ∀ (d : ℕ) (P : Set (Fin d → ℝ)), IsSimplicialDPolytope P →
    ∃ h : ℕ → ℤ, h 0 = 1 ∧ (∀ i ≤ d, h i = h (d - i)) ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - j.succ.val) : ℤ) := by
  intro d P hP
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨fun i => if i = 0 then 1 else 0, by simp, fun i hi => by simp_all, fun j => j.elim0⟩
  obtain ⟨⟨V0, hV0, hne, rfl⟩, htop⟩ := hP.1
  obtain ⟨h, h0, hs, hf⟩ := hPH d (Vp hV0) (hI hV0 hne htop) (hS hV0 hP hne htop)
    (facets_ne hV0 hP hne htop hd)
  refine ⟨h, h0, hs, fun j => ?_⟩
  rw [count hV0 hP hne htop j.val j.isLt]
  simpa [Fin.val_succ] using hf (j.val + 1) (by omega)

end GF93BR


namespace GF93BR
open Matrix Finset Grunbaum2003

open scoped Classical in
/-- B (session 17): a simplicial `d`-polytope has a shelled boundary complex on `Fin n`
whose shelling h-vector is symmetric, starts with `1`, and gives the face counts. -/
theorem polytope_shelled (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P) :
    ∃ (n : ℕ) (Fs : Finset (Finset (Fin n))) (ord : Finset (Fin n) → ℕ)
      (R : Finset (Fin n) → Finset (Fin n)),
      0 < n ∧ GF93WR.ShellData d Fs ord R ∧ Fs.Nonempty ∧
      (Fs.filter (fun F => (R F).card = 0)).card = 1 ∧
      (∀ i ≤ d, (Fs.filter (fun F => (R F).card = i)).card =
        (Fs.filter (fun F => (R F).card = d - i)).card) ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ range (d + 1), ((Fs.filter (fun F => (R F).card = i)).card : ℤ) *
          ((d - i).choose (d - j.succ.val) : ℤ) := by
  obtain ⟨⟨V0, hV0, hne, rfl⟩, htop⟩ := hP.1
  have hfne := facets_ne hV0 hP hne htop hd
  obtain ⟨hsub, ord, R', hD, h0, hsym, hcnt⟩ :=
    GF93WR.polar_shelled (Vp hV0) (hI hV0 hne htop) (hS hV0 hP hne htop) hfne
  let ι : GF93SH.E d → Fin ((Vp hV0).card + 1) := fun x =>
    if hx : x ∈ Vp hV0 then ((Vp hV0).equivFin ⟨x, hx⟩).castSucc else Fin.last _
  have hι : Set.InjOn ι (Vp hV0) := by
    intro x hx y hy h
    simp only [ι, dif_pos (show x ∈ Vp hV0 from hx), dif_pos (show y ∈ Vp hV0 from hy)] at h
    have := (Vp hV0).equivFin.injective (Fin.castSucc_injective _ h)
    exact congrArg Subtype.val this
  obtain ⟨Fs, ordT, RT, hDT, hcntT, hneT⟩ :=
    GF93WR.transport (Vp hV0) ι hι (GF93SH.facets (Vp hV0)) hsub ord R' hD
  refine ⟨_, Fs, ordT, RT, Nat.succ_pos _, hDT, hneT hfne, ?_, ?_, ?_⟩
  · rw [hcntT]; exact h0
  · intro i hi; rw [hcntT, hcntT]; exact hsym i hi
  · intro j
    rw [count hV0 hP hne htop j.val j.isLt]
    simp only [hcntT]
    simpa [Fin.val_succ] using hcnt (j.val + 1) (by omega)

end GF93BR


-- ==== from f9336347_ds.lean
set_option autoImplicit false

/-! C1a algebraic half (session 8): a symmetric h-vector gives Björner's g-form.
If `f_j = ∑_i h_i C(d-i, d-j-1)` and `h_i = h_{d-i}`, then with `g_i = h_i - h_{i-1}`,
`f_j = ∑_{i ≤ d/2} g_i M_d(i, j+1)`. -/

namespace GF93DS

open Finset Grunbaum2003

def gOf (h : ℕ → ℤ) (j : ℕ) : ℤ := h j - if j = 0 then 0 else h (j - 1)

theorem hockey (N r : ℕ) : ∑ m ∈ range N, (m.choose r : ℤ) = ((N.choose (r + 1)) : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Nat.choose_succ_succ]; push_cast; ring

theorem tele (h : ℕ → ℤ) (m : ℕ) : ∑ j ∈ range (m + 1), gOf h j = h m := by
  induction m with
  | zero => simp [gOf]
  | succ m ih => rw [sum_range_succ, ih]; simp [gOf]

theorem h_decomp (d : ℕ) (h : ℕ → ℤ) (hs : ∀ i ≤ d, h i = h (d - i)) (i : ℕ) (hi : i ≤ d) :
    h i = ∑ j ∈ range (d / 2 + 1), if j ≤ i ∧ i ≤ d - j then gOf h j else 0 := by
  rw [← sum_filter]
  by_cases hid : i ≤ d / 2
  · have : (range (d / 2 + 1)).filter (fun j => j ≤ i ∧ i ≤ d - j) = range (i + 1) := by
      ext j; simp only [mem_filter, mem_range]; omega
    rw [this, tele]
  · have : (range (d / 2 + 1)).filter (fun j => j ≤ i ∧ i ≤ d - j) = range (d - i + 1) := by
      ext j; simp only [mem_filter, mem_range]; omega
    rw [this, tele, ← hs i hi]

theorem ds_alg (d : ℕ) (h : ℕ → ℤ) (hs : ∀ i ≤ d, h i = h (d - i)) (k : ℕ) (hk : k ≤ d) :
    ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - k) : ℤ) =
      ∑ j ∈ range (d / 2 + 1), gOf h j * gTheoremMatrix d j k := by
  have step1 : ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - k) : ℤ) =
      ∑ i ∈ range (d + 1), ∑ j ∈ range (d / 2 + 1),
        (if j ≤ i ∧ i ≤ d - j then gOf h j else 0) * ((d - i).choose (d - k) : ℤ) := by
    apply sum_congr rfl
    intro i hi
    rw [h_decomp d h hs i (by simp only [mem_range] at hi; omega), sum_mul]
  rw [step1, sum_comm]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ d / 2 := by simp only [mem_range] at hj; omega
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter, ← mul_sum]
  congr 1
  have hfil : (range (d + 1)).filter (fun i => j ≤ i ∧ i ≤ d - j) = Icc j (d - j) := by
    ext i; simp only [mem_filter, mem_range, mem_Icc]; omega
  rw [hfil]
  have hrefl : ∑ i ∈ Icc j (d - j), ((d - i).choose (d - k) : ℤ) =
      ∑ m ∈ Icc j (d - j), (m.choose (d - k) : ℤ) := by
    apply sum_nbij' (fun i => d - i) (fun i => d - i)
    · intro i hi; simp only [mem_Icc] at hi ⊢; omega
    · intro i hi; simp only [mem_Icc] at hi ⊢; omega
    · intro i hi; simp only [mem_Icc] at hi; omega
    · intro i hi; simp only [mem_Icc] at hi; omega
    · intro i _; rfl
  rw [hrefl]
  have hIco : Icc j (d - j) = Ico j (d - j + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [hIco, sum_Ico_eq_sub _ (by omega), hockey, hockey]
  unfold gTheoremMatrix
  have e1 : d + 1 - j = d - j + 1 := by omega
  have e2 : d + 1 - k = d - k + 1 := by omega
  rw [e1, e2]

/-- C1a-h (OPEN): the h-vector form of Dehn–Sommerville (from a line shelling). -/
def HVectorDS : Prop :=
  ∀ (d : ℕ) (P : Set (Fin d → ℝ)), IsSimplicialDPolytope P →
    ∃ h : ℕ → ℤ, h 0 = 1 ∧ (∀ i ≤ d, h i = h (d - i)) ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ range (d + 1), h i * ((d - i).choose (d - j.succ.val) : ℤ)

/-- C1a from C1a-h. Same statement as `GF93S.DehnSommervilleG` (scratch/probe/f9336347_stmts.lean). -/
theorem dehnSommervilleG_of_h (hH : HVectorDS) :
    ∀ (d : ℕ) (P : Set (Fin d → ℝ)), IsSimplicialDPolytope P →
      ∃ g : ℕ → ℤ, g 0 = 1 ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i j.succ.val := by
  intro d P hP
  obtain ⟨h, h0, hs, hf⟩ := hH d P hP
  refine ⟨gOf h, by simp [gOf, h0], fun j => ?_⟩
  rw [hf j]
  exact ds_alg d h hs j.succ.val (Nat.lt_succ_iff.mp j.succ.isLt)


/-! ### C1a-h counting half (session 8): faces = disjoint intervals [R F, F] of a shelling. -/

theorem interval_card {α : Type*} [DecidableEq α] (R F : Finset α) (hRF : R ⊆ F) (k : ℕ)
    (hk : k ≤ F.card) :
    ((F.powerset).filter (fun G => R ⊆ G ∧ G.card = k)).card =
      (F.card - R.card).choose (F.card - k) := by
  have hc : (F \ R).card + R.card = F.card := card_sdiff_add_card_eq_card hRF
  rw [show F.card - R.card = (F \ R).card by omega, ← card_powersetCard]
  apply card_nbij' (fun G => F \ G) (fun T => F \ T)
  · intro G hG
    change G ∈ F.powerset.filter (fun G => R ⊆ G ∧ G.card = k) at hG
    show F \ G ∈ powersetCard (F.card - k) (F \ R)
    simp only [mem_filter, mem_powerset, mem_powersetCard] at hG ⊢
    refine ⟨sdiff_subset_sdiff le_rfl hG.2.1, ?_⟩
    have := card_sdiff_add_card_eq_card hG.1
    omega
  · intro T hT
    change T ∈ powersetCard (F.card - k) (F \ R) at hT
    show F \ T ∈ F.powerset.filter (fun G => R ⊆ G ∧ G.card = k)
    simp only [mem_filter, mem_powerset, mem_powersetCard] at hT ⊢
    have hTF : T ⊆ F := hT.1.trans sdiff_subset
    refine ⟨sdiff_subset, ?_, ?_⟩
    · intro x hx
      refine mem_sdiff.mpr ⟨hRF hx, fun hxT => ?_⟩
      exact (mem_sdiff.mp (hT.1 hxT)).2 hx
    · have := card_sdiff_add_card_eq_card hTF
      omega
  · intro G hG
    change G ∈ F.powerset.filter (fun G => R ⊆ G ∧ G.card = k) at hG
    simp only [mem_filter, mem_powerset] at hG
    exact Finset.sdiff_sdiff_eq_self hG.1
  · intro T hT
    change T ∈ powersetCard (F.card - k) (F \ R) at hT
    simp only [mem_powersetCard] at hT
    exact Finset.sdiff_sdiff_eq_self (hT.1.trans sdiff_subset)

theorem shell_count {α : Type*} [DecidableEq α] (Φ : Finset (Finset α)) (R : Finset α → Finset α)
    (d : ℕ) (hcard : ∀ F ∈ Φ, F.card = d) (hRF : ∀ F ∈ Φ, R F ⊆ F)
    (Δ : Finset (Finset α)) (hΔ : ∀ G, G ∈ Δ ↔ ∃ F ∈ Φ, G ⊆ F)
    (huniq : ∀ G ∈ Δ, ∃! F, F ∈ Φ ∧ R F ⊆ G ∧ G ⊆ F) (k : ℕ) (hk : k ≤ d) :
    ((Δ.filter (fun G => G.card = k)).card : ℤ) =
      ∑ i ∈ range (d + 1), ((Φ.filter (fun F => (R F).card = i)).card : ℤ) *
        ((d - i).choose (d - k) : ℤ) := by
  have hset : Δ.filter (fun G => G.card = k) =
      Φ.biUnion (fun F => F.powerset.filter (fun G => R F ⊆ G ∧ G.card = k)) := by
    ext G
    simp only [mem_filter, mem_biUnion, mem_powerset]
    constructor
    · rintro ⟨hG, hGk⟩
      obtain ⟨F, ⟨hF, hRG, hGF⟩, -⟩ := huniq G hG
      exact ⟨F, hF, hGF, hRG, hGk⟩
    · rintro ⟨F, hF, hGF, hRG, hGk⟩
      exact ⟨(hΔ G).mpr ⟨F, hF, hGF⟩, hGk⟩
  have hmaps : ∀ F ∈ Φ, (R F).card ∈ range (d + 1) := by
    intro F hF
    rw [mem_range]
    have := card_le_card (hRF F hF)
    rw [hcard F hF] at this
    omega
  rw [hset, card_biUnion, Nat.cast_sum, ← sum_fiberwise_of_maps_to hmaps]
  · apply sum_congr rfl
    intro i _
    have : ∀ F ∈ Φ.filter (fun F => (R F).card = i),
        (((F.powerset.filter (fun G => R F ⊆ G ∧ G.card = k)).card : ℕ) : ℤ) =
          ((d - i).choose (d - k) : ℤ) := by
      intro F hF
      rw [mem_filter] at hF
      rw [interval_card (R F) F (hRF F hF.1) k (by rw [hcard F hF.1]; exact hk), hcard F hF.1, hF.2]
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  · intro F hF F' hF' hne
    simp only [Function.onFun, Finset.disjoint_left, mem_filter, mem_powerset]
    rintro G ⟨hGF, hRG, -⟩ ⟨hGF', hRG', -⟩
    obtain ⟨F0, -, huF⟩ := huniq G ((hΔ G).mpr ⟨F, hF, hGF⟩)
    exact hne ((huF F ⟨hF, hRG, hGF⟩).trans (huF F' ⟨hF', hRG', hGF'⟩).symm)

end GF93DS


-- ==== from f9336347_w.lean
/-! A2b-i step Z (session 15), abstract: if `u*u = r + Σ_T θ^T y_T` with `r ∈ N`, then iterated
derivations `∂_{(i, v i)}`, `i ∈ S`, isolate `x_{v_S} y_S` modulo `J`; a kill hypothesis (Poincare
duality + independence of the `x^{R F}`) then forces every `y_T = 0`. -/

namespace GF93AN

variable {R : Type} [CommRing R] {d : ℕ} {σ : Type}

/-- Iterated derivation along a list of indices. -/
def dL (Dop : Fin d → σ → R →+ R) (v : Fin d → σ) : List (Fin d) → (R →+ R)
  | [] => AddMonoidHom.id R
  | i :: l => (Dop i (v i)).comp (dL Dop v l)

theorem dL_nil (Dop : Fin d → σ → R →+ R) (v : Fin d → σ) (f : R) : dL Dop v [] f = f := rfl

theorem dL_cons (Dop : Fin d → σ → R →+ R) (v : Fin d → σ) (i : Fin d) (l : List (Fin d)) (f : R) :
    dL Dop v (i :: l) f = Dop i (v i) (dL Dop v l f) := rfl

theorem L1 (Dop : Fin d → σ → R →+ R) (θ : Fin d → R)
    (hDmul : ∀ i v f g, Dop i v (f * g) = f * Dop i v g + g * Dop i v f)
    (hDθ0 : ∀ i v j, i ≠ j → Dop i v (θ j) = 0) (v : Fin d → σ) (j : Fin d) :
    ∀ l : List (Fin d), j ∉ l → ∀ f, dL Dop v l (θ j * f) = θ j * dL Dop v l f
  | [], _, _ => rfl
  | i :: l, h, f => by
    have hij : i ≠ j := fun e => h (by simp [e])
    have hl : j ∉ l := fun hm => h (by simp [hm])
    rw [dL_cons, dL_cons, L1 Dop θ hDmul hDθ0 v j l hl f, hDmul, hDθ0 _ _ _ hij, mul_zero, add_zero]

theorem L2 (J : AddSubgroup R) (hJmul : ∀ q p, p ∈ J → q * p ∈ J)
    (Dop : Fin d → σ → R →+ R) (θ : Fin d → R) (hθ : ∀ i, θ i ∈ J) (x : σ → R)
    (hDmul : ∀ i v f g, Dop i v (f * g) = f * Dop i v g + g * Dop i v f)
    (hDθ : ∀ i v j, Dop i v (θ j) = if i = j then x v else 0) (v : Fin d → σ) :
    ∀ l : List (Fin d), l.Nodup → ∀ y,
      dL Dop v l ((l.map θ).prod * y) - (l.map (fun i => x (v i))).prod * y ∈ J
  | [], _, y => by simp [dL_nil]
  | i :: l, hnd, y => by
    rw [List.nodup_cons] at hnd
    have hDθ0 : ∀ i v j, i ≠ j → Dop i v (θ j) = 0 := fun i v j h => by rw [hDθ, if_neg h]
    have IH := L2 J hJmul Dop θ hθ x hDmul hDθ v l hnd.2 y
    simp only [List.map_cons, List.prod_cons]
    rw [dL_cons, mul_assoc, L1 Dop θ hDmul hDθ0 v i l hnd.1, hDmul, hDθ, if_pos rfl]
    have key := J.add_mem (hJmul (Dop i (v i) (dL Dop v l ((l.map θ).prod * y))) _ (hθ i))
      (hJmul (x (v i)) _ IH)
    convert key using 1
    ring

theorem L3 (J : AddSubgroup R) (hJmul : ∀ q p, p ∈ J → q * p ∈ J)
    (Dop : Fin d → σ → R →+ R) (θ : Fin d → R) (hθ : ∀ i, θ i ∈ J)
    (hDmul : ∀ i v f g, Dop i v (f * g) = f * Dop i v g + g * Dop i v f)
    (hDθ0 : ∀ i v j, i ≠ j → Dop i v (θ j) = 0) (v : Fin d → σ)
    (T : Finset (Fin d)) (j : Fin d) (hj : j ∈ T) (l : List (Fin d)) (hjl : j ∉ l) (y : R) :
    dL Dop v l ((∏ i ∈ T, θ i) * y) ∈ J := by
  classical
  rw [← Finset.mul_prod_erase T θ hj, mul_assoc, L1 Dop θ hDmul hDθ0 v j l hjl, mul_comm]
  exact hJmul _ _ (hθ j)

theorem dL_sq (Dop : Fin d → σ → R →+ R) (hDsq : ∀ i v f, Dop i v (f * f) = 0) (v : Fin d → σ) :
    ∀ l : List (Fin d), l ≠ [] → ∀ u, dL Dop v l (u * u) = 0
  | [], h, _ => absurd rfl h
  | [i], _, u => by rw [dL_cons, dL_nil, hDsq]
  | i :: j :: l, _, u => by
    rw [dL_cons, dL_sq Dop hDsq v (j :: l) (List.cons_ne_nil _ _) u, map_zero]

theorem dL_N (N : AddSubgroup R) (Dop : Fin d → σ → R →+ R)
    (hDN : ∀ i v p, p ∈ N → Dop i v p ∈ N) (v : Fin d → σ) :
    ∀ l : List (Fin d), ∀ p, p ∈ N → dL Dop v l p ∈ N
  | [], _, hp => hp
  | i :: l, p, hp => by rw [dL_cons]; exact hDN _ _ _ (dL_N N Dop hDN v l p hp)

/-- Step Z: all `y_T` vanish, so `u*u = r ∈ N`. -/
theorem z_main (J N : AddSubgroup R) (hJmul : ∀ q p, p ∈ J → q * p ∈ J) (hNJ : ∀ p ∈ N, p ∈ J)
    (θ : Fin d → R) (hθ : ∀ i, θ i ∈ J) (x : σ → R) (Dop : Fin d → σ → R →+ R)
    (hDmul : ∀ i v f g, Dop i v (f * g) = f * Dop i v g + g * Dop i v f)
    (hDsq : ∀ i v f, Dop i v (f * f) = 0)
    (hDθ : ∀ i v j, Dop i v (θ j) = if i = j then x v else 0)
    (hDN : ∀ i v p, p ∈ N → Dop i v p ∈ N)
    (u r : R) (huu : u * u ∈ J) (hr : r ∈ N) (y : Finset (Fin d) → R)
    (hsum : u * u = r + ∑ T : Finset (Fin d), (∏ i ∈ T, θ i) * y T)
    (hkill : ∀ T, (∀ v : Fin d → σ, (∏ i ∈ T, x (v i)) * y T ∈ J) → y T = 0) :
    ∀ T, y T = 0 := by
  classical
  have hDθ0 : ∀ i v j, i ≠ j → Dop i v (θ j) = 0 := fun i v j h => by rw [hDθ, if_neg h]
  suffices H : ∀ m, ∀ T : Finset (Fin d), T.card = m → y T = 0 from fun T => H _ T rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro S hS
  apply hkill
  intro v
  have hnd : S.toList.Nodup := Finset.nodup_toList S
  have hD := congrArg (dL Dop v S.toList) hsum
  rw [map_add, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ S)] at hD
  have hother : ∀ T ∈ (Finset.univ : Finset (Finset (Fin d))).erase S,
      dL Dop v S.toList ((∏ i ∈ T, θ i) * y T) ∈ J := by
    intro T hT
    have hTS : T ≠ S := Finset.ne_of_mem_erase hT
    by_cases hc : T.card < m
    · rw [IH _ hc T rfl, mul_zero, map_zero]; exact J.zero_mem
    · have hns : ¬ T ⊆ S := fun hsub => hTS (Finset.eq_of_subset_of_card_le hsub (by omega))
      obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hns
      exact L3 J hJmul Dop θ hθ hDmul hDθ0 v T j hjT S.toList
        (fun h => hjS (Finset.mem_toList.mp h)) (y T)
  have hS2 := L2 J hJmul Dop θ hθ x hDmul hDθ v S.toList hnd (y S)
  rw [Finset.prod_map_toList, Finset.prod_map_toList] at hS2
  have huuJ : dL Dop v S.toList (u * u) ∈ J := by
    by_cases h0 : S.toList = []
    · rw [h0]; exact huu
    · rw [dL_sq Dop hDsq v _ h0]; exact J.zero_mem
  have hrJ := hNJ _ (dL_N N Dop hDN v S.toList r hr)
  have hsJ := sum_mem hother
  have e : (∏ i ∈ S, x (v i)) * y S = dL Dop v S.toList (u * u) - dL Dop v S.toList r
      - (∑ T ∈ (Finset.univ : Finset (Finset (Fin d))).erase S, dL Dop v S.toList ((∏ i ∈ T, θ i) * y T))
      - (dL Dop v S.toList ((∏ i ∈ S, θ i) * y S) - (∏ i ∈ S, x (v i)) * y S) := by
    rw [hD]; ring
  rw [e]
  exact J.sub_mem (J.sub_mem (J.sub_mem huuJ hrJ) hsJ) hS2

/-- Corollary: `u*u ∈ N`. -/
theorem z_sq_mem (J N : AddSubgroup R) (hJmul : ∀ q p, p ∈ J → q * p ∈ J) (hNJ : ∀ p ∈ N, p ∈ J)
    (θ : Fin d → R) (hθ : ∀ i, θ i ∈ J) (x : σ → R) (Dop : Fin d → σ → R →+ R)
    (hDmul : ∀ i v f g, Dop i v (f * g) = f * Dop i v g + g * Dop i v f)
    (hDsq : ∀ i v f, Dop i v (f * f) = 0)
    (hDθ : ∀ i v j, Dop i v (θ j) = if i = j then x v else 0)
    (hDN : ∀ i v p, p ∈ N → Dop i v p ∈ N)
    (u r : R) (huu : u * u ∈ J) (hr : r ∈ N) (y : Finset (Fin d) → R)
    (hsum : u * u = r + ∑ T : Finset (Fin d), (∏ i ∈ T, θ i) * y T)
    (hkill : ∀ T, (∀ v : Fin d → σ, (∏ i ∈ T, x (v i)) * y T ∈ J) → y T = 0) :
    u * u ∈ N := by
  have h0 := z_main J N hJmul hNJ θ hθ x Dop hDmul hDsq hDθ hDN u r huu hr y hsum hkill
  rw [hsum]
  simp [h0, hr]

end GF93AN

/-! A2b infrastructure (session 14): partial derivatives `∂/∂a_w` on `K = Frac(F₂[a_W])` and their
coefficientwise extension to `K[x]`, built from ring homs into dual numbers (Leibniz for free). -/

namespace GF93DR

open MvPolynomial

variable {W : Type} [DecidableEq W]

abbrev KF (W : Type) := FractionRing (MvPolynomial W (ZMod 2))

theorem two_eq_zero : (2 : KF W) = 0 := by
  have h : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have := map_natCast (algebraMap (ZMod 2) (KF W)) 2
  rw [h, map_zero] at this
  exact_mod_cast this.symm

/-- `f ↦ (f, ∂f/∂a_w)` on polynomials. -/
noncomputable def phiR (w : W) : MvPolynomial W (ZMod 2) →+* DualNumber (KF W) :=
  (aeval (fun w' => (TrivSqZeroExt.inl (algebraMap (MvPolynomial W (ZMod 2)) (KF W) (X w')) : DualNumber (KF W)) +
    if w' = w then DualNumber.eps else 0)).toRingHom

theorem fst_phiR (w : W) (f : MvPolynomial W (ZMod 2)) :
    (phiR w f).fst = algebraMap _ (KF W) f := by
  have : ((TrivSqZeroExt.fstHom (ZMod 2) (KF W) (KF W)).comp
      (aeval (fun w' => (TrivSqZeroExt.inl (algebraMap (MvPolynomial W (ZMod 2)) (KF W) (X w')) : DualNumber (KF W)) +
        if w' = w then DualNumber.eps else 0))) =
      (IsScalarTower.toAlgHom (ZMod 2) (MvPolynomial W (ZMod 2)) (KF W)) := by
    apply MvPolynomial.algHom_ext
    intro w'
    by_cases h : w' = w <;> simp [h]
  exact congrArg (fun φ => φ f) this

theorem phiR_unit (w : W) (y : nonZeroDivisors (MvPolynomial W (ZMod 2))) : IsUnit (phiR w y) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_phiR, isUnit_iff_ne_zero]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2

/-- `z ↦ (z, ∂z/∂a_w)` on the fraction field. -/
noncomputable def PhiK (w : W) : KF W →+* DualNumber (KF W) :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial W (ZMod 2))) (phiR_unit w)

theorem fst_PhiK (w : W) (z : KF W) : (PhiK w z).fst = z := by
  have : (TrivSqZeroExt.fstHom (ZMod 2) (KF W) (KF W)).toRingHom.comp (PhiK w) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial W (ZMod 2)))
    refine RingHom.ext fun f => ?_
    simp only [RingHom.comp_apply, PhiK, IsLocalization.lift_eq, RingHom.id_apply]
    exact fst_phiR w f
  exact congrArg (fun φ => φ z) this

/-- The derivation `∂/∂a_w` on `K`. -/
noncomputable def D (w : W) (z : KF W) : KF W := (PhiK w z).snd

theorem D_add (w : W) (x y : KF W) : D w (x + y) = D w x + D w y := by
  simp [D, map_add]

theorem D_mul (w : W) (x y : KF W) : D w (x * y) = x * D w y + y * D w x := by
  simp only [D, map_mul, TrivSqZeroExt.snd_mul, fst_PhiK, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

theorem D_sq (w : W) (x : KF W) : D w (x * x) = 0 := by
  rw [D_mul, show x * D w x + x * D w x = 2 * (x * D w x) by ring, two_eq_zero, zero_mul]

theorem D_X (w w' : W) : D w (algebraMap (MvPolynomial W (ZMod 2)) (KF W) (X w')) = if w' = w then 1 else 0 := by
  simp only [D, PhiK, IsLocalization.lift_eq, phiR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_X]
  split_ifs <;> simp

theorem D_one (w : W) : D w 1 = 0 := by simp [D, map_one]

variable {σ : Type}

/-- Coefficientwise extension `f ↦ (f, ∂f)` to `K[x]`. -/
noncomputable def gK (w : W) : KF W →+* DualNumber (MvPolynomial σ (KF W)) where
  toFun z := TrivSqZeroExt.inl (C z) + TrivSqZeroExt.inr (C (D w z))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        map_one, TrivSqZeroExt.fst_one]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        D_one, map_zero, TrivSqZeroExt.snd_one]
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, map_mul]
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        zero_add, add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, D_mul,
        map_add, map_mul]
      ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        map_zero, TrivSqZeroExt.fst_zero]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        D, map_zero, TrivSqZeroExt.snd_zero]
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        map_add]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        D_add, map_add]

noncomputable def PsiK (w : W) : MvPolynomial σ (KF W) →+* DualNumber (MvPolynomial σ (KF W)) :=
  eval₂Hom (gK w) (fun v => TrivSqZeroExt.inl (X v))

theorem fst_PsiK (w : W) (f : MvPolynomial σ (KF W)) : (PsiK w f).fst = f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [PsiK, gK]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, TrivSqZeroExt.fst_mul, hp]; simp [PsiK]

/-- `∂/∂a_w` acting on the coefficients of a polynomial in `x`. -/
noncomputable def Dx (w : W) (f : MvPolynomial σ (KF W)) : MvPolynomial σ (KF W) := (PsiK w f).snd

theorem Dx_add (w : W) (f g : MvPolynomial σ (KF W)) : Dx w (f + g) = Dx w f + Dx w g := by
  simp [Dx, map_add]

theorem Dx_mul (w : W) (f g : MvPolynomial σ (KF W)) : Dx w (f * g) = f * Dx w g + g * Dx w f := by
  simp only [Dx, map_mul, TrivSqZeroExt.snd_mul, fst_PsiK, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

theorem Dx_C (w : W) (z : KF W) : Dx (σ := σ) w (C z) = C (D w z) := by
  simp [Dx, PsiK, gK]

theorem Dx_X (w : W) (v : σ) : Dx (σ := σ) w (X v) = 0 := by
  simp [Dx, PsiK]

theorem Dx_sq (w : W) (f : MvPolynomial σ (KF W)) : Dx w (f * f) = 0 := by
  rw [Dx_mul, show f * Dx w f + f * Dx w f = C (2 : KF W) * (f * Dx w f) by
    rw [map_ofNat]; ring, two_eq_zero, map_zero, zero_mul]


section wl
/-! A2b-ii: weak Lefschetz from anisotropy in characteristic 2 (session 14).  For a generic
`ℓ = Σ b_v x_v` and `∂ = ∂/∂b_v` (which fixes `J`): `ℓ p ∈ J ⇒ x_v p² = p·∂(ℓp) - ℓp·∂p ∈ J` for all `v`,
so `p² ∈ J` by Poincare duality (`pd_lin`), so `p ∈ J` by anisotropy. -/
variable {σ K : Type} [Field K]

/-- Same as `GF93LG.WeakLef`. -/
def WeakLef' (J : Submodule K (MvPolynomial σ K)) (m : ℕ) : Prop :=
  ∃ ℓ : MvPolynomial σ K, ℓ.IsHomogeneous 1 ∧ ℓ ≠ 0 ∧
    ∀ k < m, ∀ p ∈ homogeneousSubmodule σ K k, ℓ * p ∈ J → p ∈ J

theorem wl_of_aniso (J : Submodule K (MvPolynomial σ K))
    (hJmul : ∀ q p, p ∈ J → q * p ∈ J) (m : ℕ)
    (ℓ : MvPolynomial σ K) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    (Dv : σ → MvPolynomial σ K → MvPolynomial σ K)
    (hDmul : ∀ v f g, Dv v (f * g) = f * Dv v g + g * Dv v f)
    (hDJ : ∀ v p, p ∈ J → Dv v p ∈ J) (hDl : ∀ v, Dv v ℓ = X v)
    (hpd : ∀ k < m, ∀ q ∈ homogeneousSubmodule σ K (2 * k), (∀ v, X v * q ∈ J) → q ∈ J)
    (hani : ∀ k < m, ∀ p ∈ homogeneousSubmodule σ K k, p * p ∈ J → p ∈ J) :
    WeakLef' J m := by
  refine ⟨ℓ, hℓ, hℓ0, fun k hk p hp hlp => hani k hk p hp ?_⟩
  have hpp : p * p ∈ homogeneousSubmodule σ K (2 * k) := by
    have := (mem_homogeneousSubmodule _ _).mp hp
    rw [mem_homogeneousSubmodule, two_mul]; exact this.mul this
  refine hpd k hk _ hpp fun v => ?_
  have h1 : p * Dv v (ℓ * p) ∈ J := hJmul _ _ (hDJ v _ hlp)
  have h2 : Dv v p * (ℓ * p) ∈ J := hJmul _ _ hlp
  rw [hDmul, hDl] at h1
  have : X v * (p * p) = p * (ℓ * Dv v p + p * X v) - Dv v p * (ℓ * p) := by ring
  rw [this]
  exact J.sub_mem h1 h2

end wl

end GF93DR

namespace GF93PI

/-- A Frobenius-semilinear additive projection onto squares, for any field of characteristic 2. -/
theorem exists_pi0 (K : Type) [Field K] [CharP K 2] :
    ∃ π0 : K →+ K, π0 1 = 1 ∧ (∀ a b, π0 (a * a * b) = a * a * π0 b) ∧
      ∀ b, ∃ a, π0 b = a * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subfield K := (frobenius K 2).fieldRange
  let f : S →ₗ[S] K := Algebra.linearMap S K
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact Subtype.ext h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hf
  have hsq : ∀ a : K, a * a ∈ S := by
    intro a
    refine ⟨a, ?_⟩
    simp [frobenius_def, pow_two]
  refine ⟨{ toFun := fun b => ((g b : S) : K), map_zero' := by simp,
            map_add' := fun x y => by simp }, ?_, ?_, ?_⟩
  · show ((g 1 : S) : K) = 1
    have : g (f 1) = 1 := by rw [← LinearMap.comp_apply, hg]; rfl
    have h1 : f 1 = (1 : K) := by simp [f]
    rw [h1] at this
    rw [this]; rfl
  · intro a b
    show ((g (a * a * b) : S) : K) = a * a * ((g b : S) : K)
    have : a * a * b = (⟨a * a, hsq a⟩ : S) • b := by
      rfl
    rw [this, LinearMap.map_smul]
    rfl
  · intro b
    obtain ⟨a, ha⟩ := (g b).2
    refine ⟨a, ?_⟩
    show ((g b : S) : K) = a * a
    rw [← ha]
    simp [frobenius_def, pow_two]

end GF93PI

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

/-! C1b-i glue (session 11): LefschetzHilbertF from a graded quotient `K[x]/J` whose degree-`k`
dimensions are `h k` and on which a linear form `ℓ` acts injectively in degrees `< m`.
`J` = Stanley-Reisner ideal + l.s.o.p. (to be supplied by children A1 FaceRingDim, A2 WeakLefschetz). -/

namespace GF93LG

/-- Same statement as `GF93S.LefschetzHilbertF` (scratch/probe/f9336347_c1b.lean). -/
def LefschetzHilbertF (m : ℕ) (g : ℕ → ℕ) : Prop :=
  ∃ (K : Type) (inst : Field K) (n : ℕ) (I : Submodule K (MvPolynomial (Fin n) K)),
    (∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I) ∧
    (1 : MvPolynomial (Fin n) K) ∉ I ∧
    ∀ k ≤ m, g k + Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) =
      Module.finrank K (homogeneousSubmodule (Fin n) K k)

def D (n k : ℕ) : Finset (Fin n →₀ ℕ) := Finset.finsuppAntidiag Finset.univ k

theorem mem_D {n k : ℕ} (μ : Fin n →₀ ℕ) : μ ∈ D n k ↔ μ.degree = k := by
  unfold D
  rw [Finset.mem_finsuppAntidiag]
  have h1 : Finset.univ.sum μ = μ.degree := by
    rw [show μ.degree = μ.sum (fun _ e => e) from rfl, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rw [h1]
  simp

theorem homog_eq (K : Type) [Field K] (n k : ℕ) :
    homogeneousSubmodule (Fin n) K k =
      AddMonoidAlgebra.supported K K (↑(D n k) : Set (Fin n →₀ ℕ)) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  congr 1
  ext μ
  simp [mem_D]

theorem homog_finite (K : Type) [Field K] (n k : ℕ) :
    Module.Finite K (homogeneousSubmodule (Fin n) K k) := by
  rw [homog_eq]
  exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
    (↑(D n k) : Set (Fin n →₀ ℕ))).symm

section
variable {K : Type} [Field K] {n : ℕ}

theorem comp_mul (ℓ : MvPolynomial (Fin n) K) (hℓ : ℓ.IsHomogeneous 1)
    (q : MvPolynomial (Fin n) K) (j : ℕ) :
    homogeneousComponent j (ℓ * q) = ∑ i ∈ Finset.range (q.totalDegree + 1),
      if j = 1 + i then ℓ * homogeneousComponent i q else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent q, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hm : ℓ * homogeneousComponent i q ∈ homogeneousSubmodule (Fin n) K (1 + i) :=
    (mem_homogeneousSubmodule _ _).mpr (hℓ.mul (homogeneousComponent_isHomogeneous i q))
  exact homogeneousComponent_of_mem hm

theorem comp0_mul (ℓ : MvPolynomial (Fin n) K) (hℓ : ℓ.IsHomogeneous 1)
    (q : MvPolynomial (Fin n) K) : homogeneousComponent 0 (ℓ * q) = 0 := by
  rw [comp_mul ℓ hℓ q 0]
  exact Finset.sum_eq_zero (fun i _ => if_neg (by omega))

theorem compS_mul (ℓ : MvPolynomial (Fin n) K) (hℓ : ℓ.IsHomogeneous 1)
    (q : MvPolynomial (Fin n) K) (k : ℕ) :
    homogeneousComponent (k + 1) (ℓ * q) = ℓ * homogeneousComponent k q := by
  rw [comp_mul ℓ hℓ q (k + 1)]
  rw [Finset.sum_congr rfl (fun i _ => (by
    show (if k + 1 = 1 + i then ℓ * homogeneousComponent i q else 0) =
      (if k = i then ℓ * homogeneousComponent i q else 0)
    exact if_congr (by omega) rfl rfl))]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero k q (by simp at h; omega), mul_zero]

theorem ideal_mul_mem (J : Submodule K (MvPolynomial (Fin n) K))
    (hX : ∀ p ∈ J, ∀ v : Fin n, X v * p ∈ J) (r : MvPolynomial (Fin n) K) :
    ∀ p ∈ J, r * p ∈ J := by
  induction r using MvPolynomial.induction_on with
  | C a => intro p hp; rw [← smul_eq_C_mul]; exact J.smul_mem a hp
  | add a b ha hb => intro p hp; rw [add_mul]; exact J.add_mem (ha p hp) (hb p hp)
  | mul_X a v ha => intro p hp; rw [mul_assoc]; exact ha _ (hX p hp v)

/-- The glue: graded quotient with Hilbert function `h` plus injective `ℓ` gives `LefschetzHilbertF`
for the first difference of `h`. -/
theorem lefschetzHilbertF_of_graded (m : ℕ) (J : Submodule K (MvPolynomial (Fin n) K))
    (hX : ∀ p ∈ J, ∀ v : Fin n, X v * p ∈ J)
    (hhom : ∀ p ∈ J, ∀ k : ℕ, homogeneousComponent k p ∈ J)
    (h1 : (1 : MvPolynomial (Fin n) K) ∉ J)
    (ℓ : MvPolynomial (Fin n) K) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    (h : ℕ → ℕ)
    (hdim : ∀ k ≤ m, h k + Module.finrank K
        (J ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) =
      Module.finrank K (homogeneousSubmodule (Fin n) K k))
    (hinj : ∀ k < m, ∀ p ∈ homogeneousSubmodule (Fin n) K k, ℓ * p ∈ J → p ∈ J) :
    (∀ k < m, h k ≤ h (k + 1)) ∧
      LefschetzHilbertF m (fun k => if k = 0 then h 0 else h k - h (k - 1)) := by
  set L : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K := LinearMap.mulLeft K ℓ with hL
  have hLapp : ∀ q, L q = ℓ * q := fun q => rfl
  have hLinj : Function.Injective L := by
    intro a b hab
    rw [hLapp, hLapp] at hab
    exact mul_left_cancel₀ hℓ0 hab
  set I : Submodule K (MvPolynomial (Fin n) K) := J ⊔ LinearMap.range L with hI
  have memI : ∀ p, p ∈ I → ∃ a ∈ J, ∃ q, a + ℓ * q = p := by
    intro p hp
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hz
    exact ⟨a, ha, q, by rw [hLapp]⟩
  have hXI : ∀ p ∈ I, ∀ v : Fin n, X v * p ∈ I := by
    intro p hp v
    obtain ⟨a, ha, q, rfl⟩ := memI p hp
    rw [mul_add]
    refine Submodule.add_mem_sup (hX a ha v) (LinearMap.mem_range.mpr ⟨X v * q, ?_⟩)
    rw [hLapp]; ring
  -- degree 0
  have deg0 : ∀ p ∈ I, p ∈ homogeneousSubmodule (Fin n) K 0 → p ∈ J := by
    intro p hp hp0
    obtain ⟨a, ha, q, rfl⟩ := memI p hp
    have e := homogeneousComponent_of_mem (m := 0) hp0
    rw [if_pos rfl, map_add, comp0_mul ℓ hℓ q, add_zero] at e
    rw [← e]; exact hhom a ha 0
  have h1I : (1 : MvPolynomial (Fin n) K) ∉ I := by
    intro h1m
    exact h1 (deg0 1 h1m ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_one _ _)))
  -- degree k+1
  have mulH : ∀ k, ∀ q ∈ homogeneousSubmodule (Fin n) K k,
      ℓ * q ∈ homogeneousSubmodule (Fin n) K (k + 1) := by
    intro k q hq
    have := hℓ.mul ((mem_homogeneousSubmodule _ _).mp hq)
    rw [add_comm] at this
    exact (mem_homogeneousSubmodule _ _).mpr this
  have degS : ∀ k, (I ⊓ homogeneousSubmodule (Fin n) K (k + 1) : Submodule K _) =
      (J ⊓ homogeneousSubmodule (Fin n) K (k + 1)) ⊔
        (homogeneousSubmodule (Fin n) K k).map L := by
    intro k
    apply le_antisymm
    · rintro p ⟨hp, hpk⟩
      obtain ⟨a, ha, q, rfl⟩ := memI p hp
      have e := homogeneousComponent_of_mem (m := k + 1) hpk
      rw [if_pos rfl, map_add, compS_mul ℓ hℓ q k] at e
      rw [← e]
      refine Submodule.add_mem_sup ⟨hhom a ha (k + 1), ?_⟩ ⟨homogeneousComponent k q, ?_, ?_⟩
      · exact (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous _ _)
      · exact (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous _ _)
      · exact hLapp _
    · refine sup_le (inf_le_inf_right _ le_sup_left) ?_
      rintro p ⟨q, hq, rfl⟩
      exact ⟨Submodule.mem_sup_right (LinearMap.mem_range_self L q), by
        rw [hLapp]; exact mulH k q hq⟩
  have interS : ∀ k < m, ((J ⊓ homogeneousSubmodule (Fin n) K (k + 1)) ⊓
        (homogeneousSubmodule (Fin n) K k).map L : Submodule K _) =
      (J ⊓ homogeneousSubmodule (Fin n) K k).map L := by
    intro k hk
    apply le_antisymm
    · rintro p ⟨⟨hpJ, -⟩, q, hq, rfl⟩
      rw [hLapp] at hpJ
      exact ⟨q, ⟨hinj k hk q hq hpJ, hq⟩, rfl⟩
    · rintro p ⟨q, ⟨hqJ, hq⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, q, hq, rfl⟩
      · rw [hLapp]; exact ideal_mul_mem J hX ℓ q hqJ
      · rw [hLapp]; exact mulH k q hq
  -- dimension count in degree k+1
  have countS : ∀ k < m, h k + Module.finrank K
        (J ⊓ homogeneousSubmodule (Fin n) K (k + 1) : Submodule K _) =
      Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K (k + 1) : Submodule K _) := by
    intro k hk
    haveI := homog_finite K n k
    haveI := homog_finite K n (k + 1)
    haveI : Module.Finite K (J ⊓ homogeneousSubmodule (Fin n) K (k + 1) : Submodule K _) :=
      Submodule.finiteDimensional_of_le inf_le_right
    haveI : Module.Finite K (J ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) :=
      Submodule.finiteDimensional_of_le inf_le_right
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq
      (J ⊓ homogeneousSubmodule (Fin n) K (k + 1)) ((homogeneousSubmodule (Fin n) K k).map L)
    rw [← degS k, interS k hk,
      ← (Submodule.equivMapOfInjective L hLinj _).finrank_eq,
      ← (Submodule.equivMapOfInjective L hLinj _).finrank_eq] at e1
    have e2 := hdim k hk.le
    omega
  have monoS : ∀ k < m, h k ≤ h (k + 1) := by
    intro k hk
    haveI := homog_finite K n (k + 1)
    have e := countS k hk
    have e2 := hdim (k + 1) hk
    have le : Module.finrank K (I ⊓ homogeneousSubmodule (Fin n) K (k + 1) : Submodule K _) ≤
        Module.finrank K (homogeneousSubmodule (Fin n) K (k + 1)) :=
      Submodule.finrank_mono inf_le_right
    omega
  refine ⟨monoS, K, inferInstance, n, I, hXI, h1I, ?_⟩
  intro k hk
  rcases k with _ | k
  · simp only [if_true]
    have e : (I ⊓ homogeneousSubmodule (Fin n) K 0 : Submodule K _) =
        J ⊓ homogeneousSubmodule (Fin n) K 0 :=
      le_antisymm (fun p hp => ⟨deg0 p hp.1 hp.2, hp.2⟩) (inf_le_inf_right _ le_sup_left)
    rw [e]; exact hdim 0 hk
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    have e := countS k (by omega)
    have e2 := hdim (k + 1) hk
    have mo := monoS k (by omega)
    omega

end

section facering
variable {K : Type} [Field K] {n : ℕ}

theorem span_X_closed (S : Set (MvPolynomial (Fin n) K))
    (hS : ∀ g ∈ S, ∀ v : Fin n, X v * g ∈ S) :
    ∀ p ∈ Submodule.span K S, ∀ v : Fin n, X v * p ∈ Submodule.span K S := by
  intro p hp v
  induction hp using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hS x hx v)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

theorem span_hom_closed (S : Set (MvPolynomial (Fin n) K))
    (hS : ∀ g ∈ S, ∃ k, g.IsHomogeneous k) :
    ∀ p ∈ Submodule.span K S, ∀ j : ℕ, homogeneousComponent j p ∈ Submodule.span K S := by
  intro p hp j
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hS x hx
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hk)]
    split_ifs
    · exact Submodule.subset_span hx
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- Generators of the Stanley-Reisner ideal of the complex with facet list `Fs`. -/
def srGen (Fs : Finset (Finset (Fin n))) : Set (MvPolynomial (Fin n) K) :=
  {p | ∃ α : Fin n →₀ ℕ, (∀ F ∈ Fs, ¬ α.support ⊆ F) ∧ p = monomial α 1}

/-- Linear forms of the (candidate) l.s.o.p. with coefficient matrix `c`. -/
noncomputable def theta {d : ℕ} (c : Fin d → Fin n → K) (i : Fin d) : MvPolynomial (Fin n) K :=
  ∑ j, C (c i j) * X j

def thGen {d : ℕ} (c : Fin d → Fin n → K) : Set (MvPolynomial (Fin n) K) :=
  {p | ∃ (μ : Fin n →₀ ℕ) (i : Fin d), p = monomial μ 1 * theta c i}

/-- `J = I_Δ + (θ)`, so that `K[x]/J = K[Δ]/(θ)`. -/
noncomputable def Jth {d : ℕ} (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) :
    Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (srGen Fs ∪ thGen c)

theorem theta_hom {d : ℕ} (c : Fin d → Fin n → K) (i : Fin d) : (theta c i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)

theorem Jth_X {d : ℕ} (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) :
    ∀ p ∈ Jth Fs c, ∀ v : Fin n, X v * p ∈ Jth Fs c := by
  apply span_X_closed
  rintro g (⟨α, hα, rfl⟩ | ⟨μ, i, rfl⟩) v
  · refine Or.inl ⟨α + Finsupp.single v 1, fun F hF hsub => hα F hF ?_, ?_⟩
    · intro x hx
      apply hsub
      rw [Finsupp.mem_support_iff] at hx ⊢
      simp only [Finsupp.coe_add, Pi.add_apply]
      omega
    · rw [X, monomial_mul, add_comm, one_mul]
  · refine Or.inr ⟨μ + Finsupp.single v 1, i, ?_⟩
    rw [← mul_assoc, X, monomial_mul, add_comm, one_mul]

theorem Jth_hom {d : ℕ} (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) :
    ∀ p ∈ Jth Fs c, ∀ j : ℕ, homogeneousComponent j p ∈ Jth Fs c := by
  apply span_hom_closed
  rintro g (⟨α, -, rfl⟩ | ⟨μ, i, rfl⟩)
  · exact ⟨_, isHomogeneous_monomial _ rfl⟩
  · exact ⟨_, (isHomogeneous_monomial (n := μ.degree) _ rfl).mul (theta_hom c i)⟩

/-- A1 (Kind-Kleinschmidt 1979 / Stanley, Combinatorics and Commutative Algebra III.2): for a complex with
facet list `Fs` (all of size `d`) carrying a shelling encoded by `ord` and restriction sets `R`
(`R F ⊆ G ⊆ F` iff `F` is the `ord`-last facet containing `G`), and `θ` whose columns on every facet are
linearly independent, `dim (K[Δ]/(θ))_k = #{F : |R F| = k}`. -/
def KK : Prop :=
  ∀ (K : Type) [Field K] (n d : ℕ) (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n)),
    (∀ F ∈ Fs, F.card = d) →
    (∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j)) →
    Set.InjOn ord Fs →
    (∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F)) →
    ∀ k : ℕ, (Fs.filter (fun F => (R F).card = k)).card +
      Module.finrank K (Jth Fs c ⊓ homogeneousSubmodule (Fin n) K k : Submodule K _) =
      Module.finrank K (homogeneousSubmodule (Fin n) K k)

/-- A2 (weak Lefschetz; Stanley 1980, McMullen 1993, Papadakis-Petrotou 2020): a linear form acting
injectively on `K[Δ]/(θ)` in degrees `< m`. -/
def WeakLef (J : Submodule K (MvPolynomial (Fin n) K)) (m : ℕ) : Prop :=
  ∃ ℓ : MvPolynomial (Fin n) K, ℓ.IsHomogeneous 1 ∧ ℓ ≠ 0 ∧
    ∀ k < m, ∀ p ∈ homogeneousSubmodule (Fin n) K k, ℓ * p ∈ J → p ∈ J

/-- C1b-i for a shelled complex: A1 + A2 give `LefschetzHilbertF` for the first difference of the
shelling h-vector. -/
theorem lefschetzHilbertF_of_KK (hKK : KK) {d : ℕ} (Fs : Finset (Finset (Fin n)))
    (c : Fin d → Fin n → K) (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (h1 : (1 : MvPolynomial (Fin n) K) ∉ Jth Fs c) (m : ℕ) (hW : WeakLef (Jth Fs c) m) :
    let h : ℕ → ℕ := fun k => (Fs.filter (fun F => (R F).card = k)).card
    (∀ k < m, h k ≤ h (k + 1)) ∧
      LefschetzHilbertF m (fun k => if k = 0 then h 0 else h k - h (k - 1)) := by
  intro h
  obtain ⟨ℓ, hℓ, hℓ0, hinj⟩ := hW
  exact lefschetzHilbertF_of_graded m (Jth Fs c) (Jth_X Fs c) (Jth_hom Fs c) h1 ℓ hℓ hℓ0 h
    (fun k _ => hKK K n d Fs c ord R hcard hli hord hsh k) hinj

end facering

section basischange
variable {K : Type} [Field K] {n : ℕ}

/-- Ideal generated by the variables outside `F`. -/
noncomputable def outI (F : Finset (Fin n)) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (X '' {v | v ∉ F})

theorem theta_dual {d : ℕ} (c : Fin d → Fin n → K) (F : Finset (Fin n)) (hF : F.card = d)
    (hli : LinearIndependent K (fun j : F => fun i : Fin d => c i j)) (j : Fin n) (hj : j ∈ F) :
    ∃ b : Fin d → K, ∀ j' ∈ F, ∑ i, b i * c i j' = if j' = j then 1 else 0 := by
  haveI : Nonempty F := ⟨⟨j, hj⟩⟩
  have hc : Fintype.card F = Module.finrank K (Fin d → K) := by simp [hF]
  set B := basisOfLinearIndependentOfCardEqFinrank hli hc
  set f := B.coord ⟨j, hj⟩
  refine ⟨fun i => f (fun i' => if i = i' then 1 else 0), fun j' hj' => ?_⟩
  have e := LinearMap.pi_apply_eq_sum_univ f (fun i => c i j')
  have hB : (fun i => c i j') = B ⟨j', hj'⟩ := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [hB] at e
  have e2 : f (B ⟨j', hj'⟩) = if j' = j then 1 else 0 := by
    show B.repr (B ⟨j', hj'⟩) ⟨j, hj⟩ = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : j' = j
    · subst h; simp
    · rw [if_neg (fun h' => h (congrArg Subtype.val h')), if_neg h]
  rw [← e2, e]
  simp only [smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem X_mod_theta {d : ℕ} (c : Fin d → Fin n → K) (F : Finset (Fin n)) (hF : F.card = d)
    (hli : LinearIndependent K (fun j : F => fun i : Fin d => c i j)) (j : Fin n) (hj : j ∈ F) :
    ∃ q : MvPolynomial (Fin d) K, q.IsHomogeneous 1 ∧
      X j - aeval (theta c) q ∈ (outI F : Ideal (MvPolynomial (Fin n) K)) := by
  obtain ⟨b, hb⟩ := theta_dual c F hF hli j hj
  refine ⟨∑ i, C (b i) * X i, IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ _), ?_⟩
  have e : aeval (theta c) (∑ i, C (b i) * X i) =
      ∑ j', C (∑ i, b i * c i j') * (X j' : MvPolynomial (Fin n) K) := by
    simp only [map_sum, map_mul, aeval_C, aeval_X, theta, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [algebraMap_eq]; ring
  rw [e]
  have eX : (X j : MvPolynomial (Fin n) K) = ∑ j', C (if j' = j then (1 : K) else 0) * X j' := by
    simp
  rw [eX, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ (fun j' _ => ?_)
  rw [← sub_mul]
  by_cases hj' : j' ∈ F
  · rw [hb j' hj', sub_self, zero_mul]; exact Ideal.zero_mem _
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j', hj', rfl⟩)

/-- A1c: modulo the variables outside a facet `F`, every monomial on `F` is a homogeneous
polynomial in the `θ_i`. -/
theorem basis_change {d : ℕ} (c : Fin d → Fin n → K) (F : Finset (Fin n)) (hF : F.card = d)
    (hli : LinearIndependent K (fun j : F => fun i : Fin d => c i j)) (β : Fin n →₀ ℕ)
    (hβ : β.support ⊆ F) :
    ∃ q : MvPolynomial (Fin d) K, q.IsHomogeneous β.degree ∧
      monomial β 1 - aeval (theta c) q ∈ (outI F : Ideal (MvPolynomial (Fin n) K)) := by
  induction β using Finsupp.induction with
  | zero => exact ⟨1, by simpa using isHomogeneous_one (Fin d) K, by simp⟩
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := by simpa using ha
    have haF : a ∈ F := hβ (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, hfa]; simpa using hb)
    have hfF : f.support ⊆ F := fun x hx => hβ (by
      rw [Finsupp.mem_support_iff] at hx ⊢
      rw [Finsupp.add_apply]; omega)
    obtain ⟨q, hq, hqI⟩ := ih hfF
    obtain ⟨l, hl, hlI⟩ := X_mod_theta c F hF hli a haF
    refine ⟨l ^ b * q, ?_, ?_⟩
    · have := (hl.pow b).mul hq
      convert this using 1
      rw [map_add, Finsupp.degree_single]; ring
    · rw [← Ideal.Quotient.eq] at hqI hlI ⊢
      have em : (monomial (Finsupp.single a b + f) (1 : K) : MvPolynomial (Fin n) K) =
          X a ^ b * monomial f 1 := by
        rw [X_pow_eq_monomial, monomial_mul, one_mul]
      rw [em, map_mul, map_mul, map_pow, hqI, hlI, map_mul, map_pow, map_pow]

end basischange

section kkproof
variable {K : Type} [Field K] {n d : ℕ}

noncomputable def ind (G : Finset (Fin n)) : Fin n →₀ ℕ := Multiset.toFinsupp G.val

theorem ind_apply (G : Finset (Fin n)) (v : Fin n) : ind G v = if v ∈ G then 1 else 0 := by
  rw [ind, Multiset.toFinsupp_apply, Multiset.count_eq_of_nodup G.nodup]
  by_cases h : v ∈ G <;> simp [h]

theorem ind_support (G : Finset (Fin n)) : (ind G).support = G := by
  ext v; rw [Finsupp.mem_support_iff, ind_apply]; split_ifs with h <;> simp [h]

theorem ind_degree (G : Finset (Fin n)) : (ind G).degree = G.card := by
  rw [show (ind G).degree = (ind G).sum (fun _ e => e) from rfl, Finsupp.sum, ind_support,
    Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl (fun v hv => by rw [ind_apply, if_pos hv])

noncomputable def xR (R : Finset (Fin n) → Finset (Fin n)) (F : Finset (Fin n)) :
    MvPolynomial (Fin n) K := monomial (ind (R F)) 1

noncomputable def ID (Fs : Finset (Finset (Fin n))) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (srGen Fs)

theorem srGen_X (Fs : Finset (Finset (Fin n))) :
    ∀ g ∈ srGen (K := K) Fs, ∀ v : Fin n, X v * g ∈ srGen (K := K) Fs := by
  rintro g ⟨α, hα, rfl⟩ v
  refine ⟨α + Finsupp.single v 1, fun F hF hsub => hα F hF ?_, ?_⟩
  · intro x hx
    apply hsub
    rw [Finsupp.mem_support_iff] at hx ⊢
    simp only [Finsupp.coe_add, Pi.add_apply]
    omega
  · rw [X, monomial_mul, add_comm, one_mul]

theorem ID_X (Fs : Finset (Finset (Fin n))) :
    ∀ p ∈ ID (K := K) Fs, ∀ v : Fin n, X v * p ∈ ID (K := K) Fs :=
  span_X_closed _ (srGen_X Fs)

theorem ID_le (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) : ID (K := K) Fs ≤ Jth Fs c :=
  Submodule.span_mono Set.subset_union_left

noncomputable def Psi (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) :
    (Finset (Fin n) → MvPolynomial (Fin d) K) →ₗ[K] MvPolynomial (Fin n) K :=
  ∑ F ∈ Fs, (LinearMap.mulLeft K (xR R F)) ∘ₗ (aeval (theta c)).toLinearMap ∘ₗ LinearMap.proj F

theorem Psi_apply (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (p : Finset (Fin n) → MvPolynomial (Fin d) K) :
    Psi Fs c R p = ∑ F ∈ Fs, xR R F * aeval (theta c) (p F) := by
  simp [Psi, LinearMap.sum_apply]

theorem Psi_single (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) {F : Finset (Fin n)} (hF : F ∈ Fs)
    (q : MvPolynomial (Fin d) K) :
    Psi Fs c R (Pi.single F q) = xR R F * aeval (theta c) q := by
  rw [Psi_apply, Finset.sum_eq_single F]
  · rw [Pi.single_eq_same]
  · intro F' _ hne; rw [Pi.single_eq_of_ne hne, map_zero, mul_zero]
  · intro h; exact absurd hF h

theorem R_sub (Fs : Finset (Finset (Fin n))) (ord : Finset (Fin n) → ℕ)
    (R : Finset (Fin n) → Finset (Fin n)) (hcard : ∀ F ∈ Fs, F.card = d)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F)) :
    ∀ F ∈ Fs, R F ⊆ F := by
  intro F hF
  refine (hsh F hF F subset_rfl).mpr (fun F' hF' hFF' => ?_)
  have : F = F' := Finset.eq_of_subset_of_card_le hFF' (by rw [hcard F hF, hcard F' hF'])
  rw [this]

theorem ord_lt (Fs : Finset (Finset (Fin n))) (ord : Finset (Fin n) → ℕ)
    (R : Finset (Fin n) → Finset (Fin n)) (hcard : ∀ F ∈ Fs, F.card = d)
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    {F F' : Finset (Fin n)} (hF : F ∈ Fs) (hF' : F' ∈ Fs) (hne : F ≠ F') (hR : R F' ⊆ F) :
    ord F < ord F' := by
  have h1 : R F' ⊆ F ∩ F' := Finset.subset_inter hR (R_sub Fs ord R hcard hsh F' hF')
  have h2 := (hsh F' hF' (F ∩ F') Finset.inter_subset_right).mp h1 F hF Finset.inter_subset_left
  rcases h2.lt_or_eq with h | h
  · exact h
  · exact absurd (hord hF hF' h) hne

theorem surj_aux (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F)) :
    ∀ N : ℕ, ∀ α : Fin n →₀ ℕ, (∀ F ∈ Fs, α.support ⊆ F → ord F < N) →
      (monomial α (1 : K) : MvPolynomial (Fin n) K) ∈ ID (K := K) Fs ⊔ LinearMap.range (Psi Fs c R) := by
  intro N
  induction N with
  | zero =>
    intro α hα
    apply Submodule.mem_sup_left
    apply Submodule.subset_span
    exact ⟨α, fun F hF hsub => absurd (hα F hF hsub) (Nat.not_lt_zero _), rfl⟩
  | succ N ih =>
    intro α hα
    by_cases hex : ∃ F ∈ Fs, α.support ⊆ F
    swap
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      exact ⟨α, fun F hF hsub => hex ⟨F, hF, hsub⟩, rfl⟩
    obtain ⟨F, hFm, hmax⟩ := Finset.exists_max_image (Fs.filter (fun F => α.support ⊆ F)) ord
      (let ⟨F, hF, hs⟩ := hex; ⟨F, Finset.mem_filter.mpr ⟨hF, hs⟩⟩)
    rw [Finset.mem_filter] at hFm
    obtain ⟨hF, hsub⟩ := hFm
    have hRα : R F ⊆ α.support := (hsh F hF α.support hsub).mpr
      (fun F' hF' hs => hmax F' (Finset.mem_filter.mpr ⟨hF', hs⟩))
    have hRF : R F ⊆ F := hRα.trans hsub
    have hle : ind (R F) ≤ α := by
      refine Finsupp.le_def.mpr (fun v => ?_)
      rw [ind_apply]
      split_ifs with hv
      · have := hRα hv; rw [Finsupp.mem_support_iff] at this; omega
      · exact Nat.zero_le _
    set β := α - ind (R F) with hβ
    have hαβ : α = ind (R F) + β := (add_tsub_cancel_of_le hle).symm
    have hβF : β.support ⊆ F := by
      intro v hv
      apply hsub
      rw [Finsupp.mem_support_iff] at hv ⊢
      rw [hβ, Finsupp.tsub_apply] at hv
      omega
    obtain ⟨q, -, hq⟩ := basis_change c F (hcard F hF) (hli F hF) β hβF
    have e : (monomial α (1 : K) : MvPolynomial (Fin n) K) =
        Psi Fs c R (Pi.single F q) + xR R F * (monomial β 1 - aeval (theta c) q) := by
      rw [Psi_single Fs c R hF, xR]
      conv_lhs => rw [hαβ, ← one_mul (1 : K), ← monomial_mul]
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_right (LinearMap.mem_range_self _ _)) ?_
    set r := (monomial β (1 : K) : MvPolynomial (Fin n) K) - aeval (theta c) q with hr
    rw [outI, mem_ideal_span_X_image] at hq
    rw [as_sum r, Finset.mul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    obtain ⟨v, hvF, hmv⟩ := hq m hm
    have em : xR R F * monomial m (coeff m r) = coeff m r • monomial (ind (R F) + m) (1 : K) := by
      rw [xR, monomial_mul, one_mul, smul_monomial, smul_eq_mul, mul_one]
    rw [em]
    refine Submodule.smul_mem _ _ (ih _ ?_)
    intro F' hF' hs
    have hne : F ≠ F' := by
      rintro rfl
      exact hvF (hs (by rw [Finsupp.mem_support_iff, Finsupp.add_apply]; omega))
    have h1 : ord F' ≤ ord F := (hsh F hF (R F) hRF).mp subset_rfl F' hF' (fun x hx => hs (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, ind_apply, if_pos hx]; omega))
    have h2 : ord F' ≠ ord F := fun h => hne (hord hF hF' h.symm)
    have h3 := hα F hF hsub
    omega

theorem surj (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (x : MvPolynomial (Fin n) K) : x ∈ ID (K := K) Fs ⊔ LinearMap.range (Psi Fs c R) := by
  rw [as_sum x]
  refine Submodule.sum_mem _ (fun m _ => ?_)
  have e : (monomial m (coeff m x) : MvPolynomial (Fin n) K) = coeff m x • monomial m (1 : K) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ (surj_aux Fs c ord R hcard hli hord hsh (Fs.sup ord + 1) m
    (fun F hF _ => Nat.lt_succ_of_le (Finset.le_sup hF)))

theorem exists_rho (c : Fin d → Fin n → K) (F : Finset (Fin n)) (hF : F.card = d)
    (hli : LinearIndependent K (fun j : F => fun i : Fin d => c i j)) :
    ∃ ρ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin d) K,
      (∀ j, j ∉ F → ρ (X j) = 0) ∧ ∀ q, ρ (aeval (theta c) q) = q := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨aeval (fun _ => 0), fun j _ => by simp, fun q => ?_⟩
    have : (aeval (fun _ : Fin n => (0 : MvPolynomial (Fin 0) K))).comp (aeval (theta c)) =
        AlgHom.id K _ := MvPolynomial.algHom_ext (fun i => i.elim0)
    exact DFunLike.congr_fun this q
  · obtain ⟨j0, hj0⟩ := Finset.card_pos.mp (hF ▸ hd)
    haveI : Nonempty F := ⟨⟨j0, hj0⟩⟩
    have hc : Fintype.card F = Module.finrank K (Fin d → K) := by simp [hF]
    set B := basisOfLinearIndependentOfCardEqFinrank hli hc
    have hB : ∀ x : F, B x = fun i => c i x := fun x => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    let b : Fin d → Fin n → K := fun i j =>
      if h : j ∈ F then B.repr (Pi.single i 1) ⟨j, h⟩ else 0
    have key : ∀ i i' : Fin d, ∑ j, c i' j * b i j = if i' = i then 1 else 0 := by
      intro i i'
      have e := congrFun (B.sum_repr (Pi.single i 1)) i'
      rw [Finset.sum_apply] at e
      simp only [Pi.smul_apply, smul_eq_mul, hB, Pi.single_apply] at e
      rw [← e, ← Finset.sum_subset (Finset.subset_univ F) (fun j _ hj => by simp [b, hj]),
        ← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp [b, x.2, mul_comm]
    refine ⟨aeval (fun j => ∑ i, C (b i j) * X i), fun j hj => by simp [b, hj], fun q => ?_⟩
    have hθ : ∀ i', aeval (fun j => ∑ i, C (b i j) * X i) (theta c i') =
        (X i' : MvPolynomial (Fin d) K) := by
      intro i'
      simp only [theta, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ i, ∑ j, C (c i' j) * (C (b i j) * X i) =
          C (if i' = i then (1 : K) else 0) * (X i : MvPolynomial (Fin d) K) := by
        intro i
        rw [← key i i', map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_mul]; ring
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_eq_single i']
      · simp
      · intro i _ hi; rw [if_neg (fun h => hi h.symm), C_0, zero_mul]
      · simp
    have : (aeval (fun j => ∑ i, C (b i j) * X i)).comp (aeval (theta c)) =
        AlgHom.id K (MvPolynomial (Fin d) K) := by
      apply MvPolynomial.algHom_ext; intro i'
      rw [AlgHom.comp_apply, aeval_X, hθ, AlgHom.id_apply]
    exact DFunLike.congr_fun this q

noncomputable def sig (F : Finset (Fin n)) : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (fun v => if v ∈ F then X v else 0)

theorem sig_mono_out (F : Finset (Fin n)) (α : Fin n →₀ ℕ) (h : ¬ α.support ⊆ F) :
    sig (K := K) F (monomial α 1) = 0 := by
  obtain ⟨v, hv, hvF⟩ := Finset.not_subset.mp h
  rw [sig, aeval_monomial, Finsupp.prod,
    Finset.prod_eq_zero hv (by simp [hvF, Finsupp.mem_support_iff.mp hv]), mul_zero]

theorem sig_mono_in (F : Finset (Fin n)) (α : Fin n →₀ ℕ) (h : α.support ⊆ F) :
    sig (K := K) F (monomial α 1) = monomial α 1 := by
  rw [sig, aeval_monomial, monomial_eq, map_one, C_1, one_mul, one_mul, Finsupp.prod, Finsupp.prod]
  exact Finset.prod_congr rfl (fun v hv => by simp [h hv])

theorem sig_ID (Fs : Finset (Finset (Fin n))) {F : Finset (Fin n)} (hF : F ∈ Fs) :
    ∀ s ∈ ID (K := K) Fs, sig F s = 0 := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => obtain ⟨α, hα, rfl⟩ := hx; exact sig_mono_out F α (hα F hF)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_C_mul, map_mul, hx, mul_zero]

theorem inj (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (p : Finset (Fin n) → MvPolynomial (Fin d) K)
    (hp : Psi Fs c R p ∈ ID (K := K) Fs) : ∀ F ∈ Fs, p F = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨F, hFm, hmax⟩ := Finset.exists_max_image (Fs.filter (fun F => p F ≠ 0)) ord
    (let ⟨F, hF, h⟩ := hcon; ⟨F, Finset.mem_filter.mpr ⟨hF, h⟩⟩)
  rw [Finset.mem_filter] at hFm
  obtain ⟨hF, hpF⟩ := hFm
  obtain ⟨ρ, hρ0, hρ⟩ := exists_rho c F (hcard F hF) (hli F hF)
  have h0 := sig_ID Fs hF _ hp
  rw [Psi_apply, map_sum, Finset.sum_eq_single F] at h0
  · rw [map_mul, xR, sig_mono_in F _ (by rw [ind_support]; exact R_sub Fs ord R hcard hsh F hF)] at h0
    have h1 : sig F (aeval (theta c) (p F)) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (by rw [monomial_eq_zero]; exact one_ne_zero)
      · exact h
    have hcomp : ρ.comp (sig F) = ρ := by
      apply MvPolynomial.algHom_ext; intro j
      simp only [AlgHom.comp_apply, sig, aeval_X]
      split_ifs with hj
      · rfl
      · rw [map_zero, hρ0 j hj]
    have e1 := DFunLike.congr_fun hcomp (aeval (theta c) (p F))
    rw [AlgHom.comp_apply, h1, map_zero, hρ] at e1
    exact hpF e1.symm
  · intro F' hF' hne
    by_cases hp' : p F' = 0
    · rw [hp', map_zero, mul_zero, map_zero]
    · have hle : ord F' ≤ ord F := hmax F' (Finset.mem_filter.mpr ⟨hF', hp'⟩)
      have hRn : ¬ (R F' ⊆ F) := fun hR =>
        absurd (ord_lt Fs ord R hcard hord hsh hF hF' (Ne.symm hne) hR) (not_lt.mpr hle)
      rw [map_mul, xR, sig_mono_out F _ (by rw [ind_support]; exact hRn), zero_mul]
  · intro h; exact absurd hF h

theorem theta_mem (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) (i : Fin d) :
    theta c i ∈ Jth Fs c :=
  Submodule.subset_span (Or.inr ⟨0, i, by rw [monomial_zero', C_1, one_mul]⟩)

theorem aeval_mem (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (q : MvPolynomial (Fin d) K) (hq : constantCoeff q = 0) : aeval (theta c) q ∈ Jth Fs c := by
  rw [as_sum q, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mem_support_iff] at hm
    exact hm (by rw [constantCoeff_eq] at hq; exact hq)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
  have hi' : m i ≠ 0 := by simpa using hi
  have hle : Finsupp.single i 1 ≤ m := by
    refine Finsupp.le_def.mpr (fun j => ?_)
    by_cases h : i = j
    · subst h; rw [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_apply, h]
  have em : (monomial m (coeff m q) : MvPolynomial (Fin d) K) =
      monomial (m - Finsupp.single i 1) (coeff m q) * X i := by
    rw [X, monomial_mul, mul_one, tsub_add_cancel_of_le hle]
  rw [em, map_mul, aeval_X]
  exact ideal_mul_mem (Jth Fs c) (Jth_X Fs c) _ _ (theta_mem Fs c i)

theorem Psi_W (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (p : Finset (Fin n) → MvPolynomial (Fin d) K)
    (hp : ∀ F, constantCoeff (p F) = 0) : Psi Fs c R p ∈ Jth Fs c := by
  rw [Psi_apply]
  exact Submodule.sum_mem _ (fun F _ => ideal_mul_mem _ (Jth_X Fs c) _ _ (aeval_mem Fs c _ (hp F)))

theorem J_rep (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F)) :
    ∀ x ∈ Jth Fs c, ∃ p : Finset (Fin n) → MvPolynomial (Fin d) K,
      (∀ F, constantCoeff (p F) = 0) ∧ x - Psi Fs c R p ∈ ID (K := K) Fs := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨α, hα, rfl⟩ | ⟨μ, i, rfl⟩
    · exact ⟨0, fun F => by simp, by rw [map_zero, sub_zero]; exact Submodule.subset_span ⟨α, hα, rfl⟩⟩
    · obtain ⟨s, hs, z, hz, hsz⟩ := Submodule.mem_sup.mp
        (surj Fs c ord R hcard hli hord hsh (monomial μ (1 : K)))
      obtain ⟨p0, rfl⟩ := LinearMap.mem_range.mp hz
      refine ⟨fun F => X i * p0 F, fun F => by simp, ?_⟩
      have e : Psi Fs c R (fun F => X i * p0 F) = theta c i * Psi Fs c R p0 := by
        rw [Psi_apply, Psi_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun F _ => ?_)
        rw [map_mul, aeval_X]; ring
      rw [e, ← hsz]
      have e2 : (s + Psi Fs c R p0) * theta c i - theta c i * Psi Fs c R p0 = theta c i * s := by ring
      rw [e2]
      exact ideal_mul_mem _ (ID_X Fs) _ s hs
  | zero => exact ⟨0, fun F => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp0, hp⟩ := hx
    obtain ⟨q, hq0, hq⟩ := hy
    refine ⟨p + q, fun F => by simp [hp0 F, hq0 F], ?_⟩
    rw [map_add]
    convert Submodule.add_mem _ hp hq using 1
    ring
  | smul a x _ hx =>
    obtain ⟨p, hp0, hp⟩ := hx
    refine ⟨a • p, fun F => by rw [Pi.smul_apply, smul_eq_C_mul, map_mul, hp0 F, mul_zero], ?_⟩
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hp

theorem sum_T (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (T : Finset (Finset (Fin n))) (hT : T ⊆ Fs)
    (a : T → K) :
    ∑ i : T, a i • xR (K := K) R i.1 =
      Psi Fs c R (fun F => C (if h : F ∈ T then a ⟨F, h⟩ else 0)) := by
  rw [Psi_apply]
  rw [← Finset.sum_subset hT (f := fun F => xR (K := K) R F *
      aeval (theta c) (C (if h : F ∈ T then a ⟨F, h⟩ else 0)))
    (fun F _ hF => by simp only [dif_neg hF, map_zero, mul_zero])]
  rw [← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [dif_pos i.2, Subtype.coe_eta, aeval_C, algebraMap_eq]
  rw [mul_comm, ← smul_eq_C_mul]

/-- A1 PROVED: Kind-Kleinschmidt dimension count. -/
theorem kk_holds : KK := by
  intro K _ n d Fs c ord R hcard hli hord hsh k
  set T := Fs.filter (fun F => (R F).card = k) with hT
  have hTsub : T ⊆ Fs := Finset.filter_subset _ _
  have hTmem : ∀ F, F ∈ T ↔ F ∈ Fs ∧ (R F).card = k := fun F => by rw [hT, Finset.mem_filter]
  set H := homogeneousSubmodule (Fin n) K k with hH
  set J := Jth Fs c with hJ
  set V : Submodule K (MvPolynomial (Fin n) K) :=
    Submodule.span K (Set.range (fun i : T => xR (K := K) R i.1)) with hV
  have hli2 : LinearIndependent K (fun i : T => xR (K := K) R i.1) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    rw [sum_T Fs c R T hTsub a] at ha
    have := inj Fs c ord R hcard hli hord hsh _ (by rw [ha]; exact Submodule.zero_mem _) i.1
      (hTsub i.2)
    simpa [i.2] using this
  have hVH : V ≤ H := by
    rw [hV, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _
      (show (ind (R i.1)).degree = k by rw [ind_degree]; exact ((hTmem _).mp i.2).2))
  have hVJ : ∀ v ∈ V, v ∈ J → v = 0 := by
    intro v hv hvJ
    rw [hV, Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨a, rfl⟩ := hv
    obtain ⟨p, hp0, hpI⟩ := J_rep Fs c ord R hcard hli hord hsh _ hvJ
    rw [sum_T Fs c R T hTsub a, ← map_sub] at hpI
    have := inj Fs c ord R hcard hli hord hsh _ hpI
    have ha : ∀ i, a i = 0 := by
      intro i
      have h1 := this i.1 (hTsub i.2)
      simp only [Pi.sub_apply, dif_pos i.2, Subtype.coe_eta] at h1
      have h2 := congrArg constantCoeff h1
      rw [map_sub, constantCoeff_C, hp0, sub_zero, map_zero] at h2
      exact h2
    rw [sum_T Fs c R T hTsub a]
    have hz : (fun F => C (if h : F ∈ T then a ⟨F, h⟩ else 0) : Finset (Fin n) → MvPolynomial (Fin d) K) = 0 := by
      funext F; split_ifs <;> simp [ha]
    rw [hz, map_zero]
  have hHle : H ≤ V ⊔ (J ⊓ H) := by
    intro h hh
    obtain ⟨s, hs, z, hz, hsz⟩ := Submodule.mem_sup.mp (surj Fs c ord R hcard hli hord hsh h)
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hz
    set p' : Finset (Fin n) → MvPolynomial (Fin d) K := fun F => p F - C (constantCoeff (p F))
      with hp'
    have hsplit : Psi Fs c R p = Psi Fs c R (fun F => C (constantCoeff (p F))) + Psi Fs c R p' := by
      rw [← map_add]; congr 1; funext F; simp [hp']
    have hj : s + Psi Fs c R p' ∈ J :=
      J.add_mem (ID_le Fs c hs) (Psi_W Fs c R p' (fun F => by simp [hp']))
    have hconst : Psi Fs c R (fun F => C (constantCoeff (p F))) =
        ∑ F ∈ Fs, constantCoeff (p F) • xR (K := K) R F := by
      rw [Psi_apply]; refine Finset.sum_congr rfl (fun F _ => ?_)
      rw [aeval_C, algebraMap_eq, mul_comm, ← smul_eq_C_mul]
    have hh' : homogeneousComponent k h = h := by
      rw [homogeneousComponent_of_mem hh, if_pos rfl]
    rw [← hh', ← hsz, hsplit, hconst,
      show s + (∑ F ∈ Fs, constantCoeff (p F) • xR (K := K) R F + Psi Fs c R p') =
        ∑ F ∈ Fs, constantCoeff (p F) • xR (K := K) R F + (s + Psi Fs c R p') by ring, map_add]
    refine Submodule.add_mem_sup ?_ ⟨Jth_hom Fs c _ hj k,
      (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous _ _)⟩
    rw [map_sum]
    refine Submodule.sum_mem _ (fun F hF => ?_)
    rw [map_smul, xR, homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule (R F).card _).mpr (isHomogeneous_monomial _
        (show (ind (R F)).degree = (R F).card from ind_degree _)))]
    split_ifs with hk
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨F, (hTmem F).mpr ⟨hF, hk.symm⟩⟩, rfl⟩)
    · rw [smul_zero]; exact Submodule.zero_mem _
  haveI := homog_finite K n k
  haveI : FiniteDimensional K V := Submodule.finiteDimensional_of_le hVH
  haveI : FiniteDimensional K (J ⊓ H : Submodule K _) := Submodule.finiteDimensional_of_le inf_le_right
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq V (J ⊓ H)
  have hsup : V ⊔ (J ⊓ H) = H := le_antisymm (sup_le hVH inf_le_right) hHle
  have hinf : V ⊓ (J ⊓ H) = ⊥ := by
    rw [eq_bot_iff]; rintro v ⟨hv, hvJ, -⟩; exact (Submodule.mem_bot K).mpr (hVJ v hv hvJ)
  have hVc : Module.finrank K V = T.card := by
    rw [hV, finrank_span_eq_card hli2, Fintype.card_coe]
  rw [hsup, hinf, finrank_bot, add_zero, hVc] at e1
  omega

theorem one_not_mem_Jth (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hne : Fs.Nonempty) : (1 : MvPolynomial (Fin n) K) ∉ Jth Fs c := by
  intro h1
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image Fs ord hne
  have hR : R F = ∅ := Finset.subset_empty.mp
    ((hsh F hF ∅ (Finset.empty_subset _)).mpr (fun F' hF' _ => hmax F' hF'))
  have e := kk_holds K n d Fs c ord R hcard hli hord hsh 0
  have hle : homogeneousSubmodule (Fin n) K 0 ≤ Jth Fs c ⊓ homogeneousSubmodule (Fin n) K 0 := by
    intro p hp
    refine ⟨?_, hp⟩
    have hp0 : p.totalDegree = 0 :=
      Nat.le_zero.mp ((mem_homogeneousSubmodule _ _).mp hp).totalDegree_le
    rw [totalDegree_eq_zero_iff_eq_C.mp hp0, ← mul_one (C _), ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ h1
  have heq : Jth Fs c ⊓ homogeneousSubmodule (Fin n) K 0 = homogeneousSubmodule (Fin n) K 0 :=
    le_antisymm inf_le_right hle
  rw [heq] at e
  have hpos : 0 < (Fs.filter (fun F => (R F).card = 0)).card :=
    Finset.card_pos.mpr ⟨F, Finset.mem_filter.mpr ⟨hF, by rw [hR, Finset.card_empty]⟩⟩
  omega

/-- C1b-i for a shelled complex, now needing only A2 (weak Lefschetz). -/
theorem lefschetzHilbertF_of_shell (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hne : Fs.Nonempty) (m : ℕ) (hW : WeakLef (Jth Fs c) m) :
    let h : ℕ → ℕ := fun k => (Fs.filter (fun F => (R F).card = k)).card
    (∀ k < m, h k ≤ h (k + 1)) ∧
      LefschetzHilbertF m (fun k => if k = 0 then h 0 else h k - h (k - 1)) :=
  lefschetzHilbertF_of_KK kk_holds Fs c ord R hcard hli hord hsh
    (one_not_mem_Jth Fs c ord R hcard hli hord hsh hne) m hW

end kkproof


section pd
/-! A2a Poincare duality for `K[Δ]/θ` (session 13): with a shelling (`hsh`), its reversal (`hrev`)
and "each ridge lies in at most two facets" (`hpm`), every facet monomial is nonzero in `K[x]/J`
and the pairing with the complementary monomials `x^{F \ R F}` is nondegenerate. -/
variable {K : Type} [Field K] {n d : ℕ}

theorem ind_insert (G : Finset (Fin n)) (w : Fin n) (hw : w ∉ G) :
    ind (insert w G) = ind G + Finsupp.single w 1 := by
  ext v
  simp only [Finsupp.add_apply, ind_apply, Finsupp.single_apply]
  by_cases h1 : v = w
  · subst h1; simp [hw]
  · by_cases h2 : v ∈ G <;> simp [h1, h2, Ne.symm h1]

theorem ind_split (F S : Finset (Fin n)) (h : S ⊆ F) : ind S + ind (F \ S) = ind F := by
  ext v
  simp only [Finsupp.add_apply, ind_apply]
  by_cases h1 : v ∈ S
  · simp [h1, h h1]
  · by_cases h2 : v ∈ F <;> simp [h1, h2]

theorem mem_supp_add (A B : Finset (Fin n)) (v : Fin n) :
    v ∈ (ind A + ind B).support ↔ v ∈ A ∨ v ∈ B := by
  rw [Finsupp.mem_support_iff, Finsupp.add_apply, ind_apply, ind_apply]
  by_cases h1 : v ∈ A <;> by_cases h2 : v ∈ B <;> simp [h1, h2]

theorem mono_mem_J (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) (α : Fin n →₀ ℕ)
    (h : ∀ F ∈ Fs, ¬ α.support ⊆ F) : monomial α (1 : K) ∈ Jth Fs c :=
  Submodule.subset_span (Set.mem_union_left _ ⟨α, h, rfl⟩)

theorem sum_eq_Psi (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (a : Finset (Fin n) → K) :
    ∑ F ∈ Fs, a F • xR (K := K) R F = Psi Fs c R (fun F => C (a F)) := by
  rw [Psi_apply]
  refine Finset.sum_congr rfl (fun F _ => ?_)
  rw [aeval_C, algebraMap_eq, mul_comm, ← smul_eq_C_mul]

theorem xR_indep (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (a : Finset (Fin n) → K) (h : ∑ F ∈ Fs, a F • xR (K := K) R F ∈ Jth Fs c) :
    ∀ F ∈ Fs, a F = 0 := by
  rw [sum_eq_Psi Fs c R a] at h
  obtain ⟨p, hp0, hpI⟩ := J_rep Fs c ord R hcard hli hord hsh _ h
  rw [← map_sub] at hpI
  have := inj Fs c ord R hcard hli hord hsh _ hpI
  intro F hF
  have h2 := congrArg constantCoeff (this F hF)
  rw [Pi.sub_apply, map_sub, constantCoeff_C, hp0, sub_zero, map_zero] at h2
  exact h2

theorem span_mod (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (x : MvPolynomial (Fin n) K) :
    ∃ a : Finset (Fin n) → K, x - ∑ F ∈ Fs, a F • xR (K := K) R F ∈ Jth Fs c := by
  obtain ⟨s, hs, z, hz, hsz⟩ := Submodule.mem_sup.mp (surj Fs c ord R hcard hli hord hsh x)
  obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hz
  refine ⟨fun F => constantCoeff (p F), ?_⟩
  rw [sum_eq_Psi Fs c R, ← hsz]
  have e2 : s + Psi Fs c R p - Psi Fs c R (fun F => C (constantCoeff (p F))) =
      s + Psi Fs c R (p - fun F => C (constantCoeff (p F))) := by rw [map_sub]; ring
  rw [e2]
  exact Submodule.add_mem _ (ID_le Fs c hs) (Psi_W Fs c R _ (fun F => by simp))

theorem theta_comb (c : Fin d → Fin n → K) (b : Fin d → K) :
    ∑ i, C (b i) * theta c i = ∑ j, C (∑ i, b i * c i j) * (X j : MvPolynomial (Fin n) K) := by
  simp only [theta, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul]; ring

/-- Ridge relation: across a ridge `G` lying only in `insert v G` and `insert w G`,
`x^{G+v} ∈ J → x^{G+w} ∈ J`. -/
theorem ridge_rel (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (G : Finset (Fin n)) (v w : Fin n) (hv : v ∉ G) (hw : w ∉ G)
    (hcard' : (insert w G).card = d)
    (hli' : LinearIndependent K (fun j : (insert w G : Finset (Fin n)) => fun i : Fin d => c i j))
    (htwo : ∀ F'' ∈ Fs, G ⊆ F'' → F'' = insert v G ∨ F'' = insert w G)
    (h : monomial (ind (insert v G)) (1 : K) ∈ Jth Fs c) :
    monomial (ind (insert w G)) (1 : K) ∈ Jth Fs c := by
  classical
  obtain ⟨b, hb⟩ := theta_dual c (insert w G) hcard' hli' w (Finset.mem_insert_self w G)
  have key : monomial (ind G) (1 : K) * ∑ i, C (b i) * theta c i ∈ Jth Fs c := by
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [mul_left_comm, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_union_right _ ⟨ind G, i, rfl⟩))
  have e : monomial (ind G) (1 : K) * ∑ i, C (b i) * theta c i =
      ∑ j, (∑ i, b i * c i j) • monomial (ind G + Finsupp.single j 1) (1 : K) := by
    rw [theta_comb, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [X, C_mul_monomial, monomial_mul, smul_monomial, smul_eq_mul, mul_one, one_mul]
  rw [e, ← Finset.add_sum_erase _ _ (Finset.mem_univ w)] at key
  have hbw : ∑ i, b i * c i w = 1 := by
    rw [hb w (Finset.mem_insert_self w G), if_pos rfl]
  have hrest : ∑ j ∈ Finset.univ.erase w,
      (∑ i, b i * c i j) • monomial (ind G + Finsupp.single j 1) (1 : K) ∈ Jth Fs c := by
    refine Submodule.sum_mem _ (fun j hj => ?_)
    have hjw : j ≠ w := Finset.ne_of_mem_erase hj
    by_cases hjG : j ∈ G
    · rw [hb j (Finset.mem_insert_of_mem hjG), if_neg hjw, zero_smul]
      exact Submodule.zero_mem _
    · rw [← ind_insert G j hjG]
      by_cases hjv : j = v
      · subst hjv; exact Submodule.smul_mem _ _ h
      · refine Submodule.smul_mem _ _ (mono_mem_J Fs c _ (fun F'' hF'' hsub => ?_))
        rw [ind_support] at hsub
        have hG : G ⊆ F'' := fun u hu => hsub (Finset.mem_insert_of_mem hu)
        have hj : j ∈ F'' := hsub (Finset.mem_insert_self j G)
        rcases htwo F'' hF'' hG with rfl | rfl
        · rcases Finset.mem_insert.mp hj with h1 | h1
          · exact hjv h1
          · exact hjG h1
        · rcases Finset.mem_insert.mp hj with h1 | h1
          · exact hjw h1
          · exact hjG h1
  have h3 := (Submodule.add_mem_iff_left _ hrest).mp key
  rw [hbw, one_smul, ← ind_insert G w hw] at h3
  exact h3

/-- Every facet monomial is nonzero in `K[Δ]/θ`. -/
theorem facet_nz (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3) :
    ∀ F ∈ Fs, monomial (ind F) (1 : K) ∉ Jth Fs c := by
  classical
  suffices H : ∀ m, ∀ F ∈ Fs, ord F = m → monomial (ind F) (1 : K) ∉ Jth Fs c from
    fun F hF => H _ F hF rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hF hm hJ
  have hRsub := R_sub Fs ord R hcard hsh F hF
  by_cases hRF : R F = F
  · have hs : ∑ F' ∈ Fs, (Pi.single F (1 : K) : Finset (Fin n) → K) F' • xR (K := K) R F' ∈
        Jth Fs c := by
      rw [Finset.sum_eq_single F (fun F' _ hne => by rw [Pi.single_eq_of_ne hne, zero_smul])
        (fun h => absurd hF h), Pi.single_eq_same, one_smul, xR, hRF]
      exact hJ
    have := xR_indep Fs c ord R hcard hli hord hsh _ hs F hF
    simp at this
  · obtain ⟨v, hvF, hvR⟩ : ∃ v ∈ F, v ∉ R F := by
      by_contra hcon; push_neg at hcon
      exact hRF (Finset.Subset.antisymm hRsub hcon)
    set G := F.erase v with hGdef
    have hnot : ¬ (F \ R F ⊆ G) := fun hs => by
      have := hs (Finset.mem_sdiff.mpr ⟨hvF, hvR⟩)
      simp [hGdef] at this
    rw [hrev F hF G (Finset.erase_subset v F)] at hnot
    push_neg at hnot
    obtain ⟨F', hF', hGF', hlt⟩ := hnot
    have hGcard : G.card + 1 = d := by
      rw [hGdef, Finset.card_erase_of_mem hvF, hcard F hF]
      have : 0 < d := by rw [← hcard F hF]; exact Finset.card_pos.mpr ⟨v, hvF⟩
      omega
    obtain ⟨w, hwF', hwG⟩ : ∃ w ∈ F', w ∉ G := by
      by_contra hcon; push_neg at hcon
      have := Finset.card_le_card (show F' ⊆ G from hcon)
      rw [hcard F' hF'] at this; omega
    have hF'eq : F' = insert w G := by
      symm
      refine Finset.eq_of_subset_of_card_le (Finset.insert_subset hwF' hGF') ?_
      rw [hcard F' hF', Finset.card_insert_of_notMem hwG]; omega
    have hFeq : F = insert v G := by rw [hGdef, Finset.insert_erase hvF]
    have hvG : v ∉ G := by simp [hGdef]
    have hFF' : F ≠ F' := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    have htwo : ∀ F'' ∈ Fs, G ⊆ F'' → F'' = insert v G ∨ F'' = insert w G := by
      intro F'' hF'' hG''
      rcases hpm G hGcard F hF F' hF' F'' hF'' (hFeq ▸ Finset.subset_insert v G) hGF' hG''
        with h | h | h
      · exact absurd h hFF'
      · left; rw [← h, hFeq]
      · right; rw [← h, hF'eq]
    have hJ' := ridge_rel Fs c G v w hvG hwG (by rw [← hF'eq]; exact hcard F' hF')
      (by rw [← hF'eq]; exact hli F' hF') htwo (by rw [← hFeq]; exact hJ)
    rw [← hF'eq] at hJ'
    exact ih (ord F') (hm ▸ hlt) F' hF' rfl hJ'

/-- A2a Poincare-duality pairing: anything nonzero in `K[Δ]/θ` pairs nontrivially with some
complementary facet monomial `x^{F \ R F}`. -/
theorem pd_core (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (x : MvPolynomial (Fin n) K) (hx : x ∉ Jth Fs c) (a : Finset (Fin n) → K)
    (ha : x - ∑ F ∈ Fs, a F • xR (K := K) R F ∈ Jth Fs c) :
    ∃ F ∈ Fs, a F ≠ 0 ∧ x * monomial (ind (F \ R F)) (1 : K) ∉ Jth Fs c := by
  classical
  by_contra hcon
  push_neg at hcon
  have hne : (Fs.filter (fun F => a F ≠ 0)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hx
    have h0 : ∑ F ∈ Fs, a F • xR (K := K) R F = 0 :=
      Finset.sum_eq_zero (fun F hF => by rw [not_not.mp (h hF), zero_smul])
    rwa [h0, sub_zero] at ha
  obtain ⟨F0, hF0S, hmax⟩ := Finset.exists_max_image _ ord hne
  rw [Finset.mem_filter] at hF0S
  obtain ⟨hF0, haF0⟩ := hF0S
  set q : MvPolynomial (Fin n) K := monomial (ind (F0 \ R F0)) 1 with hq
  have h1 : (x - ∑ F ∈ Fs, a F • xR (K := K) R F) * q ∈ Jth Fs c := by
    rw [mul_comm]; exact ideal_mul_mem _ (Jth_X Fs c) q _ ha
  have h2 : (∑ F ∈ Fs, a F • xR (K := K) R F) * q ∈ Jth Fs c := by
    have := Submodule.sub_mem _ (hcon F0 hF0 haF0) h1
    rwa [sub_mul, sub_sub_cancel] at this
  have eF : ∀ F, xR (K := K) R F * q = monomial (ind (R F) + ind (F0 \ R F0)) 1 := by
    intro F; rw [xR, hq, monomial_mul, one_mul]
  rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ hF0] at h2
  have hrest : ∑ F ∈ Fs.erase F0, a F • xR (K := K) R F * q ∈ Jth Fs c := by
    refine Submodule.sum_mem _ (fun F hF => ?_)
    obtain ⟨hFne, hFs⟩ := Finset.mem_erase.mp hF
    by_cases haF : a F = 0
    · rw [haF, zero_smul, zero_mul]; exact Submodule.zero_mem _
    have hle : ord F ≤ ord F0 := hmax F (Finset.mem_filter.mpr ⟨hFs, haF⟩)
    have hlt : ord F < ord F0 := lt_of_le_of_ne hle (fun h => hFne (hord hFs hF0 h))
    rw [smul_mul_assoc, eF]
    refine Submodule.smul_mem _ _ (mono_mem_J Fs c _ (fun F'' hF'' hsub => ?_))
    have hA : R F ⊆ F'' := fun u hu => hsub ((mem_supp_add _ _ u).mpr (Or.inl hu))
    have hB : F0 \ R F0 ⊆ F'' := fun u hu => hsub ((mem_supp_add _ _ u).mpr (Or.inr hu))
    have o1 := (hsh F hFs (R F) (R_sub Fs ord R hcard hsh F hFs)).mp subset_rfl F'' hF'' hA
    have o2 := (hrev F0 hF0 (F0 \ R F0) Finset.sdiff_subset).mp subset_rfl F'' hF'' hB
    omega
  have h3 := (Submodule.add_mem_iff_left _ hrest).mp h2
  rw [smul_mul_assoc, eF, ind_split F0 (R F0) (R_sub Fs ord R hcard hsh F0 hF0)] at h3
  have h4 := Submodule.smul_mem _ (a F0)⁻¹ h3
  rw [smul_smul, inv_mul_cancel₀ haF0, one_smul] at h4
  exact facet_nz Fs c ord R hcard hli hord hsh hrev hpm F0 hF0 h4


theorem span_mod_hom (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (k : ℕ) (x : MvPolynomial (Fin n) K) (hx : x ∈ homogeneousSubmodule (Fin n) K k) :
    ∃ a : Finset (Fin n) → K, (∀ F, a F ≠ 0 → (R F).card = k) ∧
      x - ∑ F ∈ Fs, a F • xR (K := K) R F ∈ Jth Fs c := by
  classical
  obtain ⟨a, ha⟩ := span_mod Fs c ord R hcard hli hord hsh x
  refine ⟨fun F => if (R F).card = k then a F else 0, fun F hF => ?_, ?_⟩
  · by_contra h; exact hF (if_neg h)
  have h1 := Jth_hom Fs c _ ha k
  have hxk : homogeneousComponent k x = x := by
    rw [homogeneousComponent_of_mem hx, if_pos rfl]
  have hR : ∀ F, homogeneousComponent k (xR (K := K) R F) =
      if (R F).card = k then xR (K := K) R F else 0 := by
    intro F
    have hm : xR (K := K) R F ∈ homogeneousSubmodule (Fin n) K (R F).card :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ (ind_degree _))
    rw [homogeneousComponent_of_mem hm]
    by_cases h : (R F).card = k
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  rw [map_sub, map_sum, hxk] at h1
  convert h1 using 2
  refine Finset.sum_congr rfl (fun F _ => ?_)
  rw [map_smul, hR F]
  by_cases h : (R F).card = k
  · simp only [if_pos h]
  · simp only [if_neg h, smul_zero, zero_smul]

/-- A2a, linear form version: in degrees `< d`, an element killed (mod `J`) by every variable is
zero in `K[Δ]/θ` (no socle below the top degree). -/
theorem pd_lin (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (k : ℕ) (hk : k < d) (x : MvPolynomial (Fin n) K) (hx : x ∈ homogeneousSubmodule (Fin n) K k)
    (hX : ∀ v, X v * x ∈ Jth Fs c) : x ∈ Jth Fs c := by
  classical
  by_contra hxJ
  obtain ⟨a, hak, ha⟩ := span_mod_hom Fs c ord R hcard hli hord hsh k x hx
  obtain ⟨F, hF, haF, hq⟩ := pd_core Fs c ord R hcard hli hord hsh hrev hpm x hxJ a ha
  have hRk := hak F haF
  have hRsub := R_sub Fs ord R hcard hsh F hF
  obtain ⟨v, hv⟩ : (F \ R F).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hRsub, hcard F hF, hRk]; omega
  have hins : insert v ((F \ R F).erase v) = F \ R F := Finset.insert_erase hv
  have hq' : monomial (ind (F \ R F)) (1 : K) = monomial (ind ((F \ R F).erase v)) 1 * X v := by
    rw [← hins, ind_insert _ v (Finset.notMem_erase v _), hins, X, monomial_mul, one_mul]
  apply hq
  rw [hq', mul_comm, mul_assoc]
  exact ideal_mul_mem _ (Jth_X Fs c) _ _ (hX v)

/-- A2a, pairing version. -/
theorem pd_pair (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (k : ℕ) (x : MvPolynomial (Fin n) K) (hx : x ∈ homogeneousSubmodule (Fin n) K k)
    (hxJ : x ∉ Jth Fs c) :
    ∃ F ∈ Fs, (R F).card = k ∧ x * monomial (ind (F \ R F)) (1 : K) ∉ Jth Fs c := by
  obtain ⟨a, hak, ha⟩ := span_mod_hom Fs c ord R hcard hli hord hsh k x hx
  obtain ⟨F, hF, haF, hq⟩ := pd_core Fs c ord R hcard hli hord hsh hrev hpm x hxJ a ha
  exact ⟨F, hF, hak F haF, hq⟩


/-- With a shelling and its reversal, every facet containing a ridge `G` is the ord-last or the
ord-first facet containing `G`. -/
theorem extreme (Fs : Finset (Finset (Fin n))) (ord : Finset (Fin n) → ℕ)
    (R : Finset (Fin n) → Finset (Fin n)) (hcard : ∀ F ∈ Fs, F.card = d)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (F : Finset (Fin n)) (hF : F ∈ Fs) (G : Finset (Fin n)) (hGF : G ⊆ F) (hG : G.card + 1 = d) :
    (∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F) ∨ (∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F') := by
  classical
  by_cases h : R F ⊆ G
  · exact Or.inl ((hsh F hF G hGF).mp h)
  · refine Or.inr ((hrev F hF G hGF).mp (fun u hu => ?_))
    obtain ⟨huF, huR⟩ := Finset.mem_sdiff.mp hu
    by_contra huG
    obtain ⟨u', hu'R, hu'G⟩ := Finset.not_subset.mp h
    have hu'F := R_sub Fs ord R hcard hsh F hF hu'R
    have hc : (F \ G).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset hGF, hcard F hF]; omega
    have := Finset.card_le_one.mp hc u (Finset.mem_sdiff.mpr ⟨huF, huG⟩) u'
      (Finset.mem_sdiff.mpr ⟨hu'F, hu'G⟩)
    exact huR (this ▸ hu'R)

/-- The pseudomanifold hypothesis `hpm` of `facet_nz`/`pd_lin`/`pd_pair` follows from a shelling
and its reversal. -/
theorem pm_of_shell (Fs : Finset (Finset (Fin n))) (ord : Finset (Fin n) → ℕ)
    (R : Finset (Fin n) → Finset (Fin n)) (hcard : ∀ F ∈ Fs, F.card = d)
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F')) :
    ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3 := by
  intro G hG F1 h1 F2 h2 F3 h3 g1 g2 g3
  have e : ∀ {A B : Finset (Fin n)}, A ∈ Fs → B ∈ Fs → ord A ≤ ord B → ord B ≤ ord A → A = B :=
    fun hA hB x y => hord hA hB (le_antisymm x y)
  rcases extreme Fs ord R hcard hsh hrev F1 h1 G g1 hG with a1 | a1 <;>
  rcases extreme Fs ord R hcard hsh hrev F2 h2 G g2 hG with a2 | a2 <;>
  rcases extreme Fs ord R hcard hsh hrev F3 h3 G g3 hG with a3 | a3 <;>
  first
    | exact Or.inl (e h1 h2 (a2 F1 h1 g1) (a1 F2 h2 g2))
    | exact Or.inl (e h1 h2 (a1 F2 h2 g2) (a2 F1 h1 g1))
    | exact Or.inr (Or.inl (e h1 h3 (a3 F1 h1 g1) (a1 F3 h3 g3)))
    | exact Or.inr (Or.inl (e h1 h3 (a1 F3 h3 g3) (a3 F1 h1 g1)))
    | exact Or.inr (Or.inr (e h2 h3 (a3 F2 h2 g2) (a2 F3 h3 g3)))
    | exact Or.inr (Or.inr (e h2 h3 (a2 F3 h3 g3) (a3 F2 h2 g2)))

end pd


section expansion
/-! A2b-i step E (session 15): every homogeneous `p` of degree `e` is `r + Σ_T θ^T y_T` with
`r ∈ N = I_Δ + (θ_i²)` and `y_T ∈ span {x^{R F} : |R F| + |T| = e}`; plus the kill lemma
(`x_{v_T} y_T ∈ J` for all `v` forces `y_T = 0`) from Poincare duality and independence. -/
variable {K : Type} [Field K] {n d : ℕ}

def nGen (c : Fin d → Fin n → K) : Set (MvPolynomial (Fin n) K) :=
  {p | ∃ (μ : Fin n →₀ ℕ) (i : Fin d), p = monomial μ 1 * (theta c i * theta c i)}

noncomputable def Nth (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) :
    Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (srGen Fs ∪ nGen c)

theorem Nth_X (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) :
    ∀ p ∈ Nth Fs c, ∀ v : Fin n, X v * p ∈ Nth Fs c := by
  apply span_X_closed
  rintro g (⟨α, hα, rfl⟩ | ⟨μ, i, rfl⟩) v
  · refine Or.inl ⟨α + Finsupp.single v 1, fun F hF hsub => hα F hF ?_, ?_⟩
    · intro x hx
      apply hsub
      rw [Finsupp.mem_support_iff] at hx ⊢
      simp only [Finsupp.coe_add, Pi.add_apply]
      omega
    · rw [X, monomial_mul, add_comm, one_mul]
  · refine Or.inr ⟨μ + Finsupp.single v 1, i, ?_⟩
    rw [← mul_assoc, X, monomial_mul, add_comm, one_mul]

theorem Nth_mul (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) (q p : MvPolynomial (Fin n) K)
    (hp : p ∈ Nth Fs c) : q * p ∈ Nth Fs c :=
  ideal_mul_mem _ (Nth_X Fs c) q p hp

theorem thsq_mem (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) (i : Fin d)
    (q : MvPolynomial (Fin n) K) : theta c i * theta c i * q ∈ Nth Fs c := by
  rw [mul_comm]
  refine Nth_mul Fs c q _ (Submodule.subset_span (Or.inr ⟨0, i, ?_⟩))
  rw [monomial_zero', C_1, one_mul]

theorem Nth_le (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) : Nth Fs c ≤ Jth Fs c := by
  refine Submodule.span_le.mpr ?_
  rintro g (hg | ⟨μ, i, rfl⟩)
  · exact Submodule.subset_span (Or.inl hg)
  · rw [← mul_assoc]
    exact ideal_mul_mem _ (Jth_X Fs c) _ _ (theta_mem Fs c i)

theorem ID_le_Nth (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) : ID (K := K) Fs ≤ Nth Fs c :=
  Submodule.span_mono Set.subset_union_left

noncomputable def Ycap (R : Finset (Fin n) → Finset (Fin n)) (Fs : Finset (Finset (Fin n))) (e : ℕ)
    (T : Finset (Fin d)) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (xR (K := K) R '' {F | F ∈ Fs ∧ (R F).card + T.card = e})

noncomputable def thT (c : Fin d → Fin n → K) (T : Finset (Fin d)) : MvPolynomial (Fin n) K :=
  ∏ i ∈ T, theta c i

noncomputable def Pe (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (e : ℕ) : Submodule K (MvPolynomial (Fin n) K) where
  carrier := {p | ∃ r ∈ Nth Fs c, ∃ y : Finset (Fin d) → MvPolynomial (Fin n) K,
    (∀ T, y T ∈ Ycap (K := K) R Fs e T) ∧ p = r + ∑ T : Finset (Fin d), thT c T * y T}
  add_mem' := by
    rintro a b ⟨r1, hr1, y1, hy1, rfl⟩ ⟨r2, hr2, y2, hy2, rfl⟩
    refine ⟨r1 + r2, add_mem hr1 hr2, y1 + y2, fun T => add_mem (hy1 T) (hy2 T), ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  zero_mem' := ⟨0, zero_mem _, 0, fun T => zero_mem _, by simp⟩
  smul_mem' := by
    rintro a b ⟨r, hr, y, hy, rfl⟩
    refine ⟨a • r, Submodule.smul_mem _ a hr, a • y, fun T => Submodule.smul_mem _ a (hy T), ?_⟩
    simp only [Pi.smul_apply, smul_add, Finset.smul_sum, mul_smul_comm]

theorem N_Pe (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (e : ℕ) (r : MvPolynomial (Fin n) K) (hr : r ∈ Nth Fs c) :
    r ∈ Pe Fs c R e :=
  ⟨r, hr, 0, fun T => zero_mem _, by simp⟩

theorem single_Pe (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (e : ℕ) (T : Finset (Fin d)) (y : MvPolynomial (Fin n) K)
    (hy : y ∈ Ycap (K := K) R Fs e T) : thT c T * y ∈ Pe Fs c R e := by
  classical
  refine ⟨0, zero_mem _, fun T' => if T' = T then y else 0, fun T' => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · subst h; exact hy
    · exact zero_mem _
  · simp

theorem theta_mul_Pe (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (e : ℕ) (i : Fin d) (p : MvPolynomial (Fin n) K)
    (hp : p ∈ Pe Fs c R e) : theta c i * p ∈ Pe Fs c R (e + 1) := by
  classical
  obtain ⟨r, hr, y, hy, rfl⟩ := hp
  rw [mul_add, Finset.mul_sum]
  refine add_mem (N_Pe _ _ _ _ _ (Nth_mul Fs c _ _ hr)) (sum_mem fun T _ => ?_)
  by_cases hi : i ∈ T
  · apply N_Pe
    have e1 : theta c i * (thT c T * y T) =
        theta c i * theta c i * ((∏ j ∈ T.erase i, theta c j) * y T) := by
      unfold thT; rw [← Finset.mul_prod_erase T _ hi]; ring
    rw [e1]; exact thsq_mem Fs c i _
  · have e1 : theta c i * (thT c T * y T) = thT c (insert i T) * y T := by
      unfold thT; rw [Finset.prod_insert hi, mul_assoc]
    rw [e1]
    refine single_Pe Fs c R (e + 1) _ _ (Submodule.span_mono ?_ (hy T))
    rintro _ ⟨F, ⟨hF, hc⟩, rfl⟩
    refine ⟨F, ⟨hF, ?_⟩, rfl⟩
    rw [Finset.card_insert_eq_ite, if_neg hi]; omega

theorem Ycap_hom (R : Finset (Fin n) → Finset (Fin n)) (Fs : Finset (Finset (Fin n))) (e : ℕ)
    (T : Finset (Fin d)) : Ycap (K := K) R Fs e T ≤ homogeneousSubmodule (Fin n) K (e - T.card) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨F, ⟨_, hc⟩, rfl⟩
  rw [SetLike.mem_coe, mem_homogeneousSubmodule]
  exact isHomogeneous_monomial _ (by rw [ind_degree]; omega)

theorem jth_hc (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (R : Finset (Fin n) → Finset (Fin n)) (e : ℕ)
    (hIH : ∀ e', e' + 1 = e → ∀ p ∈ homogeneousSubmodule (Fin n) K e', p ∈ Pe Fs c R e') :
    ∀ q ∈ Jth Fs c, homogeneousComponent e q ∈ Pe Fs c R e := by
  intro q hq
  induction hq using Submodule.span_induction with
  | mem g hg =>
    rcases hg with hg | ⟨μ, i, rfl⟩
    · have hS : ∀ g' ∈ srGen (K := K) Fs, ∃ k, g'.IsHomogeneous k := by
        rintro _ ⟨α, -, rfl⟩; exact ⟨_, isHomogeneous_monomial _ rfl⟩
      exact N_Pe _ _ _ _ _ (ID_le_Nth Fs c
        (span_hom_closed _ hS g (Submodule.subset_span hg) e))
    · have hm : monomial μ (1 : K) * theta c i ∈ homogeneousSubmodule (Fin n) K (μ.degree + 1) :=
        (mem_homogeneousSubmodule _ _).mpr ((isHomogeneous_monomial _ rfl).mul (theta_hom c i))
      rw [homogeneousComponent_of_mem hm]
      split_ifs with h
      · subst h
        rw [mul_comm]
        exact theta_mul_Pe Fs c R _ i _ (hIH _ rfl _
          ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ rfl)))
      · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- Step E. -/
theorem expand (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F)) :
    ∀ e, ∀ p ∈ homogeneousSubmodule (Fin n) K e, p ∈ Pe Fs c R e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e IH =>
  intro p hp
  obtain ⟨a, ha, hJ⟩ := span_mod_hom Fs c ord R hcard hli hord hsh e p hp
  have hsum : ∑ F ∈ Fs, a F • xR (K := K) R F ∈ Ycap (K := K) R Fs e (∅ : Finset (Fin d)) := by
    refine sum_mem fun F hF => ?_
    by_cases h0 : a F = 0
    · rw [h0, zero_smul]; exact zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨F, ⟨hF, by rw [Finset.card_empty, add_zero]; exact ha F h0⟩, rfl⟩)
  have hSh := Ycap_hom R Fs e (∅ : Finset (Fin d)) hsum
  have h1 := jth_hc Fs c R e (fun e' he' => IH e' (by omega)) _ hJ
  rw [map_sub, homogeneousComponent_of_mem hp, if_pos rfl, homogeneousComponent_of_mem hSh,
    if_pos (by simp)] at h1
  have h2 := single_Pe Fs c R e (∅ : Finset (Fin d)) _ hsum
  rw [thT, Finset.prod_empty, one_mul] at h2
  have h3 := add_mem h1 h2
  rwa [sub_add_cancel] at h3

theorem Ycap_rep (R : Finset (Fin n) → Finset (Fin n)) (Fs : Finset (Finset (Fin n))) (e : ℕ)
    (T : Finset (Fin d)) (y : MvPolynomial (Fin n) K) (hy : y ∈ Ycap (K := K) R Fs e T) :
    ∃ a : Finset (Fin n) → K, y = ∑ F ∈ Fs, a F • xR (K := K) R F := by
  classical
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨F, ⟨hF, -⟩, rfl⟩ := hg
    refine ⟨fun G => if G = F then 1 else 0, ?_⟩
    simp [ite_smul, hF]
  | zero => exact ⟨0, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a, rfl⟩ := hp; obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul r p _ hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨r • a, by simp [Finset.smul_sum, smul_smul]⟩

theorem peel (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (v0 : Fin d → Fin n) (T : Finset (Fin d)) :
    ∀ (m : ℕ) (y : MvPolynomial (Fin n) K), y ∈ homogeneousSubmodule (Fin n) K m →
      m + T.card ≤ d → (∀ v : Fin d → Fin n, (∏ i ∈ T, X (v i)) * y ∈ Jth Fs c) → y ∈ Jth Fs c := by
  classical
  refine Finset.induction_on T ?_ ?_
  · intro m y _ _ h; simpa using h v0
  · intro j T' hj IH m y hy hm h
    rw [Finset.card_insert_eq_ite, if_neg hj] at hm
    apply IH m y hy (by omega)
    intro w
    have hzh : (∏ i ∈ T', X (w i)) * y ∈ homogeneousSubmodule (Fin n) K (m + T'.card) := by
      rw [mem_homogeneousSubmodule]
      have hp : (∏ i ∈ T', (X (w i) : MvPolynomial (Fin n) K)).IsHomogeneous (∑ i ∈ T', 1) :=
        IsHomogeneous.prod _ _ _ (fun i _ => isHomogeneous_X _ _)
      rw [Finset.sum_const, smul_eq_mul, mul_one] at hp
      rw [add_comm]; exact hp.mul ((mem_homogeneousSubmodule _ _).mp hy)
    refine pd_lin Fs c ord R hcard hli hord hsh hrev hpm _ (by omega) _ hzh (fun s => ?_)
    have := h (Function.update w j s)
    have hpc : ∏ i ∈ T', (X (Function.update w j s i) : MvPolynomial (Fin n) K) =
        ∏ i ∈ T', X (w i) :=
      Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
    rw [Finset.prod_insert hj, Function.update_self, hpc, mul_assoc] at this
    exact this

/-- Kill lemma (hypothesis `hkill` of `GF93AN.z_main`). -/
theorem kill (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (v0 : Fin d → Fin n) (e : ℕ) (he : e ≤ d) (T : Finset (Fin d)) (y : MvPolynomial (Fin n) K)
    (hy : y ∈ Ycap (K := K) R Fs e T)
    (h : ∀ v : Fin d → Fin n, (∏ i ∈ T, X (v i)) * y ∈ Jth Fs c) : y = 0 := by
  by_cases hT : T.card ≤ e
  · have hyJ := peel Fs c ord R hcard hli hord hsh hrev hpm v0 T (e - T.card) y
      (Ycap_hom R Fs e T hy) (by omega) h
    obtain ⟨a, rfl⟩ := Ycap_rep R Fs e T _ hy
    have := xR_indep Fs c ord R hcard hli hord hsh a hyJ
    exact Finset.sum_eq_zero fun F hF => by rw [this F hF, zero_smul]
  · have hb : Ycap (K := K) R Fs e T = ⊥ := by
      rw [Ycap, Submodule.span_eq_bot]
      rintro _ ⟨F, ⟨_, hc⟩, rfl⟩
      exact absurd hc (by omega)
    rw [hb, Submodule.mem_bot] at hy
    exact hy

end expansion


section frobenius
/-! A2b-i step F (session 15): Frobenius descent `u*u ∈ N ⇒ u ∈ J` over a field of characteristic 2
with a `K²`-linear projection `π0` onto the squares (abstract; `π0` on `Frac F₂[W]` is built separately). -/
variable {K : Type} [Field K] {n d : ℕ}

def bad (Fs : Finset (Finset (Fin n))) (γ : Fin n →₀ ℕ) : Prop := ∃ F ∈ Fs, γ.support ⊆ F

theorem ID_coeff (Fs : Finset (Finset (Fin n))) (f : MvPolynomial (Fin n) K) (hf : f ∈ ID (K := K) Fs)
    (γ : Fin n →₀ ℕ) (hγ : bad Fs γ) : coeff γ f = 0 := by
  classical
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, hα, rfl⟩ := hg
    rw [coeff_monomial]
    split_ifs with h
    · subst h; obtain ⟨F, hF, hs⟩ := hγ; exact absurd hs (hα F hF)
    · rfl
  | zero => simp
  | add p q _ _ hp hq => rw [coeff_add, hp, hq, add_zero]
  | smul a p _ hp => rw [coeff_smul, hp, smul_zero]

theorem ID_of_coeff (Fs : Finset (Finset (Fin n))) (f : MvPolynomial (Fin n) K)
    (h : ∀ γ, bad Fs γ → coeff γ f = 0) : f ∈ ID (K := K) Fs := by
  classical
  rw [f.as_sum]
  refine sum_mem fun γ hγ => ?_
  have hnb : ¬ bad Fs γ := fun hb => (mem_support_iff.mp hγ) (h γ hb)
  have e : monomial γ (coeff γ f) = coeff γ f • (monomial γ (1 : K)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, fun F hF hs => hnb ⟨F, hF, hs⟩, rfl⟩)

def EvE (γ : Fin n →₀ ℕ) : Prop := ∀ i, Even (γ i)

open Classical in
noncomputable def piP (π0 : K →+ K) (f : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K :=
  ∑ γ ∈ f.support.filter EvE, monomial γ (π0 (coeff γ f))

open Classical in
theorem coeff_piP (π0 : K →+ K) (f : MvPolynomial (Fin n) K) (γ : Fin n →₀ ℕ) :
    coeff γ (piP π0 f) = if EvE γ then π0 (coeff γ f) else 0 := by
  unfold piP
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h1 : EvE γ <;> by_cases h2 : coeff γ f = 0 <;> simp [h1, h2]

theorem piP_add (π0 : K →+ K) (p q : MvPolynomial (Fin n) K) :
    piP π0 (p + q) = piP π0 p + piP π0 q := by
  ext γ; simp only [coeff_piP, coeff_add, map_add]; split_ifs <;> simp

theorem piP_zero (π0 : K →+ K) : piP π0 (0 : MvPolynomial (Fin n) K) = 0 := by
  ext γ; simp [coeff_piP]

open Classical in
theorem piP_mono (π0 : K →+ K) (γ : Fin n →₀ ℕ) (c : K) :
    piP π0 (monomial γ c) = if EvE γ then monomial γ (π0 c) else 0 := by
  ext δ
  rw [coeff_piP]
  by_cases hd : γ = δ
  · subst hd; split_ifs <;> simp
  · split_ifs <;> simp [coeff_monomial, hd]

theorem evE_dbl (α β : Fin n →₀ ℕ) : EvE (α + α + β) ↔ EvE β := by
  unfold EvE
  simp only [Finsupp.coe_add, Pi.add_apply]
  exact forall_congr' fun i => by
    rw [Nat.even_add]
    exact ⟨fun h => h.mp ⟨α i, rfl⟩, fun h => ⟨fun _ => h, fun _ => ⟨α i, rfl⟩⟩⟩

theorem piP_mono3 (π0 : K →+ K) (hpsq : ∀ a b, π0 (a * a * b) = a * a * π0 b)
    (α β : Fin n →₀ ℕ) (a b : K) :
    piP π0 (monomial α a * monomial α a * monomial β b) =
      monomial α a * monomial α a * piP π0 (monomial β b) := by
  rw [monomial_mul, monomial_mul, piP_mono, piP_mono]
  by_cases hb : EvE β
  · rw [if_pos ((evE_dbl α β).mpr hb), if_pos hb, hpsq, monomial_mul]
  · rw [if_neg (fun h => hb ((evE_dbl α β).mp h)), if_neg hb, mul_zero]

theorem two_P (h2 : (2 : K) = 0) : (2 : MvPolynomial (Fin n) K) = 0 := by
  rw [← map_ofNat (C : K →+* MvPolynomial (Fin n) K) 2, h2, C_0]

theorem piP_sq_mul (π0 : K →+ K) (hpsq : ∀ a b, π0 (a * a * b) = a * a * π0 b) (h2 : (2 : K) = 0)
    (f g : MvPolynomial (Fin n) K) : piP π0 (f * f * g) = f * f * piP π0 g := by
  have e : ∀ p q : MvPolynomial (Fin n) K, (p + q) * (p + q) = p * p + q * q := fun p q => by
    have : (p + q) * (p + q) = p * p + q * q + 2 * (p * q) := by ring
    rw [this, two_P h2, zero_mul, add_zero]
  induction g using MvPolynomial.induction_on' with
  | monomial β b =>
    induction f using MvPolynomial.induction_on' with
    | monomial α a => exact piP_mono3 π0 hpsq α β a b
    | add p q hp hq => rw [e, add_mul, piP_add, hp, hq, add_mul]
  | add g1 g2 h1 h1' => rw [mul_add, piP_add, h1, h1', piP_add, mul_add]

theorem piP_one (π0 : K →+ K) (hp1 : π0 1 = 1) : piP π0 (1 : MvPolynomial (Fin n) K) = 1 := by
  have e : (1 : MvPolynomial (Fin n) K) = monomial 0 1 := by rw [monomial_zero', C_1]
  rw [e, piP_mono, if_pos (show EvE (0 : Fin n →₀ ℕ) from fun i => by simp), hp1]

theorem piP_ID (Fs : Finset (Finset (Fin n))) (π0 : K →+ K) (f : MvPolynomial (Fin n) K)
    (hf : f ∈ ID (K := K) Fs) : piP π0 f ∈ ID (K := K) Fs := by
  apply ID_of_coeff
  intro γ hγ
  rw [coeff_piP, ID_coeff Fs f hf γ hγ, map_zero, ite_self]

theorem sq_sum2 (h2 : (2 : K) = 0) {ι : Type} (s : Finset ι) (t : ι → MvPolynomial (Fin n) K) :
    (∑ i ∈ s, t i) * (∑ i ∈ s, t i) = ∑ i ∈ s, t i * t i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha IH =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← IH]
    have : (t a + ∑ i ∈ s, t i) * (t a + ∑ i ∈ s, t i) =
        t a * t a + (∑ i ∈ s, t i) * (∑ i ∈ s, t i) + 2 * (t a * ∑ i ∈ s, t i) := by ring
    rw [this, two_P h2, zero_mul, add_zero]

noncomputable def half (γ : Fin n →₀ ℕ) : Fin n →₀ ℕ := γ.mapRange (fun k => k / 2) (by simp)

theorem half_add (γ : Fin n →₀ ℕ) (h : EvE γ) : half γ + half γ = γ := by
  ext i
  simp only [half, Finsupp.coe_add, Pi.add_apply, Finsupp.mapRange_apply]
  obtain ⟨r, hr⟩ := h i
  rw [hr]; omega

theorem piP_isSq (π0 : K →+ K) (hpim : ∀ b, ∃ a, π0 b = a * a) (h2 : (2 : K) = 0)
    (f : MvPolynomial (Fin n) K) : ∃ r, piP π0 f = r * r := by
  classical
  choose sq hsq using hpim
  refine ⟨∑ γ ∈ f.support.filter EvE, monomial (half γ) (sq (coeff γ f)), ?_⟩
  rw [sq_sum2 h2]
  unfold piP
  refine Finset.sum_congr (by congr) fun γ hγ => ?_
  rw [monomial_mul, half_add γ (Finset.mem_filter.mp hγ).2, ← hsq]

theorem Nth_rep (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) (p : MvPolynomial (Fin n) K)
    (hp : p ∈ Nth Fs c) : ∃ s ∈ ID (K := K) Fs, ∃ w : Fin d → MvPolynomial (Fin n) K,
      p = s + ∑ i, theta c i * theta c i * w i := by
  classical
  induction hp using Submodule.span_induction with
  | mem g hg =>
    rcases hg with hg | ⟨μ, i, rfl⟩
    · exact ⟨g, Submodule.subset_span hg, 0, by simp⟩
    · refine ⟨0, zero_mem _, fun j => if j = i then monomial μ 1 else 0, ?_⟩
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add]
      ring
  | zero => exact ⟨0, zero_mem _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s1, hs1, w1, rfl⟩ := hx
    obtain ⟨s2, hs2, w2, rfl⟩ := hy
    refine ⟨s1 + s2, add_mem hs1 hs2, w1 + w2, ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  | smul a x _ hx =>
    obtain ⟨s, hs, w, rfl⟩ := hx
    refine ⟨a • s, Submodule.smul_mem _ a hs, a • w, ?_⟩
    simp only [Pi.smul_apply, smul_add, Finset.smul_sum, mul_smul_comm]

theorem coeff_dbl_sq (h2 : (2 : K) = 0) (z : MvPolynomial (Fin n) K) (α : Fin n →₀ ℕ) :
    coeff (α + α) (z * z) = coeff α z * coeff α z := by
  classical
  have hz : z * z = ∑ γ ∈ z.support, monomial (γ + γ) (coeff γ z * coeff γ z) := by
    conv_lhs => rw [z.as_sum]
    rw [sq_sum2 h2]
    exact Finset.sum_congr rfl fun γ _ => by rw [monomial_mul]
  rw [hz, coeff_sum]
  simp only [coeff_monomial]
  have hinj : ∀ γ, (γ + γ = α + α) ↔ (γ = α) := fun γ => by
    constructor
    · intro h; ext i; have := congrArg (fun f => f i) h; simp only [Finsupp.coe_add, Pi.add_apply] at this; omega
    · rintro rfl; rfl
  simp only [hinj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_support_iff, not_not] at h
    rw [h, zero_mul]

theorem ID_sqrt (Fs : Finset (Finset (Fin n))) (h2 : (2 : K) = 0) (z : MvPolynomial (Fin n) K)
    (hz : z * z ∈ ID (K := K) Fs) : z ∈ ID (K := K) Fs := by
  apply ID_of_coeff
  intro γ hγ
  have hb : bad Fs (γ + γ) := by
    obtain ⟨F, hF, hs⟩ := hγ
    refine ⟨F, hF, fun i hi => hs ?_⟩
    rw [Finsupp.mem_support_iff] at hi ⊢
    simp only [Finsupp.coe_add, Pi.add_apply] at hi
    omega
  have := ID_coeff Fs _ hz _ hb
  rw [coeff_dbl_sq h2] at this
  exact mul_self_eq_zero.mp this

/-- Step F. -/
theorem frob_descent (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K) (π0 : K →+ K)
    (hp1 : π0 1 = 1) (hpsq : ∀ a b, π0 (a * a * b) = a * a * π0 b)
    (hpim : ∀ b, ∃ a, π0 b = a * a) (h2 : (2 : K) = 0)
    (u : MvPolynomial (Fin n) K) (hu : u * u ∈ Nth Fs c) : u ∈ Jth Fs c := by
  classical
  obtain ⟨s, hs, w, hw⟩ := Nth_rep Fs c _ hu
  choose r hr using fun i => piP_isSq π0 hpim h2 (w i)
  let πh : MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) K :=
    { toFun := piP π0, map_zero' := piP_zero π0, map_add' := piP_add π0 }
  have hpu : piP π0 (u * u) = u * u := by
    have := piP_sq_mul π0 hpsq h2 u 1
    rwa [mul_one, piP_one π0 hp1, mul_one] at this
  have h1 : u * u = piP π0 s + (∑ i, theta c i * r i) * (∑ i, theta c i * r i) := by
    rw [← hpu]
    conv_lhs => rw [hw]
    rw [sq_sum2 h2]
    have : piP π0 (s + ∑ i, theta c i * theta c i * w i) = πh (s + ∑ i, theta c i * theta c i * w i) := rfl
    rw [this, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show piP π0 (theta c i * theta c i * w i) = _
    rw [piP_sq_mul π0 hpsq h2, hr i]; ring
  set S := ∑ i, theta c i * r i with hS
  have hz : (u + S) * (u + S) ∈ ID (K := K) Fs := by
    have e : (u + S) * (u + S) = piP π0 s + 2 * (S * S) + 2 * (u * S) := by
      have : (u + S) * (u + S) = u * u + S * S + 2 * (u * S) := by ring
      rw [this, h1]; ring
    rw [e, two_P h2, zero_mul, zero_mul, add_zero, add_zero]
    exact piP_ID Fs π0 s hs
  have hzJ := ID_le Fs c (ID_sqrt Fs h2 _ hz)
  have hSJ : S ∈ Jth Fs c := sum_mem fun i _ => by
    rw [mul_comm]; exact ideal_mul_mem _ (Jth_X Fs c) _ _ (theta_mem Fs c i)
  have e2 : u = (u + S) - S := by ring
  rw [e2]
  exact sub_mem hzJ hSJ

end frobenius

section aniso
/-! A2b assembled abstractly (session 16): anisotropy (E + L + Z + F) and weak Lefschetz. -/
variable {K : Type} [Field K] {n d : ℕ}

theorem Dop_monomial_one (Dop : MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) K)
    (hDmul : ∀ f g, Dop (f * g) = f * Dop g + g * Dop f) (hX : ∀ v, Dop (X v) = 0)
    (h1 : Dop 1 = 0) (α : Fin n →₀ ℕ) : Dop (monomial α 1) = 0 := by
  have hpow : ∀ v (k : ℕ), Dop (X v ^ k) = 0 := by
    intro v k
    induction k with
    | zero => rw [pow_zero]; exact h1
    | succ k ihk => rw [pow_succ, hDmul, ihk, hX]; ring
  refine Finsupp.induction α ?_ ?_
  · rw [monomial_zero', C_1]; exact h1
  · intro v e f _ _ ih
    rw [monomial_single_add, hDmul, ih, hpow]; ring

theorem Dop_pres_span (S : Set (MvPolynomial (Fin n) K))
    (hX : ∀ p ∈ Submodule.span K S, ∀ v : Fin n, X v * p ∈ Submodule.span K S)
    (Dop : MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) K)
    (hDmul : ∀ f g, Dop (f * g) = f * Dop g + g * Dop f)
    (hS : ∀ g ∈ S, Dop g ∈ Submodule.span K S) :
    ∀ p ∈ Submodule.span K S, Dop p ∈ Submodule.span K S := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem g hg => exact hS g hg
  | zero => rw [map_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [map_add]; exact add_mem hp hq
  | smul a p hp0 hp =>
    rw [smul_eq_C_mul, hDmul]
    exact add_mem (ideal_mul_mem _ hX _ _ hp) (by rw [mul_comm]; exact ideal_mul_mem _ hX _ _ hp0)

/-- A2b-i anisotropy: `2k ≤ d`, `u` homogeneous of degree `k`, `u² ∈ J` ⇒ `u ∈ J`. -/
theorem aniso (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (v0 : Fin d → Fin n)
    (π0 : K →+ K) (hp1 : π0 1 = 1) (hpsq : ∀ a b, π0 (a * a * b) = a * a * π0 b)
    (hpim : ∀ b, ∃ a, π0 b = a * a) (h2 : (2 : K) = 0)
    (Dop : Fin d → Fin n → MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) K)
    (hDmul : ∀ i v f g, Dop i v (f * g) = f * Dop i v g + g * Dop i v f)
    (hDsq : ∀ i v f, Dop i v (f * f) = 0)
    (hDθ : ∀ i v j, Dop i v (theta c j) = if i = j then X v else 0)
    (hDN : ∀ i v p, p ∈ Nth Fs c → Dop i v p ∈ Nth Fs c)
    (k : ℕ) (hk : 2 * k ≤ d) (u : MvPolynomial (Fin n) K)
    (hu : u ∈ homogeneousSubmodule (Fin n) K k) (huu : u * u ∈ Jth Fs c) : u ∈ Jth Fs c := by
  have hhom : u * u ∈ homogeneousSubmodule (Fin n) K (2 * k) := by
    have := (mem_homogeneousSubmodule _ _).mp hu
    rw [mem_homogeneousSubmodule, two_mul]; exact this.mul this
  obtain ⟨r, hr, y, hy, hsum⟩ := expand Fs c ord R hcard hli hord hsh (2 * k) (u * u) hhom
  have hN : u * u ∈ (Nth Fs c).toAddSubgroup :=
    GF93AN.z_sq_mem (Jth Fs c).toAddSubgroup (Nth Fs c).toAddSubgroup
      (fun q p hp => ideal_mul_mem _ (Jth_X Fs c) q p hp) (fun p hp => Nth_le Fs c hp)
      (theta c) (fun i => theta_mem Fs c i) X Dop hDmul hDsq hDθ hDN u r huu hr y hsum
      (fun T hT => kill Fs c ord R hcard hli hord hsh hrev hpm v0 (2 * k) hk T (y T) (hy T) hT)
  exact frob_descent Fs c π0 hp1 hpsq hpim h2 u hN

/-- A2b: weak Lefschetz below `m` (with `2k < d` for `k < m`) from anisotropy + duality. -/
theorem weakLef_of_ops (Fs : Finset (Finset (Fin n))) (c : Fin d → Fin n → K)
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hli : ∀ F ∈ Fs, LinearIndependent K (fun j : F => fun i : Fin d => c i j))
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (v0 : Fin d → Fin n)
    (π0 : K →+ K) (hp1 : π0 1 = 1) (hpsq : ∀ a b, π0 (a * a * b) = a * a * π0 b)
    (hpim : ∀ b, ∃ a, π0 b = a * a) (h2 : (2 : K) = 0)
    (Dop : Fin d → Fin n → MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) K)
    (hDmul : ∀ i v f g, Dop i v (f * g) = f * Dop i v g + g * Dop i v f)
    (hDsq : ∀ i v f, Dop i v (f * f) = 0)
    (hDθ : ∀ i v j, Dop i v (theta c j) = if i = j then X v else 0)
    (hDN : ∀ i v p, p ∈ Nth Fs c → Dop i v p ∈ Nth Fs c)
    (ℓ : MvPolynomial (Fin n) K) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    (Dv : Fin n → MvPolynomial (Fin n) K → MvPolynomial (Fin n) K)
    (hDvmul : ∀ v f g, Dv v (f * g) = f * Dv v g + g * Dv v f)
    (hDvJ : ∀ v p, p ∈ Jth Fs c → Dv v p ∈ Jth Fs c) (hDl : ∀ v, Dv v ℓ = X v)
    (m : ℕ) (hm : ∀ k < m, 2 * k < d) : WeakLef (Jth Fs c) m :=
  GF93DR.wl_of_aniso (Jth Fs c) (fun q p hp => ideal_mul_mem _ (Jth_X Fs c) q p hp) m ℓ hℓ hℓ0
    Dv hDvmul hDvJ hDl
    (fun k hk q hq hX => pd_lin Fs c ord R hcard hli hord hsh hrev hpm (2 * k) (hm k hk) q hq hX)
    (fun k hk p hp hpp => aniso Fs c ord R hcard hli hord hsh hrev hpm v0 π0 hp1 hpsq hpim h2
      Dop hDmul hDsq hDθ hDN k (le_of_lt (hm k hk)) p hp hpp)

end aniso

end GF93LG

namespace GF93GN
/-! A2b-G (session 16): the generic char-2 field `K = Frac(F₂[a_{i,v}, b_v])` supplies every
hypothesis of `GF93LG.weakLef_of_ops`. -/
open MvPolynomial GF93DR GF93LG

abbrev Wd (d n : ℕ) := (Fin d × Fin n) ⊕ Fin n

noncomputable def cg (d n : ℕ) : Fin d → Fin n → KF (Wd d n) :=
  fun i v => algebraMap (MvPolynomial (Wd d n) (ZMod 2)) (KF (Wd d n)) (X (Sum.inl (i, v)))

noncomputable def bg (d n : ℕ) (v : Fin n) : KF (Wd d n) :=
  algebraMap (MvPolynomial (Wd d n) (ZMod 2)) (KF (Wd d n)) (X (Sum.inr v))

noncomputable def ellg (d n : ℕ) : MvPolynomial (Fin n) (KF (Wd d n)) := ∑ v, C (bg d n v) * X v

theorem Dx_zero' {d n : ℕ} (w : Wd d n) : Dx (σ := Fin n) w 0 = 0 := by simp [Dx]

theorem Dx_one' {d n : ℕ} (w : Wd d n) : Dx (σ := Fin n) w 1 = 0 := by
  rw [← C_1, Dx_C, D_one, map_zero]

noncomputable def DxH {d n : ℕ} (w : Wd d n) :
    MvPolynomial (Fin n) (KF (Wd d n)) →+ MvPolynomial (Fin n) (KF (Wd d n)) where
  toFun := Dx w
  map_zero' := Dx_zero' w
  map_add' := Dx_add w

theorem Dx_lin {d n : ℕ} (w : Wd d n) (a : Fin n → KF (Wd d n)) :
    Dx w (∑ v, C (a v) * X v) = ∑ v, C (D w (a v)) * X v := by
  have h := map_sum (DxH (n := n) w) (fun v => C (a v) * X v) Finset.univ
  change Dx w _ = ∑ v, Dx w (C (a v) * X v) at h
  rw [h]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Dx_mul, Dx_X, Dx_C]; ring

theorem two_eq_zero' {d n : ℕ} : (2 : KF (Wd d n)) = 0 := two_eq_zero

theorem hDθ_g {d n : ℕ} (i : Fin d) (v : Fin n) (j : Fin d) :
    DxH (Sum.inl (i, v)) (theta (cg d n) j) = if i = j then X v else 0 := by
  change Dx _ (∑ w, C (cg d n j w) * X w) = _
  rw [Dx_lin]
  simp only [cg, D_X, Sum.inl.injEq, Prod.mk.injEq]
  by_cases hij : i = j
  · subst hij
    simp only [true_and]
    rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg (fun h => hij h.1.symm), map_zero, zero_mul]

theorem Dx_inr_theta {d n : ℕ} (v : Fin n) (j : Fin d) :
    Dx (Sum.inr v) (theta (cg d n) j) = 0 := by
  change Dx _ (∑ w, C (cg d n j w) * X w) = _
  rw [Dx_lin]
  simp [cg, D_X]

theorem hDl_g {d n : ℕ} (v : Fin n) : Dx (Sum.inr v) (ellg d n) = X v := by
  unfold ellg
  rw [Dx_lin]
  simp only [bg, D_X, Sum.inr.injEq]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem Dx_mon {d n : ℕ} (w : Wd d n) (α : Fin n →₀ ℕ) :
    Dx (σ := Fin n) w (monomial α 1) = 0 :=
  Dop_monomial_one (DxH w) (Dx_mul w) (Dx_X w) (Dx_one' w) α

theorem hDN_g {d n : ℕ} (Fs : Finset (Finset (Fin n))) (w : Wd d n) :
    ∀ p ∈ Nth Fs (cg d n), DxH w p ∈ Nth Fs (cg d n) := by
  refine Dop_pres_span _ (Nth_X Fs (cg d n)) (DxH w) (Dx_mul w) ?_
  rintro g (⟨α, -, rfl⟩ | ⟨μ, i, rfl⟩)
  · change Dx w _ ∈ _; rw [Dx_mon]; exact zero_mem _
  · change Dx w _ ∈ _; rw [Dx_mul, Dx_sq, Dx_mon]; simp

theorem hDJ_g {d n : ℕ} (Fs : Finset (Finset (Fin n))) (v : Fin n) :
    ∀ p ∈ Jth Fs (cg d n), Dx (Sum.inr v) p ∈ Jth Fs (cg d n) := by
  refine Dop_pres_span _ (Jth_X Fs (cg d n)) (DxH (Sum.inr v)) (Dx_mul _) ?_
  rintro g (⟨α, -, rfl⟩ | ⟨μ, i, rfl⟩)
  · change Dx _ _ ∈ _; rw [Dx_mon]; exact zero_mem _
  · change Dx _ _ ∈ _; rw [Dx_mul, Dx_inr_theta, Dx_mon]; simp

theorem hli_g {d n : ℕ} (Fs : Finset (Finset (Fin n))) (hcard : ∀ F ∈ Fs, F.card = d) :
    ∀ F ∈ Fs, LinearIndependent (KF (Wd d n)) (fun j : F => fun i : Fin d => cg d n i j) := by
  intro F hF
  let e : F ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hcard F hF])
  let f : Fin d × Fin d → Wd d n := fun p => Sum.inl (p.1, (e.symm p.2 : Fin n))
  have hf : Function.Injective f := by
    intro p q h
    simp only [f, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.1 (e.symm.injective (Subtype.ext h.2))
  let φ : MvPolynomial (Fin d × Fin d) (ZMod 2) →+* KF (Wd d n) :=
    (algebraMap (MvPolynomial (Wd d n) (ZMod 2)) (KF (Wd d n))).comp (rename f).toRingHom
  have hφ : Function.Injective φ :=
    (IsFractionRing.injective (MvPolynomial (Wd d n) (ZMod 2)) (KF (Wd d n))).comp
      (rename_injective f hf)
  let A : Matrix (Fin d) (Fin d) (KF (Wd d n)) := (Matrix.mvPolynomialX (Fin d) (Fin d) (ZMod 2)).map φ
  have hA : A.det ≠ 0 := by
    rw [show A.det = φ (Matrix.mvPolynomialX (Fin d) (Fin d) (ZMod 2)).det from
      (RingHom.map_det φ _).symm]
    intro h0
    exact Matrix.det_mvPolynomialX_ne_zero (Fin d) (ZMod 2) (hφ (h0.trans (map_zero φ).symm))
  have hcol := Matrix.linearIndependent_cols_of_det_ne_zero hA
  have : (fun j : F => fun i : Fin d => cg d n i j) = A.col ∘ e := by
    funext j i
    show cg d n i j = φ (Matrix.mvPolynomialX (Fin d) (Fin d) (ZMod 2) i (e j))
    simp [φ, f, cg, Matrix.mvPolynomialX, rename_X]
  rw [this]
  exact hcol.comp e e.injective

theorem pi0_g {d n : ℕ} : ∃ π0 : KF (Wd d n) →+ KF (Wd d n), π0 1 = 1 ∧
    (∀ a b, π0 (a * a * b) = a * a * π0 b) ∧ ∀ b, ∃ a, π0 b = a * a := by
  have : CharP (KF (Wd d n)) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero two_eq_zero'
  exact GF93PI.exists_pi0 _

/-- A2b for the generic char-2 l.s.o.p. -/
theorem weakLef_g {d n : ℕ} (Fs : Finset (Finset (Fin n)))
    (ord : Finset (Fin n) → ℕ) (R : Finset (Fin n) → Finset (Fin n))
    (hcard : ∀ F ∈ Fs, F.card = d)
    (hord : Set.InjOn ord Fs)
    (hsh : ∀ F ∈ Fs, ∀ G ⊆ F, (R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F' ≤ ord F))
    (hrev : ∀ F ∈ Fs, ∀ G ⊆ F, (F \ R F ⊆ G ↔ ∀ F' ∈ Fs, G ⊆ F' → ord F ≤ ord F'))
    (hpm : ∀ G : Finset (Fin n), G.card + 1 = d → ∀ F1 ∈ Fs, ∀ F2 ∈ Fs, ∀ F3 ∈ Fs,
      G ⊆ F1 → G ⊆ F2 → G ⊆ F3 → F1 = F2 ∨ F1 = F3 ∨ F2 = F3)
    (v0 : Fin d → Fin n) (v1 : Fin n) (m : ℕ) (hm : ∀ k < m, 2 * k < d) :
    WeakLef (Jth Fs (cg d n)) m := by
  obtain ⟨π0, hp1, hpsq, hpim⟩ := pi0_g (d := d) (n := n)
  have hℓ0 : ellg d n ≠ 0 := by
    intro h
    have := hDl_g (d := d) v1
    rw [h, Dx_zero'] at this
    exact X_ne_zero v1 this.symm
  refine weakLef_of_ops Fs (cg d n) ord R hcard (hli_g Fs hcard) hord hsh hrev hpm v0 π0 hp1 hpsq
    hpim two_eq_zero' (fun i v => DxH (Sum.inl (i, v))) (fun i v => Dx_mul _) (fun i v => Dx_sq _)
    hDθ_g (fun i v => hDN_g Fs _) (ellg d n) ?_ hℓ0 (fun v => Dx (Sum.inr v)) (fun v => Dx_mul _)
    (hDJ_g Fs) hDl_g m hm
  exact IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)

end GF93GN


-- ==== from f9336347.lean
set_option autoImplicit false
open scoped BigOperators

namespace GF93

open Grunbaum2003

/-- In an M-sequence, a zero entry forces every later entry (up to m) to be zero. -/
theorem mseq_zero_prop (m : ℕ) (g : ℕ → ℕ) (hg : IsMSequence m g) (k : ℕ)
    (hk0 : 0 < k) (hkm : k ≤ m) (hprev : g (k - 1) = 0) : g k = 0 := by
  rcases hg.2 k hk0 hkm with h | ⟨i, a, hi0, hik, hai, _hmono, _hsum, hbd⟩
  · exact h
  · exfalso
    have hpos : 0 < Nat.choose (a i - 1) (i - 1) := Nat.choose_pos (by omega)
    have hle : Nat.choose (a i - 1) (i - 1) ≤
        ∑ r ∈ Finset.Icc i k, Nat.choose (a r - 1) (r - 1) :=
      Finset.single_le_sum (f := fun r => Nat.choose (a r - 1) (r - 1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_Icc.mpr ⟨le_rfl, hik⟩)
    omega

theorem mseq_zero_from (m : ℕ) (g : ℕ → ℕ) (hg : IsMSequence m g) (s : ℕ) (hs : 0 < s)
    (hz : g s = 0) : ∀ k, s ≤ k → k ≤ m → g k = 0 := by
  intro k hsk hkm
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hsk with h | h
    · rw [← h]; exact hz
    · exact mseq_zero_prop m g hg (n + 1) (by omega) hkm (by simpa using ih (by omega) (by omega))

theorem gM_1_2 (n : ℕ) : gTheoremMatrix (n + 4) 1 2 = ((n + 4 : ℕ) : ℤ) := by
  unfold gTheoremMatrix
  have h1 : n + 4 + 1 - 1 = (n + 3) + 1 := by omega
  have h2 : n + 4 + 1 - 2 = n + 3 := by omega
  rw [h1, h2, Nat.choose_succ_self_right, Nat.choose_eq_zero_of_lt (by omega : 1 < n + 3)]
  push_cast; ring

/-- Glue: the leaf follows from the g-theorem necessity (Stanley 1980) for `P`. -/
theorem parent_of_gthm (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hV_gt : d + 1 < faceCount P 0)
    (hNonStacked : ¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
      (Nat.choose (d + 1) j.succ.val : ℤ) +
        ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val)
    (hUpper :
      (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
      (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
      (∀ (g : ℕ → ℕ) (k : ℕ), k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
          (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
      (∀ (k : ℕ), k ≤ d →
        gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ)))
    (g : ℕ → ℕ) (hg : IsMSequence (d / 2) g)
    (hrep : ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      g 0 = 1 ∧
      g 1 = faceCount P 0 - (d + 1) ∧
      0 < g 1 ∧
      0 < g 2 ∧
      (g 2 : ℤ) = (faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) - (d : ℤ) * (g 1 : ℤ) ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  obtain ⟨hU1, _hU2, hU3, hU4⟩ := hUpper
  have hm2 : 2 ≤ d / 2 := by omega
  have g0 : g 0 = 1 := hg.1
  -- j = 0
  have e0 : (faceCount P 0 : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i 1 := hrep ⟨0, by omega⟩
  rw [hU3 g 1 (by omega)] at e0
  simp only [Finset.sum_range_one, zero_add] at e0
  rw [hU4 1 (by omega), g0] at e0
  simp only [Nat.choose_one_right, Nat.cast_one, one_mul] at e0
  have g1eq : g 1 = faceCount P 0 - (d + 1) := by
    have : (faceCount P 0 : ℤ) = (d : ℤ) + 1 + (g 1 : ℤ) := by rw [e0]; push_cast; ring
    omega
  -- j = 1
  have e1 : (faceCount P 1 : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i 2 := hrep ⟨1, by omega⟩
  rw [hU3 g 2 hm2] at e1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at e1
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 4 := ⟨d - 4, by omega⟩
  rw [hU4 2 (by omega), g0, gM_1_2 n] at e1
  have g2eq : (g 2 : ℤ) = (faceCount P 1 : ℤ) - (Nat.choose (n + 4 + 1) 2 : ℤ) -
      ((n + 4 : ℕ) : ℤ) * (g 1 : ℤ) := by
    rw [e1]; push_cast; ring
  have g2pos : 0 < g 2 := by
    by_contra hcon
    have hz : g 2 = 0 := by omega
    apply hNonStacked
    intro j
    rw [hrep j]
    have hsub : Finset.range 2 ⊆ Finset.range ((n + 4) / 2 + 1) :=
      Finset.range_subset_range.mpr (by omega)
    rw [← Finset.sum_subset hsub (fun i hi hni => by
      have hi' : i < (n + 4) / 2 + 1 := Finset.mem_range.mp hi
      have hni' : ¬ i < 2 := fun h => hni (Finset.mem_range.mpr h)
      rw [mseq_zero_from _ g hg 2 (by omega) hz i (by omega) (by omega)]
      simp)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hU4 _ (by have := j.isLt; simp only [Fin.val_succ]; omega), g0, g1eq]
    push_cast; ring
  exact ⟨g, hg, g0, g1eq, by omega, g2pos, by push_cast at g2eq ⊢; linarith, hrep⟩

end GF93


namespace GF93FIN
open Finset Grunbaum2003

/-- C1 (Stanley 1980): the g-vector of a simplicial `d`-polytope is an M-sequence. -/
theorem gthm (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧ ∀ j : Fin d, (faceCount P j.val : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  obtain ⟨n, Fs, ord, R, hn, ⟨hcard, _, hord, hsh, hrev⟩, hne, _, hsym, hf⟩ :=
    GF93BR.polytope_shelled d hd P hP
  have hpm := GF93LG.pm_of_shell Fs ord R hcard hord hsh hrev
  have hW := GF93GN.weakLef_g Fs ord R hcard hord hsh hrev hpm (fun _ => ⟨0, hn⟩) ⟨0, hn⟩
    (d / 2) (fun k hk => by omega)
  obtain ⟨hmono, hL⟩ := GF93LG.lefschetzHilbertF_of_shell Fs (GF93GN.cg d n) ord R hcard
    (GF93GN.hli_g Fs hcard) hord hsh hne (d / 2) hW
  refine ⟨_, GF93S.mseq_of_lefschetzHilbertF _ _ hL, fun j => ?_⟩
  have hk : j.succ.val ≤ d := by have := j.isLt; simp only [Fin.val_succ]; omega
  have e := GF93DS.ds_alg d (fun i => ((Fs.filter (fun F => (R F).card = i)).card : ℤ))
    (fun i hi => by exact_mod_cast hsym i hi) j.succ.val hk
  rw [hf j, e]
  apply sum_congr rfl
  intro i hi
  congr 1
  simp only [GF93DS.gOf]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · have hm := hmono (i - 1) (by simp only [mem_range] at hi; omega)
    rw [Nat.sub_add_cancel hi0] at hm
    rw [if_neg hi0.ne', if_neg hi0.ne', Nat.cast_sub hm]

end GF93FIN

open Grunbaum2003 in
theorem solution (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) (hV_gt : d + 1 < faceCount P 0)
    (hNonStacked : ¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
      (Nat.choose (d + 1) j.succ.val : ℤ) +
        ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val)
    (hUpper :
      (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
      (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
      (∀ (g : ℕ → ℕ) (k : ℕ), k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
          (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
      (∀ (k : ℕ), k ≤ d →
        gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ))) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      g 0 = 1 ∧
      g 1 = faceCount P 0 - (d + 1) ∧
      0 < g 1 ∧
      0 < g 2 ∧
      (g 2 : ℤ) = (faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) - (d : ℤ) * (g 1 : ℤ) ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  obtain ⟨g, hg, hrep⟩ := GF93FIN.gthm d (by omega) P hP
  exact GF93.parent_of_gthm d hd P hV_gt hNonStacked hUpper g hg hrep
