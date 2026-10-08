-- Prove2me | solution 1 for MathieuM23.triple_mem_sigmaC
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T10:20:48.064328+00:00
-- url     : https://prove2.me/submissions/800d81cc-18f4-4139-b6ba-9498b41c2250

import Definitions.Def_MathieuM23_Nielsen
import Mathlib

/-!
Reusable pieces: the (shortened) binary Golay code `C ⊂ F₂^23` that is invariant under `M23`
is described by 11 parity checks `hTab`.  A 7-subset `S` of `Fin 23` is a heptad (block of the
Steiner system S(4,7,23)) iff `Good S`: `|S| = 7` and all 11 parities vanish.
`Good` is preserved by every element of `M23` (`good_of_mem_M23`), and `g₃ = (g₁ g₂)⁻¹`.
-/

open MathieuM23

set_option maxRecDepth 100000

/-- The 11 parity checks (rows indexed by `j`, columns by points `0..22`). -/
def hTab : List (List ℕ) := [
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1],
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1],
  [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0]]

/-- Matrix expressing the checks composed with `g₁` in terms of the checks. -/
def a1Tab : List (List ℕ) := [
  [0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0],
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0],
  [0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0],
  [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1]]

/-- Matrix expressing the checks composed with `g₂` in terms of the checks. -/
def a2Tab : List (List ℕ) := [
  [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0],
  [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
  [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
  [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0],
  [0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1],
  [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0],
  [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]]

def hF (j : Fin 11) (i : Fin 23) : ZMod 2 := (((hTab.getD j.val []).getD i.val 0 : ℕ) : ZMod 2)
def a1F (j j' : Fin 11) : ZMod 2 := (((a1Tab.getD j.val []).getD j'.val 0 : ℕ) : ZMod 2)
def a2F (j j' : Fin 11) : ZMod 2 := (((a2Tab.getD j.val []).getD j'.val 0 : ℕ) : ZMod 2)

/-- `S` is a heptad of the Steiner system S(4,7,23). -/
def Good (S : Finset (Fin 23)) : Prop := S.card = 7 ∧ ∀ j, ∑ i ∈ S, hF j i = 0

/-- `p` maps heptads to heptads. -/
def PresG (p : Equiv.Perm (Fin 23)) : Prop := ∀ S : Finset (Fin 23), Good S → Good (S.image p)

lemma presG_one : PresG 1 := by
  intro S hS; simpa using hS

lemma presG_mul {p q : Equiv.Perm (Fin 23)} (hp : PresG p) (hq : PresG q) : PresG (p * q) := by
  intro S hS
  have := hp _ (hq S hS)
  rw [Finset.image_image] at this
  simpa [Equiv.Perm.coe_mul] using this

lemma presG_pow {p : Equiv.Perm (Fin 23)} (hp : PresG p) (n : ℕ) : PresG (p ^ n) := by
  induction n with
  | zero => simpa using presG_one
  | succ n ih => rw [pow_succ]; exact presG_mul ih hp

lemma presG_inv {p : Equiv.Perm (Fin 23)} (hp : PresG p) : PresG p⁻¹ := by
  have h : p⁻¹ = p ^ (orderOf p - 1) := by
    have hpos : 0 < orderOf p := orderOf_pos p
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [h]; exact presG_pow hp _

lemma presG_of_cert {p : Equiv.Perm (Fin 23)} (A : Fin 11 → Fin 11 → ZMod 2)
    (hA : ∀ j i, hF j (p i) = ∑ j', A j j' * hF j' i) : PresG p := by
  intro S ⟨hc, hz⟩
  refine ⟨by rw [Finset.card_image_of_injective _ p.injective, hc], fun j => ?_⟩
  rw [Finset.sum_image (fun x _ y _ h => p.injective h)]
  simp_rw [hA j]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hz, mul_zero, Finset.sum_const_zero]

lemma presG_g₁ : PresG g₁ :=
  presG_of_cert a1F (by unfold hF a1F; decide +kernel)

lemma presG_g₂ : PresG g₂ :=
  presG_of_cert a2F (by unfold hF a2F; decide +kernel)

/-- Every element of `M23` maps heptads to heptads. -/
lemma good_of_mem_M23 {p : Equiv.Perm (Fin 23)} (hp : p ∈ M23) : PresG p := by
  unfold M23 at hp
  induction hp using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact presG_g₁
    · exact presG_g₂
  | one => exact presG_one
  | mul x y _ _ hx hy => exact presG_mul hx hy
  | inv x _ hx => exact presG_inv hx

lemma prod_eq_one : g₁ * g₂ * g₃ = 1 := by decide +kernel

lemma g₃_eq : g₃ = (g₁ * g₂)⁻¹ := eq_inv_of_mul_eq_one_right prod_eq_one

/-- `g₃ = (g₁ * g₂)⁻¹ ∈ M23`. -/
lemma g₃_mem_M23 : g₃ ∈ M23 := by
  rw [g₃_eq]
  exact M23.inv_mem (M23.mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)))

/-- The heptad `{0,1,2,3,4,10,16}`. -/
def S0 : Finset (Fin 23) := {(0 : Fin 23), (1 : Fin 23), (2 : Fin 23), (3 : Fin 23), (4 : Fin 23), (10 : Fin 23), (16 : Fin 23)}

lemma S0_good : Good S0 := by unfold Good S0 hF; decide +kernel

/-- Index `i` with `(g₂ ^ i) 0 = x`. -/
def idx (x : Fin 23) : ℕ := ((List.range 23).find? (fun i => (g₂ ^ i) 0 == x)).getD 0

lemma idx_spec : ∀ x : Fin 23, (g₂ ^ idx x) 0 = x := by
  unfold idx; decide +kernel

lemma no_candidate : ∀ a : Fin 23, ¬ Good (S0.image (fun x => (g₃ ^ idx x) a)) := by
  unfold Good S0 hF idx; decide +kernel

lemma g₃_not_mem_classIn : g₃ ∉ classIn g₂ := by
  rintro ⟨k, hk, hkg⟩
  have hc : k * g₂ = g₃ * k := by
    rw [hkg]; group
  have hpow : ∀ i : ℕ, k * g₂ ^ i = g₃ ^ i * k := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hc, ← mul_assoc, ← pow_succ]
  have hkx : ∀ x, k x = (g₃ ^ idx x) (k 0) := by
    intro x
    conv_lhs => rw [← idx_spec x]
    have := congrArg (fun f : Equiv.Perm (Fin 23) => f 0) (hpow (idx x))
    simpa using this
  apply no_candidate (k 0)
  have := good_of_mem_M23 hk S0 S0_good
  convert this using 2
  funext x
  exact (hkx x).symm

theorem solution :
    (g₁, g₂, g₃) ∈ sigmaC ∧ g₃ ∉ classIn g₂ ∧
      orderOf g₁ = 2 ∧ orderOf g₂ = 23 ∧ orderOf g₃ = 23 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have o1 : orderOf g₁ = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have o2 : orderOf g₂ = 23 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have o3 : orderOf g₃ = 23 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  refine ⟨⟨⟨1, M23.one_mem, by simp⟩, ⟨1, M23.one_mem, by simp⟩, ⟨1, M23.one_mem, by simp⟩,
    prod_eq_one, ?_⟩, g₃_not_mem_classIn, o1, o2, o3⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact g₃_mem_M23
  · exact Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with h | h <;> simp [h])

#print axioms solution
