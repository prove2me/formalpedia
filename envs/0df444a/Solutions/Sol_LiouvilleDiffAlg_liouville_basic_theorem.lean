-- Prove2me | solution 1 for LiouvilleDiffAlg.liouville_basic_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T10:26:23.016816+00:00
-- url     : https://prove2.me/submissions/809ae3c0-2c20-40c6-b81e-9cbae47042fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form
import Theorems.Thm_LiouvilleDiffAlg_deriv_gen_mem_of_isAlgebraic
import Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_algebraic
import Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_logarithmic
import Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_exponential

open scoped Differential
open LiouvilleDiffAlg

/-- If `K` is closed under `D` and `D t ∈ K⟮t⟯`, then `K⟮t⟯` is closed under `D`. -/
private lemma closed_adjoin_aux {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) (t : G)
    (ht : t′ ∈ IntermediateField.adjoin F (insert t (K : Set G))) :
    ∀ x ∈ IntermediateField.adjoin F (insert t (K : Set G)),
      x′ ∈ IntermediateField.adjoin F (insert t (K : Set G)) := by
  intro x hx
  have hKL : K ≤ IntermediateField.adjoin F (insert t (K : Set G)) := by
    intro y hy
    exact IntermediateField.subset_adjoin F _ (Set.mem_insert_of_mem _ hy)
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ht
    · exact hKL (hK x hx)
  | algebraMap a =>
    exact hKL (hK _ (IntermediateField.algebraMap_mem K a))
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | inv x hx ihx =>
    rw [Derivation.leibniz_inv]
    exact mul_mem (neg_mem (pow_mem (inv_mem hx) 2)) ihx
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz]
    exact add_mem (mul_mem hx ihy) (mul_mem hy ihx)

theorem solution {F G : Type*} [Field F] [Field G] [Differential F]
    [Differential G] [Algebra F G] [DifferentialAlgebra F G] [CharZero F]
    (hcon : algebraMap F G '' constants F = constants G)
    (helem : IsElementaryDifferentialExtension F G)
    (f : F) (g : G) (hg : g′ = algebraMap F G f) :
    ∃ (n : ℕ) (c : Fin n → F) (u : Fin n → F) (v : F),
      (∀ i, c i ∈ constants F) ∧ (∀ i, u i ≠ 0) ∧
      f = ∑ i, c i * ((u i)′ / u i) + v′ := by
  classical
  have : CharZero G := charZero_of_injective_algebraMap (algebraMap F G).injective
  obtain ⟨m, K, hK0, hKm, hstep⟩ := helem
  choose! t htK hts using hstep
  -- every `K i` contains the image of `F`, hence every constant of `G`
  have hconst : ∀ i, constants G ⊆ (K i : Set G) := by
    intro i c hc
    rw [← hcon] at hc
    obtain ⟨a, -, rfl⟩ := hc
    exact IntermediateField.algebraMap_mem (K i) a
  -- every `K i` (for `i ≤ m`) is closed under the derivation
  have hclosed : ∀ i, i ≤ m → ∀ x ∈ K i, x′ ∈ K i := by
    intro i
    induction i with
    | zero =>
      intro _ x hx
      rw [hK0, IntermediateField.mem_bot] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [deriv_algebraMap, hK0]
      exact IntermediateField.algebraMap_mem _ _
    | succ i ih =>
      intro hi
      have him : i < m := hi
      rw [htK i him]
      have hKi := ih him.le
      refine closed_adjoin_aux (K i) hKi (t i) ?_
      rcases hts i him with h | h | h
      · exact deriv_gen_mem_of_isAlgebraic (K i) hKi h
      · obtain ⟨-, s, hs, hs0, hts'⟩ := h
        rw [hts']
        exact IntermediateField.subset_adjoin F _
          (Set.mem_insert_of_mem _ (by
            exact div_mem (hKi s hs) hs))
      · obtain ⟨htr, s, hs, hts'⟩ := h
        have ht0 : t i ≠ 0 := fun h0 => htr (by rw [h0]; exact isAlgebraic_zero)
        have : (t i)′ = (s)′ * t i := by
          field_simp at hts' ⊢
          linear_combination hts'
        rw [this]
        exact mul_mem
          (IntermediateField.subset_adjoin F _ (Set.mem_insert_of_mem _ (hKi s hs)))
          (IntermediateField.subset_adjoin F _ (Set.mem_insert _ _))
  -- descending induction along the tower
  have key : ∀ k, k ≤ m → LiouvilleFormIn (K (m - k) : Set G) (algebraMap F G f) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, fun i => i.elim0, fun i => i.elim0, g, ?_, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · rw [Nat.sub_zero, hKm]; trivial
      · simp [hg]
    | succ k ih =>
      intro hk
      obtain ⟨i, hi⟩ : ∃ i, m - k = i + 1 := ⟨m - (k + 1), by omega⟩
      have hi' : m - (k + 1) = i := by omega
      have him : i < m := by omega
      have hL := ih (by omega)
      rw [hi, htK i him] at hL
      rw [hi']
      have hh : algebraMap F G f ∈ K i := IntermediateField.algebraMap_mem _ _
      have hKi := hclosed i him.le
      rcases hts i him with h | h | h
      · exact liouvilleForm_descent_algebraic (K i) hKi (hconst i) h hh hL
      · exact liouvilleForm_descent_logarithmic (K i) hKi (hconst i) h hh hL
      · exact liouvilleForm_descent_exponential (K i) hKi (hconst i) h hh hL
  obtain ⟨n, c, u, v, hc, hu, hv, hfe⟩ := by
    have := key m le_rfl
    rwa [Nat.sub_self, hK0] at this
  -- pull everything back to `F`
  have hc' : ∀ i, ∃ a ∈ constants F, algebraMap F G a = c i := by
    intro i
    have := hc i
    rw [← hcon] at this
    obtain ⟨a, ha, h⟩ := this
    exact ⟨a, ha, h⟩
  have hu' : ∀ i, ∃ a : F, algebraMap F G a = u i := by
    intro i
    have := (hu i).1
    rw [SetLike.mem_coe, IntermediateField.mem_bot] at this
    exact this
  have hv' : ∃ a : F, algebraMap F G a = v := by
    have := hv
    rw [SetLike.mem_coe, IntermediateField.mem_bot] at this
    exact this
  choose c₀ hc₀ hc₀e using hc'
  choose u₀ hu₀ using hu'
  obtain ⟨v₀, hv₀⟩ := hv'
  refine ⟨n, c₀, u₀, v₀, hc₀, ?_, ?_⟩
  · intro i h0
    apply (hu i).2
    rw [← hu₀ i, h0, map_zero]
  · have hcf : c = fun i => algebraMap F G (c₀ i) := funext fun i => (hc₀e i).symm
    have huf : u = fun i => algebraMap F G (u₀ i) := funext fun i => (hu₀ i).symm
    subst hcf huf hv₀
    apply (algebraMap F G).injective
    rw [hfe]
    simp only [map_add, map_sum, map_mul, map_div₀, deriv_algebraMap]
