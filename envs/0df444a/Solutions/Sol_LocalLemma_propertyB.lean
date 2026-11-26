-- Prove2me | solution 1 for LocalLemma.propertyB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:29:47.592649+00:00
-- url     : https://prove2.me/submissions/80159634-6efc-4cde-916b-650e9f23decb

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_exists_good_coloring

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {V : Type*} [DecidableEq V] (H : Finset (Finset V)) {k d : ℕ}
    (hk : ∀ e ∈ H, e.card = k)
    (hd : ∀ e ∈ H, (H.filter fun f => f ≠ e ∧ ¬ Disjoint e f).card ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ (k - 1)) :
    ∃ c : V → Bool, ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    rcases k with _ | j
    · exfalso
      simp only [zero_tsub, pow_zero] at h
      have h1 : 1 + 1 < Real.exp 1 := Real.add_one_lt_exp one_ne_zero
      have h2 : (0:ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    · exact ⟨j, rfl⟩
  simp only [add_tsub_cancel_right] at h
  set W := H.biUnion id with hW
  set f : Fin H.card ≃ H := H.equivFin.symm with hf
  let D : Fin H.card → Finset {v // v ∈ W} := fun a => (f a).1.subtype (· ∈ W)
  have hfW : ∀ a, ∀ v ∈ (f a).1, v ∈ W := fun a v hv =>
    Finset.mem_biUnion.2 ⟨(f a).1, (f a).2, hv⟩
  let Γ : SimpleGraph (Fin H.card) := SimpleGraph.fromRel fun a b => ¬ Disjoint (f a).1 (f b).1
  have hΓ : ∀ i j, j ≠ i → ¬ Γ.Adj i j → Disjoint (D i) (D j) := by
    intro i j hji hadj
    have hdis : Disjoint (f i).1 (f j).1 := by
      by_contra hc
      exact hadj ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hji.symm, Or.inl hc⟩)
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rw [Finset.mem_subtype] at hvi hvj
    exact Finset.disjoint_left.1 hdis hvi hvj
  have hD : ∀ a, j + 1 ≤ (D a).card := by
    intro a
    simp only [D, Finset.card_subtype]
    rw [Finset.filter_true_of_mem (hfW a), hk _ (f a).2]
  have hdeg : ∀ a, Γ.degree a ≤ d := by
    intro a
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine le_trans ?_ (hd (f a).1 (f a).2)
    refine Finset.card_le_card_of_injOn (fun b => (f b).1) ?_ ?_
    · intro b hb
      rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset, SimpleGraph.fromRel_adj] at hb
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨(f b).2, fun he => hb.1 (f.injective (Subtype.ext he.symm)), ?_⟩
      rcases hb.2 with h' | h'
      · exact h'
      · exact fun h'' => h' h''.symm
    · intro b _ b' _ he
      exact f.injective (Subtype.ext he)
  have hc : Real.exp 1 * (2 * (1 / 2) ^ (j + 1)) * (d + 1) ≤ 1 := by
    have h2 : (2:ℝ) * (1 / 2) ^ (j + 1) = 1 / 2 ^ j := by
      rw [pow_succ, one_div_pow]; field_simp
    rw [h2, mul_one_div, div_mul_eq_mul_div, div_le_one (by positivity)]
    exact h
  obtain ⟨ω, hω⟩ := exists_good_coloring D Γ hΓ hD hdeg hc
  refine ⟨fun v => if hv : v ∈ W then ω ⟨v, hv⟩ else true, fun e he => ?_⟩
  by_contra hne
  push Not at hne
  set a := f.symm ⟨e, he⟩
  have hfa : (f a).1 = e := by simp [a]
  apply hω a
  rcases e.eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
  · refine ⟨true, fun v hv => ?_⟩
    rw [Finset.mem_subtype, hfa, h0] at hv
    simp at hv
  · refine ⟨if hv : x0 ∈ W then ω ⟨x0, hv⟩ else true, fun v hv => ?_⟩
    rw [Finset.mem_subtype, hfa] at hv
    have := hne v hv x0 hx0
    simpa [v.2] using this
end LocalLemma
