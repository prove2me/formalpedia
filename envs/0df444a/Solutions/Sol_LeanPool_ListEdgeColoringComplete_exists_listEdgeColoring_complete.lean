-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.exists_listEdgeColoring_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:32:49.294107+00:00
-- url     : https://prove2.me/submissions/9159d179-a847-4d4e-b44a-cb58c4f930fd

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Main
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_isEmpty_edgeSet_top_of_card_le_one
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_exists_starMember_eq_inl
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_canonicalPerm_inl_lt
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_canonicalPerm_inr_lt
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_coeff_graphPoly_certificate_ne_zero
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_starPoly_eval_ne_zero
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_totalDegree_graphPoly


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution
    {V Color : Type*} [Fintype V]
    (lists : (⊤ : SimpleGraph V).edgeSet → Finset Color)
    (hLists : ∀ e, Fintype.card V ≤ (lists e).card) :
    ∃ coloring : (⊤ : SimpleGraph V).lineGraph.Coloring Color,
      ∀ e, coloring e ∈ lists e := by
  classical
  by_cases hn : Fintype.card V ≤ 1
  · -- no edges at all
    have := isEmpty_edgeSet_top_of_card_le_one hn
    exact ⟨SimpleGraph.Coloring.mk (fun e => isEmptyElim e) (fun {e} => isEmptyElim e),
      fun e => isEmptyElim e⟩
  -- labels `0, …, n-1`
  set n := Fintype.card V with hn_def
  let f : V ≃ Fin n := Fintype.equivFin V
  -- injective encoding of the colours occurring in some list into `ℚ`
  let U : Finset Color := univ.biUnion lists
  let enc : Color → ℚ := fun c => if h : c ∈ U then ((U.equivFin ⟨c, h⟩ : ℕ) : ℚ) else 0
  have hU : ∀ e, ∀ c ∈ lists e, c ∈ U := fun e c hc => mem_biUnion.mpr ⟨e, mem_univ _, hc⟩
  have henc : ∀ e, Set.InjOn enc (lists e) := by
    intro e c hc d hd hcd
    simp only [enc, hU e c hc, hU e d hd, ↓reduceDIte, Nat.cast_inj] at hcd
    exact congrArg Subtype.val (U.equivFin.injective (Fin.ext hcd))
  -- the lists for the Nullstellensatz: encoded colours, and `{0, …, n-1}` for stars
  let S : StarVar V → Finset ℚ := fun v => match v with
    | Sum.inl e => (lists e).image enc
    | Sum.inr _ => (range n).image (fun k : ℕ => (k : ℚ))
  have hS : ∀ v, expo f (canonicalPerm f) v < #(S v) := by
    rintro (e | u)
    · change _ < #((lists e).image enc)
      rw [card_image_of_injOn (henc e)]
      exact (expo_canonicalPerm_inl_lt f e).trans_le (hLists e)
    · change _ < #((range n).image (fun k : ℕ => (k : ℚ)))
      rw [card_image_of_injective _ Nat.cast_injective, card_range]
      exact expo_canonicalPerm_inr_lt f u
  obtain ⟨x, hxS, hx⟩ := combinatorial_nullstellensatz_exists_eval_nonzero (graphPoly f)
    (expo f (canonicalPerm f)) (coeff_graphPoly_certificate_ne_zero f)
    (totalDegree_graphPoly f) S hS
  -- every star receives distinct values
  have hstar : ∀ v, Function.Injective (fun k => x (starMember f v k)) := by
    intro v
    apply starPoly_eval_ne_zero
    have : ∏ u, eval x (starPoly f u) ≠ 0 := by
      simpa [graphPoly, map_prod] using hx
    exact (prod_ne_zero_iff.mp this) v (mem_univ v)
  -- decode the chosen values back into colours
  have hchoice : ∀ e, ∃ c ∈ lists e, enc c = x (Sum.inl e) := fun e => by
    simpa [S] using hxS (Sum.inl e)
  choose col hcol henc_col using hchoice
  refine ⟨SimpleGraph.Coloring.mk col ?_, hcol⟩
  intro e e' hadj hsame
  obtain ⟨hne, v, hv, hv'⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
  obtain ⟨k, hk⟩ := exists_starMember_eq_inl f e hv
  obtain ⟨k', hk'⟩ := exists_starMember_eq_inl f e' hv'
  have hxx : x (starMember f v k) = x (starMember f v k') := by
    rw [hk, hk', ← henc_col, ← henc_col, hsame]
  have hkk := hstar v hxx
  rw [hkk, hk'] at hk
  exact hne (Sum.inl_injective hk).symm
end LeanPool.ListEdgeColoringComplete
