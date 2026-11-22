-- Prove2me | solution 1 for Menger27.Curves.satz_gamma
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:54:50.298799+00:00
-- url     : https://prove2.me/submissions/47238353-8396-4252-b39e-50df0c53aa49

import Mathlib
import Definitions.Def_Menger27_Curves_Separation

set_option autoImplicit false

namespace Menger27.Curves.SatzGammaProof

open Set

variable {X : Type*} [TopologicalSpace X]

/-- `x` is joined to `A` inside `U` by a compact connected set. -/
def Reach (U A : Set X) (x : X) : Prop :=
  ∃ K : Set X, IsCompact K ∧ IsPreconnected K ∧ K ⊆ U ∧ x ∈ K ∧ (K ∩ A).Nonempty

/-- Reachability propagates along a compact connected set inside `U`. -/
theorem reach_extend {U A L : Set X} {x w : X} (hLc : IsCompact L) (hLp : IsPreconnected L)
    (hLU : L ⊆ U) (hx : x ∈ L) (hw : w ∈ L) (hr : Reach U A x) : Reach U A w := by
  obtain ⟨K, hKc, hKp, hKU, hxK, a, haK, haA⟩ := hr
  exact ⟨K ∪ L, hKc.union hLc, IsPreconnected.union x hxK hx hKp hLp,
    union_subset hKU hLU, Or.inr hw, a, Or.inl haK, haA⟩

/-- In a compact, regular, locally connected space every point of an open set `U` has an open
neighbourhood whose closure is compact, connected and contained in `U`. -/
theorem exists_nbhd [RegularSpace X] [CompactSpace X] [LocallyConnectedSpace X] {U : Set X}
    (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsCompact (closure W) ∧ IsPreconnected (closure W) ∧
      closure W ⊆ U := by
  obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hx)
  obtain ⟨V, hVt, hVo, hxV, hVc⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp ‹_›) x t ht
  exact ⟨V, hVo, hxV, isClosed_closure.isCompact, hVc.isPreconnected.closure,
    (closure_minimal hVt htc).trans htU⟩

end Menger27.Curves.SatzGammaProof

open Set Menger27.Curves Menger27.Curves.SatzGammaProof

set_option linter.unusedVariables false in
theorem solution {X : Type*} [MetricSpace X]
    [CompactSpace X] [LocallyConnectedSpace X]
    [Finite (ConnectedComponents X)]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) (C : ℕ → Set X)
    (hclosed : ∀ k, IsClosed (C k))
    (hnested : ∀ k, C (k + 1) ⊆ C k)
    (hsep : ∀ k, Separates Set.univ (C k) A B) :
    Separates Set.univ (⋂ k, C k) A B := by
  set D := ⋂ k, C k with hD
  have hUo : IsOpen Dᶜ := (isClosed_iInter hclosed).isOpen_compl
  -- No point of `B` outside `D` is joined to `A` by a compact connected set avoiding `D`:
  -- such a set would already avoid some `C N`, which separates `A` from `B`.
  have key : ∀ b ∈ B, b ∉ D → ¬ Reach Dᶜ A b := by
    rintro b hbB hbD ⟨K, hKc, hKp, hKU, hbK, a, haK, haA⟩
    have hanti : Antitone C := antitone_nat_of_succ_le hnested
    have hcov : K ⊆ ⋃ k, (C k)ᶜ := by
      intro y hy
      have hy' : y ∉ D := hKU hy
      rw [hD, mem_iInter] at hy'
      push Not at hy'
      simpa using hy'
    obtain ⟨N, hN⟩ := hKc.elim_directed_cover (fun k => (C k)ᶜ)
      (fun k => (hclosed k).isOpen_compl) hcov
      (Monotone.directed_le fun i j hij => compl_subset_compl.mpr (hanti hij))
    obtain ⟨M₁, M₂, hU, hd, h1, h2, hA', hB'⟩ := hsep N
    have haM : a ∈ M₁ := hA' ⟨haA, hN haK⟩
    have hbM : b ∈ M₂ := hB' ⟨hbB, hN hbK⟩
    have hKsub : K ⊆ closure M₁ ∪ closure M₂ := by
      intro y hy
      have hyN : y ∈ univ \ C N := ⟨trivial, hN hy⟩
      rw [hU] at hyN
      rcases hyN with h | h
      · exact Or.inl (subset_closure h)
      · exact Or.inr (subset_closure h)
    obtain ⟨y, hyK, hy1, hy2⟩ := (isPreconnected_closed_iff.mp hKp) _ _ isClosed_closure
      isClosed_closure hKsub ⟨a, haK, subset_closure haM⟩ ⟨b, hbK, subset_closure hbM⟩
    have hyN : y ∈ univ \ C N := ⟨trivial, hN hyK⟩
    have hy1' : y ∈ M₁ := by rw [h1]; exact ⟨hyN, hy1⟩
    have hy2' : y ∈ M₂ := by rw [h2]; exact ⟨hyN, hy2⟩
    exact disjoint_left.mp hd hy1' hy2'
  refine ⟨{x | x ∉ D ∧ Reach Dᶜ A x}, {x | x ∉ D ∧ ¬ Reach Dᶜ A x},
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_sdiff, mem_univ, true_and, mem_union, mem_ofPred_eq]
    tauto
  · rw [disjoint_left]
    rintro x ⟨-, h⟩ ⟨-, h'⟩
    exact h' h
  · ext x
    constructor
    · intro hx
      exact ⟨⟨trivial, hx.1⟩, subset_closure hx⟩
    · rintro ⟨⟨-, hxD⟩, hxcl⟩
      refine ⟨hxD, ?_⟩
      by_contra hnr
      obtain ⟨W, hWo, hxW, hWc, hWp, hWU⟩ := exists_nbhd hUo hxD
      obtain ⟨z, hzW, -, hzr⟩ := mem_closure_iff.mp hxcl W hWo hxW
      exact hnr (reach_extend hWc hWp hWU (subset_closure hzW) (subset_closure hxW) hzr)
  · ext x
    constructor
    · intro hx
      exact ⟨⟨trivial, hx.1⟩, subset_closure hx⟩
    · rintro ⟨⟨-, hxD⟩, hxcl⟩
      refine ⟨hxD, fun hr => ?_⟩
      obtain ⟨W, hWo, hxW, hWc, hWp, hWU⟩ := exists_nbhd hUo hxD
      obtain ⟨z, hzW, -, hzr⟩ := mem_closure_iff.mp hxcl W hWo hxW
      exact hzr (reach_extend hWc hWp hWU (subset_closure hxW) (subset_closure hzW) hr)
  · rintro a ⟨haA, haD⟩
    obtain ⟨W, hWo, haW, hWc, hWp, hWU⟩ := exists_nbhd hUo haD
    exact ⟨haD, closure W, hWc, hWp, hWU, subset_closure haW, a, subset_closure haW, haA⟩
  · rintro b ⟨hbB, hbD⟩
    exact ⟨hbD, key b hbB hbD⟩
