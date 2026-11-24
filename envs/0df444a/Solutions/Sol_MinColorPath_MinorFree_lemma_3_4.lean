-- Prove2me | solution 1 for MinColorPath.MinorFree.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:16:48.052978+00:00
-- url     : https://prove2.me/submissions/c65cf715-0af2-49be-96af-d6400d6536ff

import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition

namespace SolMinColorThreeFour

open SimpleGraph MinColorPath.MinorFree

/-- In a tree, if `z` lies below `x` (the root path of `z` passes through `x`) and the root path
of `y` avoids `x`, then every walk from `z` to `y` passes through `x`. -/
theorem walk_through {T : Type} (t : SimpleGraph T) (ht : t.IsTree) (root x z y : T)
    (p : t.Walk root z) (hp : p.IsPath) (hxp : x ∈ p.support)
    (hy : ∀ q : t.Walk root y, q.IsPath → x ∉ q.support) (r : t.Walk z y) :
    x ∈ r.support := by
  classical
  by_contra hxr
  obtain ⟨q⟩ := ht.connected.preconnected root y
  have hq := hy q.bypass q.bypass_isPath
  have hw : x ∉ (q.bypass.append r.reverse).bypass.support := by
    intro hx
    have hx' := (q.bypass.append r.reverse).support_bypass_subset_support hx
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx'
    rcases hx' with h | h
    · exact hq h
    · exact hxr h
  have heq := (ht.isAcyclic.subsingleton_path _ _).elim
    ⟨(q.bypass.append r.reverse).bypass, Walk.bypass_isPath _⟩ ⟨p, hp⟩
  have heq' : (q.bypass.append r.reverse).bypass = p := congrArg Subtype.val heq
  rw [heq'] at hw
  exact hw hxp

/-- A vertex of `γ(x)` adjacent to a vertex outside `γ(x)` lies in `β(x)`. -/
theorem bag_of_boundary {V : Type} [DecidableEq V] {G : SimpleGraph V} (𝒯 : RTD G)
    (x : 𝒯.T) (u v : V) (hadj : G.Adj u v) (hv : v ∈ 𝒯.gamma x) (hu : u ∉ 𝒯.gamma x) :
    v ∈ 𝒯.bag x := by
  classical
  obtain ⟨htree, -, hedge, hpath⟩ := 𝒯.isTD
  obtain ⟨y, huy, hvy⟩ := hedge u v hadj
  unfold RTD.gamma at hv hu
  rw [Finset.mem_biUnion] at hv
  obtain ⟨z, hz, hvz⟩ := hv
  have hyn : ¬ 𝒯.InSub x y := by
    intro hin
    apply hu
    rw [Finset.mem_biUnion]
    exact ⟨y, by simp [RTD.subtree, hin], huy⟩
  have hz' : 𝒯.InSub x z := by
    simpa [RTD.subtree] using hz
  obtain ⟨p, hp, hxp⟩ := hz'
  obtain ⟨r⟩ := htree.connected.preconnected z y
  have hx := walk_through 𝒯.t htree 𝒯.root x z y p hp hxp
    (fun q hq hxq => hyn ⟨q, hq, hxq⟩) r.bypass
  exact hpath z x y r.bypass r.bypass_isPath hx (Finset.mem_inter.2 ⟨hvz, hvy⟩)

end SolMinColorThreeFour

open MinColorPath.MinorFree SolMinColorThreeFour in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (𝒯 : RTD G)
    {s t : V} (π : G.Walk s t) (hπ : π.IsPath) (x : 𝒯.T) (i j : Fin π.support.length)
    (hseg : 𝒯.IsSegment (fun B v => v ∈ B) π.support x i j) :
    (π.support.get i ∈ 𝒯.bag x ∨ π.support.get i = s ∨ π.support.get i = t) ∧
      (π.support.get j ∈ 𝒯.bag x ∨ π.support.get j = s ∨ π.support.get j = t) := by
  obtain ⟨hij, hin, hleft, hright⟩ := hseg
  have hlen := π.length_support
  have hadj : ∀ (k : ℕ) (hk : k + 1 < π.support.length),
      G.Adj (π.support[k]'(by omega)) (π.support[k+1]'hk) := by
    intro k hk
    rw [SimpleGraph.Walk.support_getElem_eq_getVert, SimpleGraph.Walk.support_getElem_eq_getVert]
    exact π.adj_getVert_succ (by omega)
  constructor
  · by_cases h0 : i.val = 0
    · right; left
      have : π.support.get i = π.support[0]'(by omega) := by
        simp only [List.get_eq_getElem, h0]
      rw [this, SimpleGraph.Walk.support_getElem_zero]
    · left
      have hk := hleft ⟨i.val - 1, by omega⟩ (by simp only; omega)
      have hiγ := hin i le_rfl hij
      apply bag_of_boundary 𝒯 x (π.support.get ⟨i.val - 1, by omega⟩) (π.support.get i) _ hiγ hk
      have := hadj (i.val - 1) (by omega)
      simp only [List.get_eq_getElem]
      convert this using 2
      all_goals omega
  · by_cases hl : j.val + 1 = π.support.length
    · right; right
      have : π.support.get j = π.support[π.length]'(by omega) := by
        simp only [List.get_eq_getElem]
        congr 1; omega
      rw [this, SimpleGraph.Walk.support_getElem_length]
    · left
      have hk := hright ⟨j.val + 1, by omega⟩ (by simp only)
      have hjγ := hin j hij le_rfl
      apply bag_of_boundary 𝒯 x (π.support.get ⟨j.val + 1, by omega⟩) (π.support.get j) _ hjγ hk
      have := hadj j.val (by omega)
      simp only [List.get_eq_getElem]
      exact this.symm
