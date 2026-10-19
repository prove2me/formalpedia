-- Prove2me | solution 1 for HadwigerConj.hc_of_le_three
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:19:21.101333+00:00
-- url     : https://prove2.me/submissions/10f673a6-80c7-4fab-9129-e58d62c565f9

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Theorems.Thm_HadwigerConj_exists_degree_le_two_of_no_K4_minor
import Theorems.Thm_HadwigerConj_colorable_of_isDegenerate

namespace HDRed
open HadwigerConj SimpleGraph

lemma sing {V : Type} (G : SimpleGraph V) (v : V) : (G.induce {v}).Connected := by
  have := (Walk.nil : G.Walk v v).connected_induce_support
  have e : {y | y ∈ (Walk.nil : G.Walk v v).support} = {v} := by ext; simp
  rwa [e] at this

/-- A vertex gives a `K₁` minor. -/
lemma k1 {V : Type} (G : SimpleGraph V) (v : V) : HasCompleteMinor G 1 := by
  refine ⟨fun _ => {v}, fun _ => ?_, fun a b h => absurd (Subsingleton.elim a b) h, fun a b h => ?_⟩
  · exact sing G v
  · exact absurd (Subsingleton.elim a b) (by simpa using h)

/-- An edge gives a `K₂` minor. -/
lemma k2 {V : Type} (G : SimpleGraph V) {u v : V} (h : G.Adj u v) : HasCompleteMinor G 2 := by
  refine ⟨![{u}, {v}], fun i => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · fin_cases i <;> exact sing G _
  · have := G.ne_of_adj h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  · fin_cases a <;> fin_cases b <;> simp_all [h.symm]

/-- A cycle gives a `K₃` minor. -/
lemma k3 {V : Type} (G : SimpleGraph V) (hG : ¬ G.IsAcyclic) : HasCompleteMinor G 3 := by
  simp only [IsAcyclic, not_forall, not_not] at hG
  obtain ⟨u, c, hc⟩ := hG
  cases c with
  | nil => exact absurd hc (Walk.not_isCycle_nil)
  | @cons _ v1 _ h p =>
    rw [Walk.cons_isCycle_iff] at hc
    obtain ⟨hp, hne⟩ := hc
    have hpr : p.reverse.IsPath := hp.reverse
    cases hq : p.reverse with
    | nil =>
      exact absurd (G.ne_of_adj h) (by simp)
    | @cons _ w _ h' r =>
      rw [hq] at hpr
      have hr : r.IsPath := hpr.of_cons
      have hu : u ∉ r.support := (Walk.cons_isPath_iff _ _).1 hpr |>.2
      cases r with
      | nil =>
        -- p is the single edge v1 u, contradicting s(u,v1) ∉ p.edges
        exfalso; apply hne
        have : p = (Walk.cons h' Walk.nil).reverse := by rw [← hq, Walk.reverse_reverse]
        subst this; simp [Sym2.eq_swap]
      | @cons _ x _ hwx r' =>
        have hw : w ∉ r'.support := (Walk.cons_isPath_iff _ _).1 hr |>.2
        have hu' : u ≠ w ∧ u ∉ r'.support := by simpa using hu
        refine ⟨![{u}, {w}, {y | y ∈ r'.support}], fun i => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
        · fin_cases i
          · exact sing G _
          · exact sing G _
          · exact r'.connected_induce_support
        · rw [Set.disjoint_iff]
          fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
        · fin_cases a <;> fin_cases b <;> simp at hab ⊢
          · exact h'
          · exact ⟨v1, r'.end_mem_support, h⟩
          · exact h'.symm
          · exact ⟨x, r'.start_mem_support, hwx⟩
          · exact ⟨v1, r'.end_mem_support, h.symm⟩
          · exact ⟨x, r'.start_mem_support, hwx.symm⟩

/-- A complete minor of an induced subgraph lifts. -/
lemma lift {V : Type} (G : SimpleGraph V) (S : Set V) (t : ℕ)
    (h : HasCompleteMinor (G.induce S) t) : HasCompleteMinor G t := by
  obtain ⟨B, hc, hd, ha⟩ := h
  refine ⟨fun w => Subtype.val '' B w, fun w => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · let f : (G.induce S).induce (B w) →g G.induce (Subtype.val '' B w) :=
      { toFun := fun y => ⟨y.1.1, y.1, y.2, rfl⟩
        map_rel' := fun {a b} hab => by simpa using hab }
    refine (hc w).map f ?_
    rintro ⟨y, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · exact (Set.disjoint_image_iff Subtype.val_injective).2 (hd a b hab)
  · obtain ⟨u, hu, v, hv, huv⟩ := ha a b hab
    exact ⟨u.1, ⟨u, hu, rfl⟩, v.1, ⟨v, hv, rfl⟩, huv⟩

lemma degen {V : Type} [Finite V] (G : SimpleGraph V) (hG : ¬ HasCompleteMinor G 4) :
    IsDegenerate G 2 := by
  intro S hS
  have : Nonempty S := hS.to_subtype
  have h4 : ¬ HasCompleteMinor (G.induce S) 4 := fun h => hG (lift G S 4 h)
  obtain ⟨v, hv⟩ := exists_degree_le_two_of_no_K4_minor (G.induce S) h4
  refine ⟨v.1, v.2, ?_⟩
  have : G.neighborSet v.1 ∩ S = Subtype.val '' (G.induce S).neighborSet v := by
    ext y; constructor
    · rintro ⟨hy, hyS⟩; exact ⟨⟨y, hyS⟩, by simpa using hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨by simpa using hz, z.2⟩
  rw [this, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact hv

end HDRed

open HadwigerConj SimpleGraph in
theorem solution (t : ℕ) (ht : t ≤ 3) : HC t := by
  intro V _ G hG
  interval_cases t
  · have : IsEmpty V := ⟨fun v => hG (HDRed.k1 G v)⟩
    exact Colorable.of_isEmpty 0
  · refine ⟨Coloring.mk (fun _ => 0) fun {u v} h => absurd (HDRed.k2 G h) hG⟩
  · exact (by_contra fun hA => hG (HDRed.k3 G hA) : G.IsAcyclic).colorable_two
  · exact colorable_of_isDegenerate G 2 (HDRed.degen G hG)
