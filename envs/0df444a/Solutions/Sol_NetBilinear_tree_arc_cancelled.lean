-- Prove2me | solution 1 for NetBilinear.tree_arc_cancelled
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:37:33.752334+00:00
-- url     : https://prove2.me/submissions/219268d3-23dc-44a8-b280-ae00ea8c7eb0

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_IsECRAssignmentOne
import Definitions.Def_NetBilinear_Network_IsECRAssignment

open NetBilinear in
theorem solution {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : Network V A) (Itil : Finset V) (T : G.underlying.Subgraph)
    (hT : T.verts = (Itil : Set V)) (hTree : T.coe.IsTree) (l : A)
    (hl : Xor (G.tail l ∈ Itil) (G.head l ∈ Itil))
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (hunion : I1 ∪ I2 = Itil) (s : Sign) (r : A)
    (hr_tail : G.tail r ∈ Itil) (hr_head : G.head r ∈ Itil) :
    (G.head l ∈ Itil →
        IsCancelled G.incRow l s (rowsWith s I1) (rowsWith s.flip I2)
          (fun _ => 1) (fun _ => 1) r) ∧
    (G.tail l ∈ Itil →
        IsCancelled G.incRow l s.flip (rowsWith s I1) (rowsWith s.flip I2)
          (fun _ => 1) (fun _ => 1) r) := by
  have hsum : ∀ (σ' : Sign) (X : Finset V),
      ∑ t ∈ rowsWith σ' X, (fun _ => (1 : ℝ)) t * G.incRow t r =
        σ'.toReal * ((if G.tail r ∈ X then 1 else 0) - (if G.head r ∈ X then 1 else 0)) := by
    intro σ' X
    unfold rowsWith
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    simp only [one_mul, Network.incRow]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  have hflip : s.flip.toReal = -s.toReal := by
    cases s <;> simp [Sign.flip, Sign.toReal]
  have hone : ∀ x ∈ Itil, (if x ∈ I1 then (1 : ℝ) else 0) + (if x ∈ I2 then 1 else 0) = 1 := by
    intro x hx
    rw [← hunion, Finset.mem_union] at hx
    by_cases h1 : x ∈ I1
    · have h2 : x ∉ I2 := Finset.disjoint_left.mp hdisj h1
      simp [h1, h2]
    · have h2 : x ∈ I2 := hx.resolve_left h1
      simp [h1, h2]
  have ht := hone _ hr_tail
  have hh := hone _ hr_head
  have hagg : ∀ σ : Sign, r ≠ l →
      aggCoef G.incRow l σ (rowsWith s I1) (rowsWith s.flip I2) (fun _ => 1) (fun _ => 1) r = 0 := by
    intro σ hrl
    unfold aggCoef baseContrib
    rw [if_neg hrl, hsum s I1, hsum s.flip I2, hflip]
    linear_combination s.toReal * ht - s.toReal * hh
  have hinc : ∀ σ' : Sign, G.incRow (G.tail r, σ') r ≠ 0 := by
    intro σ'
    have hne : G.head r ≠ G.tail r := (G.loopless r).symm
    cases σ' <;> simp [Network.incRow, Sign.toReal, hne]
  have hcreated : ∀ σ : Sign,
      IsCreated G.incRow l σ (rowsWith s I1) (rowsWith s.flip I2) (fun _ => 1) (fun _ => 1) r := by
    intro σ
    have hx : G.tail r ∈ I1 ∪ I2 := by rw [hunion]; exact hr_tail
    rcases Finset.mem_union.mp hx with h1 | h2
    · refine Or.inr (Or.inl ⟨(G.tail r, s), Finset.mem_image_of_mem _ h1, ?_⟩)
      simp only [one_mul]
      exact hinc s
    · refine Or.inr (Or.inr ⟨(G.tail r, s.flip), Finset.mem_image_of_mem _ h2, ?_⟩)
      simp only [one_mul]
      exact hinc s.flip
  constructor
  · intro hhead
    have htl : G.tail l ∉ Itil := by
      rcases hl with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact absurd hhead h2
      · exact h2
    have hrl : r ≠ l := by
      rintro rfl
      exact htl hr_tail
    exact ⟨hcreated s, hagg s hrl⟩
  · intro htail
    have hhl : G.head l ∉ Itil := by
      rcases hl with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2
      · exact absurd htail h2
    have hrl : r ≠ l := by
      rintro rfl
      exact hhl hr_head
    exact ⟨hcreated s.flip, hagg s.flip hrl⟩
