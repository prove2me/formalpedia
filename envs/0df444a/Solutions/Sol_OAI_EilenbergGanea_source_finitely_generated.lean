-- Prove2me | solution 1 for OAI.EilenbergGanea.source_finitely_generated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T00:15:09.720347+00:00
-- url     : https://prove2.me/submissions/d6a6851d-a898-4ea5-bc7c-cbda6defbe63

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEG018

section
-- module Solutions.OAIEG.RightAngledArtin_Basic
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea


section FiniteGeneration
variable {V : Type*} (L : SimpleGraph V)

theorem edge_difference_mem {v w : V} (h : L.Adj v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L :=
  Subgroup.subset_closure ⟨v, w, h, rfl⟩

theorem reachable_difference_mem {v w : V} (h : L.Reachable v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    simpa only [mul_assoc, inv_mul_cancel_left] using
      (edgeGenerated L).mul_mem (edge_difference_mem L huv) ih

theorem reachable_inv_difference_mem {v w : V} (h : L.Reachable v w) :
    (artinGenerator L v)⁻¹ * artinGenerator L w ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hc := (adjacent_generators_commute L huv).inv_left
    have he : (artinGenerator L u)⁻¹ * artinGenerator L v ∈ edgeGenerated L := by
      rw [hc.eq]
      exact edge_difference_mem L huv.symm
    simpa only [mul_assoc, mul_inv_cancel_left] using (edgeGenerated L).mul_mem he ih


/-- A group-theoretic conjugation identity used with edge differences. -/
theorem conjugate_mem_of_difference {A : Type*} [Group A] (K : Subgroup A)
    {g a e : A} (hga : g * a⁻¹ ∈ K) (he : e ∈ K) (ha : Commute a e) :
    g * e * g⁻¹ ∈ K := by
  have hm := K.mul_mem (K.mul_mem hga he) (K.inv_mem hga)
  have hi : (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * e * g⁻¹ := by
    calc
      (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * (a⁻¹ * e * a) * g⁻¹ := by group
      _ = g * e * g⁻¹ := by rw [ha.inv_left.eq]; simp [mul_assoc]
  rwa [hi] at hm

theorem generator_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    artinGenerator L v * x * (artinGenerator L v)⁻¹ ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤ (edgeGenerated L).comap (MulAut.conj (artinGenerator L v)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    exact conjugate_mem_of_difference (edgeGenerated L)
      (reachable_difference_mem L (hconn v b)) (edge_difference_mem L hbc)
      ((Commute.refl _).mul_right (adjacent_generators_commute L hbc).inv_right)
  exact hh hx

theorem generator_inv_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    (artinGenerator L v)⁻¹ * x * artinGenerator L v ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤
      (edgeGenerated L).comap (MulAut.conj ((artinGenerator L v)⁻¹)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    change (artinGenerator L v)⁻¹ * (artinGenerator L b * (artinGenerator L c)⁻¹) *
      ((artinGenerator L v)⁻¹)⁻¹ ∈ edgeGenerated L
    apply conjugate_mem_of_difference (edgeGenerated L) (a := (artinGenerator L b)⁻¹)
    · simpa using reachable_inv_difference_mem L (hconn v b)
    · exact edge_difference_mem L hbc
    · exact ((Commute.refl _).mul_right
        (adjacent_generators_commute L hbc).inv_right).inv_left
  simpa using hh hx

theorem edgeGenerated_normal (hconn : L.Preconnected) : (edgeGenerated L).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply (Subgroup.eq_top_iff' _).mpr
  apply PresentedGroup.generated_by
  intro v
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact generator_conjugate_mem L hconn v
  · intro hx
    simpa [mul_assoc] using generator_inv_conjugate_mem L hconn v hx

/-- For a connected defining graph, edge differences generate the full height kernel. -/
theorem edgeGenerated_eq_height_kernel (hconn : L.Preconnected) (v₀ : V) :
    edgeGenerated L = (height L).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨v, w, _, rfl⟩
    simp [MonoidHom.mem_ker]
  · let _ := edgeGenerated_normal L hconn
    let q := QuotientGroup.mk' (edgeGenerated L)
    let z := zpowersHom _ (q (artinGenerator L v₀))
    have hq : q = z.comp (height L) := by
      apply PresentedGroup.ext
      intro v
      change q (artinGenerator L v) = z (height L (artinGenerator L v))
      rw [height_generator]
      change q (artinGenerator L v) = q (artinGenerator L v₀) ^ (1 : ℤ)
      rw [zpow_one]
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (reachable_difference_mem L (hconn v v₀))
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change q x = 1
    rw [hq, MonoidHom.comp_apply, (MonoidHom.mem_ker.mp hx), map_one]

theorem height_kernel_fg [Finite V] (hconn : L.Preconnected) (v₀ : V) :
    Group.FG (height L).ker := by
  rw [Group.fg_iff_subgroup_fg, ← edgeGenerated_eq_height_kernel L hconn v₀]
  apply (Subgroup.fg_iff _).mpr
  refine ⟨edgeDifferences L, rfl, ?_⟩
  apply Set.Finite.subset
    (Set.finite_range (fun p : V × V => artinGenerator L p.1 * (artinGenerator L p.2)⁻¹))
  rintro x ⟨v, w, _, rfl⟩
  exact ⟨(v, w), rfl⟩

end FiniteGeneration

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Seed
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea

theorem seed_vertex_edge_adj {v : SeedVertex} {e : SeedEdge} (h : v ∈ edgeVertices e) :
    seedGraph.Adj (.inl v) (.inr (.inl e)) := Or.inl h

theorem seed_edge_sector_adj {e : SeedEdge} {s : Sector} (h : e ∈ sectorEdges s) :
    seedGraph.Adj (.inr (.inl e)) (.inr (.inr s)) := Or.inl h

theorem rose_vertex_reachable (v : RoseVertex) :
    seedGraph.Reachable seedBase (.inl (.inl v)) := by
  rcases v with _ | ⟨b, i⟩
  · exact .refl _
  · fin_cases i
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 0))))
          (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 1))))
          (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm

theorem seed_vertex_reachable (v : SeedVertex) :
    seedGraph.Reachable seedBase (.inl v) := by
  rcases v with v | r
  · exact rose_vertex_reachable v
  · let s := firstSector r
    have h₁ : seedGraph.Adj (.inl (.inl (sectorStart s))) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices]
    have h₂ : seedGraph.Adj (.inl (.inr r)) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices, s, firstSector]
    exact ((rose_vertex_reachable (sectorStart s)).trans h₁.reachable).trans h₂.reachable.symm

theorem seed_edge_reachable (e : SeedEdge) :
    seedGraph.Reachable seedBase (.inr (.inl e)) := by
  rcases e with e | s
  · apply (seed_vertex_reachable (.inl (circleStart e))).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]
  · apply (seed_vertex_reachable (.inr s.1)).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]

theorem seed_cell_reachable (x : SeedCell) : seedGraph.Reachable seedBase x := by
  rcases x with v | e
  · exact seed_vertex_reachable v
  · rcases e with e | s
    · exact seed_edge_reachable e
    · apply (seed_edge_reachable (.inl (sectorCircleEdge s))).trans
      apply SimpleGraph.Adj.reachable
      apply seed_edge_sector_adj
      simp [sectorEdges]

theorem seed_connected : seedGraph.Connected := by
  exact { preconnected := fun v w =>
    (seed_cell_reachable v).symm.trans (seed_cell_reachable w), nonempty := ⟨seedBase⟩ }


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Model
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea
/-- The finite-generation conjunct for the exact source height kernel. -/
theorem source_finitely_generated_oai : Group.FG SourceGroup :=
  height_kernel_fg seedGraph seed_connected.preconnected seedBase



end EilenbergGanea



end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.source_finitely_generated_oai := @OAI.EilenbergGanea.source_finitely_generated_oai
