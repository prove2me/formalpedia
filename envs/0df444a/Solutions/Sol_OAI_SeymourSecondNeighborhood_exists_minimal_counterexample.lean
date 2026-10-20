-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.exists_minimal_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:40:31.818765+00:00
-- url     : https://prove2.me/submissions/91d90346-1dd5-4d4e-b20f-5e395be6612a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MinimalCounterexample.lean:L132-L160
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.exists_minimal_counterexample. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample

-- ---- from OAI.Combinatorics.SecondNeighborhood.ReductionCore ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Counterexample.first_nonempty {r : V → V → Prop}
    (h : Counterexample r) (v : V) : (firstNeighbors r v).Nonempty := by
  apply Finset.card_pos.mp
  exact lt_of_le_of_lt (Nat.zero_le _) (h v)

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.Reindex ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V W : Type*}

theorem isOriented_reindex (e : V ≃ W) {r : V → V → Prop}
    (hr : IsOriented r) : IsOriented (reindex e r) where
  loopless w := hr.loopless (e.symm w)
  asymmetric hxy hyx := hr.asymmetric hxy hyx

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem counterexample_reindex (e : V ≃ W) {r : V → V → Prop}
    (h : Counterexample r) : Counterexample (reindex e r) := by
  intro w
  rw [card_secondNeighbors_reindex, card_firstNeighbors_reindex]
  exact h (e.symm w)

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.MinimalCounterexample ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem isOriented_induced {r : V → V → Prop} (hr : IsOriented r)
    (S : Finset V) : IsOriented (induced r S) where
  loopless x := hr.loopless x.val
  asymmetric hxy hyx := hr.asymmetric hxy hyx

omit [DecidableEq V] in
theorem firstNeighbors_induced_map {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (firstNeighbors (induced r S) v).map
      (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ V) = firstNeighbors r v.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_map.mp hw
    change z.val = w at hzw
    subst w
    have hz' : induced r S v z := mem_firstNeighbors.mp hz
    exact mem_firstNeighbors.mpr hz'
  · intro hw
    have hvw := mem_firstNeighbors.mp hw
    have hwS : w ∈ S := hclosed (mem_image.mpr ⟨v.val, v.property, hvw⟩)
    exact Finset.mem_map.mpr ⟨⟨w, hwS⟩, mem_firstNeighbors.mpr hvw, rfl⟩

theorem secondNeighbors_induced_map {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (secondNeighbors (induced r S) v).map
      (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ V) = secondNeighbors r v.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_map.mp hw
    change z.val = w at hzw
    subst w
    obtain ⟨hne, hnr, u, hvu, huz⟩ := mem_secondNeighbors.mp hz
    apply mem_secondNeighbors.mpr
    refine ⟨?_, hnr, ⟨u.val, hvu, huz⟩⟩
    intro heq
    exact hne (Subtype.ext heq)
  · intro hw
    obtain ⟨hne, hnr, u, hvu, huw⟩ := mem_secondNeighbors.mp hw
    have huS : u ∈ S := hclosed (mem_image.mpr ⟨v.val, v.property, hvu⟩)
    have hwS : w ∈ S := hclosed (mem_image.mpr ⟨u, huS, huw⟩)
    apply Finset.mem_map.mpr
    refine ⟨⟨w, hwS⟩, mem_secondNeighbors.mpr ?_, rfl⟩
    refine ⟨?_, hnr, ⟨⟨u, huS⟩, hvu, huw⟩⟩
    intro heq
    exact hne (congrArg Subtype.val heq)

omit [DecidableEq V] in
theorem card_firstNeighbors_induced {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (firstNeighbors (induced r S) v).card = (firstNeighbors r v.val).card := by
  rw [← firstNeighbors_induced_map hclosed v, Finset.card_map]

theorem card_secondNeighbors_induced {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (secondNeighbors (induced r S) v).card = (secondNeighbors r v.val).card := by
  rw [← secondNeighbors_induced_map hclosed v, Finset.card_map]

theorem counterexample_induced {r : V → V → Prop} (hbad : Counterexample r)
    {S : Finset V} (hclosed : image r S ⊆ S) : Counterexample (induced r S) := by
  intro v
  rw [card_secondNeighbors_induced hclosed v, card_firstNeighbors_induced hclosed v]
  exact hbad v.val

theorem OrderMinimal.nonemptyBoundary {r : V → V → Prop}
    (hmin : OrderMinimal r) (hr : IsOriented r) (hbad : Counterexample r) :
    NonemptyBoundary r := by
  classical
  intro S hS hproper
  by_contra hboundary
  have hclosed : image r S ⊆ S := by
    intro w hw
    by_contra hwS
    exact hboundary ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwS⟩⟩
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hpos : 0 < Fintype.card S := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.mpr hS
  have hle := hmin (Fintype.card S) hpos (reindex e (induced r S))
    (isOriented_reindex e (isOriented_induced hr S))
    (counterexample_reindex e (counterexample_induced hbad hclosed))
  have hlt : Fintype.card S < Fintype.card V := by
    rw [Fintype.card_coe]
    exact (Finset.card_lt_iff_ne_univ S).mpr hproper
  exact (not_le_of_gt hlt) hle

theorem NonemptyBoundary.positiveIndegree {r : V → V → Prop}
    (hboundary : NonemptyBoundary r) (hr : IsOriented r)
    (hbad : Counterexample r) : PositiveIndegree r := by
  classical
  intro v
  obtain ⟨w, hvw⟩ := hbad.first_nonempty v
  have hvw' := mem_firstNeighbors.mp hvw
  have hwv : w ≠ v := by
    intro heq
    subst w
    exact hr.loopless v hvw'
  have hnonempty : (Finset.univ.erase v : Finset V).Nonempty :=
    ⟨w, Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩⟩
  have hproper : (Finset.univ.erase v : Finset V) ≠ Finset.univ := by
    intro heq
    have hv : v ∈ (Finset.univ.erase v : Finset V) := heq.symm ▸ Finset.mem_univ v
    exact Finset.notMem_erase v Finset.univ hv
  obtain ⟨x, hx⟩ := hboundary (Finset.univ.erase v) hnonempty hproper
  obtain ⟨hximage, hxnot⟩ := Finset.mem_sdiff.mp hx
  have hxv : x = v := by
    by_contra hne
    exact hxnot (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
  obtain ⟨u, _, hux⟩ := mem_image.mp hximage
  exact ⟨u, hxv ▸ hux⟩

theorem exists_minimal_counterexample [Nonempty V] {r : V → V → Prop}
    (hr : IsOriented r) (hbad : Counterexample r) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : Fin n → Fin n → Prop,
      IsOriented s ∧ Counterexample s ∧ ArcMinimal s ∧
        NonemptyBoundary s ∧ PositiveIndegree s := by
  classical
  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ s : Fin n → Fin n → Prop,
    IsOriented s ∧ Counterexample s
  have hex : ∃ n, P n := by
    refine ⟨Fintype.card V, Fintype.card_pos_iff.mpr inferInstance,
      reindex (Fintype.equivFin V) r, ?_, ?_⟩
    · exact isOriented_reindex (Fintype.equivFin V) hr
    · exact counterexample_reindex (Fintype.equivFin V) hbad
  let n := Nat.find hex
  obtain ⟨hn, t, ht, htb⟩ := Nat.find_spec hex
  have harcs : ∃ a : ℕ, ∃ s : Fin n → Fin n → Prop,
      IsOriented s ∧ Counterexample s ∧ (arcSet s).card = a :=
    ⟨(arcSet t).card, t, ht, htb, rfl⟩
  obtain ⟨s, hs, hsb, hscard⟩ := Nat.find_spec harcs
  have hsmin : ArcMinimal s := by
    intro u hu hub
    rw [hscard]
    exact Nat.find_min' harcs ⟨u, hu, hub, rfl⟩
  have hsorder : OrderMinimal s := by
    intro k hk u hu hub
    simpa only [Fintype.card_fin] using (Nat.find_min' hex ⟨hk, u, hu, hub⟩)
  have hboundary := hsorder.nonemptyBoundary hs hsb
  exact ⟨n, hn, s, hs, hsb, hsmin, hboundary,
    hboundary.positiveIndegree hs hsb⟩

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.exists_minimal_counterexample := @_root_.OAI.SeymourSecondNeighborhood.exists_minimal_counterexample
