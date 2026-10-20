-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.subsetDeficit_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:46:16.994011+00:00
-- url     : https://prove2.me/submissions/bcf1dcfe-6c9a-4db4-ae73-309697f1aa06

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/SubsetDeficit.lean:L44-L58
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.subsetDeficit_of_minimal. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Theorems.Thm_OAI_SeymourSecondNeighborhood_deficitPotential_step
import Theorems.Thm_OAI_SeymourSecondNeighborhood_strict_deficit_of_augmentation

-- ---- from OAI.Combinatorics.SecondNeighborhood.SubsetDeficit ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deficitPotential_terminal (r : V → V → Prop) (S : Finset V) :
    deficitPotential r S (image r S \ S) =
      (image r (image r S) \ image r S).card := by
  classical
  have hsplit : (image r S ∩ S) ∪ (image r S \ S) = image r S := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).1
      · exact (Finset.mem_sdiff.mp hv).1
    · intro hv
      by_cases hs : v ∈ S
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hv, hs⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hv, hs⟩))
  unfold deficitPotential
  rw [hsplit]
  congr 1
  ext v
  constructor
  · intro hv
    obtain ⟨hpath, hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨u, hu, huv⟩ := mem_image.mp hpath
    exact Finset.mem_sdiff.mpr
      ⟨mem_image.mpr ⟨u, (Finset.mem_sdiff.mp hu).1, huv⟩, hnot⟩
  · intro hv
    obtain ⟨hpath, hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨u, hu, huv⟩ := mem_image.mp hpath
    have huS : u ∉ S := by
      intro huS
      exact hnot (mem_image.mpr ⟨u, huS, huv⟩)
    exact Finset.mem_sdiff.mpr
      ⟨mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, huS⟩, huv⟩, hnot⟩

theorem subsetDeficit_of_minimal {r : V → V → Prop}
    (hr : IsOriented r) (hcounter : Counterexample r)
    (hminimal : ArcMinimal r) (hboundary : NonemptyBoundary r) :
    SubsetDeficit r := by
  classical
  intro S hS hproper
  have hE := hboundary S hS hproper
  have hg : deficitPotential r S (image r S \ S) < (image r S \ S).card := by
    apply strict_deficit_of_augmentation (image r S \ S) hE
      (deficitPotential r S)
    · simp [deficitPotential]
    · intro T hT hTproper
      exact deficitPotential_step r hr hcounter hminimal S T hT hTproper
  rw [deficitPotential_terminal] at hg
  exact hg

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.subsetDeficit_of_minimal := @_root_.OAI.SeymourSecondNeighborhood.subsetDeficit_of_minimal
