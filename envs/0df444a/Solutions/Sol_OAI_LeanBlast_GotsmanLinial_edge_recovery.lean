-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.edge_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:16:54.599548+00:00
-- url     : https://prove2.me/submissions/bb4ee978-c0a0-47f7-b748-b61df0d70916

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean:L177-L201
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.edge_recovery. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_adjacent_iff_hammingDist_eq_one
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_anticommutator_energy_ge_selected
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_twice_mass_sub_neighbor_le_distance

-- ---- from OAI.Combinatorics.GotsmanLinial.SignParity ----
namespace OAI

/-!
# Removing threshold zeros and turning sensitive edges into constant-sign edges

All graph pairs are ordered. The cube coordinates are the real
signs encoded by `Bool` in the public statement.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

theorem orderedNeighborPairs_eq_map {n : ℕ} :
    orderedNeighborPairs n = Finset.univ.map (directedEdgeEmbedding n) := by
  classical
  ext e
  constructor
  · intro he
    have hd : hammingDist e.1 e.2 = 1 := (Finset.mem_filter.mp he).2
    obtain ⟨i, hi⟩ := (adjacent_iff_hammingDist_eq_one e.1 e.2).mpr hd
    exact Finset.mem_map.mpr ⟨(i, e.1), Finset.mem_univ _, Prod.ext rfl hi⟩
  · intro he
    obtain ⟨⟨i, x⟩, _, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hammingDist_flip i x⟩

/-- The `n * 2^n` count includes both orientations of every cube edge. -/
theorem card_orderedNeighborPairs (n : ℕ) :
    (orderedNeighborPairs n).card = n * 2 ^ n := by
  rw [orderedNeighborPairs_eq_map]
  simp

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.EdgeRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Recovering constant-sign edges from grading energy

The counting argument is separated from construction of the grading matrix.
Its hypotheses are explicit entrywise, total-energy, and distance-energy facts.
No edge-count or anticommutator conclusion is assumed.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- The sum of the nonnegative neighbor deficits is controlled by twice the
distance-zero energy. Equivalently, `A₀ + F ≤ 2 A₀`. -/
theorem neighbor_deficit_le_twice_zero_mass (d : α → ℕ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (htotal : (∑ a, w a) = ((distanceShell d 1).card : ℝ) / 4)
    (henergy : (∑ a, (d a : ℝ) * w a) ≤ ∑ a, w a) :
    (∑ a ∈ distanceShell d 1, ((1 / 4 : ℝ) - w a)) ≤
      2 * (∑ a ∈ distanceShell d 0, w a) := by
  have hpoint := twice_mass_sub_neighbor_le_distance d w hw
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Restricting the nonnegative deficits to any chosen neighbor subset gives
the counting bound needed before applying the anticommutator identity. -/
theorem selected_neighbor_card_le_eight_mass (d : α → ℕ) (w : α → ℝ)
    (s : Finset α) (hs : s ⊆ distanceShell d 1)
    (hw : ∀ a, 0 ≤ w a)
    (hcap : ∀ a ∈ distanceShell d 1, w a ≤ (1 / 4 : ℝ))
    (htotal : (∑ a, w a) = ((distanceShell d 1).card : ℝ) / 4)
    (henergy : (∑ a, (d a : ℝ) * w a) ≤ ∑ a, w a) :
    (s.card : ℝ) ≤ 8 * ((∑ a ∈ distanceShell d 0, w a) + ∑ a ∈ s, w a) := by
  have hrestrict := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun a ha _ => sub_nonneg.mpr (hcap a ha))
  have hdeficit := neighbor_deficit_le_twice_zero_mass d w hw htotal henergy
  have hmass : 0 ≤ ∑ a ∈ s, w a := Finset.sum_nonneg fun a _ => hw a
  have hselected : (∑ a ∈ s, ((1 / 4 : ℝ) - w a)) =
      (s.card : ℝ) / 4 - ∑ a ∈ s, w a := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hselected] at hrestrict
  linarith

/-- Abstract edge recovery from the exact finite matrix energy hypotheses.
The chosen set may be any subset of constant-sign distance-one pairs. -/
theorem edge_recovery_for_subset [DecidableEq ι]
    (ρ : ι → ι → ℕ) (hzero : ∀ i j, ρ i j = 0 → i = j)
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (s : Finset (ι × ι))
    (hs : s ⊆ distanceShell (fun p : ι × ι => ρ p.1 p.2) 1)
    (hsign : ∀ p ∈ s, h p.1 = h p.2)
    (hcap : ∀ i j, ρ i j = 1 → ‖M i j‖ ^ 2 ≤ (1 / 4 : ℝ))
    (htotal : hsNormSq M =
      ((distanceShell (fun p : ι × ι => ρ p.1 p.2) 1).card : ℝ) / 4)
    (henergy : (∑ i, ∑ j, (ρ i j : ℝ) * ‖M i j‖ ^ 2) ≤ hsNormSq M) :
    (s.card : ℝ) ≤ 2 * hsNormSq
      (M * Matrix.diagonal (fun i => (h i : ℂ)) +
        Matrix.diagonal (fun i => (h i : ℂ)) * M) := by
  have hcount := selected_neighbor_card_le_eight_mass
    (fun p : ι × ι => ρ p.1 p.2) (fun p => ‖M p.1 p.2‖ ^ 2) s hs
    (fun p => sq_nonneg _) (fun p hp => hcap p.1 p.2 (by simpa only [mem_distanceShell] using hp))
    (by simpa only [hsNormSq, Fintype.sum_prod_type] using htotal)
    (by simpa only [hsNormSq, Fintype.sum_prod_type] using henergy)
  have hanti := anticommutator_energy_ge_selected ρ hzero M h hh s hs hsign
  linarith

/-- The edge-recovery inequality on the Boolean cube, from the three
matrix facts established by the grading and commutator constructions. -/
theorem edge_recovery {n : ℕ} (M : Matrix (Cube n) (Cube n) ℂ)
    (h : Cube n → ℝ) (hh : ∀ x, h x = 1 ∨ h x = -1)
    (htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4)
    (hdistance : (∑ x, ∑ y, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M)
    (hcap : ∀ x y, x ≠ y → ‖M x y‖ ^ 2 ≤ (1 / 4 : ℝ)) :
    ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * Matrix.diagonal (fun x => (h x : ℂ)) +
        Matrix.diagonal (fun x => (h x : ℂ)) * M) := by
  classical
  apply edge_recovery_for_subset (fun x y : Cube n => hammingDist x y)
    (fun _ _ hxy => hammingDist_eq_zero.mp hxy) M h hh (orderedConstantEdges h)
  · exact Finset.filter_subset _ _
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro x y hxy
    apply hcap x y
    intro heq
    subst y
    simp only [hammingDist_self, Nat.zero_ne_one] at hxy
  · change hsNormSq M = ((orderedNeighborPairs n).card : ℝ) / 4
    rw [card_orderedNeighborPairs]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using htotal
  · exact hdistance

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.edge_recovery := @_root_.OAI.LeanBlast.GotsmanLinial.edge_recovery
