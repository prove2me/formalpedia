-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.copy_incidence_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:18:47.891721+00:00
-- url     : https://prove2.me/submissions/68650f7e-89c4-4bae-8a39-ae15a26eaf71

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/CopyOrbits.lean:L166-L188
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.copy_incidence_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits

-- ---- from OAI.Combinatorics.GraphThreshold.CopyOrbits ----
namespace OAI

/-!
# Distinct subset copies under a finite group action

Copies are distinct orbit elements, not group elements or labeled embeddings.
All counting and probability statements therefore retain the stabilizer
multiplicities correctly, including for the empty subset.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace LeanBlast.SecondKahnKalai

universe u v

variable (G : Type u) [Group G] [Fintype G]
variable {X : Type v} [DecidableEq X] [MulAction G X]

/-- Acting permutes the distinct orbit elements with no multiplicity. -/
theorem sum_copyOrbit_smul (g : G) (F : Finset X) (f : Finset X → ℕ) :
    (∑ J ∈ copyOrbit G F, f (g • J)) = ∑ J ∈ copyOrbit G F, f J := by
  calc
    _ = ∑ J : OrbitCopy G F, f (g • J.val) :=
      (Finset.sum_coe_sort (copyOrbit G F) (fun J => f (g • J))).symm
    _ = ∑ J : OrbitCopy G F, f J.val :=
      (orbitCopyEquiv G g F).sum_comp (fun J : OrbitCopy G F => f J.val)
    _ = _ := Finset.sum_coe_sort (copyOrbit G F) f

theorem internalCopyCount_smul (g : G) (I F : Finset X) :
    internalCopyCount G (g • I) F = internalCopyCount G I F := by
  have h := sum_copyOrbit_smul G g F (fun J => if J ⊆ g • I then 1 else 0)
  simpa only [Finset.smul_finset_subset_smul_finset_iff, Finset.sum_boole,
    Nat.cast_id, internalCopyCount] using h.symm

theorem containingCopyCount_smul (g : G) (I U : Finset X) :
    containingCopyCount G I (g • U) = containingCopyCount G I U := by
  have h := sum_copyOrbit_smul G g I (fun J => if g • U ⊆ J then 1 else 0)
  simpa only [Finset.smul_finset_subset_smul_finset_iff, Finset.sum_boole,
    Nat.cast_id, containingCopyCount] using h.symm

theorem internalCopyCount_eq_of_mem_copyOrbit {I I₀ F : Finset X}
    (hI : I₀ ∈ copyOrbit G I) : internalCopyCount G I₀ F = internalCopyCount G I F := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hI
  exact internalCopyCount_smul G g I F

theorem containingCopyCount_eq_of_mem_copyOrbit {I F F₀ : Finset X}
    (hF : F₀ ∈ copyOrbit G F) :
    containingCopyCount G I F₀ = containingCopyCount G I F := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hF
  exact containingCopyCount_smul G g I F

/-- Double-count containment pairs of distinct orbit copies. -/
theorem copy_incidence_identity (I F : Finset X) :
    orbitCount G F * containingCopyCount G I F =
      orbitCount G I * internalCopyCount G I F := by
  have h : (∑ U ∈ copyOrbit G F, ∑ J ∈ copyOrbit G I, if U ⊆ J then (1 : ℕ) else 0) =
      ∑ J ∈ copyOrbit G I, ∑ U ∈ copyOrbit G F, if U ⊆ J then (1 : ℕ) else 0 :=
    Finset.sum_comm
  simp only [Finset.sum_boole] at h
  change (∑ U ∈ copyOrbit G F, containingCopyCount G I U) =
    ∑ J ∈ copyOrbit G I, internalCopyCount G J F at h
  have hleft : (∑ U ∈ copyOrbit G F, containingCopyCount G I U) =
      orbitCount G F * containingCopyCount G I F := by
    calc
      _ = ∑ _U ∈ copyOrbit G F, containingCopyCount G I F :=
        Finset.sum_congr rfl (fun _ hU => containingCopyCount_eq_of_mem_copyOrbit G hU)
      _ = _ := by simp [orbitCount]
  have hright : (∑ J ∈ copyOrbit G I, internalCopyCount G J F) =
      orbitCount G I * internalCopyCount G I F := by
    calc
      _ = ∑ _J ∈ copyOrbit G I, internalCopyCount G I F :=
        Finset.sum_congr rfl (fun _ hJ => internalCopyCount_eq_of_mem_copyOrbit G hJ)
      _ = _ := by simp [orbitCount]
  rwa [hleft, hright] at h

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators Pointwise


theorem solution.{u,v} : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.copy_incidence_identity.{u,v} := @_root_.OAI.LeanBlast.SecondKahnKalai.copy_incidence_identity.{u,v}
