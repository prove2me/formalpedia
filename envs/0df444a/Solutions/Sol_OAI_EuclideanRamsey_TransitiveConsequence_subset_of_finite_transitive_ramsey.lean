-- Prove2me | solution 1 for OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:01:50.62398+00:00
-- url     : https://prove2.me/submissions/f593fe7a-ff37-4a48-b274-07223c904698

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Transitive.lean:L136-L153
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_EuclideanRamsey_TransitiveConsequence_subset_of_finite_transitive_ramsey) verbatim and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Transitive
import Theorems.Thm_OAI_EuclideanRamsey_TransitiveConsequence_averaged_realCriterion
import Theorems.Thm_OAI_EuclideanRamsey_fieldCriterion_ramsey
import Theorems.Thm_OAI_EuclideanRamsey_full_affine_representative
import Theorems.Thm_OAI_EuclideanRamsey_ramsey_congruent_iff
import Theorems.Thm_OAI_EuclideanRamsey_realCriterion_fieldCriterion

-- ---- from OAI.Combinatorics.EuclideanRamsey.Congruence ----
namespace OAI

universe uIndex uDomain uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

theorem singleton_ramsey {d : ℕ} (a : Fin 1 → Space d) : Ramsey a := by
  intro r hr
  refine ⟨1, by omega, ?_⟩
  intro c
  refine ⟨fun _ => 0, ?_, c 0, ?_⟩
  · intro i j
    have : i = j := Subsingleton.elim _ _
    simp [this]
  · intro i
    rfl

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Transitive ----
namespace OAI

/-! Finite transitive Euclidean configurations and their subsets are Ramsey. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace EuclideanRamsey
namespace TransitiveConsequence

theorem isometric_subconfiguration_ramsey {s d t D : ℕ}
    (a : Fin s → Space d) (hs : 0 < s) (ha : Function.Injective a)
    (y : Fin t → Space D) (hy : IsTransitive y)
    (e : Fin s → Fin t) (he : Congruent a (fun i => y (e i))) : Ramsey a := by
  classical
  by_cases hs1 : s = 1
  · subst s
    exact singleton_ramsey a
  have hs2 : 2 ≤ s := by omega
  obtain ⟨d', hd', b, hb, hab, hspan⟩ := full_affine_representative a hs2 ha
  have hbe : Congruent b (fun i => y (e i)) := by
    intro i j
    exact (he i j).trans (hab i j).symm
  have hreal : RealCriterion b :=
    averaged_realCriterion b hs hspan y hy e hbe
  have hrb : Ramsey b := fieldCriterion_ramsey b hs2 hd' hb
    (realCriterion_fieldCriterion b hreal)
  exact (ramsey_congruent_iff hab).mpr hrb

theorem subset_of_finite_transitive_ramsey {s t D : ℕ}
    (a : Fin s → Space D) (y : Fin t → Space D)
    (hs : 0 < s) (ha : Function.Injective a) (_hy : Function.Injective y)
    (htrans : ∀ i j : Fin t, ∃ σ : Equiv.Perm (Fin t),
      (∀ k l : Fin t, dist (y (σ k)) (y (σ l)) = dist (y k) (y l)) ∧ σ i = j)
    (hsub : Set.range a ⊆ Set.range y) : Ramsey a := by
  classical
  have htrans' : IsTransitive y := by
    intro i j
    obtain ⟨σ, hσ, hij⟩ := htrans i j
    exact ⟨⟨σ, hσ⟩, hij⟩
  have hex (i : Fin s) : ∃ j : Fin t, y j = a i :=
    hsub (Set.mem_range_self i)
  choose e he using hex
  apply isometric_subconfiguration_ramsey a hs ha y htrans' e
  intro i j
  change dist (y (e i)) (y (e j)) = dist (a i) (a j)
  rw [he i, he j]

end TransitiveConsequence
end EuclideanRamsey

end

end OAI

-- ---- mission target ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.TransitiveConsequence
open scoped TensorProduct BigOperators

namespace OAI
namespace EuclideanRamsey
namespace TransitiveConsequence
theorem _root_.solution {s t D : ℕ}
    (a : Fin s → Space D) (y : Fin t → Space D)
    (hs : 0 < s) (ha : Function.Injective a) (_hy : Function.Injective y)
    (htrans : ∀ i j : Fin t, ∃ σ : Equiv.Perm (Fin t),
      (∀ k l : Fin t, dist (y (σ k)) (y (σ l)) = dist (y k) (y l)) ∧ σ i = j)
    (hsub : Set.range a ⊆ Set.range y) : Ramsey a := by
  first
    | exact OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey a y hs ha _hy htrans hsub
    | exact OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey
    | (apply OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey <;> assumption)
    | (intros; apply OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey <;> assumption)
end TransitiveConsequence
end EuclideanRamsey
end OAI
