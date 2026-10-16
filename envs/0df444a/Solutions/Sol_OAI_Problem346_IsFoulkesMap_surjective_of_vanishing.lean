-- Prove2me | solution 1 for OAI.Problem346.IsFoulkesMap.surjective_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:19:07.778822+00:00
-- url     : https://prove2.me/submissions/a8cc9bff-0b2b-4623-90ef-f6802392c30c

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Annihilator.lean:L12-L34
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.IsFoulkesMap.surjective_of_vanishing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Theorems.Thm_OAI_Problem346_linearMap_eq_zero_of_symMonomial

-- ---- from OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear ----
namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace Problem346

theorem symMonomial_permute (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (σ : Equiv.Perm (Fin n)) (x : Fin n → V) :
    symMonomial n V (fun i => x (σ i)) = symMonomial n V x := by
  apply Subtype.ext
  exact Equiv.prod_comp σ (fun i => SymmetricAlgebra.ι ℂ V (x i))

theorem monomialFunctional_symmetric (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) :
    IsSymmetricMultilinearForm a b V (monomialFunctional a b V φ) := by
  intro σ x
  simp only [monomialFunctional_apply, symMonomial_permute]

theorem monomialFunctional_eq_zero_iff (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) :
    monomialFunctional a b V φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    apply linearMap_eq_zero_of_symMonomial
    intro x
    exact congrArg (fun T : SymmetricMultilinearForm a b V => T x) h
  · rintro rfl
    rfl

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FoulkesDiagonal ----
namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

variable (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

 theorem foulkesFormula_diagonal (u : Fin b → V) :
    foulkesFormula a b V (fun j _ => u j) =
      symMonomial a (SymPow b V) (fun _ => symMonomial b V u) := by
  classical
  simp [foulkesFormula, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    Nat.factorial_ne_zero]

 theorem IsFoulkesMap.map_diagonal
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V))
    (hμ : IsFoulkesMap a b V μ) (u : Fin b → V) :
    μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j))) =
      symMonomial a (SymPow b V) (fun _ => symMonomial b V u) := by
  rw [hμ, foulkesFormula_diagonal]

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.Annihilator ----
namespace OAI

noncomputable section

universe u

namespace Problem346

/-- The diagonal vanishing criterion forces every canonical Foulkes map to be
surjective. This dual separation argument does not require finite dimension. -/
theorem IsFoulkesMap.surjective_of_vanishing (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V))
    (hμ : IsFoulkesMap a b V μ)
    (hvan : ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) → T = 0) :
    Function.Surjective μ := by
  apply LinearMap.dualMap_injective_iff.mp
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro φ hφ
  change φ = 0
  rw [LinearMap.mem_ker] at hφ
  apply (monomialFunctional_eq_zero_iff a b V φ).mp
  apply hvan _ (monomialFunctional_symmetric a b V φ)
  intro u
  rw [monomialFunctional_apply, ← hμ.map_diagonal a b V μ u]
  have h := congrArg (fun L : SymPow b (SymPow a V) →ₗ[ℂ] ℂ =>
    L (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j)))) hφ
  exact h

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346


theorem solution.{u} : type_of% @_root_.OAI.Problem346.IsFoulkesMap.surjective_of_vanishing.{u} := @_root_.OAI.Problem346.IsFoulkesMap.surjective_of_vanishing.{u}
