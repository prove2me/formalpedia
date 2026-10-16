-- Prove2me | solution 1 for OAI.Problem346.span_purePowers_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:05:42.439444+00:00
-- url     : https://prove2.me/submissions/0e6ad1d9-77d7-4ac0-ae05-b22cb5755294

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/PowerSpan.lean:L13-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.span_purePowers_eq_top. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Theorems.Thm_OAI_Problem346_linearMap_eq_zero_of_symMonomial
import Theorems.Thm_OAI_Problem346_symmetric_multilinear_eq_zero_of_diagonal

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

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.PowerSpan ----
namespace OAI

noncomputable section

namespace Problem346

universe u v

/-- Pure powers span each symmetric power, including degree zero. -/
theorem span_purePowers_eq_top (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    Submodule.span ℂ (Set.range (fun x : V => symMonomial b V (fun _ => x))) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm
  · intro f hf
    change f = 0
    apply linearMap_eq_zero_of_symMonomial b V f
    have hz : f.compMultilinearMap (symMonomialMultilinear b V) = 0 := by
      apply symmetric_multilinear_eq_zero_of_diagonal
      · intro σ x
        change f (symMonomial b V (fun i => x (σ i))) = f (symMonomial b V x)
        rw [symMonomial_permute]
      · intro x
        exact (Submodule.mem_dualAnnihilator f).mp hf _
          (Submodule.subset_span ⟨x, rfl⟩)
    intro x
    exact DFunLike.congr_fun hz x
  · exact bot_le

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346


theorem solution.{u} : type_of% @_root_.OAI.Problem346.span_purePowers_eq_top.{u} := @_root_.OAI.Problem346.span_purePowers_eq_top.{u}
