-- Prove2me | solution 1 for OAI.Problem346.vanishing_induction_from_transfer_steps
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:24:21.953987+00:00
-- url     : https://prove2.me/submissions/434022e5-1ce1-4521-8e30-449ad6d8d97d

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Vanishing.lean:L13-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.vanishing_induction_from_transfer_steps. The node keeps its source
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
import Theorems.Thm_OAI_Problem346_vanishing_on_products_one

-- ---- from OAI.RepresentationTheory.FoulkesHowe.VanishingInduction ----
namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Fixing the first argument and pulling back all other arguments preserves symmetry. -/
theorem symmetric_form_curry_comp {r b m : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V)
    (hT : IsSymmetricMultilinearForm (r+1) b V T)
    (z : SymPow b V) (L : SymPow m V →ₗ[ℂ] SymPow b V) :
    IsSymmetricMultilinearForm r m V ((T.curryLeft z).compLinearMap (fun _ => L)) := by
  intro σ x
  let τ : Equiv.Perm (Fin (r+1)) :=
    (finSuccEquiv r).trans ((Equiv.optionCongr σ).trans (finSuccEquiv r).symm)
  have heq : (fun i : Fin (r+1) => (Fin.cons z (fun j => L (x j)) :
      Fin (r+1) → SymPow b V) (τ i)) =
      (Fin.cons z (fun i => L (x (σ i))) : Fin (r+1) → SymPow b V) := by
    funext i
    cases i using Fin.cases <;> simp [τ]
  simpa only [MultilinearMap.compLinearMap_apply, MultilinearMap.curryLeft_apply, heq]
    using hT τ (Fin.cons z (fun i => L (x i)))

theorem lowerProductForm_symmetric (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (hT : IsSymmetricMultilinearForm (r+1) (r+m) V T) (x t : V) :
    IsSymmetricMultilinearForm r m V (lowerProductForm r m T x t) :=
  symmetric_form_curry_comp T hT _ _

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.Vanishing ----
namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The induction on the number of slots, isolated from the two polynomial
transfer arguments. The first argument packages the binary-pencil identity and
the first transfer; the second is the common-power-removal transfer. -/
theorem vanishing_induction_from_transfer_steps
    (firstTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ y : Fin (r+m) → V, T (fun _ => symMonomial (r+m) V y) = 0) →
      ∀ x t : V, ∀ y : Fin m → V,
        lowerProductForm r m T x t (fun _ => symMonomial m V y) = 0)
    (secondTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ x t : V, ∀ Q : Fin r → SymPow m V, lowerProductForm r m T x t Q = 0) →
      ∀ v : Fin (r+1) → V,
        T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0)
    (purePowerExt : ∀ a b : ℕ, ∀ T : SymmetricMultilinearForm a b V,
      (∀ v : Fin a → V, T (fun i => symMonomial b V (fun _ => v i)) = 0) → T = 0) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a*(a-1) ≤ b →
      ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ y : Fin b → V, T (fun _ => symMonomial b V y) = 0) → T = 0 := by
  intro a
  induction a with
  | zero =>
      intro b ha
      omega
  | succ r ih =>
      intro b ha hb hab T hT hdiag
      by_cases hr : r = 0
      · subst r
        exact vanishing_on_products_one V b T hdiag
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hrb : r ≤ b := by
        have hmul : r ≤ (r+1)*r := by nlinarith
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hmul.trans hab
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrb
      have hbound : (r+1)*r ≤ r+m := by simpa only [Nat.succ_eq_add_one,
        Nat.add_sub_cancel] using hab
      have hm : 0 < m := by nlinarith
      have hmrange : r*(r-1) ≤ m := by
        have hsub : r-1 ≤ r := Nat.sub_le ..
        have hmul : r*(r-1) ≤ r*r := Nat.mul_le_mul_left r hsub
        nlinarith
      have hrestricted : ∀ x t : V, lowerProductForm r m T x t = 0 := by
        intro x t
        exact ih m hrpos hm hmrange (lowerProductForm r m T x t)
          (lowerProductForm_symmetric r m T hT x t)
          (firstTransfer r m hrpos hm hbound T hT hdiag x t)
      apply purePowerExt (r+1) (r+m) T
      apply secondTransfer r m hrpos hm hbound T hT
      intro x t Q
      rw [hrestricted x t]
      rfl

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346


theorem solution.{u} : type_of% @_root_.OAI.Problem346.vanishing_induction_from_transfer_steps.{u} := @_root_.OAI.Problem346.vanishing_induction_from_transfer_steps.{u}
