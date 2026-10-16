-- Prove2me | solution 1 for OAI.Problem346.flattened_derivative_eq_card_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:55:18.845129+00:00
-- url     : https://prove2.me/submissions/5c27e2b8-99dc-4634-949d-c5affda00737

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/TransferDerivative.lean:L58-L87
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.flattened_derivative_eq_card_smul. The node keeps its source
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
import Theorems.Thm_OAI_Problem346_SlotPolynomial_derivation_polynomial
import Theorems.Thm_OAI_Problem346_SlotPolynomial_polynomial_update_eq

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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FlattenedForm ----
namespace OAI

noncomputable section

namespace Problem346

universe u

variable {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Independent permutations within the rows preserve the flattened form. -/
theorem flattenedSymmetricForm_inner_permute
    (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T (fun p => v (p.1, σ p.1 p.2)) =
      flattenedSymmetricForm T v := by
  apply congrArg T
  funext i
  exact symMonomial_permute b V (σ i) (fun j => v (i, j))

/-- Implicit-parameter factor symmetry used by the transfer sequences. -/
theorem flattenedForm_factor_perm (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (v : Fin a × Fin b → V) :
    flattenedForm T (fun p => v (p.1, σ p.1 p.2)) = flattenedForm T v :=
  flattenedSymmetricForm_inner_permute T σ v

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SlotDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SlotPolynomial

variable {R A S I B : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq S]

variable [Fintype S] [Fintype I]

/-- If all source-labelled slots are interchangeable, the derivative is a single replacement
multiplied by their number. -/
theorem derivation_polynomial_eq_card_smul [DecidableEq B]
    (c : (S → I) → R) (l : S → B) (src dst : B) (t : S) (ht : l t = src)
    (D : Derivation R (MvPolynomial (B × I) R) (MvPolynomial (B × I) R))
    (hD : ∀ b i, D (MvPolynomial.X (b, i)) =
      if b = src then MvPolynomial.X (dst, i) else 0)
    (hc : ∀ s, l s = src → ∀ k, c (k ∘ Equiv.swap s t) = c k) :
    D (polynomial c l) =
      (Finset.univ.filter (fun s => l s = src)).card •
        polynomial c (Function.update l t dst) := by
  classical
  rw [derivation_polynomial c l src dst D hD, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := (Finset.mem_filter.mp hs).2
  exact polynomial_update_eq c l s t dst (hs'.trans ht.symm) (hc s hs')

end Problem346.SlotPolynomial

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.TransferDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

theorem multilinearPolynomial_eq_slotPolynomial
    {S K B V : Type*} [Fintype S] [DecidableEq S] [Fintype K]
    [AddCommGroup V] [Module ℂ V]
    (T : MultilinearMap ℂ (fun _ : S => V) ℂ) (e : K → V) (l : S → B) :
    multilinearPolynomial T e l =
      SlotPolynomial.polynomial (fun k => T (fun s => e (k s))) l := by
  classical
  unfold multilinearPolynomial SlotPolynomial.polynomial
  congr 1
  ext k
  simp

private theorem swap_pair_same_row {A B : Type*} [DecidableEq A] [DecidableEq B]
    (i : A) (j k : B) (p : A × B) :
    Equiv.swap (i, j) (i, k) p =
      (p.1, if p.1 = i then Equiv.swap j k p.2 else p.2) := by
  rcases p with ⟨q, t⟩
  by_cases hq : q = i
  · subst q
    by_cases htj : t = j
    · subst t
      simp
    · by_cases htk : t = k
      · subst t
        simp
      · simp [Equiv.swap_apply_of_ne_of_ne, htj, htk]
  · have h1 : (q,t) ≠ (i,j) := by intro h; exact hq (congrArg Prod.fst h)
    have h2 : (q,t) ≠ (i,k) := by intro h; exact hq (congrArg Prod.fst h)
    simp [Equiv.swap_apply_of_ne_of_ne h1 h2, hq]

/-- The flattened form is invariant under swapping two factors in a single row. -/
theorem flattenedForm_swap_row (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (i : Fin a) (j k : Fin b) (x : Fin a × Fin b → V) :
    flattenedForm T (x ∘ Equiv.swap (i,j) (i,k)) =
      flattenedForm T x := by
  classical
  have h := flattenedForm_factor_perm T
    (fun q => if q = i then Equiv.swap j k else Equiv.refl _) x
  convert h using 1
  congr 1
  funext p
  rw [Function.comp_apply, swap_pair_same_row]
  by_cases hp : p.1 = i <;> simp [hp]

/-- If the source label occurs only in one row, every occurrence gives the same
coordinate-polynomial derivative term, by symmetry of factors in that row. -/
theorem flattened_derivative_eq_card_smul
    (a b : ℕ) (V K B : Type*) [AddCommGroup V] [Module ℂ V]
    [Fintype K] [DecidableEq B]
    (T : SymmetricMultilinearForm a b V) (e : K → V)
    (l : Fin a × Fin b → B) (src dst : B) (i : Fin a) (j : Fin b)
    (hj : l (i,j) = src)
    (hrow : ∀ p, l p = src → p.1 = i)
    (D : Derivation ℂ (MvPolynomial (B × K) ℂ) (MvPolynomial (B × K) ℂ))
    (hD : ∀ q k, D (MvPolynomial.X (q,k)) =
      if q = src then MvPolynomial.X (dst,k) else 0) :
    D (multilinearPolynomial (flattenedForm T) e l) =
      (Finset.univ.filter (fun p => l p = src)).card •
        multilinearPolynomial (flattenedForm T) e
          (Function.update l (i,j) dst) := by
  classical
  let c : ((Fin a × Fin b) → K) → ℂ :=
    fun k => flattenedForm T (fun p => e (k p))
  have hc : ∀ p, l p = src → ∀ k, c (k ∘ Equiv.swap p (i,j)) = c k := by
    intro p hp k
    rcases p with ⟨q,t⟩
    have hq := hrow (q,t) hp
    dsimp at hq
    subst q
    exact flattenedForm_swap_row a b V T i t j (fun p => e (k p))
  have h := SlotPolynomial.derivation_polynomial_eq_card_smul
    c l src dst (i,j) hj D hD hc
  rw [multilinearPolynomial_eq_slotPolynomial, multilinearPolynomial_eq_slotPolynomial]
  exact h

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.flattened_derivative_eq_card_smul := @_root_.OAI.Problem346.flattened_derivative_eq_card_smul
