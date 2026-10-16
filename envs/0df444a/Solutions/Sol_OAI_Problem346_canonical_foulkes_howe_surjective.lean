-- Prove2me | solution 1 for OAI.Problem346.canonical_foulkes_howe_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:18:49.512929+00:00
-- url     : https://prove2.me/submissions/893a9d57-2894-4ddb-a6d5-c67e78f4f762

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Stabilization.lean:L15-L23
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Problem346.canonical_foulkes_howe_surjective.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Problem346_canonical_foulkes_howe_surjective) verbatim and is proved by it.
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap
import Theorems.Thm_OAI_Problem346_IsFoulkesMap_surjective_of_vanishing
import Theorems.Thm_OAI_Problem346_SecondTransfer_second_transfer
import Theorems.Thm_OAI_Problem346_binary_power_factorization
import Theorems.Thm_OAI_Problem346_exists_symPow_lift_on_spanning
import Theorems.Thm_OAI_Problem346_firstPolynomial_zero_of_final
import Theorems.Thm_OAI_Problem346_plethysm_linearMap_ext
import Theorems.Thm_OAI_Problem346_span_purePowers_eq_top
import Theorems.Thm_OAI_Problem346_symmetric_diagonal_mixed_zero
import Theorems.Thm_OAI_Problem346_vanishing_induction_from_transfer_steps

-- ---- from OAI.RepresentationTheory.FoulkesHowe.Spanning ----
namespace OAI

noncomputable section
open scoped BigOperators
universe u v
namespace Problem346

/-- The defining formula determines a Foulkes map uniquely. -/
theorem IsFoulkesMap.unique (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    {f g : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    (hf : IsFoulkesMap a b V f) (hg : IsFoulkesMap a b V g) : f = g := by
  apply plethysm_linearMap_ext a b V
  intro x
  exact (hf x).trans (hg x).symm

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FoulkesSymmetries ----
namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

/-- Reindexing the factors of a symmetric monomial does not change it. -/
theorem symMonomial_perm_reindex (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin n → V)
    (τ : Equiv.Perm (Fin n)) :
    symMonomial n V (fun i => v (τ i)) = symMonomial n V v := by
  apply Subtype.ext
  exact Equiv.prod_comp τ (fun i => SymmetricAlgebra.ι ℂ V (v i))

/-- The canonical averaging formula is invariant under independent permutations
of the entries in each row. -/
theorem foulkesFormula_inner_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V)
    (τ : Fin b → Equiv.Perm (Fin a)) :
    foulkesFormula a b V (fun j i => v j (τ j i)) =
      foulkesFormula a b V v := by
  classical
  unfold foulkesFormula
  congr 1
  exact Fintype.sum_equiv
    (Equiv.piCongrRight (fun j => Equiv.mulLeft (τ j))) _ _ (fun σ => rfl)

/-- The canonical averaging formula is invariant under permutation of rows. -/
theorem foulkesFormula_outer_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V)
    (τ : Equiv.Perm (Fin b)) :
    foulkesFormula a b V (fun j i => v (τ j) i) =
      foulkesFormula a b V v := by
  classical
  unfold foulkesFormula
  congr 1
  apply Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl (Equiv.Perm (Fin a))))
  intro σ
  congr 1
  funext i
  simpa using symMonomial_perm_reindex b V
    (fun j => v j (σ (τ.symm j) i)) τ

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.CanonicalMap ----
namespace OAI

noncomputable section
namespace Problem346

theorem foulkesRowFormSpanning_symmetric (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V) (j : Fin b)
    (σ : Equiv.Perm (Fin a)) (u : Fin a → V) :
    foulkesRowFormSpanning a b V v j (fun i => u (σ i)) =
      foulkesRowFormSpanning a b V v j u := by
  classical
  rw [foulkesRowFormSpanning_apply, foulkesRowFormSpanning_apply]
  have h := foulkesFormula_inner_permute a b V (Function.update v j u)
    (Function.update (fun _ => Equiv.refl (Fin a)) j σ)
  convert h using 1
  congr 1
  funext k i
  by_cases hkj : k = j
  · subst k
    simp
  · simp [Function.update_of_ne hkj]

/-- The specified canonical formula defines a linear map in every bidegree. -/
theorem exists_foulkesMap_from_spanning (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] :
    ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
      IsFoulkesMap a b V μ := by
  classical
  apply exists_symPow_lift_on_spanning (symMonomial a V) (span_symMonomial a V)
    (foulkesFormula a b V)
  · intro v j
    obtain ⟨L, hL⟩ := exists_symPow_lift (foulkesRowFormSpanning a b V v j)
      (foulkesRowFormSpanning_symmetric a b V v j)
    exact ⟨L, fun u => (hL u).trans (foulkesRowFormSpanning_apply a b V v j u)⟩
  · intro σ v
    exact foulkesFormula_outer_permute a b V v σ

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.Surjectivity ----
namespace OAI

noncomputable section
namespace Problem346

/-- Existence, surjectivity, and uniqueness reduce entirely to the vanishing theorem. -/
theorem canonical_surjective_unique_of_vanishing (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V]
    (hvan : ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) → T = 0) :
    ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
      IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧
      ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
        IsFoulkesMap a b V ν → ν = μ := by
  obtain ⟨μ, hμ⟩ := exists_foulkesMap_from_spanning a b V
  exact ⟨μ, hμ, IsFoulkesMap.surjective_of_vanishing a b V μ hμ hvan,
    fun ν hν => IsFoulkesMap.unique a b V hν hμ⟩

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.BinaryFactorization ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- In the symmetric algebra, a binary sum of pure powers is a product of vectors. -/
theorem symMonomialRaw_binary_power (V : Type*) [AddCommGroup V] [Module ℂ V]
    (r : ℕ) (hr : 0 < r) (x y : V) (c : ℂ) :
    ∃ v : Fin r → V, symMonomialRaw r V v =
      (SymmetricAlgebra.ι ℂ V x) ^ r + c • (SymmetricAlgebra.ι ℂ V y) ^ r := by
  obtain ⟨z, hz⟩ := binary_power_factorization r hr
    (SymmetricAlgebra.ι ℂ V x) (SymmetricAlgebra.ι ℂ V y) c
  refine ⟨fun i => x - z i • y, ?_⟩
  simpa only [symMonomialRaw, map_sub, map_smul] using hz

/-- Multiplying a split binary power by a product remains a product, with the exact degree. -/
theorem symMonomialRaw_binary_power_mul (V : Type*) [AddCommGroup V] [Module ℂ V]
    (r m : ℕ) (hr : 0 < r) (x y : V) (c : ℂ) (u : Fin m → V) :
    ∃ v : Fin (r + m) → V, symMonomialRaw (r + m) V v =
      ((SymmetricAlgebra.ι ℂ V x) ^ r + c • (SymmetricAlgebra.ι ℂ V y) ^ r) *
        symMonomialRaw m V u := by
  obtain ⟨w, hw⟩ := symMonomialRaw_binary_power V r hr x y c
  refine ⟨Fin.append w u, ?_⟩
  rw [← hw]
  simp only [symMonomialRaw, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- The split binary form is a genuine product in the prescribed symmetric-power subtype. -/
theorem symMonomial_binary_power_mul (V : Type*) [AddCommGroup V] [Module ℂ V]
    (r m : ℕ) (hr : 0 < r) (x y : V) (c : ℂ) (u : Fin m → V) :
    ∃ v : Fin (r + m) → V, symMonomial (r + m) V v =
      symMonomial (r + m) V (Fin.append (fun _ : Fin r => x) u) +
        c • symMonomial (r + m) V (Fin.append (fun _ : Fin r => y) u) := by
  obtain ⟨v, hv⟩ := symMonomialRaw_binary_power_mul V r m hr x y c u
  refine ⟨v, Subtype.ext ?_⟩
  change symMonomialRaw (r + m) V v = _
  rw [hv]
  simp only [symMonomial, Submodule.coe_add, Submodule.coe_smul, symMonomialRaw,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, add_mul, smul_mul_assoc]

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.DiagonalCoefficient ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- The same coefficient extraction with the distinguished slot placed first. -/
theorem symmetric_diagonal_cons_zero {r : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin (r + 1) => E) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin (r + 1))) (v : Fin (r + 1) → E),
      T (fun k => v (σ k)) = T v)
    (x y : E) (h : ∀ c : ℂ, T (fun _ => x + c • y) = 0) :
    T (Fin.cons y (fun _ : Fin r => x)) = 0 := by
  have hz := symmetric_diagonal_mixed_zero T hsym x y 0 h
  convert hz using 1
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.BinaryVanishing ----
namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The split-pencil consequence of diagonal vanishing, expressed using the
graded multiplication and first-slot convention of the induction. -/
theorem binary_diagonal_to_mixed_products (r m : ℕ) (hr : 0 < r)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (hT : IsSymmetricMultilinearForm (r+1) (r+m) V T)
    (hdiag : ∀ y : Fin (r+m) → V, T (fun _ => symMonomial (r+m) V y) = 0)
    (x t : V) (y : Fin m → V) :
    T (Fin.cons
      (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
      (fun _ : Fin r =>
        symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0 := by
  apply symmetric_diagonal_cons_zero T hT
  intro c
  obtain ⟨v, hv⟩ := symMonomial_binary_power_mul V r m hr x t c y
  simp only [symPowMul_symMonomial]
  rw [← hv]
  exact hdiag v

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.MultilinearPolynomial ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

universe uι uκ uβ uV
variable {ι : Type uι} {κ : Type uκ} {β : Type uβ} {V : Type uV}
variable [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℂ V]

/-- Evaluation of the multilinear polynomial on arbitrary coordinate assignments. -/
theorem eval_multilinearPolynomial
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) (z : β × κ → ℂ) :
    MvPolynomial.eval z (multilinearPolynomial L e block) =
      L (fun i => ∑ k, z (block i, k) • e k) := by
  classical
  simp only [multilinearPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, MvPolynomial.eval_X]
  rw [L.map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [L.map_smul_univ]
  simp only [smul_eq_mul]
  exact mul_comm _ _

/-- With basis coordinates, evaluation is literal evaluation on the chosen vector blocks. -/
theorem eval_multilinearPolynomial_basis
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : Module.Basis κ ℂ V) (block : ι → β) (v : β → V) :
    MvPolynomial.eval (fun z : β × κ => e.repr (v z.1) z.2)
      (multilinearPolynomial L e block) = L (fun i => v (block i)) := by
  rw [eval_multilinearPolynomial]
  simp only [e.sum_repr]

/-- Pointwise vanishing on vector blocks implies the corresponding polynomial identity. -/
theorem multilinearPolynomial_eq_zero
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β)
    (h : ∀ v : β → V, L (fun i => v (block i)) = 0) :
    multilinearPolynomial L e block = 0 := by
  apply MvPolynomial.funext
  intro z
  rw [eval_multilinearPolynomial, map_zero]
  exact h (fun j => ∑ k, z (j, k) • e k)

/-- Conversely, a polynomial identity gives the vector-valued identity by basis evaluation. -/
theorem multilinearPolynomial_eq_zero_iff
    (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : Module.Basis κ ℂ V) (block : ι → β) :
    multilinearPolynomial L e block = 0 ↔
      ∀ v : β → V, L (fun i => v (block i)) = 0 := by
  constructor
  · intro h v
    rw [← eval_multilinearPolynomial_basis L e block v, h, map_zero]
  · exact multilinearPolynomial_eq_zero L e block

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.TransferEndpoints ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- Evaluation of the initial label configuration. -/
theorem firstLabel_initial_form {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V) (y : Fin m → V) :
    flattenedForm T (fun p => firstVectors x t y (firstLabel r m 0 p)) =
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) := by
  rw [flattenedForm_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => exact firstLabel_initial_monomial r m x t y
  | succ i => exact firstLabel_other_monomial r m 0 x t y i

/-- Evaluation of the terminal label configuration, with t^r times the common product. -/
theorem firstLabel_final_form {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V) (y : Fin m → V) :
    flattenedForm T (fun p => firstVectors x t y (firstLabel r m m p)) =
      T (Fin.cons (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) := by
  rw [flattenedForm_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => exact firstLabel_final_monomial r m x t y
  | succ i => exact firstLabel_other_monomial r m m x t y i

/-- The binary identity makes the terminal polynomial zero. -/
theorem firstPolynomial_final_eq_zero {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (h : ∀ (x t : V) (y : Fin m → V),
      T (Fin.cons (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0) :
    firstPolynomial T e m = 0 := by
  apply multilinearPolynomial_eq_zero
  intro v
  have hv : firstVectors (v none) (v (some none)) (fun j => v (some (some j))) = v := by
    funext b
    cases b with
    | none => rfl
    | some b => cases b <;> rfl
  rw [← hv]
  rw [firstLabel_final_form]
  exact h _ _ _

/-- A zero initial polynomial gives the freed-last-slot identity. -/
theorem firstPolynomial_initial_vanishing {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : Module.Basis κ ℂ V)
    (h : firstPolynomial T e 0 = 0) (x t : V) (y : Fin m → V) :
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0 := by
  rw [← firstLabel_initial_form]
  have hp := (multilinearPolynomial_eq_zero_iff (flattenedForm T) e
    (firstLabel r m 0)).mp h
  exact hp (firstVectors x t y)

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FirstTransfer ----
namespace OAI

noncomputable section

namespace Problem346

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- The first transfer in the stabilization argument: the common product can be
removed from the distinguished argument, while the other arguments remain fixed.
No outer symmetry or positive-degree assumptions are needed for this step. -/
theorem first_transfer [FiniteDimensional ℂ V] {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ (x t : V) (y : Fin m → V),
      T (Fin.cons (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0) :
    ∀ (x t : V) (y : Fin m → V),
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0 := by
  let e := Module.finBasis ℂ V
  have hm := firstPolynomial_final_eq_zero T e h
  have hzero := firstPolynomial_zero_of_final T e hm
  exact firstPolynomial_initial_vanishing T e hzero

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.PowerSpan ----
namespace OAI

noncomputable section

namespace Problem346

universe u v

/-- Multilinearity extends vanishing on independent pure powers to vanishing everywhere. -/
theorem multilinear_eq_zero_of_pure_powers (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin a => SymPow b V) W)
    (hT : ∀ x : Fin a → V, T (fun i => symMonomial b V (fun _ => x i)) = 0) :
    T = 0 := by
  apply MultilinearMap.ext_of_span_eq_top
    (g := fun {_ : Fin a} (x : V) => symMonomial b V (fun _ => x))
    (fun _ => span_purePowers_eq_top b V)
  exact hT

/-- Independent pure powers detect a symmetric multilinear form. -/
theorem symmetricMultilinearForm_eq_zero_of_pure_powers (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V)
    (hT : ∀ x : Fin a → V, T (fun i => symMonomial b V (fun _ => x i)) = 0) :
    T = 0 :=
  multilinear_eq_zero_of_pure_powers a b V T hT

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.VanishingFirst ----
namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Diagonal vanishing gives the diagonal vanishing of the lower-arity form.
This combines binary splitting, coefficient extraction, and the first transfer. -/
theorem lowerProductForm_diagonal_zero (r m : ℕ) (hr : 0 < r)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (hT : IsSymmetricMultilinearForm (r+1) (r+m) V T)
    (hdiag : ∀ y : Fin (r+m) → V, T (fun _ => symMonomial (r+m) V y) = 0)
    (x t : V) (y : Fin m → V) :
    lowerProductForm r m T x t (fun _ => symMonomial m V y) = 0 := by
  exact first_transfer T (binary_diagonal_to_mixed_products r m hr T hT hdiag) x t y

/-- With the first transfer and pure-power detection established, the common-power
removal transfer is the sole remaining input to the vanishing induction. -/
theorem vanishing_on_products_of_second_transfer
    (secondTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ x t : V, ∀ Q : Fin r → SymPow m V, lowerProductForm r m T x t Q = 0) →
      ∀ v : Fin (r+1) → V,
        T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a*(a-1) ≤ b →
      ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ y : Fin b → V, T (fun _ => symMonomial b V y) = 0) → T = 0 := by
  apply vanishing_induction_from_transfer_steps
  · intro r m hr _ _ T hT hdiag
    exact lowerProductForm_diagonal_zero r m hr T hT hdiag
  · exact secondTransfer
  · intro a b T hT
    exact symmetricMultilinearForm_eq_zero_of_pure_powers a b V T hT

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.ProductVanishing ----
namespace OAI

noncomputable section

namespace Problem346

universe u

/-- Quadratic stabilization of diagonal vanishing on products. Both differential
transfers and all of the induction hypotheses are discharged in this theorem. -/
theorem vanishing_on_products_aux (V : Type u)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a*(a-1) ≤ b)
    (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (hdiag : ∀ y : Fin b → V, T (fun _ => symMonomial b V y) = 0) : T = 0 := by
  refine vanishing_on_products_of_second_transfer (V := V) ?_ a b ha hb hab T hT hdiag
  intro r m _ _ hbound S _ hrest
  exact SecondTransfer.second_transfer r m (by simpa only [Nat.mul_comm] using hbound) S hrest

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.Stabilization ----
namespace OAI

noncomputable section

universe u

namespace Problem346

theorem canonical_foulkes_howe_surjective :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 2 ≤ a → a * (a - 1) ≤ b → ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧ ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V ν → ν = μ := by
  intro V _ _ _ a b ha hab
  apply canonical_surjective_unique_of_vanishing a b V
  have hb : 1 ≤ b := by
    have hpred : 1 ≤ a - 1 := by omega
    have hprod := Nat.mul_le_mul ha hpred
    omega
  exact vanishing_on_products_aux V a b (by omega) hb hab

end Problem346

end

end OAI

-- ---- mission target ----
open OAI OAI.Problem346
open scoped BigOperators
universe u

theorem solution :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 2 ≤ a → a * (a - 1) ≤ b → ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧ ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V ν → ν = μ := by
  first
    | exact OAI.Problem346.canonical_foulkes_howe_surjective
    | (apply OAI.Problem346.canonical_foulkes_howe_surjective <;> assumption)
    | (intros; apply OAI.Problem346.canonical_foulkes_howe_surjective <;> assumption)
