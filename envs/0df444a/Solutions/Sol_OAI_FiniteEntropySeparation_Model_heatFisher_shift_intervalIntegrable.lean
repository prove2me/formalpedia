-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.Model.heatFisher_shift_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:14:32.065253+00:00
-- url     : https://prove2.me/submissions/5f56dd48-2029-4919-a301-d55d4b7bb4e5

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002
import Theorems.Thm_OAI_FiniteEntropySeparation_lowerSemicontinuous_freeFisher

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem trace_add {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A + B) = trace τ A + trace τ B := by
  simp [trace]

 theorem trace_smul {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (z : ℂ) (A : H →L[ℂ] H) : trace τ (z • A) = z * trace τ A := by
  simp [trace]

 theorem trace_sum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {α : Type u1} (s : Finset α) (A : α → H →L[ℂ] H) :
    trace τ (∑ a ∈ s, A a) = ∑ a ∈ s, trace τ (A a) := by
  simp [trace]

theorem ConjugateSystem.unique {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ η : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (hη : ConjugateSystem τ X η) : ξ = η := by
  funext i
  have hmem : ξ i - η i ∈ polynomialL2 τ X :=
    (polynomialL2 τ X).sub_mem (hξ i).1 (hη i).1
  have hker : polynomialL2 τ X ≤ (innerSL ℂ (ξ i - η i)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change inner ℂ (ξ i - η i) (wordEval X w τ.vacuum) = 0
      rw [inner_sub_left, (hξ i).2 w, (hη i).2 w, sub_self]
    · exact (innerSL ℂ (ξ i - η i)).isClosed_ker
  have hd : inner ℂ (ξ i - η i) (ξ i - η i) = 0 := hker hmem
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hd)

theorem freeFisher_eq_of_conjugate {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ENNReal.ofReal (∑ i, ‖ξ i‖ ^ 2) := by
  apply le_antisymm
  · exact iInf_le_of_le ξ (iInf_le_of_le hξ le_rfl)
  · refine le_iInf fun η => le_iInf fun hη => ?_
    rw [hξ.unique τ hη]

 theorem wordVector_mem_polynomialL2 {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (w : List (Fin n)) :
    wordEval X w τ.vacuum ∈ polynomialL2 τ X :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)

 theorem projectedConjugate_system {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    ConjugateSystem τ X (projectedConjugate τ X η) := by
  intro i
  refine ⟨(polynomialL2 τ X).starProjection_apply_mem _, fun w => ?_⟩
  have h := (polynomialL2 τ X).starProjection_inner_eq_zero (η i)
    (wordEval X w τ.vacuum) (wordVector_mem_polynomialL2 τ X w)
  rw [inner_sub_left, hη i w] at h
  exact (sub_eq_zero.mp h).symm

theorem freeFisher_le_testVectors {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    freeFisher τ X ≤ ENNReal.ofReal (∑ i, ‖η i‖ ^ 2) := by
  rw [freeFisher_eq_of_conjugate τ (projectedConjugate_system τ X η hη)]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) ((polynomialL2 τ X).norm_starProjection_apply_le _) _

 theorem conjugate_coordinate_pairing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) : inner ℂ (ξ i) (X i τ.vacuum) = 1 := by
  have h := (hξ i).2 [i]
  simpa [wordEval, derivativeMoment, wordMoment, trace_one] using h

theorem conjugate_norm_sq_lower {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) :
    1 / ‖X i τ.vacuum‖ ^ 2 ≤ ‖ξ i‖ ^ 2 := by
  have h : 1 ≤ ‖ξ i‖ * ‖X i τ.vacuum‖ := by
    simpa only [conjugate_coordinate_pairing τ hξ i, norm_one] using
      norm_inner_le_norm (𝕜 := ℂ) (ξ i) (X i τ.vacuum)
  have hp : 0 < ‖X i τ.vacuum‖ := by
    have hn := norm_nonneg (X i τ.vacuum)
    by_contra hh
    have hz : ‖X i τ.vacuum‖ = 0 := le_antisymm (not_lt.mp hh) hn
    rw [hz, mul_zero] at h
    linarith
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith [sq_nonneg (‖ξ i‖ * ‖X i τ.vacuum‖ - 1)]

omit [CompleteSpace H] in
 theorem commutatorKernel_cons {n : ℕ} (P : H →L[ℂ] H)
    (X : Fin n → H →L[ℂ] H) (i j : Fin n) (w : List (Fin n)) :
    commutatorKernel P X i (j :: w) =
      (if j = i then P * wordEval X w else 0) + X j * commutatorKernel P X i w := by
  simp only [commutatorKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

omit [CompleteSpace H] in
 theorem commutator_word {n : ℕ} (P a : H →L[ℂ] H) (X : Fin n → H →L[ℂ] H)
    (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • P else 0)
    (w : List (Fin n)) :
    a * wordEval X w = wordEval X w * a + c • commutatorKernel P X i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval X (j :: w) = X j * wordEval X w := by simp [wordEval]
    rw [hw, commutatorKernel_cons, ← mul_assoc, h, add_mul, mul_assoc, ih]
    by_cases hji : j = i <;>
      simp [hji, mul_add, mul_assoc, smul_add, _root_.add_assoc, _root_.add_comm,
        _root_.add_left_comm]

 theorem trace_vacuumRankOne_product {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A * vacuumRankOne τ * B) = trace τ A * trace τ B := by
  simp only [trace, vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
    map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) :
    trace τ (commutatorKernel (vacuumRankOne τ) X i w) = derivativeMoment τ X i w := by
  rw [commutatorKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_vacuumRankOne_product, wordMoment]

theorem commutator_integration_by_parts {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (a : H →L[ℂ] H) (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • vacuumRankOne τ else 0)
    (hz : a τ.vacuum = 0) (w : List (Fin n)) :
    inner ℂ (star a τ.vacuum) (wordEval X w τ.vacuum) = c * derivativeMoment τ X i w := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change trace τ (a * wordEval X w) = _
  rw [commutator_word _ _ _ _ _ h, trace_add, trace_smul, trace_commutatorKernel]
  have hzero : trace τ (wordEval X w * a) = 0 := by
    simp [trace, mul_apply_eq_comp, hz]
  rw [hzero, zero_add]

namespace Fock

open scoped lp
variable {ι : Type} [DecidableEq ι]

 theorem creation_commutes_rightCreation (i j : ι) :
    Commute (creation i) (rightCreation j) := by
  show creation i * rightCreation j = rightCreation j * creation i
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creation i (rightCreation j (lp.single 2 w z)) =
    rightCreation j (creation i (lp.single 2 w z))
  simp

 theorem rightAnnihilation_creation (i j : ι) :
    star (rightCreation i) * creation j = creation j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreation i) (creation j (lp.single 2 w z)) =
    creation j (star (rightCreation i) (lp.single 2 w z)) +
      (if i = j then vacuumProjection else 0) (lp.single 2 w z)
  induction w using List.reverseRecOn with
  | nil =>
    rw [creation_single, show [j] = [] ++ [j] from rfl, rightAnnihilation_single_append]
    by_cases h : i = j <;> simp [h]
  | append_singleton w k _ =>
    rw [creation_single, show j :: (w ++ [k]) = (j :: w) ++ [k] from rfl,
      rightAnnihilation_single_append]
    have hp : (if i = j then vacuumProjection else 0) (lp.single 2 (w ++ [k]) z) = 0 := by
      split_ifs <;> simp
    rw [hp, rightAnnihilation_single_append]
    by_cases h : i = k <;> simp [h]

theorem rightAnnihilation_semicircular (i j : ι) :
    star (rightCreation i) * semicircular j = semicircular j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  have h : star (rightCreation i) * star (creation j) =
      star (creation j) * star (rightCreation i) := by
    simpa only [star_mul] using congrArg star (creation_commutes_rightCreation j i).eq
  rw [semicircular, mul_add, add_mul, rightAnnihilation_creation, h]
  abel

 theorem derivativeKernel_cons {n : ℕ} (i j : Fin n) (w : List (Fin n)) :
    derivativeKernel i (j :: w) =
      (if j = i then vacuumProjection * wordEval semicircular w else 0) +
        semicircular j * derivativeKernel i w := by
  simp only [derivativeKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

 theorem rightAnnihilation_word {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    star (rightCreation i) * wordEval semicircular w =
      wordEval semicircular w * star (rightCreation i) + derivativeKernel i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval semicircular (j :: w) = semicircular j * wordEval semicircular w := by
      simp [wordEval]
    rw [hw, derivativeKernel_cons, ← mul_assoc, rightAnnihilation_semicircular,
      add_mul, mul_assoc, ih, mul_add]
    by_cases h : i = j <;> simp [h, eq_comm, mul_assoc, add_assoc, add_comm, add_left_comm]

 theorem trace_projection_product (A B : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (A * vacuumProjection * B) =
      trace (tracialVector ι) A * trace (tracialVector ι) B := by
  simp only [trace, tracialVector, vacuumProjection, mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply, map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_derivativeKernel {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (derivativeKernel i w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [derivativeKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_projection_product, wordMoment]

 theorem trace_semicircular_left (i : ι) (A : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (semicircular i * A) =
      trace (tracialVector ι) (star (rightCreation i) * A) := by
  simp only [trace, tracialVector, mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left (semicircular i),
    ← ContinuousLinearMap.adjoint_inner_left (star (rightCreation i))]
  simp only [← ContinuousLinearMap.star_eq_adjoint, star_star,
    (semicircular_selfAdjoint i).star_eq, basisVector,
    semicircular_single_nil, rightCreation_single, List.nil_append]

theorem semicircular_integration_by_parts {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (semicircular i * wordEval semicircular w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [trace_semicircular_left, rightAnnihilation_word, trace_add, trace_derivativeKernel]
  suffices trace (tracialVector (Fin n))
      (wordEval semicircular w * star (rightCreation i)) = 0 by rw [this, zero_add]
  simp [trace, tracialVector, basisVector, mul_apply_eq_comp]

end Fock

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem freeFisher_lt_top_iff {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) :
    freeFisher τ X < ⊤ ↔ ∃ ξ, ConjugateSystem τ X ξ := by
  constructor
  · intro h
    by_contra! hn
    have he : freeFisher τ X = ⊤ := by simp [freeFisher, hn]
    rw [he] at h
    exact lt_irrefl _ h
  · rintro ⟨ξ,hξ⟩
    rw [freeFisher_eq_of_conjugate τ hξ]
    exact ENNReal.ofReal_lt_top

 theorem exists_conjugate_of_fisher_le {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (c : ℝ)
    (h : freeFisher τ X ≤ ENNReal.ofReal c) : ∃ ξ, ConjugateSystem τ X ξ :=
  (freeFisher_lt_top_iff τ X).mp (h.trans_lt ENNReal.ofReal_lt_top)

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TracialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem trace_unitaryG (g : G) :
    trace (tracialVector B N G) (unitaryG g) = if g = 1 then 1 else 0 := by
  change inner ℂ (basis empty) (unitaryG g (basis empty)) = _
  rw [unitaryG_basis]
  by_cases hg : g = 1 <;> simp [basis, leftG, empty, lp.inner_single_left, lp.single_apply, hg, eq_comm]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem vacuumBoundary_eq_rankOne :
    vacuumBoundary (B := B) (N := N) (G := G) = vacuumRankOne (tracialVector B N G) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change vacuumBoundary (lp.single 2 w z) = _
  rw [vacuumBoundary_single]
  by_cases hw : w = empty
  · subst w
    simp [vacuumRankOne, tracialVector, basis, lp.inner_single_left]
    simpa using (lp.single_smul (E := fun _ : Word B N G => ℂ) 2 (empty : Word B N G) z (1 : ℂ))
  · simp [hw, vacuumRankOne, tracialVector, basis, lp.inner_single_left, lp.single_apply, Ne.symm hw]

 theorem rightAnnihilationN_semicircularN (i j : N) :
    star (rightCreationN (B := B) (G := G) i) * semicircularN j =
      semicircularN j * star (rightCreationN i) + if i = j then
        vacuumRankOne (tracialVector B N G) else 0 := by
  have h : Commute (creationN (B := B) (G := G) j) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftN_rightN j i)
  have hs := h.star_star.symm.eq
  rw [semicircularN, mul_add, add_mul, rightAnnihilationN_creationN, hs,
    vacuumBoundary_eq_rankOne]
  abel

 theorem rightAnnihilationN_commutes_semicircularB (i : N) (b : B) :
    Commute (star (rightCreationN (G := G) i)) (semicircularB b) := by
  have h : Commute (creationB (G := G) b) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftB_rightN b i)
  exact (creationB_commutes_rightAnnihilationN b i).symm.add_right h.star_star.symm

 theorem rightAnnihilationN_background {i : N} {J : Set N} (hi : i ∉ J)
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    Commute (star (rightCreationN i)) T := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨j,hj,rfl⟩)
    · exact rightAnnihilationN_commutes_semicircularB i b
    · exact (unitaryG_commutes_rightAnnihilationN g i).symm
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      show _ * _ = _ * _
      simpa [hij] using rightAnnihilationN_semicircularN (B := B) (G := G) i j
  | algebraMap z => exact (Algebra.commute_algebraMap_left z _).symm
  | add T U _ _ hT hU => exact hT.add_right hU
  | mul T U _ _ hT hU => exact hT.mul_right hU

theorem heat_freeFisher_le {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    freeFisher (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) ≤
      ENNReal.ofReal ((n : ℝ) / u) := by
  let Z := heatTuple X (fun i => semicircularN (σ i)) u
  let η : Fin n → Space B N G := fun i =>
    ((Real.sqrt u)⁻¹ : ℂ) • basis (leftN (σ i) empty)
  have hc (i j : Fin n) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
    change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
    rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
      rightAnnihilationN_semicircularN]
    change _ = (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) *
      star (rightCreationN (σ i)) +
      if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0
    by_cases hij : j = i
    · subst j
      simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
      congr 1
      exact smul_add _ _ _
    · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
      simp only [hij, hneq, ↓reduceIte, add_zero, add_mul, smul_mul_assoc]
  have hu' : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have hη (i : Fin n) (w : List (Fin n)) :
      inner ℂ (η i) (wordEval Z w (tracialVector B N G).vacuum) =
        derivativeMoment (tracialVector B N G) Z i w := by
    have h := commutator_integration_by_parts (tracialVector B N G) Z
      (star (rightCreationN (σ i))) i (Real.sqrt u) (hc i)
      (by simp [tracialVector, basis, empty]) w
    simp only [star_star, tracialVector, basis, rightCreationN_single] at h
    have he : rightN (σ i) (empty : Word B N G) = leftN (σ i) empty := by
      simp [rightN_eq_append, empty, leftN, push, append]
    rw [he] at h
    change inner ℂ (((Real.sqrt u : ℂ)⁻¹) • lp.single 2 (leftN (σ i) empty) 1)
      (wordEval Z w (lp.single 2 empty 1)) = _
    rw [inner_smul_left, h]
    simp [hu', tracialVector, basis]
  refine (freeFisher_le_testVectors (tracialVector B N G) Z η hη).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnorm (i : Fin n) : ‖η i‖ ^ 2 = u⁻¹ := by
    simp [η, norm_smul, basis, norm_inv,
      lp.norm_single (E := fun _ : Word B N G => ℂ) (p := 2),
      abs_of_nonneg (Real.sqrt_nonneg u), inv_pow, Real.sq_sqrt (le_of_lt hu)]
  simp [hnorm, div_eq_mul_inv]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem continuous_heatTuple {n : ℕ} (X S : Fin n → H →L[ℂ] H) (i : Fin n) :
    Continuous (fun u : ℝ => heatTuple X S u i) := by
  unfold heatTuple
  fun_prop

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem heat_conjugates_exist {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    ∃ ξ, ConjugateSystem (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u) ξ :=
  exists_conjugate_of_fisher_le _ _ (n/u) (heat_freeFisher_le J X hX σ hσ hs u hu)

 theorem heat_freeFisher_measurable {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    Measurable (fun u : Set.Ioi (0 : ℝ) => freeFisher (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u.val)) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_freeFisher (tracialVector B N G)
  · intro i
    exact (continuous_heatTuple X (fun i => semicircularN (σ i)) i).comp continuous_subtype_val
  · intro u
    exact heat_conjugates_exist J X hX σ hσ hs u.val u.property

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

 theorem conv_sum_splits (f g : Series α) (w : List α) :
    conv f g w = ∑ k ∈ range (w.length+1), f (w.take k) * g (w.drop k) := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [conv_cons, ih, List.length_cons]
    conv_rhs => rw [sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons, deriv_apply]
    ring

@[simp] theorem conv_zero_left (f : Series α) : conv 0 f = 0 := by
  funext w
  simp [conv_sum_splits]
@[simp] theorem conv_zero_right (f : Series α) : conv f 0 = 0 := by
  funext w
  simp [conv_sum_splits]

@[simp] theorem conv_unit_left (f : Series α) : conv unit f = f := by
  funext w
  cases w <;> simp [conv, deriv_unit]

theorem length_induction {P : List α → Prop} (w : List α)
    (h : ∀ w, (∀ v, v.length < w.length → P v) → P w) : P w :=
  (measure List.length).wf.induction w h

 theorem subst_cons (M f : Series α) (a : α) (w : List α) :
    subst M f (a::w) = conv M (subst M (deriv a f)) w := by
  rw [subst, conv_sum_splits]

 theorem subst_smul (M f : Series α) (c : ℂ) : subst M (c • f) = c • subst M f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.smul_apply, smul_eq_mul]
      simp_rw [show deriv a (c • f) = c • deriv a f from rfl]
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_left_comm]

@[simp] theorem subst_zero (M : Series α) : subst M 0 = 0 := by
  have h := subst_smul M 0 0
  simpa using h
@[simp] theorem subst_unit (M : Series α) : subst M unit = unit := by
  funext w
  cases w with
  | nil => simp
  | cons a w => simp [subst_cons]

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SemicircularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α]

 theorem deriv_letter (i j : α) : deriv j (letter i) = if j=i then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : j=i <;> simp [deriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : j=i <;> simp [deriv, letter, unit, h]
 theorem subst_letter_cons (M : Series α) (i j : α) (w : List α) :
    subst M (letter i) (j::w) = if j=i then M w else 0 := by
  rw [subst_cons, deriv_letter]
  split_ifs <;> simp
 theorem deriv_quadratic (i : α) : deriv i (quadratic : Series α) = letter i := by
  funext w
  cases w with
  | nil => rfl
  | cons a w => cases w <;> rfl

 theorem quadratic_subst_derivative {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    subst M quadratic (i::w) = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [subst_cons, deriv_quadratic, conv_sum_splits, sum_range_succ]
  simp only [List.take_length, List.drop_length, subst_nil, letter_nil, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => M (w.take k) * subst M (letter i) (w.drop k))]
  apply sum_congr rfl
  intro k hk
  rw [List.drop_eq_getElem_cons k.isLt, subst_letter_cons]
  split_ifs <;> simp

 theorem fockMoments_eq (p : ℕ) : fockMoments p = unit + subst (fockMoments p) quadratic := by
  funext w
  cases w with
  | nil => simp [fockMoments]
  | cons i w =>
    simp only [Pi.add_apply, unit_cons, zero_add, quadratic_subst_derivative]
    exact Fock.semicircular_integration_by_parts i w

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Signal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

theorem norm_sum_sq_orthogonal {H : Type u1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type u2} [Fintype ι] (x : ι → H)
    (h : ∀ i j, i ≠ j → inner ℂ (x i) (x j) = 0) :
    ‖∑ i, x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
  have hs (i : ι) : inner ℂ (x i) (∑ j, x j) = inner ℂ (x i) (x i) := by
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hji => h i j (Ne.symm hji)) (by simp)
  simp_rw [hs]
  simp only [map_sum, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

namespace FreeTensor

variable {B N A : Type} [DecidableEq B] [DecidableEq N] [AddCommGroup A]
  [Fintype A] [DecidableEq A]

omit [Fintype A] in
 theorem groupUnitary_add (a b : A) :
    groupUnitary (B := B) (N := N) (a + b) = groupUnitary a * groupUnitary b :=
  unitaryG_mul _ _

 theorem groupUnitary_mul_characterProjection (a : A) (ψ : AddChar A ℂ) :
    groupUnitary (B := B) (N := N) a * characterProjection ψ = ψ a • characterProjection ψ := by
  unfold characterProjection
  rw [mul_smul_comm, Finset.mul_sum, smul_comm (ψ a)]
  congr 1
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addLeft a)
  intro b
  rw [mul_smul_comm]
  change ψ (-b) • (groupUnitary (B := B) (N := N) a * groupUnitary b) =
    ψ a • (ψ (-(a + b)) • groupUnitary (a + b))
  simp only [← groupUnitary_add, smul_smul]
  congr 1
  rw [neg_add, AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel]
  simp

 theorem characterProjection_mul (ψ φ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ * characterProjection φ =
      if ψ = φ then characterProjection ψ else 0 := by
  classical
  rw [characterProjection, smul_mul_assoc, Finset.sum_mul]
  simp only [smul_mul_assoc, groupUnitary_mul_characterProjection, smul_smul,
    ← Finset.sum_smul]
  have hs : (∑ a : A, ψ (-a) * φ a) = if ψ = φ then (Fintype.card A : ℂ) else 0 := by
    have he (a : A) : ψ (-a) * φ a = (-ψ + φ) a := by
      simp [AddChar.add_apply, AddChar.neg_apply, AddChar.map_neg_eq_inv]
    simp_rw [he]
    rw [AddChar.sum_eq_ite]
    congr 1
    exact propext neg_add_eq_zero
  rw [hs]
  by_cases h : ψ = φ
  · subst φ
    simp [Fintype.card_ne_zero, characterProjection]
  · simp only [h, ↓reduceIte, mul_zero,
      zero_smul ℂ (characterProjection (B := B) (N := N) φ)]

 theorem sum_characterProjection :
    ∑ ψ : AddChar A ℂ, characterProjection (B := B) (N := N) ψ = 1 := by
  classical
  unfold characterProjection
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero]
  simp [smul_smul, Fintype.card_ne_zero]

omit [Fintype A] in
 theorem trace_groupUnitary (a : A) :
    trace (tracialVector B N (Multiplicative A)) (groupUnitary a) = if a = 0 then 1 else 0 := by
  rw [trace_unitaryG]
  rfl

 theorem trace_characterProjection (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A)) (characterProjection ψ) =
      (Fintype.card A : ℂ)⁻¹ := by
  rw [characterProjection, trace_smul, trace_sum]
  simp [trace_smul, trace_groupUnitary]

 theorem spectralSignal_selfAdjoint (y : AddChar A ℂ → ℝ) :
    IsSelfAdjoint (spectralSignal (B := B) (N := N) y) := by
  show star _ = _
  simp [spectralSignal,
    star_sum (R := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A))]

 theorem spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    spectralSignal (B := B) (N := N) y ^ k = ∑ ψ, ((y ψ : ℂ) ^ k) • characterProjection ψ := by
  classical
  induction k with
  | zero => simpa using (sum_characterProjection (B := B) (N := N) (A := A)).symm
  | succ k ih =>
    rw [pow_succ, ih, spectralSignal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [smul_mul_assoc, Finset.mul_sum]
    simp only [mul_smul_comm, characterProjection_mul]
    simp only [smul_ite, smul_zero (M := ℂ) (A := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A)),
      Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, smul_smul, pow_succ]

 theorem trace_spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    trace (tracialVector B N (Multiplicative A)) (spectralSignal y ^ k) =
      (Fintype.card A : ℂ)⁻¹ * ∑ ψ, (y ψ : ℂ) ^ k := by
  rw [spectralSignal_pow, trace_sum]
  simp only [trace_smul, trace_characterProjection, ← Finset.sum_mul]
  exact mul_comm _ _

 theorem characterProjection_orthogonal (ψ φ : AddChar A ℂ) (h : ψ ≠ φ)
    (v w : Space B N (Multiplicative A)) :
    inner ℂ (characterProjection ψ v) (characterProjection φ w) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    star_characterProjection, ← mul_apply_eq_comp, characterProjection_mul, ite_eq_right (Ne.symm h)]
  simp

 theorem spectralSignal_norm_le (y : AddChar A ℂ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ ψ, |y ψ| ≤ R) : ‖spectralSignal (B := B) (N := N) y‖ ≤ R := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  have hx : ∑ ψ : AddChar A ℂ, characterProjection ψ x = x := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun T : Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A) => T x)
        (sum_characterProjection (B := B) (N := N) (A := A))
  have hn : ∑ ψ : AddChar A ℂ, ‖characterProjection ψ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← norm_sum_sq_orthogonal _ (fun ψ φ h => characterProjection_orthogonal ψ φ h x x), hx]
  have hn' : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 =
      ∑ ψ : AddChar A ℂ, |y ψ| ^ 2 * ‖characterProjection ψ x‖ ^ 2 := by
    simp only [spectralSignal, sum_apply, smul_apply]
    rw [norm_sum_sq_orthogonal _ (by
      intro ψ φ h
      simp [characterProjection_orthogonal ψ φ h x x])]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hsq : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 ≤ R ^ 2 * ‖x‖ ^ 2 := by
    rw [hn', ← hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ψ _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (hy ψ) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  simpa only [mul_pow] using hsq

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem signalSlice_semicircular [Group G] (g : G) (b : B) :
    (semicircularB b).comp (signalSlice (N := N) g) =
      (signalSlice g).comp (Fock.semicircular b) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircularB b (signalSlice g (lp.single 2 w z)) =
    signalSlice g (Fock.semicircular b (lp.single 2 w z))
  rw [signalSlice_single]
  cases w with
  | nil => simp [semicircularB, creationB_single, annihilationB_single, removeB, leftB]
  | cons c w =>
    simp only [semicircularB, add_apply, creationB_single, annihilationB_single, removeB,
      Fock.semicircular_single_cons, map_add, signalSlice_single, leftB]
    by_cases h : b = c <;> simp [h]

 theorem signalSlice_word (g : G) (w : List B) :
    ((w.map (semicircularB (N := N) (G := G))).prod).comp (signalSlice g) =
      (signalSlice g).comp ((w.map Fock.semicircular).prod) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G => T x) ih
    have hc := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G =>
      T ((w.map Fock.semicircular).prod x)) (signalSlice_semicircular (N := N) g b)
    simp only [ContinuousLinearMap.comp_apply] at hi hc
    simpa only [ContinuousLinearMap.comp_apply, List.map_cons, List.prod_cons,
      mul_apply_eq_comp, hi] using hc

 theorem signalSlice_vacuum_coefficient (g : G) (x : Fock.Space B) :
    inner ℂ (basis (empty : Word B N G)) (signalSlice g x) =
      if g = 1 then inner ℂ (Fock.basisVector []) x else 0 := by
  have h : (innerSL ℂ (basis (empty : Word B N G))).comp (signalSlice g) =
      if g = 1 then innerSL ℂ (Fock.basisVector ([] : List B)) else 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro v
    apply ContinuousLinearMap.ext
    intro z
    by_cases hg : g = 1 <;> by_cases hv : v = [] <;>
      simp [hg, hv, basis, empty, Fock.basisVector, lp.inner_single_left, lp.single_apply, eq_comm]
  have hx := congrArg (fun f : Fock.Space B →L[ℂ] ℂ => f x) h
  by_cases hg : g = 1 <;> simpa [hg] using hx

theorem tensor_word_moment (w : List B) (g : G) :
    trace (tracialVector B N G) ((w.map semicircularB).prod * unitaryG g) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        (if g = 1 then 1 else 0) := by
  change inner ℂ (basis (empty : Word B N G))
    (((w.map (semicircularB (N := N) (G := G))).prod * unitaryG (B := B) (N := N) g) (basis empty)) = _
  rw [mul_apply_eq_comp, unitaryG_basis]
  have hv : basis (leftG g (empty : Word B N G)) = signalSlice g (Fock.basisVector []) := by
    simp [leftG, empty]
  rw [hv, ← ContinuousLinearMap.comp_apply, signalSlice_word,
    ContinuousLinearMap.comp_apply, signalSlice_vacuum_coefficient]
  by_cases hg : g = 1 <;> simp [hg, trace, Fock.tracialVector]

 theorem unitaryG_commutes_creationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (creationB b) := by
  apply LabelHilbert.lift_commute
  intro w
  rfl

 theorem unitaryG_commutes_semicircularB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (semicircularB b) := by
  apply (unitaryG_commutes_creationB g b).add_right
  simpa using (unitaryG_commutes_creationB (N := N) g⁻¹ b).star_star

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NoiseTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G]

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem noise_basis_orthonormal : Orthonormal ℂ (fun w : List N =>
    basis (noiseWord (B := B) (G := G) w)) := by
  rw [orthonormal_iff_ite]
  intro v w
  by_cases h : v = w
  · subst w
    simp [basis, ]
  · have h' : noiseWord (B := B) (G := G) v ≠ noiseWord w :=
      fun hh => h (noiseWord_injective hh)
    simp [basis, lp.inner_single_left, lp.single_apply, h, h']

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EquidiscreteSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

 theorem equidiscreteAtom_abs_le {p : ℕ} (hp : 2 ≤ p) (l : Fin p) :
    |equidiscreteAtom p l| ≤ 1 := by
  have hd : 0 < (p : ℝ) - 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hl : (l.val : ℝ) ≤ (p : ℝ) - 1 := by
    have hn : l.val + 1 ≤ p := l.isLt
    exact_mod_cast (show (l.val : ℤ) ≤ (p : ℤ) - 1 by omega)
  rw [abs_le, equidiscreteAtom]
  constructor
  · have h := div_nonneg (show 0 ≤ 2 * (l.val : ℝ) by positivity) hd.le
    linarith
  · have h : 2 * (l.val : ℝ) / ((p : ℝ) - 1) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
    linarith

namespace FreeTensor
variable {B N : Type} [DecidableEq B] [DecidableEq N] (p : ℕ) [NeZero p]

 theorem equidiscreteSignal_selfAdjoint : IsSelfAdjoint (equidiscreteSignal (B := B) (N := N) p) :=
  spectralSignal_selfAdjoint _

 theorem equidiscreteSignal_norm_le (hp : 2 ≤ p) :
    ‖equidiscreteSignal (B := B) (N := N) p‖ ≤ 1 :=
  spectralSignal_norm_le _ 1 zero_le_one (fun _character => equidiscreteAtom_abs_le hp _)

 theorem equidiscreteSignal_moments (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p))) (equidiscreteSignal p ^ k) =
      (p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k := by
  rw [equidiscreteSignal, trace_spectralSignal_pow]
  simp only [ZMod.card]
  congr 1
  exact (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)

 theorem characterProjection_mem_background {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (J : Set N) (ψ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).smul_mem
  apply (backgroundAlgebra J).sum_mem
  intro a _
  apply (backgroundAlgebra J).smul_mem
  exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨Multiplicative.ofAdd a,rfl⟩))

 theorem equidiscreteSignal_mem_background (J : Set N) :
    equidiscreteSignal (B := B) (N := N) p ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).sum_mem
  intro ψ _
  exact (backgroundAlgebra J).smul_mem (characterProjection_mem_background J ψ) _

 theorem characterProjection_commutes_B {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (ψ : AddChar A ℂ) (b : B) :
    Commute (characterProjection (B := B) (N := N) ψ) (semicircularB b) := by
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  exact (unitaryG_commutes_semicircularB (Multiplicative.ofAdd a) b).smul_left _

 theorem equidiscreteSignal_commutes_B (b : B) :
    Commute (equidiscreteSignal (B := B) (N := N) p) (semicircularB b) := by
  apply Commute.sum_left
  intro ψ _
  exact (characterProjection_commutes_B ψ b).smul_left _

 theorem tensor_characterProjection_moment {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (w : List B) (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A))
      ((w.map semicircularB).prod * characterProjection ψ) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) * (Fintype.card A : ℂ)⁻¹ := by
  simp only [characterProjection, mul_smul_comm, Finset.mul_sum, trace_smul, trace_sum,
    groupUnitary, tensor_word_moment]
  have hi (a : A) : (Multiplicative.ofAdd a = (1 : Multiplicative A)) ↔ a = 0 := Iff.rfl
  simp only [hi]
  simp
  ring

 theorem tensor_equidiscrete_moment (w : List B) (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p)))
      ((w.map semicircularB).prod * equidiscreteSignal p ^ k) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        ((p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k) := by
  rw [equidiscreteSignal, spectralSignal_pow, Finset.mul_sum, trace_sum]
  simp only [mul_smul_comm, trace_smul, tensor_characterProjection_moment, ZMod.card]
  rw [← Finset.sum_mul]
  have hs := (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)
  change _ = _ at hs
  rw [hs]
  ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ActualTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem semicircularB_selfAdjoint [Group G] (b : B) : IsSelfAdjoint (semicircularB (N := N) (G := G) b) :=
  IsSelfAdjoint.add_star_self (creationB (N := N) (G := G) b)

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))

end FreeTensor

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem initialIndex_injective [NeZero p] : Function.Injective (initialIndex p) := Fin.castAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_injective [NeZero p] : Function.Injective (auxiliaryIndex p) := Fin.natAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_fresh [NeZero p] (i : Fin (p+1)) : auxiliaryIndex p i ∉ oldNoise p := by
  rintro ⟨j,h⟩
  have hv := congrArg Fin.val h
  simp only [initialIndex, auxiliaryIndex, Fin.val_castAdd, Fin.val_natAdd] at hv
  have hj := j.isLt
  omega

 theorem C_selfAdjoint (i : Fin (p+1)) : IsSelfAdjoint (C p i) := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_selfAdjoint p
  | cast i => rw [C_castSucc]; exact semicircularB_selfAdjoint i

 theorem C_mem_background (J : Set (Fin ((p+1)+(p+1)))) (i : Fin (p+1)) :
    C p i ∈ backgroundAlgebra J := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_mem_background p J
  | cast i => rw [C_castSucc]; exact semicircularB_mem_background J i

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries

section Product
variable {α A : Type} [DecidableEq α] [Monoid A]
 theorem option_word_product (B : α → A) (Y : A) (h : ∀ i, Commute Y (B i)) (w : List (Option α)) :
    (w.map (optionTuple B Y)).prod = ((w.filterMap id).map B).prod * Y^(w.count none) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a with
    | none =>
      simp only [List.map_cons, List.prod_cons, optionTuple, List.filterMap_cons, id_eq, ih]
      have hc := Commute.list_prod_right ((w.filterMap id).map B) Y (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact h i)
      simp only [List.count_cons_self]
      change Y * (((w.filterMap id).map B).prod * Y ^ w.count none) = _
      rw [← mul_assoc, hc.eq, mul_assoc, pow_succ']
      rfl
    | some i => simp [optionTuple, ih, mul_assoc]
end Product

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem signal_option_product (w : List (Option (Fin p))) :
    wordEval (C p) (w.map (optionFin p)) =
      ((w.filterMap id).map (semicircularB (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)))).prod *
        equidiscreteSignal p ^ (w.count none) := by
  unfold wordEval
  rw [List.map_map]
  have hf : (fun a => C p (optionFin p a)) = optionTuple semicircularB (equidiscreteSignal p) := by
    funext a
    cases a <;> simp [optionTuple]
  change (w.map (fun a => C p (optionFin p a))).prod = _
  rw [hf]
  exact option_word_product _ _ (equidiscreteSignal_commutes_B p) w
 theorem signal_option_moments (w : List (Option (Fin p))) :
    signalMoments p (w.map (optionFin p)) = fockMoments p (w.filterMap id) *
      trace (τ p) (equidiscreteSignal p ^ (w.count none)) := by
  unfold signalMoments wordMoment
  rw [signal_option_product, tensor_equidiscrete_moment, equidiscreteSignal_moments]
  rfl
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem inner_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) (v : H) :
    inner ℂ v (commutatorKernel (vacuumRankOne τ) X i w τ.vacuum) =
      ∑ r : Fin w.length, if w[r.val] = i then
        inner ℂ v (wordEval X (w.take r.val) τ.vacuum) *
          wordMoment τ X (w.drop (r.val + 1)) else 0 := by
  rw [commutatorKernel, sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · simp only [vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      map_smul, inner_smul_right, wordMoment, trace]
    exact mul_comm _ _
  · simp

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem rightAnnihilationN_heat {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i j : Fin n) :
    star (rightCreationN (σ i)) * heatTuple X (fun k => semicircularN (σ k)) u j =
      heatTuple X (fun k => semicircularN (σ k)) u j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
  change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
  rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
    rightAnnihilationN_semicircularN]
  dsimp [heatTuple]
  by_cases hij : j = i
  · subst j
    simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
    congr 1
    exact smul_add _ _ _
  · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
    simp only [ite_eq_right hij, ite_eq_right hneq, add_zero, add_mul, smul_mul_assoc]

theorem wick_testing {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (js w : List (Fin n)) :
    inner ℂ (basis (noiseWord ((js.map σ).reverse)))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
  let Z := heatTuple X (fun k => semicircularN (σ k)) u
  change inner ℂ _ (wordEval Z w _) = _ * reverseDerivativeMoment _ Z js w
  induction js generalizing w with
  | nil => simp [reverseDerivativeMoment, wordMoment, trace, tracialVector]
  | cons i js ih =>
    have hvec : basis (noiseWord (((i :: js).map σ).reverse)) =
        rightCreationN (σ i) (basis (noiseWord ((js.map σ).reverse)) : Space B N G) := by
      simp only [List.map_cons, List.reverse_cons, basis, rightCreationN_single, rightN_noiseWord]
    rw [hvec, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint]
    have hc := commutator_word (vacuumRankOne (tracialVector B N G))
      (star (rightCreationN (σ i))) Z i (Real.sqrt u : ℂ)
      (rightAnnihilationN_heat J X hX σ hσ hs u i) w
    have hc' := congrArg (fun T : Space B N G →L[ℂ] Space B N G =>
      T (tracialVector B N G).vacuum) hc
    have hz : star (rightCreationN (σ i)) (tracialVector B N G).vacuum = 0 := by
      simp [tracialVector, basis, empty]
    simp only [mul_apply_eq_comp, hz, map_zero, add_apply, zero_add, smul_apply] at hc'
    rw [hc', inner_smul_right, inner_commutatorKernel]
    simp_rw [ih]
    rw [reverseDerivativeMoment, List.length_cons, pow_succ, Finset.mul_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem inner_selfAdjoint_word {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) = wordMoment τ X (i::w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (hX i).star_eq]
  rfl
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TwoNoiseFisher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_sq_sqrt_pair [CompleteSpace H] {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = 0) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(Real.sqrt a : ℂ) • x + (Real.sqrt b : ℂ) • y‖ ^ 2 = a + b := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, hxy]
  simp [norm_smul, hx, hy,
    Real.norm_eq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb,
    abs_of_nonneg (Real.sqrt_nonneg a), abs_of_nonneg (Real.sqrt_nonneg b)]

end General

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem noise_basis_test {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (basis (noiseWord [σ i]))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) * derivativeMoment (tracialVector B N G)
        (heatTuple X (fun k => semicircularN (σ k)) u) i w := by
  simpa only [List.map_cons, List.map_nil, List.reverse_singleton, List.length_singleton, pow_one,
    reverseDerivativeMoment, derivativeMoment] using wick_testing J X hX σ hσ hs u [i] w

 theorem semicircularN_vacuum (i : N) :
    semicircularN i (tracialVector B N G).vacuum = basis (noiseWord [i]) := by
  simp [semicircularN, tracialVector, basis, creationN_single, annihilationN_single,
    removeN, empty, noiseWord_cons, noiseWord_nil]
end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem noiseVector₀_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₀ p i‖ = 1 := by
  simp [noiseVector₀, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]

omit [NeZero p] in
theorem noiseVector₁_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₁ p i‖ = 1 := by
  simp [noiseVector₁, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]
 theorem noiseVector_orthogonal (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (noiseVector₁ p j) = 0 := by
  have hneq : [initialIndex p i] ≠ [auxiliaryIndex p j] := by
    intro he
    have he' : initialIndex p i = auxiliaryIndex p j := List.cons.inj he |>.1
    exact auxiliaryIndex_fresh p j ⟨i,he'⟩
  exact noise_basis_orthonormal.inner_eq_zero hneq

 theorem noiseVector₀_C (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₀] using ht
 theorem noiseVector₁_C (i j : Fin (p+1)) : inner ℂ (noiseVector₁ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (auxiliaryIndex p)
    (auxiliaryIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₁] using ht

 theorem doublyNoised_vacuum (h s : ℝ) (i : Fin (p+1)) :
    doublyNoised p h s i (τ p).vacuum = C p i (τ p).vacuum +
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) := by
  change (C p i (τ p).vacuum + (Real.sqrt h : ℂ) •
    semicircularN (initialIndex p i) (τ p).vacuum) +
    (Real.sqrt s : ℂ) • semicircularN (auxiliaryIndex p i) (τ p).vacuum = _
  rw [semicircularN_vacuum, semicircularN_vacuum]
  simp only [noiseVector₀, noiseVector₁, add_assoc]

 theorem doublyNoised_variance (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (i : Fin (p+1)) :
    ‖doublyNoised p h s i (τ p).vacuum‖ ^ 2 = ‖C p i (τ p).vacuum‖ ^ 2 + h+s := by
  have hc : inner ℂ (C p i (τ p).vacuum)
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) = 0 := by
    rw [← inner_conj_symm, inner_add_left, inner_smul_left, inner_smul_left,
      noiseVector₀_C, noiseVector₁_C]
    simp
  rw [doublyNoised_vacuum, norm_add_sq (𝕜 := ℂ), hc,
    norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs]
  simp
  ring

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem variance_nonneg (i : Fin (p+1)) : 0 ≤ variance p i := sq_nonneg _

omit [NeZero p] in
theorem fockMoments_one [NeZero p] (i : Fin p) : fockMoments p [i] = 0 := by
  have he := congrFun (fockMoments_eq p) [i]
  simpa [subst_cons, conv_nil, quadratic] using he

omit [NeZero p] in
theorem fockMoments_two [NeZero p] (i j : Fin p) : fockMoments p [i,j] = if j=i then 1 else 0 := by
  have he := congrFun (fockMoments_eq p) [i,j]
  simp only [Pi.add_apply, unit_cons, zero_add, subst_cons, conv_cons, subst_nil, conv_nil,
    FreeSeries.deriv_apply, quadratic] at he
  simpa [fockMoments] using he
 theorem C_offDiagonal (i j : Fin (p+1)) (hij : j ≠ i) : signalMoments p [i,j] = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      have he := signal_option_moments p [none, some j]
      simpa [fockMoments_one] using he
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      have he := signal_option_moments p [some i, none]
      simpa [fockMoments_one] using he
    | cast j =>
      have hj : j ≠ i := fun h => hij (congrArg Fin.castSucc h)
      have he := signal_option_moments p [some i, some j]
      simpa [fockMoments_two, hj] using he
 theorem C_covariance (i j : Fin (p+1)) :
    signalMoments p [i,j] = if j=i then (variance p i : ℂ) else 0 := by
  by_cases hj : j=i
  · subst j
    rw [ite_eq_left rfl]
    have he := inner_selfAdjoint_word (τ p) (C p) (C_selfAdjoint p) i [i]
    simpa [signalMoments, wordEval, variance, inner_self_eq_norm_sq_to_K] using he.symm
  · rw [ite_eq_right hj]; exact C_offDiagonal p i j hj
 theorem variance_last_le_one (hp : 2 ≤ p) : variance p (Fin.last p) ≤ 1 := by
  have he := (C p (Fin.last p)).le_opNorm (τ p).vacuum
  rw [(τ p).norm_vacuum, mul_one, C_last] at he
  have hn := equidiscreteSignal_norm_le (B := Fin p) (N := Fin ((p+1)+(p+1))) p hp
  unfold variance
  rw [C_last]
  nlinarith [norm_nonneg (equidiscreteSignal p (τ p).vacuum)]
 theorem variance_castSucc (i : Fin p) : variance p i.castSucc = 1 := by
  have he := C_covariance p i.castSucc i.castSucc
  have ht := signal_option_moments p [some i,some i]
  simp only [List.map_cons, List.map_nil, optionFin_some, List.filterMap_cons, List.filterMap_nil,
    id_eq, fockMoments_two, ite_true] at ht
  simp at ht
  rw [ite_eq_left rfl, ht] at he
  exact_mod_cast he.symm
 theorem variance_le_one (hp : 2 ≤ p) (i : Fin (p+1)) : variance p i ≤ 1 := by
  induction i using Fin.lastCases with
  | last => exact variance_last_le_one p hp
  | cast i => rw [variance_castSucc]
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem X_variance (u : ℝ) (hu : 0 ≤ u) (i : Fin (p+1)) :
    ‖X p u i (τ p).vacuum‖^2 = variance p i + u := by
  simpa [doublyNoised, heatTuple, variance] using doublyNoised_variance p u 0 hu (le_refl 0) i
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set
namespace FiniteEntropySeparation

 theorem logarithmicPrimitive_deriv {a : ℝ} (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (logarithmicPrimitive a) (reciprocalDifference a s) s := by
  unfold logarithmicPrimitive reciprocalDifference
  have h1 : 1+s ≠ 0 := by linarith
  have h2 : a+s ≠ 0 := by linarith
  convert (((hasDerivAt_id s).const_add 1).log h1).sub (((hasDerivAt_id s).const_add a).log h2) using 1
  all_goals rfl

 theorem logarithmicPrimitive_atTop (a : ℝ) :
    Tendsto (logarithmicPrimitive a) atTop (𝓝 0) := by
  have h := (Real.tendsto_log_comp_add_sub_log 1).sub (Real.tendsto_log_comp_add_sub_log a)
  unfold logarithmicPrimitive
  convert h using 1 <;> simp [add_comm, sub_sub_sub_cancel_right]

 theorem reciprocalDifference_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (reciprocalDifference a) (Ioi 0) := by
  by_cases ha1 : 1 ≤ a
  · apply integrableOn_Ioi_deriv_of_nonneg' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (fun s hs => ?_) (logarithmicPrimitive_atTop a)
    have hs : 0 < s := hs
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by linarith : 0 < 1+s)
    linarith
  · apply integrableOn_Ioi_deriv_of_nonpos' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (fun s hs => ?_) (logarithmicPrimitive_atTop a)
    have hs : 0 < s := hs
    apply sub_nonpos.mpr
    apply one_div_le_one_div_of_le (by linarith : 0 < a+s)
    linarith

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem heatFisher_ne_top (u : ℝ) (hu : 0 < u) : freeFisher (τ p) (X p u) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (heat_freeFisher_le ∅ (C p) (C_mem_background p ∅) (initialIndex p)
      (initialIndex_injective p) (by simp) u hu)
 theorem heatFisherReal_upper (u : ℝ) (hu : 0 < u) : heatFisherReal p u ≤ (p+1 : ℕ)/u := by
  have he := heat_freeFisher_le ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) u hu
  exact (ENNReal.toReal_le_toReal (heatFisher_ne_top p u hu) ENNReal.ofReal_ne_top).mpr he |>.trans_eq
    (ENNReal.toReal_ofReal (by positivity))
 theorem heatFisherReal_lower (u : ℝ) (hu : 0 < u) : covarianceFisher p u ≤ heatFisherReal p u := by
  obtain ⟨ξ,hξ⟩ := heat_conjugates_exist ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) u hu
  change ConjugateSystem (τ p) (X p u) ξ at hξ
  unfold heatFisherReal
  rw [freeFisher_eq_of_conjugate _ hξ, ENNReal.toReal_ofReal (sum_nonneg (fun _ _ => sq_nonneg _))]
  apply sum_le_sum
  intro i _
  simpa only [X_variance p u hu.le, one_div] using conjugate_norm_sq_lower (τ p) hξ i
 theorem heatFisherReal_measurable : Measurable (fun u : Ioi (0 : ℝ) => heatFisherReal p u) :=
  ENNReal.measurable_toReal.comp (heat_freeFisher_measurable ∅ (C p) (C_mem_background p ∅)
    (initialIndex p) (initialIndex_injective p) (by simp))
 theorem heatFisherReal_shift_aesm (a : ℝ) (ha : 0 < a) :
    AEStronglyMeasurable (fun s => heatFisherReal p (a+s)) (volume.restrict (Ioi 0)) := by
  let g : ℝ → Ioi (0 : ℝ) := fun s => ⟨a+max s 0, by exact lt_of_lt_of_le ha (le_add_of_nonneg_right (le_max_right s 0))⟩
  have hg : Continuous g := by continuity
  have hm := ((heatFisherReal_measurable p).comp hg.measurable).aestronglyMeasurable (μ := volume.restrict (Ioi 0))
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change heatFisherReal p (a+max s 0) = _
  rw [max_eq_left (le_of_lt hs)]
 theorem heatFisherReal_broad_lower (hp : 2 ≤ p) (u : ℝ) (hu : 0 < u) :
    (p+1 : ℕ)/(u+4) ≤ heatFisherReal p u := by
  apply le_trans _ (heatFisherReal_lower p u hu)
  have he (i : Fin (p+1)) : 1/(u+4) ≤ (variance p i+u)⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith [variance_nonneg p i])
      (by linarith [variance_le_one p hp i])
  simpa [covarianceFisher, div_eq_mul_inv] using sum_le_sum (s := (univ : Finset (Fin (p+1)))) (fun i _ => he i)
 theorem entropyIntegrand_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun s : ℝ => (p+1 : ℕ)/(1+s)) (volume.restrict (Ioi 0)) := by
    exact (by fun_prop : Measurable (fun s : ℝ => (p+1 : ℕ)/(1+s))).aestronglyMeasurable
  apply integrable_of_le_of_le (hm.sub (heatFisherReal_shift_aesm p a ha))
    (g₁ := fun s => (p+1 : ℕ) * reciprocalDifference a s)
    (g₂ := fun s => (p+1 : ℕ) * reciprocalDifference (a+4) s)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have he := heatFisherReal_upper p (a+s) (by linarith [show 0<s from hs])
    dsimp [reciprocalDifference]
    simp only [mul_sub, mul_one_div]
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have he := heatFisherReal_broad_lower p hp (a+s) (by linarith [show 0<s from hs])
    dsimp [reciprocalDifference]
    simp only [mul_sub, mul_one_div]
    convert sub_le_sub_left he ((p+1 : ℕ)/(1+s)) using 1 ; congr 2 ; ring
  · exact (reciprocalDifference_integrable ha).const_mul _
  · exact (reciprocalDifference_integrable (by linarith : 0 < a+4)).const_mul _
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation

namespace Model
variable (p : ℕ) [NeZero p]

 theorem covarianceCorrection_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => ∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) (Ioi 0) :=
  integrable_finsetSum _ (fun i _ => reciprocalDifference_integrable (by linarith [variance_nonneg p i]))
 theorem covarianceCorrection_identity (a s : ℝ) :
    (∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) -
      ((p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) = fisherDeficit p (a+s) := by
  simp only [reciprocalDifference, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [fisherDeficit, covarianceFisher, heatFisherReal, one_div]
  have he : (∑ i : Fin (p+1), (a+variance p i+s)⁻¹) = ∑ i : Fin (p+1), (variance p i+(a+s))⁻¹ := by
    apply sum_congr rfl; intro i _; congr 1; ring
  rw [he]
  simp only [div_eq_mul_inv]
  ring
 theorem fisherDeficit_shift_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => fisherDeficit p (a+s)) (Ioi 0) := by
  have hh := (covarianceCorrection_integrable p a ha).sub (entropyIntegrand_integrable p hp a ha)
  change IntegrableOn (fun s => (∑ i : Fin (p+1), reciprocalDifference (a+variance p i) s) -
    ((p+1 : ℕ)/(1+s) - heatFisherReal p (a+s))) (Ioi 0) at hh
  simpa only [covarianceCorrection_identity] using hh
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.RealTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
namespace FiniteEntropySeparation
 theorem integrableOn_Ioi_translate {f : ℝ → ℝ} (a : ℝ) :
    IntegrableOn (fun s => f (a+s)) (Ioi 0) ↔ IntegrableOn f (Ioi a) := by
  have he : (fun s : ℝ => a+s) ⁻¹' Ioi a = Ioi 0 := by ext s; simp
  simpa only [he, Function.comp_def] using
    (measurePreserving_add_left volume a).integrableOn_comp_preimage (measurableEmbedding_addLeft a)
      (f := f) (s := Ioi a)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter Finset
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
theorem fisherDeficit_tail_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fisherDeficit p) (Ioi a) :=
  (integrableOn_Ioi_translate a).mp (fisherDeficit_shift_integrable p hp a ha)
end FiniteEntropySeparation.Model

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FreeEntropyFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter Finset
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
theorem reciprocal_variance_intervalIntegrable (i : Fin (p+1)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => (variance p i + u)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn
  intro u hu
  rw [uIcc_of_le hab] at hu
  change variance p i + u ≠ 0
  exact ne_of_gt (by linarith [variance_nonneg p i, hu.1])
theorem covarianceFisher_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (covarianceFisher p) volume a b := by
  change IntervalIntegrable (fun u => ∑ i : Fin (p+1), (variance p i + u)⁻¹) volume a b
  simpa only [Finset.sum_fn] using (IntervalIntegrable.sum univ (fun i _ => reciprocal_variance_intervalIntegrable p i a b ha hab))
theorem fisherDeficit_intervalIntegrable (hp : 2 ≤ p) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fisherDeficit p) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (fisherDeficit_tail_integrable p hp a ha).mono_set (fun u hu => hu.1)
theorem heatFisherReal_intervalIntegrable (hp : 2 ≤ p) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (heatFisherReal p) volume a b := by
  have hh := (fisherDeficit_intervalIntegrable p hp a b ha hab).add
    (covarianceFisher_intervalIntegrable p a b ha hab)
  change IntervalIntegrable (fun x => (freeFisher (τ p) (X p x)).toReal) volume a b
  simpa only [fisherDeficit, sub_add_cancel] using hh

end FiniteEntropySeparation.Model

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ModelFlowLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
 theorem heatFisher_shift_intervalIntegrable_oai (hp : 2≤p) {h a t : ℝ}
    (hh : 0<h) (ha : 0≤a) (hat : a≤t) :
    IntervalIntegrable (fun s => heatFisherReal p (h+s)) volume a t := by
  have hi := (heatFisherReal_intervalIntegrable p hp (h+a) (h+t) (by linarith) (by linarith)).comp_add_left h
  simpa only [add_sub_cancel_left] using hi
end FiniteEntropySeparation.Model

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.Model.heatFisher_shift_intervalIntegrable_oai := @OAI.FiniteEntropySeparation.Model.heatFisher_shift_intervalIntegrable_oai
