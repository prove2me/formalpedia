-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:24:33.85199+00:00
-- url     : https://prove2.me/submissions/e4be1b02-4701-4096-bdc1-7a6ec8c830d6

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002
import Theorems.Thm_OAI_FiniteEntropySeparation_Model_chiStar_tail_formula
import Theorems.Thm_OAI_FiniteEntropySeparation_Model_chi_gt_bot
import Theorems.Thm_OAI_FiniteEntropySeparation_chosen_chi_bound

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

theorem FreeSubalgebras.mono {κ : Type} {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {A B : κ → Subalgebra ℂ (H →L[ℂ] H)} (hA : FreeSubalgebras τ A)
    (hBA : ∀ i, B i ≤ A i) : FreeSubalgebras τ B := by
  intro k hk j a ha hc hadj
  exact hA k hk j a (fun r => hBA (j r) (ha r)) hc hadj

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

theorem semicircular_moment_succ {n : ℕ} (i : Fin n) (k : ℕ) :
    trace (tracialVector (Fin n)) (semicircular i ^ (k + 1)) =
      ∑ r ∈ Finset.range k, trace (tracialVector (Fin n)) (semicircular i ^ r) *
        trace (tracialVector (Fin n)) (semicircular i ^ (k - (r + 1))) := by
  have hw (j : ℕ) : wordEval semicircular (List.replicate j i) = semicircular i ^ j := by
    simp [wordEval]
  rw [pow_succ', ← hw k, semicircular_integration_by_parts]
  simp only [derivativeMoment, List.getElem_replicate,
    ite_true, wordMoment, List.take_replicate, List.drop_replicate]
  simp only [hw]
  rw [Fin.sum_univ_eq_sum_range (fun r =>
    trace (tracialVector (Fin n)) (semicircular i ^ min r k) *
      trace (tracialVector (Fin n)) (semicircular i ^ (k - (r + 1))))
    (List.replicate k i).length, List.length_replicate]
  apply Finset.sum_congr rfl
  intro r hr
  rw [min_eq_left (Nat.le_of_lt (Finset.mem_range.mp hr))]

private theorem sum_range_double {α : Type u2} [AddCommMonoid α] (f : ℕ → α) (k : ℕ) :
    ∑ r ∈ Finset.range (2 * k), f r =
      ∑ r ∈ Finset.range k, (f (2 * r) + f (2 * r + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show 2 * k + 2 = (2 * k + 1) + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem semicircular_moments {n : ℕ} (i : Fin n) (k : ℕ) :
    trace (tracialVector (Fin n)) (semicircular i ^ k) =
      if Even k then (catalan (k / 2) : ℂ) else 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [trace, tracialVector, basisVector]
    · rw [semicircular_moment_succ]
      rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
      · rw [ite_eq_right (by rw [Nat.even_iff]; omega : ¬Even (2 * m + 1))]
        apply Finset.sum_eq_zero
        intro r hr
        have hr' := Finset.mem_range.mp hr
        rw [ih r (by omega), ih (2 * m - (r + 1)) (by omega)]
        rcases Nat.mod_two_eq_zero_or_one r with he | ho
        · have : ¬ Even (2 * m - (r + 1)) := by rw [Nat.even_iff]; omega
          simp [this]
        · have : ¬ Even r := by rw [Nat.even_iff]; omega
          simp [this]
      · have he : Even (2 * m + 1 + 1) := by rw [Nat.even_iff]; omega
        rw [ite_eq_left he, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
          Finset.sum_range_succ, sum_range_double]
        have hs : ∀ r < m,
            trace (tracialVector (Fin n)) (semicircular i ^ (2 * r)) *
                trace (tracialVector (Fin n)) (semicircular i ^ (2 * m + 1 - (2 * r + 1))) +
              trace (tracialVector (Fin n)) (semicircular i ^ (2 * r + 1)) *
                trace (tracialVector (Fin n)) (semicircular i ^ (2 * m + 1 - (2 * r + 1 + 1))) =
            (catalan r : ℂ) * (catalan (m - r) : ℂ) := by
          intro r hr
          rw [ih (2 * r) (by omega), ih (2 * m + 1 - (2 * r + 1)) (by omega),
            ih (2 * r + 1) (by omega)]
          have h₁ : Even (2 * r) := by rw [Nat.even_iff]; omega
          have h₂ : Even (2 * m + 1 - (2 * r + 1)) := by rw [Nat.even_iff]; omega
          have h₃ : ¬Even (2 * r + 1) := by rw [Nat.even_iff]; omega
          simp only [h₁, h₂, h₃, ite_true, ite_false, zero_mul, add_zero]
          rw [show 2 * r / 2 = r by omega,
            show (2 * m + 1 - (2 * r + 1)) / 2 = m - r by omega]
        rw [Finset.sum_congr rfl (fun r hr => hs r (Finset.mem_range.mp hr))]
        rw [ih (2 * m) (by omega), ih (2 * m + 1 - (2 * m + 1)) (by omega)]
        have h₁ : Even (2 * m) := by rw [Nat.even_iff]; omega
        simp only [Nat.sub_self, h₁, ite_true, show Even (0 : ℕ) from ⟨0, rfl⟩, Nat.zero_div,
          catalan_zero, Nat.cast_one, mul_one]
        rw [show 2 * m / 2 = m by omega, catalan_succ,
          Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, catalan_zero,
          mul_one, Nat.cast_mul]

end Fock

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

 theorem leftGenerator_mem (k : Generator B N G) : leftGenerator k ∈ algebra B N G :=
  (mem_algebra_iff _).mpr (generators_commute k)

 theorem semicircularB_mem (b : B) : semicircularB (N := N) (G := G) b ∈ algebra B N G :=
  leftGenerator_mem (.inl b)
 theorem semicircularN_mem (i : N) : semicircularN (B := B) (G := G) i ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inl i))
 theorem unitaryG_mem (g : G) : unitaryG (B := B) (N := N) g ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inr g))

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

 theorem trace_semicircularB_pow {p : ℕ} (b : Fin p) (k : ℕ) :
    trace (tracialVector (Fin p) N G) (semicircularB b ^ k) =
      if Even k then (catalan (k / 2) : ℂ) else 0 := by
  have h := tensor_word_moment (N := N) (List.replicate k b) (1 : G)
  simpa [Fock.semicircular_moments] using h

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

 theorem noiseSlice_semicircular (i : N) :
    (semicircularN i).comp (noiseSlice (B := B) (G := G)) =
      noiseSlice.comp (Fock.semicircular i) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircularN i (noiseSlice (lp.single 2 w z)) =
    noiseSlice (Fock.semicircular i (lp.single 2 w z))
  rw [noiseSlice_single]
  cases w with
  | nil => simp [semicircularN, annihilationN_single, removeN, empty]
  | cons j w =>
    simp only [noiseWord_cons, semicircularN, add_apply, creationN_single,
      annihilationN_single, Fock.semicircular_single_cons, map_add, noiseSlice_single]
    by_cases hij : i = j <;> simp [removeN, leftN, push, hij]

 theorem noiseSlice_word (w : List N) :
    ((w.map (semicircularN (B := B) (G := G))).prod).comp noiseSlice =
      noiseSlice.comp ((w.map Fock.semicircular).prod) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun T : Fock.Space N →L[ℂ] Space B N G => T x) ih
    have hc := congrArg (fun T : Fock.Space N →L[ℂ] Space B N G =>
      T ((w.map Fock.semicircular).prod x)) (noiseSlice_semicircular (B := B) (G := G) i)
    simp only [ContinuousLinearMap.comp_apply] at hi hc
    simpa only [ContinuousLinearMap.comp_apply, List.map_cons, List.prod_cons,
      mul_apply_eq_comp, hi] using hc

 theorem noiseSlice_vacuum_coefficient (x : Fock.Space N) :
    inner ℂ (basis (empty : Word B N G)) (noiseSlice x) =
      inner ℂ (Fock.basisVector []) x := by
  have h := (LabelHilbert.embedding (noiseWord (B := B) (G := G)) noiseWord_injective).inner_map_map
    (Fock.basisVector []) x
  change inner ℂ (noiseSlice (Fock.basisVector [])) (noiseSlice x) = _ at h
  simpa using h

 theorem noise_word_moment (w : List N) :
    trace (tracialVector B N G) ((w.map semicircularN).prod) =
      trace (Fock.tracialVector N) ((w.map Fock.semicircular).prod) := by
  change inner ℂ (basis (empty : Word B N G)) ((w.map semicircularN).prod (basis empty)) = _
  rw [← noiseWord_nil, ← noiseSlice_basis, ← ContinuousLinearMap.comp_apply,
    noiseSlice_word, ContinuousLinearMap.comp_apply, noiseSlice_basis, noiseWord_nil,
    noiseSlice_vacuum_coefficient]
  rfl

 theorem trace_semicircularN_pow {k : ℕ} (i : Fin k) (r : ℕ) :
    trace (tracialVector B (Fin k) G) (semicircularN i ^ r) =
      if Even r then (catalan (r / 2) : ℂ) else 0 := by
  have h := noise_word_moment (B := B) (G := G) (List.replicate r i)
  simpa [Fock.semicircular_moments] using h

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorConcat
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

 theorem leftB_concat (i : B) (w v : Word B N G) :
    leftB i (concat w v) = concat (leftB i w) v := by
  rcases w with ⟨⟨l,g⟩,t⟩
  cases t <;> rfl

 theorem leftN_concat (i : N) (w v : Word B N G) :
    leftN i (concat w v) = concat (leftN i w) v := rfl

 theorem leftG_concat (g : G) (w v : Word B N G) :
    leftG g (concat w v) = concat (leftG g w) v := by
  rcases w with ⟨⟨l,h⟩,t⟩
  cases t with
  | nil => simp [concat, concatAux, atomMul, leftG, mul_assoc]
  | cons a t => rfl

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem creationB_suffix (i : B) (v : Word B N G) :
    Commute (creationB i) (suffixEmbedding v) := by
  apply LabelHilbert.lift_commute
  intro w
  exact leftB_concat i w v

 theorem creationN_suffix (i : N) (v : Word B N G) :
    Commute (creationN i) (suffixEmbedding v) := by
  apply LabelHilbert.lift_commute
  intro w
  exact leftN_concat i w v

 theorem unitaryG_suffix (g : G) (v : Word B N G) :
    Commute (unitaryG g) (suffixEmbedding v) := by
  apply LabelHilbert.lift_commute
  intro w
  exact leftG_concat g w v

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_empty [DecidableEq B] [DecidableEq N] [DecidableEq G] (J : Set N) : Supported J (empty : Word B N G) := by
  simp [Supported, empty]

omit [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_leftB [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G} (hw : Supported J w) (i : B) :
    Supported J (leftB i w) := hw

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_leftG [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G} (hw : Supported J w) (g : G) :
    Supported J (leftG g w) := hw

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_leftN [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G} (hw : Supported J w)
    {i : N} (hi : i ∈ J) : Supported J (leftN i w) := by
  simpa [Supported, leftN, push] using And.intro hi hw

omit [DecidableEq N] in
theorem supported_ne_empty_starts [DecidableEq N] {J : Set N} {w : Word B N G}
    (hw : Supported J w) (hne : w ≠ empty) : StartsBackground J w := by
  by_cases ha : w.1 = ([],1)
  · rcases w with ⟨a,t⟩
    cases ha
    cases t with
    | nil => exact False.elim (hne rfl)
    | cons p t =>
      rcases p with ⟨i,a⟩
      exact Or.inr ⟨i, hw (i,a) (by simp), (a,t), rfl⟩
  · exact Or.inl ha

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem startsBackground_concat [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G}
    (hw : StartsBackground J w) {i : N} {v : Word B N G} (hv : StartsNoise i v) :
    StartsBackground J (concat w v) := by
  obtain ⟨v,rfl⟩ := hv
  rcases hw with (ha | ⟨j,hj,u,rfl⟩)
  · left
    rcases w with ⟨a,t⟩
    cases t with
    | nil => simpa [concat, concatAux, atomMul, leftN, push] using ha
    | cons p t => exact ha
  · exact Or.inr ⟨j,hj,concat u (leftN i v),rfl⟩

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem startsBackground_not_noise [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G}
    (hw : StartsBackground J w) {i : N} (hi : i ∉ J) : ¬ StartsNoise i w := by
  rintro ⟨v,rfl⟩
  rcases hw with (hw | ⟨j,hj,u,he⟩)
  · exact hw rfl
  · have : i = j := by simpa [leftN, push, Prod.mk.injEq] using congrArg (fun w => w.2.head?.map Prod.fst) he
    exact hi (this ▸ hj)

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorFreeness
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
theorem basis_mem_labelSpace [Group G] {P : Word B N G → Prop} {w : Word B N G} (hw : P w) :
    basis w ∈ labelSpace P := Submodule.subset_span ⟨w, hw, rfl⟩

omit [Group G] in
theorem labelSpace_action [Group G] {P Q : Word B N G → Prop} {T : Space B N G →L[ℂ] Space B N G}
    (hT : ∀ w, P w → T (basis w) ∈ labelSpace Q) {x : Space B N G}
    (hx : x ∈ labelSpace P) : T x ∈ labelSpace Q := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w,hw,rfl⟩ := hx; exact hT w hw
  | zero => simp
  | add x y _ _ hx hy => simpa using (labelSpace Q).add_mem hx hy
  | smul z x _ hx => simpa using (labelSpace Q).smul_mem z hx

 theorem centered_labelSpace_suffix {P Q : Word B N G → Prop}
    {x : Space B N G} (hx : x ∈ labelSpace P) (v : Word B N G)
    (hPQ : ∀ w, P w → w ≠ empty → Q (concat w v)) :
    suffixEmbedding v (x - x empty • basis empty) ∈ labelSpace Q := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    by_cases he : w = empty
    · subst w
      simp [basis, lp.single_apply]
    · have hz : (basis w : Space B N G) empty = 0 := by
        simp [basis, lp.single_apply, Ne.symm he]
      rw [hz, zero_smul, sub_zero, suffixEmbedding_basis]
      exact basis_mem_labelSpace (hPQ w hw he)
  | zero => simp
  | add x y _ _ hx hy =>
    have h : (x + y) - (x + y) empty • basis empty =
        (x - x empty • basis empty) + (y - y empty • basis empty) := by
      change (x + y) - (x empty + y empty) • basis empty = _
      rw [add_smul]; abel
    rw [h, map_add]
    exact (labelSpace Q).add_mem hx hy
  | smul z x _ hx =>
    have h : z • x - (z • x) empty • basis empty =
        z • (x - x empty • basis empty) := by
      change z • x - (z * x empty) • basis empty = _
      rw [smul_sub, smul_smul]
    rw [h, map_smul]
    exact (labelSpace Q).smul_mem z hx

 theorem labelSpace_vacuum_zero {P : Word B N G → Prop} (hP : ¬ P empty)
    {x : Space B N G} (hx : x ∈ labelSpace P) : x empty = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    have hne : empty ≠ w := fun h => hP (h ▸ hw)
    simp [basis, lp.single_apply, hne]
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul z x _ hx => simp [hx]

 theorem trace_eq_vacuum_coefficient (T : Space B N G →L[ℂ] Space B N G) :
    trace (tracialVector B N G) T = (T (basis empty)) empty := by
  simp [trace, tracialVector, basis, lp.inner_single_left]

 theorem annihilationB_preserves_supported {J : Set N} {w : Word B N G}
    (hw : Supported J w) (b : B) :
    star (creationB b) (basis w) ∈ labelSpace (Supported J) := by
  rw [basis, annihilationB_single]
  cases h : removeB b w with
  | none => exact (labelSpace _).zero_mem
  | some v =>
    have hv := (removeB_spec b v w).mp h
    subst w
    exact basis_mem_labelSpace hw

 theorem annihilationN_preserves_supported {J : Set N} {w : Word B N G}
    (hw : Supported J w) (i : N) :
    star (creationN i) (basis w) ∈ labelSpace (Supported J) := by
  rw [basis, annihilationN_single]
  cases h : removeN i w with
  | none => exact (labelSpace _).zero_mem
  | some v =>
    have hv := (removeN_spec i v w).mp h
    subst w
    apply basis_mem_labelSpace
    intro p hp
    exact hw p (List.mem_cons_of_mem _ hp)

 theorem background_preserves_supported {J : Set N}
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    ∀ x ∈ labelSpace (Supported J), T x ∈ labelSpace (Supported J) := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,hi,rfl⟩)
    · apply labelSpace_action
      intro w hw
      change creationB b (basis w) + star (creationB b) (basis w) ∈ _
      apply Submodule.add_mem
      · simpa [basis] using basis_mem_labelSpace (supported_leftB hw b)
      · exact annihilationB_preserves_supported hw b
    · apply labelSpace_action
      intro w hw
      simpa [basis] using basis_mem_labelSpace (supported_leftG hw g)
    · apply labelSpace_action
      intro w hw
      change creationN i (basis w) + star (creationN i) (basis w) ∈ _
      apply Submodule.add_mem
      · simpa [basis] using basis_mem_labelSpace (supported_leftN hw hi)
      · exact annihilationN_preserves_supported hw i
  | algebraMap z =>
    intro x hx
    simpa using (labelSpace (Supported J)).smul_mem z hx
  | add T U _ _ hT hU =>
    intro x hx
    exact Submodule.add_mem _ (hT x hx) (hU x hx)
  | mul T U _ _ hT hU =>
    intro x hx
    exact hT (U x) (hU x hx)

omit [DecidableEq N] [DecidableEq G] in
theorem removeB_concat_noise [DecidableEq N] [DecidableEq G] (b : B) (w v : Word B N G) (i : N) :
    removeB b (concat w (leftN i v)) = (removeB b w).map (fun u => concat u (leftN i v)) := by
  rcases w with ⟨⟨l,g⟩,t⟩
  cases t with
  | nil =>
    cases l with
    | nil => simp [concat, concatAux, atomMul, leftN, push, removeB]
    | cons c l =>
      by_cases h : b = c <;> simp [concat, concatAux, atomMul, leftN, push, removeB, h]
  | cons p t =>
    rcases p with ⟨j,a⟩
    cases l with
    | nil => rfl
    | cons c l =>
      by_cases h : b = c <;> simp [concat, concatAux, leftN, push, removeB, h]

 theorem removeN_concat_noise (i k : N) (hik : i ≠ k) (w v : Word B N G) :
    removeN i (concat w (leftN k v)) = (removeN i w).map (fun u => concat u (leftN k v)) := by
  rcases w with ⟨a,t⟩
  cases t with
  | nil =>
    by_cases ha : a = ([],1)
    · subst a
      simp [concat, concatAux, atomMul, leftN, push, removeN, hik]
    · have ham : atomMul a ([],1) = a := by simp [atomMul]
      simp [concat, concatAux, leftN, push, removeN, ha, ham]
  | cons p t =>
    rcases p with ⟨j,a'⟩
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [concat, concatAux, leftN, push, removeN, ha, hij]

 theorem annihilationB_suffix_noise (b : B) (i : N) (v : Word B N G) :
    Commute (star (creationB b)) (suffixEmbedding (leftN i v)) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (creationB b) (suffixEmbedding (leftN i v) (lp.single 2 w z)) =
    suffixEmbedding (leftN i v) (star (creationB b) (lp.single 2 w z))
  rw [suffixEmbedding_single, annihilationB_single, annihilationB_single, removeB_concat_noise]
  cases removeB b w <;> simp

 theorem annihilationN_suffix_noise (i k : N) (hik : i ≠ k) (v : Word B N G) :
    Commute (star (creationN i)) (suffixEmbedding (leftN k v)) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (creationN i) (suffixEmbedding (leftN k v) (lp.single 2 w z)) =
    suffixEmbedding (leftN k v) (star (creationN i) (lp.single 2 w z))
  rw [suffixEmbedding_single, annihilationN_single, annihilationN_single,
    removeN_concat_noise i k hik]
  cases removeN i w <;> simp

 theorem background_commutes_suffix {J : Set N} {k : N} (hk : k ∉ J) (v : Word B N G)
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    Commute T (suffixEmbedding (leftN k v)) := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,hi,rfl⟩)
    · exact (creationB_suffix b _).add_left (annihilationB_suffix_noise b k v)
    · exact unitaryG_suffix g _
    · exact (creationN_suffix i _).add_left
        (annihilationN_suffix_noise i k (fun h => hk (h ▸ hi)) v)
  | algebraMap z => exact Algebra.commute_algebraMap_left z _
  | add T U _ _ hT hU => exact hT.add_left hU
  | mul T U _ _ hT hU => exact hT.mul_left hU

 theorem centered_background_basis {J : Set N}
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J)
    (hcenter : trace (tracialVector B N G) T = 0) {k : N} (hk : k ∉ J)
    {v : Word B N G} (hv : StartsNoise k v) :
    T (basis v) ∈ labelSpace (StartsBackground J) := by
  obtain ⟨v,rfl⟩ := hv
  have hc := congrArg (fun A : Space B N G →L[ℂ] Space B N G => A (basis empty))
    (background_commutes_suffix hk v hT).eq
  simp only [mul_apply_eq_comp, suffixEmbedding_basis, concat_empty_left] at hc
  have hx := background_preserves_supported hT (basis empty)
    (basis_mem_labelSpace (supported_empty J))
  have hz : (T (basis empty)) empty = 0 := by rwa [← trace_eq_vacuum_coefficient]
  have hs := centered_labelSpace_suffix hx (leftN k v)
    (fun w hw hne => startsBackground_concat (supported_ne_empty_starts hw hne) ⟨v,rfl⟩)
  simpa only [hz, zero_smul, sub_zero, ← hc] using hs

 theorem removeN_none_iff (i : N) (w : Word B N G) :
    removeN i w = none ↔ ¬ StartsNoise i w := by
  constructor
  · intro h ⟨v,hv⟩
    have hv' := (removeN_spec i v w).mpr hv.symm
    rw [h] at hv'
    contradiction
  · intro h
    cases he : removeN i w with
    | none => rfl
    | some v => exact False.elim (h ⟨v, ((removeN_spec i v w).mp he).symm⟩)

 theorem semicircularN_basis_leftN (i j : N) (w : Word B N G) :
    semicircularN i (basis (leftN j w)) =
      basis (leftN i (leftN j w)) + if i = j then basis w else 0 := by
  by_cases h : i = j <;> simp [semicircularN, basis, annihilationN_single, removeN, leftN, push, h]

 theorem semicircularN_basis_not_starts (i : N) (w : Word B N G)
    (hw : ¬ StartsNoise i w) :
    semicircularN i (basis w) = basis (leftN i w) := by
  simp [semicircularN, basis, annihilationN_single, (removeN_none_iff i w).mpr hw]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem pureSupported_empty [DecidableEq B] [DecidableEq N] [DecidableEq G] (J : Set N) : PureSupported J (empty : Word B N G) :=
  ⟨[], by simp, rfl⟩

 theorem semicircularN_preserves_pureSupported {J : Set N} {i : N} (hi : i ∈ J)
    {x : Space B N G} (hx : x ∈ labelSpace (PureSupported J)) :
    semicircularN i x ∈ labelSpace (PureSupported J) := by
  apply labelSpace_action (x := x) _ hx
  rintro w ⟨l,hl,rfl⟩
  cases l with
  | nil =>
    have hn : ¬ StartsNoise i (empty : Word B N G) := by
      rintro ⟨v,hv⟩
      simp [empty, leftN, push] at hv
    rw [noiseWord_nil, semicircularN_basis_not_starts i empty hn]
    exact basis_mem_labelSpace ⟨[i], by simpa using hi, rfl⟩
  | cons j l =>
    rw [noiseWord_cons, semicircularN_basis_leftN]
    apply Submodule.add_mem
    · exact basis_mem_labelSpace ⟨i :: j :: l, by simpa using And.intro hi hl, rfl⟩
    · split_ifs
      · exact basis_mem_labelSpace ⟨l, fun k hk => hl k (List.mem_cons_of_mem _ hk), rfl⟩
      · exact Submodule.zero_mem _

 theorem semicircularN_pureSuffix {J : Set N} {i : N} (hi : i ∈ J)
    (v : Word B N G) (hv : ∀ j ∈ J, ¬ StartsNoise j v)
    {x : Space B N G} (hx : x ∈ labelSpace (PureSupported J)) :
    semicircularN i (suffixEmbedding v x) = suffixEmbedding v (semicircularN i x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,⟨l,hl,rfl⟩,rfl⟩ := hx
    cases l with
    | nil =>
      rw [noiseWord_nil, suffixEmbedding_basis, concat_empty_left,
        semicircularN_basis_not_starts i v (hv i hi)]
      have hn : ¬ StartsNoise i (empty : Word B N G) := by
        rintro ⟨w,hw⟩
        simp [empty, leftN, push] at hw
      rw [semicircularN_basis_not_starts i empty hn, suffixEmbedding_basis]
      rw [← leftN_concat, concat_empty_left]
    | cons j l =>
      rw [noiseWord_cons, suffixEmbedding_basis, ← leftN_concat,
        semicircularN_basis_leftN, semicircularN_basis_leftN, map_add]
      by_cases h : i = j <;> simp [h, suffixEmbedding_basis, ← leftN_concat]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul z x _ hx => simp [hx]

 theorem noise_adjoin_suffix {J : Set N} {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ Algebra.adjoin ℂ (semicircularN '' J)) (v : Word B N G)
    (hv : ∀ j ∈ J, ¬ StartsNoise j v) :
    ∀ x ∈ labelSpace (PureSupported J), T x ∈ labelSpace (PureSupported J) ∧
      T (suffixEmbedding v x) = suffixEmbedding v (T x) := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨i,hi,rfl⟩ := hT
    exact fun x hx => ⟨semicircularN_preserves_pureSupported hi hx,
      semicircularN_pureSuffix hi v hv hx⟩
  | algebraMap z =>
    intro x hx
    exact ⟨by simpa using (labelSpace (PureSupported J)).smul_mem z hx, by simp⟩
  | add T U _ _ hT hU =>
    intro x hx
    exact ⟨Submodule.add_mem _ (hT x hx).1 (hU x hx).1,
      by simp only [add_apply, (hT x hx).2, (hU x hx).2, map_add]⟩
  | mul T U _ _ hT hU =>
    intro x hx
    exact ⟨(hT (U x) (hU x hx).1).1,
      by simp only [mul_apply_eq_comp, (hU x hx).2, (hT (U x) (hU x hx).1).2]⟩

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem pureSupported_ne_empty_concat [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G}
    (hw : PureSupported J w) (hne : w ≠ empty) (v : Word B N G) :
    StartsNoiseIn J (concat w v) := by
  obtain ⟨l,hl,rfl⟩ := hw
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons i l => exact ⟨i, hl i (by simp), concat (noiseWord l) v, rfl⟩

 theorem centered_noise_basis {J : Set N} {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ Algebra.adjoin ℂ (semicircularN '' J))
    (hc : trace (tracialVector B N G) T = 0) (v : Word B N G)
    (hv : ∀ j ∈ J, ¬ StartsNoise j v) :
    T (basis v) ∈ labelSpace (StartsNoiseIn J) := by
  have h := noise_adjoin_suffix hT v hv (basis empty)
    (basis_mem_labelSpace (pureSupported_empty J))
  have hz : (T (basis empty)) empty = 0 := by rwa [← trace_eq_vacuum_coefficient]
  have hs := centered_labelSpace_suffix h.1 v
    (fun w hw hne => pureSupported_ne_empty_concat hw hne v)
  simpa only [hz, zero_smul, sub_zero, ← h.2, suffixEmbedding_basis,
    concat_empty_left] using hs

 theorem centered_coordinate_basis {i : N} {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ Algebra.adjoin ℂ {semicircularN i})
    (hc : trace (tracialVector B N G) T = 0) (v : Word B N G) (hv : ¬ StartsNoise i v) :
    T (basis v) ∈ labelSpace (StartsNoise i) := by
  have hT' : T ∈ Algebra.adjoin ℂ (semicircularN '' {i}) := by simpa using hT
  have h := centered_noise_basis hT' hc v (by simpa using hv)
  have he : StartsNoiseIn ({i} : Set N) = (StartsNoise i : Word B N G → Prop) := by
    funext w
    simp [StartsNoiseIn]
  rwa [he] at h

 theorem centered_background_vacuum {J : Set N}
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J)
    (hc : trace (tracialVector B N G) T = 0) :
    T (basis empty) ∈ labelSpace (StartsBackground J) := by
  have hx := background_preserves_supported hT (basis empty)
    (basis_mem_labelSpace (supported_empty J))
  have hz : (T (basis empty)) empty = 0 := by rwa [← trace_eq_vacuum_coefficient]
  have hs := centered_labelSpace_suffix hx empty
    (fun w hw hne => by simpa using supported_ne_empty_starts hw hne)
  have hid : suffixEmbedding (empty : Word B N G) = 1 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro w
    apply ContinuousLinearMap.ext
    intro z
    simp
  simpa only [hz, zero_smul, sub_zero, hid, one_apply_eq_self] using hs

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem startsNoise_injective [DecidableEq B] [DecidableEq N] [DecidableEq G] {i j : N} {w : Word B N G}
    (hi : StartsNoise i w) (hj : StartsNoise j w) : i = j := by
  obtain ⟨v,rfl⟩ := hi
  obtain ⟨u,hu⟩ := hj
  have h := congrArg (fun w : Word B N G => w.2.head?.map Prod.fst) hu
  simpa [leftN, push] using h

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem not_startsNoise_empty [DecidableEq B] [DecidableEq N] [DecidableEq G] (i : N) : ¬ StartsNoise i (empty : Word B N G) := by
  rintro ⟨v,hv⟩
  simp [empty, leftN, push] at hv

 theorem not_startsBackground_empty (J : Set N) : ¬ StartsBackground J (empty : Word B N G) := by
  rintro (h | ⟨i,_,hi⟩)
  · exact h rfl
  · exact not_startsNoise_empty i hi

 theorem centered_noiseAlgebras_vacuum {κ : Type} (J : Set N) (σ : κ → N)
    (i : Option κ) {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ noiseAlgebras J σ i) (hc : trace (tracialVector B N G) T = 0) :
    T (basis empty) ∈ labelSpace (StartsColor J σ i) := by
  cases i with
  | none => exact centered_background_vacuum hT hc
  | some i => exact centered_coordinate_basis hT hc empty (not_startsNoise_empty _)

 theorem centered_noiseAlgebras_starts {κ : Type} (J : Set N) (σ : κ → N)
    (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    {i j : Option κ} (hij : i ≠ j) {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ noiseAlgebras J σ i) (hc : trace (tracialVector B N G) T = 0)
    {x : Space B N G} (hx : x ∈ labelSpace (StartsColor J σ j)) :
    T x ∈ labelSpace (StartsColor J σ i) := by
  apply labelSpace_action (x := x) _ hx
  intro w hw
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some j => exact centered_background_basis hT hc (hs j) hw
  | some i =>
    apply centered_coordinate_basis hT hc
    cases j with
    | none => exact startsBackground_not_noise hw (hs i)
    | some j =>
      intro hi
      exact hij (congrArg some (hσ (startsNoise_injective hi hw)))

 theorem alternating_noise_product_starts {κ : Type} (J : Set N) (σ : κ → N)
    (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    ∀ (k : ℕ) (hk : 0 < k) (j : Fin k → Option κ)
      (a : Fin k → Space B N G →L[ℂ] Space B N G),
      (∀ r, a r ∈ noiseAlgebras J σ (j r)) →
      (∀ r, trace (tracialVector B N G) (a r) = 0) →
      (∀ (r : ℕ) (hr : r + 1 < k),
        j ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ ≠ j ⟨r + 1, hr⟩) →
      (List.ofFn a).prod (basis empty) ∈ labelSpace (StartsColor J σ (j ⟨0,hk⟩)) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk j a ha hc hadj
    rw [List.ofFn_succ, List.prod_cons, mul_apply_eq_comp]
    cases k with
    | zero => exact centered_noiseAlgebras_vacuum J σ (j 0) (ha 0) (hc 0)
    | succ k =>
      have ht := ih (by omega) (fun r => j r.succ) (fun r => a r.succ)
        (fun r => ha r.succ) (fun r => hc r.succ) (by
          intro r hr
          exact hadj (r+1) (by omega))
      exact centered_noiseAlgebras_starts J σ hσ hs (hadj 0 (by omega)) (ha 0) (hc 0) ht

theorem free_noiseAlgebras {κ : Type} (J : Set N) (σ : κ → N)
    (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    FreeSubalgebras (tracialVector B N G) (noiseAlgebras J σ) := by
  intro k hk j a ha hc hadj
  rw [trace_eq_vacuum_coefficient]
  apply labelSpace_vacuum_zero _ (alternating_noise_product_starts J σ hσ hs k hk j a ha hc hadj)
  cases j ⟨0,hk⟩ with
  | none => exact not_startsBackground_empty J
  | some i => exact not_startsNoise_empty (σ i)

theorem freeStandardNoise {m n : ℕ} (J : Set (Fin m))
    (X : Fin n → Space B (Fin m) G →L[ℂ] Space B (Fin m) G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → Fin m) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    FreeStandardNoise (tracialVector B (Fin m) G) X (fun i => semicircularN (σ i)) := by
  refine ⟨fun i k => trace_semicircularN_pow (σ i) k, ?_⟩
  apply (free_noiseAlgebras J σ hσ hs).mono
  intro j
  cases j with
  | none =>
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact hX i
  | some i => exact le_rfl

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

namespace FreeTensor
variable {B N : Type} [DecidableEq B] [DecidableEq N] (p : ℕ) [NeZero p]

 theorem equidiscreteSignal_selfAdjoint : IsSelfAdjoint (equidiscreteSignal (B := B) (N := N) p) :=
  spectralSignal_selfAdjoint _

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
 theorem semicircularN_selfAdjoint (i : N) : IsSelfAdjoint (semicircularN (B := B) (G := G) i) :=
  IsSelfAdjoint.add_star_self (creationN (B := B) (G := G) i)

 theorem backgroundAlgebra_le (J : Set N) :
    backgroundAlgebra (B := B) (G := G) J ≤ (algebra B N G).toStarSubalgebra.toSubalgebra := by
  apply Algebra.adjoin_le
  rintro _ ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,_,rfl⟩)
  · exact semicircularB_mem b
  · exact unitaryG_mem g
  · exact semicircularN_mem i

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))
 theorem semicircularN_mem_background (J : Set N) {i : N} (hi : i ∈ J) :
    semicircularN (B := B) (G := G) i ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inr ⟨i,hi,rfl⟩)

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

 theorem heatTuple_mem_background {n : ℕ} (J : Set N)
    (X S : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (hS : ∀ i, S i ∈ backgroundAlgebra J)
    (u : ℝ) (i : Fin n) : heatTuple X S u i ∈ backgroundAlgebra J :=
  (backgroundAlgebra J).add_mem (hX i) ((backgroundAlgebra J).smul_mem (hS i) _)

end FreeTensor

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

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

 theorem X_mem_background (h : ℝ) (i : Fin (p+1)) :
    X p h i ∈ backgroundAlgebra (oldNoise p) := by
  apply heatTuple_mem_background _ _ _ (C_mem_background p (oldNoise p))
  intro j
  exact semicircularN_mem_background _ ⟨j,rfl⟩

 theorem auxiliaryNoise_free (h : ℝ) : FreeStandardNoise (τ p) (X p h) (auxiliaryNoise p) :=
  freeStandardNoise (oldNoise p) (X p h) (X_mem_background p h) (auxiliaryIndex p)
    (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p)

 theorem X_mem (h : ℝ) (i : Fin (p+1)) : X p h i ∈ M p :=
  backgroundAlgebra_le _ (X_mem_background p h i)
 theorem X_selfAdjoint (h : ℝ) (i : Fin (p+1)) : IsSelfAdjoint (X p h i) :=
  heatTuple_selfAdjoint (C p) (initialNoise p) (C_selfAdjoint p)
    (fun _index => semicircularN_selfAdjoint _) h i

omit [NeZero p] in
theorem auxiliaryNoise_mem [NeZero p] (i : Fin (p+1)) : auxiliaryNoise p i ∈ M p := semicircularN_mem _

omit [NeZero p] in
theorem auxiliaryNoise_selfAdjoint [NeZero p] (i : Fin (p+1)) : IsSelfAdjoint (auxiliaryNoise p i) :=
  semicircularN_selfAdjoint _

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixSpectralMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem equidiscreteAtom_injective {p : ℕ} (hp : 2≤p) : Function.Injective (equidiscreteAtom p) := by
  intro l k h
  have hd : (p:ℝ)-1≠0 := by
    have hh : (2:ℝ)≤p := by exact_mod_cast hp
    linarith
  unfold equidiscreteAtom at h
  have he : (l.val:ℝ)=(k.val:ℝ) := by field_simp [hd] at h; linarith
  exact Fin.ext (by exact_mod_cast he)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralTestFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter
open scoped Topology ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem univariateMoment_continuous (q : Polynomial ℝ) (i : Fin n) : Continuous (fun m : List (Fin n) → ℂ => univariateMoment m q i) := by
  unfold univariateMoment
  fun_prop
 theorem commutatorMoment_continuous (i j : Fin n) : Continuous (fun m : List (Fin n) → ℂ => commutatorMoment m i j) := by
  unfold commutatorMoment
  fun_prop
 section Operators
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M)
 theorem continuous_tuple_wordMoments : Continuous (fun X : Fin n → H →L[ℂ] H => wordMoment τ X) := by
  apply continuous_pi
  intro w
  unfold wordMoment trace wordEval
  fun_prop
 theorem univariateMoment_word (X : Fin n → H →L[ℂ] H) (q : Polynomial ℝ) (i : Fin n) :
    univariateMoment (wordMoment τ X) q i=∑k∈q.support,q.coeff k*(trace τ (X i^k)).re := by
  simp [univariateMoment,wordMoment,wordEval]
 theorem commutatorMoment_word_zero (X : Fin n → H →L[ℂ] H) (i j : Fin n) (hc : Commute (X i) (X j)) :
    commutatorMoment (wordMoment τ X) i j=0 := by
  have h1 : X i*(X j*(X j*X i))=X i*(X j*(X i*X j)) := by rw [hc.eq.symm]
  have h2 : X j*(X i*(X j*X i))=X j*(X i*(X i*X j)) := by rw [hc.eq.symm]
  simp only [commutatorMoment,wordMoment,wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,h1,h2,sub_self,zero_sub,neg_add_cancel,Complex.zero_re]
end Operators
namespace Model
variable (p : ℕ) [NeZero p]
 theorem continuous_X : Continuous (X p) := by
  apply continuous_pi
  intro i
  unfold X heatTuple
  fun_prop
 theorem continuous_X_moments : Continuous (fun h : ℝ => wordMoment (τ p) (X p h)) :=
  (continuous_tuple_wordMoments (τ p)).comp (continuous_X p)
 theorem X_zero : X p 0=C p := by ext i; simp [X,heatTuple]
 theorem C_second (i : Fin p) : (wordMoment (τ p) (C p) [i.castSucc,i.castSucc]).re=1 := by
  have he := FreeTensor.trace_semicircularB_pow (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)) i 2
  simpa [wordMoment,wordEval,pow_two,C_castSucc] using congrArg Complex.re he
 theorem C_fourth (i : Fin p) : (wordMoment (τ p) (C p) [i.castSucc,i.castSucc,i.castSucc,i.castSucc]).re=2 := by
  have he := FreeTensor.trace_semicircularB_pow (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)) i 4
  simpa [wordMoment,wordEval,pow_succ,mul_assoc,C_castSucc,catalan,show Even (4:ℕ) from ⟨2,by norm_num⟩] using congrArg Complex.re he
 theorem C_commutator (i : Fin p) : commutatorMoment (wordMoment (τ p) (C p)) i.castSucc (Fin.last p)=0 := by
  apply commutatorMoment_word_zero
  rw [C_castSucc,C_last]
  exact (FreeTensor.equidiscreteSignal_commutes_B p i).symm
 theorem C_univariateMoment (q : Polynomial ℝ) :
    univariateMoment (wordMoment (τ p) (C p)) q (Fin.last p)=(p:ℝ)⁻¹*∑l : Fin p,q.eval (equidiscreteAtom p l) := by
  rw [univariateMoment_word]
  simp only [C_last,FreeTensor.equidiscreteSignal_moments,← Complex.ofReal_pow,← Complex.ofReal_sum,
    ← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_mul,Complex.ofReal_re]
  simp only [mul_left_comm (q.coeff _),← mul_sum]
  congr 1
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [sum_comm]
  simp only [mul_sum]
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {p : ℕ}
 theorem badFraction_pos [NeZero p] : 0<badFraction p := by
  have hp : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  unfold badFraction
  positivity
 theorem spectralBasis_eval (hp : 2≤p) (l k : Fin p) :
    (spectralBasis p l).eval (equidiscreteAtom p k)=if l=k then 1 else 0 := by
  by_cases h : l=k
  · subst k; simp [spectralBasis,Lagrange.eval_basis_self (equidiscreteAtom_injective hp).injOn]
  · simp [spectralBasis,h,Lagrange.eval_basis_of_ne h]
 theorem spectralAnnihilator_eval (r : ℝ) :
    (spectralAnnihilator p).eval r=∏l : Fin p,(r-equidiscreteAtom p l) := by
  rw [spectralAnnihilator, Polynomial.eval_prod]
  simp
 theorem spectralAnnihilator_at (l : Fin p) : (spectralAnnihilator p).eval (equidiscreteAtom p l)=0 := by
  rw [spectralAnnihilator_eval]
  exact prod_eq_zero (mem_univ l) (sub_self _)
 theorem exists_spectral_parameters [NeZero p] (hp : 2≤p) : ∃δ Δ : ℝ,0<δ ∧ 0<Δ ∧ δ≤Δ/4 ∧
    (∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|) ∧
    (∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2) := by
  classical
  let Δ : ℝ := univ.inf' univ_nonempty (fun ij : Fin p×Fin p => if ij.1=ij.2 then 1 else |equidiscreteAtom p ij.1-equidiscreteAtom p ij.2|)
  have hΔ : 0<Δ := by
    apply (lt_inf'_iff _).mpr
    rintro ⟨i,j⟩ _
    dsimp
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr (fun he => h (equidiscreteAtom_injective hp he)))
  have hsep (i j : Fin p) (h : i≠j) : Δ≤|equidiscreteAtom p i-equidiscreteAtom p j| := by
    have hh := inf'_le (s := (univ:Finset (Fin p×Fin p))) (f := fun ij : Fin p×Fin p => if ij.1=ij.2 then (1:ℝ) else |equidiscreteAtom p ij.1-equidiscreteAtom p ij.2|) (mem_univ (i,j))
    simpa only [ite_eq_right h] using hh
  have hev : ∀ᶠs : ℝ in 𝓝 0,∀l : Fin p,(3:ℝ)/4<((spectralBasis p l).eval (equidiscreteAtom p l+s))^2 := by
    rw [eventually_all]
    intro l
    have hc : Continuous (fun s : ℝ => ((spectralBasis p l).eval (equidiscreteAtom p l+s))^2) := by fun_prop
    have hh : (3:ℝ)/4<((spectralBasis p l).eval (equidiscreteAtom p l+0))^2 := by norm_num [spectralBasis_eval hp]
    exact (isOpen_lt continuous_const hc).mem_nhds hh
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hev
  let δ := min (Δ/4) (ε/2)
  refine ⟨δ,Δ,lt_min (by positivity) (by positivity),hΔ,min_le_left _ _,hsep,?_⟩
  intro l r hr
  have hs : r-equidiscreteAtom p l ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact hr.trans_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hh := he hs l
  convert hh.le using 1 ; congr 2 ; ring
 theorem spectralGood_isOpen (p : ℕ) (δ Δ : ℝ) : IsOpen {m | spectralGood p δ Δ m} := by
  unfold spectralGood
  simp only [ofPred_and,ofPred_forall]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply _))).inter
      ((isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const).inter
      (isOpen_lt (commutatorMoment_continuous _ _) continuous_const))
  · exact (isOpen_iInter_of_finite (fun l => isOpen_lt (univariateMoment_continuous _ _) continuous_const)).inter
      (isOpen_lt (univariateMoment_continuous _ _) continuous_const)
 theorem spectralGood_C [NeZero p] (hp : 2≤p) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) :
    spectralGood p δ Δ (wordMoment (Model.τ p) (Model.C p)) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [Model.C_second,Model.C_fourth,Model.C_commutator]
    refine ⟨by norm_num,by norm_num,by positivity⟩
  · intro l
    rw [Model.C_univariateMoment]
    simp only [Polynomial.eval_pow,spectralBasis_eval hp]
    have he : (∑k : Fin p,(if l=k then (1:ℝ) else 0)^2)=1 := by simp [eq_comm]
    rw [he,mul_one]
    have hp' : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
    apply (mul_lt_mul_iff_left₀ hp').mp
    field_simp
    norm_num
  · rw [Model.C_univariateMoment]
    simp only [Polynomial.eval_pow,spectralAnnihilator_at,zero_pow (by norm_num : 2≠0),sum_const_zero,mul_zero]
    exact mul_pos badFraction_pos (pow_pos hδ _)
 theorem exists_small_h_spectralGood [NeZero p] (hp : 2≤p) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) :
    ∃h : ℝ,0<h ∧ h<1 ∧ spectralGood p δ Δ (wordMoment (Model.τ p) (Model.X p h)) := by
  have hh : {h : ℝ | spectralGood p δ Δ (wordMoment (Model.τ p) (Model.X p h))} ∈ 𝓝 0 := by
    apply ((spectralGood_isOpen p δ Δ).preimage (Model.continuous_X_moments p)).mem_nhds
    simpa [Model.X_zero] using spectralGood_C hp hδ hΔ
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hh
  let h := min (ε/2) (1/2)
  have hp' : 0<h := lt_min (by positivity) (by norm_num)
  refine ⟨h,hp',lt_of_le_of_lt (min_le_right _ _) (by norm_num),he ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hp']
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockGaussianQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem chosenP_ge_two : 2≤chosenP := by norm_num [chosenP]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation

theorem main_oai :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (M : VonNeumannAlgebra H) (τ : TracialVector M)
      (n : ℕ) (X S : Fin n → H →L[ℂ] H),
      2 ≤ n ∧
      (∀ i, X i ∈ M ∧ IsSelfAdjoint (X i)) ∧
      (∀ i, S i ∈ M ∧ IsSelfAdjoint (S i)) ∧
      FreeStandardNoise τ X S ∧
      (⊥ : EReal) < chi τ X ∧
      chi τ X ≤ chiStar τ X S - (1 / 2 : EReal) ∧
      chiStar τ X S - (1 / 2 : EReal) < (⊤ : EReal) := by
  obtain ⟨δ,Δ,hδ,hΔ,hδΔ,hsep,hq⟩ := exists_spectral_parameters chosenP_ge_two
  obtain ⟨h,hh0,hh1,hh⟩ := exists_small_h_spectralGood chosenP_ge_two hδ hΔ
  refine ⟨Model.H chosenP,inferInstance,inferInstance,inferInstance,Model.M chosenP,
    Model.τ chosenP,chosenP+1,Model.X chosenP h,Model.auxiliaryNoise chosenP,
    by have := chosenP_ge_two; omega,
    (fun i => ⟨Model.X_mem chosenP h i,Model.X_selfAdjoint chosenP h i⟩),
    (fun i => ⟨Model.auxiliaryNoise_mem chosenP i,Model.auxiliaryNoise_selfAdjoint chosenP i⟩),
    Model.auxiliaryNoise_free chosenP h,Model.chi_gt_bot chosenP chosenP_ge_two hh0,
    chosen_chi_bound hh0 hh1 hδ hΔ hδΔ hsep hq hh,?_⟩
  rw [Model.chiStar_tail_formula chosenP chosenP_ge_two h hh0]
  change ((Model.gaussianEntropy chosenP h-(1/2:ℝ)*(∫u in Set.Ioi h,Model.fisherDeficit chosenP u):ℝ):EReal)-(((1/2:ℝ):ℝ):EReal)<⊤
  rw [← EReal.coe_sub]
  exact EReal.coe_lt_top _

end FiniteEntropySeparation

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.main_oai := @OAI.FiniteEntropySeparation.main_oai
