-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:53:54.067827+00:00
-- url     : https://prove2.me/submissions/07f3f36d-0b43-4c11-84a0-676193417ead

import Mathlib
import Definitions.Def_OAIQ081S060

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeCounting
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite counting lemmas for the local-code exhaustive search. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open scoped BigOperators

theorem exists_avoiding_of_budget
    {A B : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (s : Finset B) (bad : B → Finset A) (K : ℕ)
    (hbudget : ∀ b ∈ s, (bad b).card * K ≤ Fintype.card A)
    (hsmall : s.card < K) :
    ∃ a : A, ∀ b ∈ s, a ∉ bad b := by
  classical
  by_contra h
  have hcover : Finset.univ ⊆ s.biUnion bad := by
    intro a _
    simp only [not_exists, not_forall, not_not] at h
    obtain ⟨b, hb, hab⟩ := h a
    exact Finset.mem_biUnion.mpr ⟨b, hb, hab⟩
  have hcard : Fintype.card A ≤ ∑ b ∈ s, (bad b).card := by
    exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hmul : Fintype.card A * K ≤ s.card * Fintype.card A := by
    calc
      Fintype.card A * K ≤ (∑ b ∈ s, (bad b).card) * K :=
        Nat.mul_le_mul_right K hcard
      _ = ∑ b ∈ s, (bad b).card * K := Finset.sum_mul _ _ _
      _ ≤ ∑ _b ∈ s, Fintype.card A := Finset.sum_le_sum hbudget
      _ = s.card * Fintype.card A := by simp
  have hlt := Nat.mul_lt_mul_of_pos_right hsmall (Fintype.card_pos (α := A))
  rw [mul_comm] at hmul
  exact (not_lt_of_ge hmul) hlt

theorem card_zero_fiber_mul
    {A B : Type*} [AddGroup A] [AddGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Fintype.card {x : A // f x = 0} * Fintype.card B = Fintype.card A := by
  classical
  have hsame (b : B) :
      Fintype.card {x : A // f x = b} = Fintype.card {x : A // f x = 0} := by
    obtain ⟨a, ha⟩ := hf b
    exact Fintype.card_congr (fiberEquivZero f b a ha)
  have hsum := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Fintype.card_sigma, hsame, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm] using hsum

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

section Words

variable {C R : Type*} [Fintype C]

theorem weight_pos_iff (w : C → F3) : 0 < weight w ↔ w ≠ 0 := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, weight_eq_zero_iff]

end Words

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeExistence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact finite random-row counting, with no probabilistic hypothesis. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open scoped BigOperators
open SparseCode

section Evaluation

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

omit [Fintype R] [DecidableEq R] in
theorem evaluationHom_surjective {v : C → F3} (hv : v ≠ 0) :
    Function.Surjective (evaluationHom (R := R) v) := by
  classical
  have hex : ∃ c, v c ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨c, hc⟩ := hex
  intro y
  refine ⟨fun r c' => if c' = c then y r / v c else 0, ?_⟩
  ext r
  simp [evaluationHom, check, ite_mul, hc]

omit [Fintype R] [DecidableEq R] [DecidableEq C] in
theorem evaluationHom_eq_zero_iff (v : C → F3) (Q : CheckMatrix R C) :
    evaluationHom v Q = 0 ↔ IsCodeword Q v := by
  exact Iff.intro (fun h r => congrFun h r) (fun h => funext h)

theorem killedMatrices_card {v : C → F3} (hv : v ≠ 0) :
    (killedMatrices (R := R) v).card * 3 ^ Fintype.card R =
      Fintype.card (CheckMatrix R C) := by
  classical
  have h := card_zero_fiber_mul (evaluationHom (R := R) v)
    (evaluationHom_surjective hv)
  simpa only [Fintype.card_subtype, Fintype.card_fun, ZMod.card,
    killedMatrices] using h

theorem exists_matrix_avoiding
    (s : Finset (C → F3)) (hzero : ∀ v ∈ s, v ≠ 0)
    (hsmall : s.card < 3 ^ Fintype.card R) :
    ∃ Q : CheckMatrix R C, ∀ v ∈ s, ¬ IsCodeword Q v := by
  classical
  obtain ⟨Q, hQ⟩ := exists_avoiding_of_budget s
    (killedMatrices (R := R)) (3 ^ Fintype.card R)
    (fun v hv => (killedMatrices_card (hzero v hv)).le) hsmall
  refine ⟨Q, fun v hv hcode => hQ v hv ?_⟩
  simp only [killedMatrices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (evaluationHom_eq_zero_iff v Q).mpr hcode

end Evaluation

/-- The combinatorial existence criterion for a finite local code. Its
cardinality hypothesis will be discharged by the low-weight word estimate. -/
theorem exists_distance_of_card (D t d : ℕ)
    (hsmall : (Finset.univ.filter fun v : Fin D → F3 =>
      v ≠ 0 ∧ weight v < d).card < 3 ^ t) :
    ∃ Q : CheckMatrix (Fin t) (Fin D), HasDistance Q d := by
  classical
  obtain ⟨Q, hQ⟩ := exists_matrix_avoiding (R := Fin t)
    (Finset.univ.filter fun v : Fin D → F3 => v ≠ 0 ∧ weight v < d)
    (by intro v hv; exact (Finset.mem_filter.mp hv).2.1)
    (by simpa using hsmall)
  refine ⟨Q, fun v hv hv0 => ?_⟩
  by_contra h
  exact hQ v (by simp [hv0, Nat.lt_of_not_ge h]) hv

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeWeight
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary low-weight counting by successive single-coordinate updates. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

theorem support_update_zero {D : ℕ} (w : Fin D → F3) (c : Fin D) :
    support (Function.update w c 0) = (support w).erase c := by
  ext i
  by_cases hi : i = c
  · subst i; simp
  · simp [hi ]

theorem weight_update_zero {D : ℕ} (w : Fin D → F3) (c : Fin D)
    (hc : w c ≠ 0) : weight (Function.update w c 0) + 1 = weight w := by
  rw [weight, support_update_zero]
  exact Finset.card_erase_add_one ((mem_support w c).mpr hc)

theorem lowWords_succ_cover (D h : ℕ) :
    lowWords D (h + 1) ⊆
      ((Finset.univ : Finset (UpdateSymbol D)) ×ˢ lowWords D h).image
        (fun p => applySymbol p.1 p.2) := by
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact Finset.mem_image.mpr ⟨(none, 0), by simp, rfl⟩
  · have hex : ∃ c, w c ≠ 0 := by
      by_contra! hn
      exact hw0 (funext hn)
    obtain ⟨c, hc⟩ := hex
    have hlow : Function.update w c 0 ∈ lowWords D h := by
      rw [mem_lowWords]
      have hweight := weight_update_zero w c hc
      have hw' := (mem_lowWords w).mp hw
      omega
    refine Finset.mem_image.mpr
      ⟨(some (c, w c), Function.update w c 0), by simp [hlow], ?_⟩
    simp [applySymbol]

theorem lowWords_card_le (D h : ℕ) :
    (lowWords D h).card ≤ (1 + 3 * D) ^ h := by
  induction h with
  | zero =>
      have heq : lowWords D 0 = {0} := by
        ext w
        simp
      simp [heq]
  | succ h ih =>
      calc
        (lowWords D (h + 1)).card ≤
            (((Finset.univ : Finset (UpdateSymbol D)) ×ˢ lowWords D h).image
              (fun p => applySymbol p.1 p.2)).card :=
          Finset.card_le_card (lowWords_succ_cover D h)
        _ ≤ ((Finset.univ : Finset (UpdateSymbol D)) ×ˢ lowWords D h).card :=
          Finset.card_image_le
        _ = (1 + 3 * D) * (lowWords D h).card := by
          simp [UpdateSymbol, Fintype.card_option, Fintype.card_prod,
            ZMod.card, Nat.mul_comm, Nat.add_comm]
        _ ≤ (1 + 3 * D) * (1 + 3 * D) ^ h := Nat.mul_le_mul_left _ ih
        _ = (1 + 3 * D) ^ (h + 1) := by rw [pow_succ, Nat.mul_comm]

theorem lowWords_card_le_four (D h : ℕ) (hD : 0 < D) :
    (lowWords D h).card ≤ (4 * D) ^ h := by
  exact (lowWords_card_le D h).trans
    (Nat.pow_le_pow_left (by omega : 1 + 3 * D ≤ 4 * D) h)

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeLogBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The reviewed log-size variant of the local code, using only integer bounds. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

theorem local_exponent_lt (D B ell t : ℕ) (hB : 0 < B) (hell : 0 < ell)
    (ht : D ≤ 8 * B * t) (hh : 0 < D / (100 * B * ell)) :
    3 * ell * (D / (100 * B * ell)) < t := by
  have hdiv := Nat.div_mul_le_self D (100 * B * ell)
  have hprod : B * (100 * ell * (D / (100 * B * ell))) ≤ B * (8 * t) := by
    nlinarith
  have hcancel := Nat.le_of_mul_le_mul_left hprod hB
  have hpositive := Nat.mul_pos hell hh
  nlinarith

theorem four_mul_le_log_power (D ell : ℕ) (hell : 0 < ell)
    (hD : D ≤ 2 ^ ell) : 4 * D ≤ 2 ^ (3 * ell) := by
  calc
    4 * D ≤ 4 * 2 ^ ell := Nat.mul_le_mul_left _ hD
    _ = 2 ^ (ell + 2) := by simp [pow_add, Nat.mul_comm]
    _ ≤ 2 ^ (3 * ell) := Nat.pow_le_pow_right (by decide) (by omega)

/-- An unconditional finite local-code existence theorem. `ell` only needs
to bound the binary logarithm of the local length; no entropy estimate is
assumed. The row budget is expressed without rounded division. -/
theorem exists_local_code_log_bound_oai (D B ell t : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell)
    (ht : D ≤ 8 * B * t) :
    ∃ Q : CheckMatrix (Fin t) (Fin D),
      HasDistance Q (D / (100 * B * ell) + 1) := by
  classical
  apply exists_distance_of_card
  by_cases hh : D / (100 * B * ell) = 0
  · have he : (Finset.univ.filter fun v : Fin D → F3 =>
        v ≠ 0 ∧ weight v < D / (100 * B * ell) + 1) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
      intro hv
      have hp := (weight_pos_iff v).mpr hv
      omega
    rw [he, Finset.card_empty]
    positivity
  · have hhpos : 0 < D / (100 * B * ell) := Nat.pos_of_ne_zero hh
    have hDpos : 0 < D := by
      by_contra hn
      have : D = 0 := by omega
      simp [this] at hh
    have hsubset : (Finset.univ.filter fun v : Fin D → F3 =>
        v ≠ 0 ∧ weight v < D / (100 * B * ell) + 1) ⊆
        lowWords D (D / (100 * B * ell)) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact (mem_lowWords v).mpr (Nat.lt_succ_iff.mp hv.2)
    calc
      (Finset.univ.filter fun v : Fin D → F3 =>
          v ≠ 0 ∧ weight v < D / (100 * B * ell) + 1).card
          ≤ (lowWords D (D / (100 * B * ell))).card := Finset.card_le_card hsubset
      _ ≤ (4 * D) ^ (D / (100 * B * ell)) := lowWords_card_le_four _ _ hDpos
      _ ≤ (2 ^ (3 * ell)) ^ (D / (100 * B * ell)) :=
        Nat.pow_le_pow_left (four_mul_le_log_power D ell hell hD) _
      _ = 2 ^ (3 * ell * (D / (100 * B * ell))) := (pow_mul _ _ _).symm
      _ < 2 ^ t := Nat.pow_lt_pow_right (by decide)
        (local_exponent_lt D B ell t hB hell ht hhpos)
      _ ≤ 3 ^ t := Nat.pow_le_pow_left (by decide) _

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound_oai
