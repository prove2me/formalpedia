-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_prepared_higher_shift_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T07:38:02.920705+00:00
-- url     : https://prove2.me/submissions/9ecd7a45-59f1-4b98-a60a-38541c649cf2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B124
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_prescribed_partition_expansion

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

open Module
open scoped NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Metric

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t n : ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

universe u

theorem cyclic_upperComparison_mul_niltest
    {degree low N : ℕ} [NeZero N] {P R error : ℝ}
    (f g : ZMod N → ℝ) (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (hlow : low ≤ degree) (hR : 0 ≤ R)
    (hBudget : productNiltestBudget (raisedNiltestBudget R) ≤ P)
    {L₁ : Type u} [lie₁ : LieRing L₁] [alg₁ : LieAlgebra ℚ L₁] {s₁ dim₁ : ℕ}
    [top₁ : TopologicalSpace (ℝ ⊗[ℚ] L₁)] [add₁ : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [smul₁ : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [t2₁ : T2Space (ℝ ⊗[ℚ] L₁)]
    (D₁ : RationalFilteredNilmanifold L₁ s₁ dim₁) (hs₁ : s₁ ≤ degree)
    (A : D₁.Niltest (fun _ : Unit => 1)) (hA : A.UnitIntervalValued) (hAc : A.ComplexityLE R) :
    CyclicNiltestUpperComparison.{u} low N R error
      (fun x => f x * (A.evalCyclic N (fun _ => x)).re)
      (fun x => g x * (A.evalCyclic N (fun _ => x)).re) := by
  intro L₂ lie₂ alg₂ s₂ dim₂ top₂ add₂ smul₂ t2₂ D₂ hs₂ T hT hTc
  let K : Bool → Type u := BoolLieFamily L₁ L₂
  let dims : Bool → ℕ := fun b => Bool.rec dim₂ dim₁ b
  let D : ∀ b, RationalFilteredNilmanifold (K b) degree (dims b) := fun b => by
    cases b
    · exact D₂.raiseStep (hs₂.trans hlow)
    · exact D₁.raiseStep hs₁
  let U : ∀ b, (D b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact T.raiseStep (hs₂.trans hlow)
    · exact A.raiseStep hs₁
  have hUc : ∀ b, (U b).ComplexityLE (raisedNiltestBudget R) := by
    intro b
    cases b
    · exact T.raiseStep_complexity (hs₂.trans hlow) hR hTc
    · exact A.raiseStep_complexity hs₁ hR hAc
  have hU : ∀ b, (U b).UnitIntervalValued := by
    intro b
    cases b
    · exact T.raiseStep_unit_interval (hs₂.trans hlow) hT
    · exact A.raiseStep_unit_interval hs₁ hA
  have hR' : 0 ≤ raisedNiltestBudget R := hR.trans (le_raisedNiltestBudget R)
  have hcard : (Fintype.card Bool : ℝ) ≤ raisedNiltestBudget R := by
    norm_num only [Fintype.card_bool, Nat.cast_ofNat]
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (R + 2)]
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let S := RationalFilteredNilmanifold.piNiltest D U hR' hcard hUc
  have hSc : S.ComplexityLE P :=
    (RationalFilteredNilmanifold.piNiltest_complexity D U hR' hcard hUc).mono hBudget
  have hSu : S.UnitIntervalValued :=
    RationalFilteredNilmanifold.piNiltest_unit_interval D U hR' hcard hUc hU
  have h := hcompare (RationalFilteredNilmanifold.pi D) le_rfl S hSu hSc
  have heval (x : ZMod N) : S.evalCyclic N (fun _ : Unit => x) =
      A.evalCyclic N (fun _ : Unit => x) * T.evalCyclic N (fun _ : Unit => x) := by
    change (RationalFilteredNilmanifold.piNiltest D U hR' hcard hUc).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    change (A.raiseStep hs₁).eval (fun _ : Unit => (x.val : ℤ)) *
      (T.raiseStep (hs₂.trans hlow)).eval (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    rfl
  convert h using 1
  apply Finset.expect_congr rfl
  intro x _
  rw [heval, Complex.mul_re, (A.unit_interval_evalCyclic hA N (fun _ => x)).1,
    (T.unit_interval_evalCyclic hT N (fun _ => x)).1]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace PositiveCyclicNiltest

universe u

theorem mul_upperComparison {degree low N : ℕ} [NeZero N] {P R error : ℝ}
    {a f g : ZMod N → ℝ} (ha : PositiveCyclicNiltest.{u} degree N R a)
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (hlow : low ≤ degree) (hR : 0 ≤ R)
    (hBudget : productNiltestBudget (raisedNiltestBudget R) ≤ P) :
    CyclicNiltestUpperComparison.{u} low N R error
      (fun x => f x * a x) (fun x => g x * a x) := by
  rcases ha with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  have heq : a = fun x => (T.evalCyclic N (fun _ => x)).re := funext heval
  rw [heq]
  exact @cyclic_upperComparison_mul_niltest degree low N _ P R error
    f g @hcompare hlow hR hBudget L lie alg s dim top add smul t2 D hs T hT hTc

theorem apply_shiftBound {degree N : ℕ} [NeZero N] {p error : ℝ}
    {a J c : ZMod N → ℝ} {E : Finset (ZMod N)}
    (hc : PositiveCyclicNiltest.{u} degree N p c)
    (hbound : CyclicNiltestShiftBound.{u} degree N p error a J E)
    {h : ZMod N} (hh : h ∉ E) :
    (𝔼 n, a n * J (n + h) * c n) ≤ error := by
  rcases hc with ⟨D, hs, T, hT, hTc, heval⟩
  simp_rw [heval]
  exact hbound h hh D hs T hT hTc

end PositiveCyclicNiltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

universe u

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedListPowerBudget
namespace OAI

section

namespace Erdos3

theorem fixedListWorkingBudget_lower {p b : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) :
    2 ≤ fixedListWorkingBudget p b ∧ p ≤ fixedListWorkingBudget p b := by
  unfold fixedListWorkingBudget
  constructor <;> linarith

theorem fixedListBudgetPolynomial_eval (B c : ℕ) (p : ℝ) :
    (fixedListBudgetPolynomial B c).eval₂ (Nat.castRingHom ℝ) p =
      fixedListRequiredBudget B c p := by
  simp [fixedListBudgetPolynomial, fixedListRequiredBudget, fixedListComparisonBudget,
    fixedListWorkingBudget, productNiltestBudget, productObservableLipBudget,
    raisedNiltestBudget, Polynomial.eval₂_pow]

theorem exists_fixedListBudget_power (B c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      fixedListComparisonBudget B c p ≤ (p + 2) ^ C ∧
      productNiltestBudget (raisedNiltestBudget (fixedListComparisonBudget B c p)) ≤
        (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (fixedListBudgetPolynomial B c)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hsum : fixedListRequiredBudget B c p ≤ (p + 2) ^ C := by
    simpa only [fixedListBudgetPolynomial_eval] using hbound p hp
  have hR : 0 ≤ fixedListComparisonBudget B c p := by
    unfold fixedListComparisonBudget fixedListWorkingBudget
    positivity
  have hprod : 0 ≤ productNiltestBudget (raisedNiltestBudget (fixedListComparisonBudget B c p)) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  unfold fixedListRequiredBudget at hsum
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PartitionFixedListLogBudget
namespace OAI

section

namespace Erdos3

theorem partition_pair_log_bound {F Q : ℝ} (hF : 0 ≤ F) (hQ : 0 ≤ Q)
    (hcard : F ≤ Real.exp Q) : Real.log (F + F ^ 2 + 2) ≤ 2 * Q + 4 := by
  have h1 : 1 ≤ Real.exp Q := Real.one_le_exp hQ
  have hE : Real.exp Q ≤ Real.exp Q ^ 2 := by nlinarith
  have hF2 : F ^ 2 ≤ Real.exp Q ^ 2 := pow_le_pow_left₀ hF hcard 2
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsum : F + F ^ 2 + 2 ≤ Real.exp (2 * Q + 4) := by
    calc
      _ ≤ 4 * Real.exp Q ^ 2 := by nlinarith
      _ ≤ Real.exp 4 * Real.exp Q ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = Real.exp (2 * Q + 4) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hsum

theorem log_reciprocal_of_exp_lower {R δ : ℝ} (hδ : Real.exp (-R) ≤ δ) :
    Real.log (1 / δ) ≤ R := by
  have hh := Real.log_le_log (Real.exp_pos (-R)) hδ
  rw [Real.log_exp] at hh
  rw [one_div, Real.log_inv]
  linarith

theorem exists_partition_fixed_list_log_budget (C k : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ p : ℝ, 0 ≤ p →
      3 * ((p + C) ^ C + 2) + 4 + 2 * (p + 2) ^ k ≤ (p + 2) ^ b := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨b, hb, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (3 * ((X + Polynomial.C C) ^ C + 2) + 4 + 2 * (X + 2) ^ k)
  refine ⟨b, hb, ?_⟩
  intro p hp
  simpa [X, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem exists_avoiding_exceptional_family {G K : Type*} [Fintype G] [Nonempty G]
    [Fintype K] (H : Finset G) (E : K → Finset G) {sigma eta : ℝ}
    (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hE : ∀ k, ((E k).card : ℝ) ≤ eta * Fintype.card G)
    (hsmall : (Fintype.card K : ℝ) * eta < sigma) :
    ∃ h ∈ H, ∀ k, h ∉ E k := by
  classical
  by_contra hnone
  push Not at hnone
  have hcover : H ⊆ Finset.univ.biUnion E := by
    intro h hh
    obtain ⟨k, hk⟩ := hnone h hh
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hk⟩
  have hbound : (H.card : ℝ) ≤ (Fintype.card K : ℝ) * (eta * Fintype.card G) := by
    calc
      _ ≤ ((Finset.univ.biUnion E).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
      _ ≤ ((∑ k, (E k).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ = ∑ k, ((E k).card : ℝ) := by simp
      _ ≤ ∑ _k : K, eta * Fintype.card G := Finset.sum_le_sum (fun k _ => hE k)
      _ = _ := by simp
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hstrict := mul_lt_mul_of_pos_right hsmall hcard
  nlinarith only [hH, hbound, hstrict]

end Erdos3

namespace Erdos3

open scoped BigOperators

theorem abs_expect_mul_le_cap {G : Type*} [Fintype G]
    (w e : G → ℝ) {M : ℝ} (hw : ∀ x, |w x| ≤ M) :
    |𝔼 x, w x * e x| ≤ M * (𝔼 x, |e x|) := by
  rw [Finset.mul_expect]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le_expect
  intro x _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hw x) (abs_nonneg _)

theorem signed_shift_weight_bound {f g J p epsilon : ℝ}
    (hf : 0 ≤ f ∧ f ≤ Real.exp p) (hg : 0 ≤ g ∧ g ≤ Real.exp p)
    (hJ : 0 ≤ J ∧ J ≤ Real.exp p) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    |(f - (1 + epsilon) * g) * J| ≤ 3 * Real.exp (2 * p) := by
  have hnonneg : 0 ≤ (1 + epsilon) * g := mul_nonneg (by linarith) hg.1
  have hupper := mul_le_mul_of_nonneg_right (show 1 + epsilon ≤ 2 by linarith) hg.1
  have habs : |f - (1 + epsilon) * g| ≤ 3 * Real.exp p :=
    abs_le.mpr ⟨by nlinarith [Real.exp_pos p], by nlinarith [Real.exp_pos p]⟩
  rw [abs_mul, abs_of_nonneg hJ.1]
  calc
    _ ≤ (3 * Real.exp p) * Real.exp p :=
      mul_le_mul habs hJ.2 hJ.1 (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add, show p + p = 2 * p by ring]

theorem fixed_list_error_cost {G : Type*} [Fintype G]
    (w e : G → ℝ) {p delta : ℝ}
    (hw : ∀ x, |w x| ≤ 3 * Real.exp (2 * p))
    (he : (𝔼 x, |e x|) ≤ delta * Real.exp (-2 * p) / 6) :
    (𝔼 x, w x * e x) ≤ delta / 2 := by
  have hexp : Real.exp (2 * p) * Real.exp (-2 * p) = 1 := by
    rw [← Real.exp_add]
    rw [show 2 * p + -2 * p = (0 : ℝ) by ring, Real.exp_zero]
  calc
    _ ≤ |𝔼 x, w x * e x| := le_abs_self _
    _ ≤ (3 * Real.exp (2 * p)) * (𝔼 x, |e x|) := abs_expect_mul_le_cap w e hw
    _ ≤ (3 * Real.exp (2 * p)) * (delta * Real.exp (-2 * p) / 6) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (delta / 2) * (Real.exp (2 * p) * Real.exp (-2 * p)) := by ring
    _ = delta / 2 := by rw [hexp, mul_one]

theorem larger_slack_weighted_term_le {f g J A B C epsilon : ℝ}
    (hg : 0 ≤ g) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hepsilon : 0 ≤ epsilon) :
    (f - (1 + epsilon) * g) * J * (A * B * C) ≤
      (f * A - (1 + epsilon / 2) * (g * A)) * (J * B) * C := by
  have hbase : f - (1 + epsilon) * g ≤ f - (1 + epsilon / 2) * g := by
    nlinarith [mul_nonneg hepsilon hg]
  have hw : 0 ≤ J * A * B * C := by positivity
  calc
    _ = (f - (1 + epsilon) * g) * (J * A * B * C) := by ring
    _ ≤ (f - (1 + epsilon / 2) * g) * (J * A * B * C) :=
      mul_le_mul_of_nonneg_right hbase hw
    _ = _ := by ring

end Erdos3

namespace Erdos3

theorem partition_expansion_error_small {p R E A N δ : ℝ}
    (hE : 0 ≤ E) (hA : E + R + 2 * p + 32 ≤ A)
    (hN : Real.exp A ≤ N) (hδ : Real.exp (-R) ≤ δ) :
    Real.exp E * Real.exp (-A) + 3 / N ≤ δ * Real.exp (-2 * p) / 6 := by
  let z := Real.exp (-R - 2 * p - 32)
  have hfirst : Real.exp E * Real.exp (-A) ≤ z := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hrecip : 1 / N ≤ Real.exp (-A) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos A) hN
    simpa only [one_div, Real.exp_neg] using hh
  have hsecond : 3 / N ≤ 3 * z := by
    have hh : Real.exp (-A) ≤ z := Real.exp_le_exp.mpr (by linarith)
    calc
      3 / N = 3 * (1 / N) := by ring
      _ ≤ 3 * Real.exp (-A) := mul_le_mul_of_nonneg_left hrecip (by norm_num)
      _ ≤ 3 * z := mul_le_mul_of_nonneg_left hh (by norm_num)
  have h32 : (24 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have hcancel : z * Real.exp 32 = Real.exp (-R) * Real.exp (-2 * p) := by
    dsimp [z]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hcap : 24 * z ≤ δ * Real.exp (-2 * p) := by
    calc
      _ ≤ z * Real.exp 32 := by nlinarith [Real.exp_pos (-R - 2 * p - 32)]
      _ = Real.exp (-R) * Real.exp (-2 * p) := hcancel
      _ ≤ δ * Real.exp (-2 * p) := mul_le_mul_of_nonneg_right hδ (Real.exp_pos _).le
  linarith

theorem exists_partition_expansion_precision (B k : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      (p + B) ^ B + (p + 2) ^ k + 2 * p + 32 ≤ (p + 2) ^ a := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_fixed_power_budget
    ((X + Polynomial.C B) ^ B + (X + 2) ^ k + 2 * X + 32)
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [X, Polynomial.eval₂_pow] using hbound p hp

theorem partition_expansion_precision_properties {p : ℝ} (hp : 0 ≤ p) (a : ℕ) :
    0 < Real.exp (-((p + 2) ^ a)) ∧ Real.exp (-((p + 2) ^ a)) ≤ 1 ∧
      1 / Real.exp (-((p + 2) ^ a)) = Real.exp ((p + 2) ^ a) := by
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg (by linarith) _))
  · simp only [one_div, Real.exp_neg, inv_inv]

end Erdos3

namespace Erdos3

open scoped BigOperators

theorem density_parameter_le_one {G : Type*} [Fintype G] [Nonempty G]
    (H : Finset G) {sigma : ℝ} (hH : sigma * Fintype.card G ≤ (H.card : ℝ)) :
    sigma ≤ 1 := by
  have hcard : (H.card : ℝ) ≤ Fintype.card G := by exact_mod_cast Finset.card_le_univ H
  have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  nlinarith

theorem positive_shift_mean_cap {G : Type*} [Fintype G] [Nonempty G]
    (f g J T : G → ℝ) {p epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p)
    (hg : ∀ n, 0 ≤ g n) (hJ : ∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p)
    (hT : ∀ n, 0 ≤ T n ∧ T n ≤ 1) :
    (𝔼 n, (f n - (1 + epsilon) * g n) * J n * T n) ≤ Real.exp (2 * p) := by
  have hpoint (n : G) :
      (f n - (1 + epsilon) * g n) * J n * T n ≤ Real.exp (2 * p) := by
    have hsub : f n - (1 + epsilon) * g n ≤ f n :=
      sub_le_self _ (mul_nonneg (by linarith) (hg n))
    calc
      _ ≤ f n * J n * T n := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsub (hJ n).1) (hT n).1
      _ ≤ Real.exp p * Real.exp p * 1 :=
        mul_le_mul (mul_le_mul (hf n).2 (hJ n).2 (hJ n).1 (Real.exp_nonneg _))
          (hT n).2 (hT n).1 (by positivity)
      _ = _ := by rw [mul_one, ← Real.exp_add]; congr 1; ring
  exact (Finset.expect_le_expect (fun n _ => hpoint n)).trans_eq
    (Finset.expect_const Finset.univ_nonempty _)

theorem fixed_list_log_components {p Q F M sigma delta b : ℝ}
    (hQ : 0 ≤ Q) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaCap : delta ≤ Real.exp (2 * p))
    (hbudget : Q + Real.log (F + M + 2) + Real.log (1 / sigma) +
      Real.log (1 / delta) ≤ b) :
    Q ≤ b + 2 * p ∧ Real.log (F + M + 2) ≤ b + 2 * p ∧
      Real.log (1 / sigma) ≤ b + 2 * p ∧ Real.log (1 / delta) ≤ b := by
  have hL : 0 ≤ Real.log (F + M + 2) := Real.log_nonneg (by linarith)
  have hS : 0 ≤ Real.log (1 / sigma) := Real.log_nonneg ((le_div_iff₀ hsigma).mpr (by simpa))
  have hD : -2 * p ≤ Real.log (1 / delta) := by
    rw [one_div, Real.log_inv]
    have hd := (Real.log_le_iff_le_exp hdelta).mpr hdeltaCap
    linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

namespace Erdos3

open scoped BigOperators

theorem fixed_list_contradiction_of_pair_bounds
    {G I J K : Type*} [AddCommGroup G] [Fintype G]
    [Fintype I] [Fintype J] [Fintype K]
    (f g weight : G → ℝ) (A : I → G → ℝ) (B : J → G → ℝ)
    (H : Finset G) (E : I → J → Finset G)
    (i : G → K → I) (j : G → K → J) (C : G → K → G → ℝ)
    (T e : G → G → ℝ) {p epsilon sigma delta eta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p)
    (hweight : ∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p)
    (hA : ∀ a n, 0 ≤ A a n) (hB : ∀ b n, 0 ≤ B b n) (hC : ∀ h k n, 0 ≤ C h k n)
    (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hE : ∀ a b, ((E a b).card : ℝ) ≤ eta * Fintype.card G)
    (hpairs : (Fintype.card I : ℝ) * Fintype.card J * eta < sigma)
    (hterms : (Fintype.card K : ℝ) * eta ≤ delta / 2)
    (happrox : ∀ h ∈ H, ∀ n, T h n =
      (∑ k, A (i h k) n * B (j h k) (n + h) * C h k n) + e h n)
    (herror : ∀ h ∈ H, (𝔼 n, |e h n|) ≤ delta * Real.exp (-2 * p) / 6)
    (hbound : ∀ a b h, h ∉ E a b → ∀ k,
      (𝔼 n, (f n * A a n - (1 + epsilon / 2) * (g n * A a n)) *
        (weight (n + h) * B b (n + h)) * C h k n) ≤ eta)
    (hviolate : ∀ h ∈ H,
      delta < 𝔼 n, (f n - (1 + epsilon) * g n) * weight (n + h) * T h n) : False := by
  obtain ⟨h, hh, hgood⟩ := exists_avoiding_exceptional_family H
    (fun ab : I × J => E ab.1 ab.2) hH (fun ab => hE ab.1 ab.2)
    (by simpa only [Fintype.card_prod, Nat.cast_mul] using hpairs)
  let w : G → ℝ := fun n => (f n - (1 + epsilon) * g n) * weight (n + h)
  have hterm (k : K) :
      (𝔼 n, w n * (A (i h k) n * B (j h k) (n + h) * C h k n)) ≤ eta := by
    apply (Finset.expect_le_expect (fun n (_ : n ∈ (Finset.univ : Finset G)) =>
      larger_slack_weighted_term_le (hg n).1 (hweight (n + h)).1
        (hA (i h k) n) (hB (j h k) (n + h)) (hC h k n) hepsilon)).trans
    exact hbound (i h k) (j h k) h (hgood (i h k, j h k)) k
  have hsum :
      (∑ k, 𝔼 n, w n * (A (i h k) n * B (j h k) (n + h) * C h k n)) ≤
        (Fintype.card K : ℝ) * eta := by
    exact (Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) => hterm k)).trans_eq
      (by simp)
  have hw : ∀ n, |w n| ≤ 3 * Real.exp (2 * p) := fun n =>
    signed_shift_weight_bound (hf n) (hg n) (hweight (n + h)) hepsilon hepsilon1
  have herr := fixed_list_error_cost w (e h) hw (herror h hh)
  have hid : (𝔼 n, w n * T h n) =
      (∑ k, 𝔼 n, w n * (A (i h k) n * B (j h k) (n + h) * C h k n)) +
        (𝔼 n, w n * e h n) := by
    simp_rw [happrox h hh, mul_add, Finset.mul_sum, Finset.expect_add_distrib]
    rw [Finset.expect_sum_comm]
  have hupper : (𝔼 n, w n * T h n) ≤ delta := by
    rw [hid]
    linarith
  exact (hviolate h hh).not_ge hupper

end Erdos3

namespace Erdos3

theorem fixed_list_working_budget_suffices {p Q F M sigma delta b : ℝ}
    (hp : 0 ≤ p) (hb : 0 ≤ b) (hQ : 0 ≤ Q) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaCap : delta ≤ Real.exp (2 * p))
    (hbudget : Q + Real.log (F + M + 2) + Real.log (1 / sigma) +
      Real.log (1 / delta) ≤ b) :
    2 ≤ fixedListWorkingBudget p b ∧ p ≤ fixedListWorkingBudget p b ∧
      Q ≤ fixedListWorkingBudget p b ∧
      F ^ 2 * Real.exp (-fixedListWorkingBudget p b) < sigma ∧
      M * Real.exp (-fixedListWorkingBudget p b) ≤ delta / 2 := by
  obtain ⟨hQb, hLb, hSb, hDb⟩ :=
    fixed_list_log_components hQ hF hM hsigma hsigma1 hdelta hdeltaCap hbudget
  obtain ⟨hq2, hpq⟩ := fixedListWorkingBudget_lower hp hb
  refine ⟨hq2, hpq, ?_, ?_, ?_⟩
  · unfold fixedListWorkingBudget
    linarith
  · let L := Real.log (F + M + 2)
    let S := Real.log (1 / sigma)
    let q := fixedListWorkingBudget p b
    have hFL : F ≤ Real.exp L :=
      (show F ≤ F + M + 2 by linarith).trans (Real.le_exp_log _)
    calc
      F ^ 2 * Real.exp (-q) ≤ Real.exp L ^ 2 * Real.exp (-q) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hF hFL 2) (Real.exp_nonneg _)
      _ = Real.exp (2 * L - q) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ < Real.exp (-S) := Real.exp_lt_exp.mpr (by
        dsimp [L, S, q, fixedListWorkingBudget]
        linarith)
      _ = sigma := by
        dsimp [S]
        rw [one_div, Real.log_inv, neg_neg, Real.exp_log hsigma]
  · let L := Real.log (F + M + 2)
    let D := Real.log (1 / delta)
    let q := fixedListWorkingBudget p b
    have hML : M ≤ Real.exp L :=
      (show M ≤ F + M + 2 by linarith).trans (Real.le_exp_log _)
    have hterm : M * Real.exp (-q) ≤ Real.exp (L - q) := by
      calc
        _ ≤ Real.exp L * Real.exp (-q) :=
          mul_le_mul_of_nonneg_right hML (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, sub_eq_add_neg]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hcap : Real.exp (L - q) * 2 ≤ delta := by
      calc
        _ ≤ Real.exp (L - q) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
        _ = Real.exp (L - q + 1) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-D) := Real.exp_le_exp.mpr (by
          dsimp [L, D, q, fixedListWorkingBudget]
          linarith)
        _ = delta := by
          dsimp [D]
          rw [one_div, Real.log_inv, neg_neg, Real.exp_log hdelta]
    linarith

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u

theorem cyclic_fixed_list_contradiction
    {N r : ℕ} [NeZero N] {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f g weight : ZMod N → ℝ) (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (H : Finset (ZMod N)) (i : ZMod N → K → I) (j : ZMod N → K → J)
    (C : ZMod N → K → ZMod N → ℝ) (T e : ZMod N → ZMod N → ℝ)
    {p Q q R P epsilon sigma delta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hpq : p ≤ q) (hQq : Q ≤ q) (hq : 0 ≤ q) (hqR : q ≤ R) (hRP : R ≤ P)
    (hBudget : productNiltestBudget (raisedNiltestBudget R) ≤ P)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p)
    (hweight : ∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p)
    (hA : ∀ a, PositiveCyclicNiltest.{u} (r + 1) N Q (A a))
    (hB : ∀ b, PositiveCyclicNiltest.{u} (r + 1) N Q (B b))
    (hC : ∀ h k, PositiveCyclicNiltest.{u} (r - 1) N Q (C h k))
    (hH : sigma * N ≤ (H.card : ℝ))
    (hpairs : (Fintype.card I : ℝ) * Fintype.card J * Real.exp (-q) < sigma)
    (hterms : (Fintype.card K : ℝ) * Real.exp (-q) ≤ delta / 2)
    (happrox : ∀ h ∈ H, ∀ n, T h n =
      (∑ k, A (i h k) n * B (j h k) (n + h) * C h k n) + e h n)
    (herror : ∀ h ∈ H, (𝔼 n, |e h n|) ≤ delta * Real.exp (-2 * p) / 6)
    (hshift : ∀ a b w : ZMod N → ℝ,
      (∀ n, 0 ≤ a n ∧ a n ≤ Real.exp q) →
      (∀ n, 0 ≤ b n ∧ b n ≤ Real.exp q) →
      (∀ n, 0 ≤ w n ∧ w n ≤ Real.exp q) →
      CyclicNiltestUpperComparison.{u} r N R (Real.exp (-R)) a b →
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-q) * N ∧
        CyclicNiltestShiftBound.{u} (r - 1) N q (Real.exp (-q))
          (fun n => a n - (1 + epsilon / 2) * b n) w E)
    (hcompare : CyclicNiltestUpperComparison.{u} (r + 1) N P (Real.exp (-P)) f g)
    (hviolate : ∀ h ∈ H,
      delta < 𝔼 n, (f n - (1 + epsilon) * g n) * weight (n + h) * T h n) : False := by
  classical
  have hcap {v a : ZMod N → ℝ}
      (hv : ∀ n, 0 ≤ v n ∧ v n ≤ Real.exp p)
      (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1) (n : ZMod N) :
      0 ≤ v n * a n ∧ v n * a n ≤ Real.exp q := by
    refine ⟨mul_nonneg (hv n).1 (ha n).1, ?_⟩
    calc
      v n * a n ≤ v n * 1 := mul_le_mul_of_nonneg_left (ha n).2 (hv n).1
      _ = v n := mul_one _
      _ ≤ Real.exp p := (hv n).2
      _ ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have hpair (a : I) (b : J) :
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-q) * N ∧
        CyclicNiltestShiftBound.{u} (r - 1) N q (Real.exp (-q))
          (fun n => f n * A a n - (1 + epsilon / 2) * (g n * A a n))
          (fun n => weight n * B b n) E := by
    apply hshift _ _ _ (hcap hf (hA a).unit_interval)
      (hcap hg (hA a).unit_interval) (hcap hweight (hB b).unit_interval)
    have hmul : CyclicNiltestUpperComparison.{u} r N R (Real.exp (-P))
        (fun n => f n * A a n) (fun n => g n * A a n) :=
      @PositiveCyclicNiltest.mul_upperComparison (r + 1) r N _ P R (Real.exp (-P))
        (A a) f g ((hA a).mono le_rfl (hQq.trans hqR))
        @hcompare (Nat.le_succ r) (hq.trans hqR) hBudget
    intro L _ _ s dim _ _ _ _ D hs S hS hSc
    exact (hmul D hs S hS hSc).trans (Real.exp_le_exp.mpr (neg_le_neg hRP))
  choose E hE hbound using hpair
  apply fixed_list_contradiction_of_pair_bounds f g weight A B H E i j C T e
    hepsilon hepsilon1 hf hg hweight
    (fun a n => ((hA a).unit_interval n).1)
    (fun b n => ((hB b).unit_interval n).1)
    (fun h k n => ((hC h k).unit_interval n).1)
    (by simpa only [ZMod.card] using hH)
    (fun a b => by simpa only [ZMod.card] using hE a b)
    hpairs hterms happrox herror _ hviolate
  intro a b h hh k
  exact ((hC h k).mono le_rfl hQq).apply_shiftBound (hbound a b) hh

end Erdos3

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u v

theorem exists_cyclic_fixed_list_power (B c r : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{u} r (epsilon / 2) c) :
    ∃ D : ℕ, 2 ≤ D ∧
      ∀ (N : ℕ) [NeZero N] (p Q sigma delta : ℝ) (F : ℕ)
        (I J K : Type v) [Fintype I] [Fintype J] [Fintype K]
        (f g weight : ZMod N → ℝ) (A : I → ZMod N → ℝ) (Btest : J → ZMod N → ℝ)
        (H : Finset (ZMod N)) (i : ZMod N → K → I) (j : ZMod N → K → J)
        (C : ZMod N → K → ZMod N → ℝ) (T e : ZMod N → ZMod N → ℝ),
      2 ≤ p → 2 ≤ Q → 0 < sigma → 0 < delta → Odd N →
      Real.exp ((p + 2) ^ D) ≤ N → Fintype.card I ≤ F → Fintype.card J ≤ F →
      Q + Real.log ((F : ℝ) + Fintype.card K + 2) + Real.log (1 / sigma) +
        Real.log (1 / delta) ≤ (p + 2) ^ B →
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      (∀ a, PositiveCyclicNiltest.{u} (r + 1) N Q (A a)) →
      (∀ b, PositiveCyclicNiltest.{u} (r + 1) N Q (Btest b)) →
      (∀ h k, PositiveCyclicNiltest.{u} (r - 1) N Q (C h k)) →
      sigma * N ≤ (H.card : ℝ) →
      (∀ h ∈ H, ∀ n, 0 ≤ T h n ∧ T h n ≤ 1) →
      (∀ h ∈ H, ∀ n, T h n =
        (∑ k, A (i h k) n * Btest (j h k) (n + h) * C h k n) + e h n) →
      (∀ h ∈ H, (𝔼 n, |e h n|) ≤ delta * Real.exp (-2 * p) / 6) →
      CyclicNiltestUpperComparison.{u} (r + 1) N ((p + 2) ^ D)
        (Real.exp (-((p + 2) ^ D))) f g →
      (∀ h ∈ H, delta < 𝔼 n, (f n - (1 + epsilon) * g n) * weight (n + h) * T h n) →
      False := by
  obtain ⟨D, hD, hpower⟩ := exists_fixedListBudget_power B c
  refine ⟨D, hD, ?_⟩
  intro N hNz p Q sigma delta F I J K hI hJ hK f g weight A Btest H i j C T e
    hp hQ hsigma hdelta hodd hN hIF hJF hlog hf hg hweight hA hB hC hH hT
    happrox herror hcompare hviolate
  have hp0 : 0 ≤ p := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hHpos : (0 : ℝ) < H.card := (mul_pos hsigma hN0).trans_le hH
  obtain ⟨h, hh⟩ : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast hHpos)
  have hsigma1 : sigma ≤ 1 := density_parameter_le_one H (by simpa only [ZMod.card] using hH)
  have hdeltaCap : delta ≤ Real.exp (2 * p) := (hviolate h hh).le.trans
    (positive_shift_mean_cap f g (fun n => weight (n + h)) (T h) hepsilon.le
      hf (fun n => (hg n).1) (fun n => hweight (n + h)) (hT h hh))
  let q := fixedListWorkingBudget p ((p + 2) ^ B)
  let R := fixedListComparisonBudget B c p
  obtain ⟨hq2, hpq, hQq, hpairsF, hterms⟩ := fixed_list_working_budget_suffices
    hp0 (show 0 ≤ (p + 2) ^ B by positivity) (show 0 ≤ Q by linarith)
    (show (0 : ℝ) ≤ F by positivity) (show (0 : ℝ) ≤ Fintype.card K by positivity)
    hsigma hsigma1 hdelta hdeltaCap hlog
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hqR : q ≤ R := le_power_budget hq0 (by omega)
  have hRP : R ≤ (p + 2) ^ D := (hpower p hp0).1
  have hproduct : productNiltestBudget (raisedNiltestBudget R) ≤ (p + 2) ^ D :=
    (hpower p hp0).2
  have hRN : Real.exp R ≤ N := (Real.exp_le_exp.mpr hRP).trans hN
  have hcardProduct : (Fintype.card I : ℝ) * Fintype.card J ≤ (F : ℝ) ^ 2 := by
    have hiF : (Fintype.card I : ℝ) ≤ F := by exact_mod_cast hIF
    have hjF : (Fintype.card J : ℝ) ≤ F := by exact_mod_cast hJF
    calc
      _ ≤ (F : ℝ) * F := mul_le_mul hiF hjF (by positivity) (by positivity)
      _ = _ := (pow_two _).symm
  have hpairs : (Fintype.card I : ℝ) * Fintype.card J * Real.exp (-q) < sigma :=
    (mul_le_mul_of_nonneg_right hcardProduct (Real.exp_nonneg _)).trans_lt hpairsF
  refine cyclic_fixed_list_contradiction f g weight A Btest H i j C T e
    hepsilon.le hepsilon1.le hpq hQq hq0 hqR hRP hproduct hf hg hweight hA hB hC hH
    hpairs hterms happrox herror ?_ @hcompare hviolate
  intro a b w ha hb hw hab
  exact hshift N q hq2 hodd hRN a b w ha hb hw @hab

end Erdos3

section

universe u v

namespace Erdos3

open scoped BigOperators

theorem exists_cyclic_partition_expansion_contradiction (B k c r : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{u} r (epsilon / 2) c) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ C : ℕ, ∃ D : ℕ, 2 ≤ D ∧ a ≤ D ∧
      ∀ (N : ℕ) [NeZero N] {I : Type v} [Fintype I] (p sigma delta : ℝ)
        (f g weight : ZMod N → ℝ) (A : I → ZMod N → ℝ) (H : Finset (ZMod N))
        (U : I → I → ZMod N → ZMod N → ℝ) (T err : ZMod N → ZMod N → ℝ),
      2 ≤ p → Odd N → Real.exp ((p + 2) ^ D) ≤ N →
      (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) →
      Real.exp (-((p + 2) ^ k)) ≤ sigma → Real.exp (-((p + 2) ^ k)) ≤ delta →
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      (∀ i, PositiveCyclicNiltest.{u} (r + 1) N ((p + C) ^ C) (A i)) →
      (∀ i j h, PositiveCyclicNiltest.{u} (r - 1) N ((p + C) ^ C) (U i j h)) →
      sigma * N ≤ (H.card : ℝ) →
      (∀ h ∈ H, ∀ n, 0 ≤ T h n ∧ T h n ≤ 1) →
      (∀ h ∈ H, ∀ n, T h n = (∑ i, ∑ j, A i n * A j (n + h) * U i j h n) + err h n) →
      (∀ h ∈ H, (𝔼 n, |err h n|) ≤
        Real.exp ((p + B) ^ B) * Real.exp (-((p + 2) ^ a)) + 3 / N) →
      CyclicNiltestUpperComparison.{u} (r + 1) N ((p + 2) ^ D)
        (Real.exp (-((p + 2) ^ D))) f g →
      (∀ h ∈ H, delta < 𝔼 n, (f n - (1 + epsilon) * g n) * weight (n + h) * T h n) → False := by
  obtain ⟨a, ha, hprecision⟩ := exists_partition_expansion_precision B k
  refine ⟨a, ha, ?_⟩
  intro C
  obtain ⟨b, _, hlogBudget⟩ := exists_partition_fixed_list_log_budget C k
  obtain ⟨D₀, hD₀, hfixed⟩ := exists_cyclic_fixed_list_power.{u, v} b c r hc hepsilon hepsilon1 hshift
  let D := max D₀ a
  refine ⟨D, hD₀.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro N _ I _ p sigma delta f g weight A H U T err hp hodd hN hcard hsigma hdelta
    hf hg hweight hA hU hH hT happrox herror hcompare hviolate
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hD₀D : (p + 2) ^ D₀ ≤ (p + 2) ^ D := pow_le_pow_right₀ hbase (le_max_left _ _)
  have haD : (p + 2) ^ a ≤ (p + 2) ^ D := pow_le_pow_right₀ hbase (le_max_right _ _)
  have hND₀ : Real.exp ((p + 2) ^ D₀) ≤ N := (Real.exp_le_exp.mpr hD₀D).trans hN
  have hNa : Real.exp ((p + 2) ^ a) ≤ N := (Real.exp_le_exp.mpr haD).trans hN
  have hsigma0 : 0 < sigma := (Real.exp_pos _).trans_le hsigma
  have hdelta0 : 0 < delta := (Real.exp_pos _).trans_le hdelta
  let Q := (p + C) ^ C + 2
  have hpow : 0 ≤ (p + C) ^ C := by positivity
  have hQ : 2 ≤ Q := by dsimp [Q]; linarith
  have hCQ : (p + C) ^ C ≤ Q := by dsimp [Q]; linarith
  have hcardQ : (Fintype.card I : ℝ) ≤ Real.exp Q := hcard.trans (Real.exp_le_exp.mpr hCQ)
  have hpairs : Real.log ((Fintype.card I : ℝ) + Fintype.card (I × I) + 2) ≤ 2 * Q + 4 := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using
      partition_pair_log_bound (Nat.cast_nonneg (Fintype.card I)) (by linarith : 0 ≤ Q) hcardQ
  have hlog : Q + Real.log ((Fintype.card I : ℝ) + Fintype.card (I × I) + 2) +
      Real.log (1 / sigma) + Real.log (1 / delta) ≤ (p + 2) ^ b := by
    have hs := log_reciprocal_of_exp_lower hsigma
    have hd := log_reciprocal_of_exp_lower hdelta
    have hb : 3 * Q + 4 + 2 * (p + 2) ^ k ≤ (p + 2) ^ b := hlogBudget p hp0
    linarith
  have hsmall (h : ZMod N) (hh : h ∈ H) : (𝔼 n, |err h n|) ≤ delta * Real.exp (-2 * p) / 6 :=
    (herror h hh).trans (partition_expansion_error_small
      (by positivity : 0 ≤ (p + B) ^ B) (hprecision p hp0) hNa hdelta)
  have hcompare₀ : CyclicNiltestUpperComparison.{u} (r + 1) N ((p + 2) ^ D₀)
      (Real.exp (-((p + 2) ^ D₀))) f g := by
    intro L _ _ s dim _ _ _ _ E hs S hS hSc
    exact (hcompare E hs S hS (hSc.mono hD₀D)).trans (Real.exp_le_exp.mpr (neg_le_neg hD₀D))
  apply hfixed N p Q sigma delta (Fintype.card I) I I (I × I) f g weight A A H
    (fun _ z => z.1) (fun _ z => z.2) (fun h z => U z.1 z.2 h) T err
    hp hQ hsigma0 hdelta0 hodd hND₀ le_rfl le_rfl hlog hf hg hweight
    (fun i => (hA i).mono le_rfl hCQ) (fun i => (hA i).mono le_rfl hCQ)
    (fun h z => (hU z.1 z.2 h).mono le_rfl hCQ) hH hT _ hsmall @hcompare₀ hviolate
  intro h hh n
  simpa only [Fintype.sum_prod_type] using happrox h hh n

end Erdos3

end

section

universe u v

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_partition_expansion_contradiction (B k c s : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{u} (s + 1) (epsilon / 2) c) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ C : ℕ, ∃ D : ℕ, 2 ≤ D ∧ a ≤ D ∧
      ∀ {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
        [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
        (D₀ : RationalFilteredNilmanifold L (s + 1) d) (Q : RationalFilteredNilmanifold M s e)
        (N : ℕ) [NeZero N] {I : Type v} [Fintype I] (p sigma delta : ℝ)
        (f g weight : ZMod N → ℝ) (A : I → ZMod N → ℝ) (H : Finset (ZMod N))
        (U : I → I → ZMod N → Q.Niltest (fun _ : Unit => 1))
        (S : ZMod N → D₀.Niltest (fun _ : Unit => 1)) (err : ZMod N → ZMod N → ℝ),
      2 ≤ p → Odd N → Real.exp ((p + 2) ^ D) ≤ N →
      (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) →
      Real.exp (-((p + 2) ^ k)) ≤ sigma → Real.exp (-((p + 2) ^ k)) ≤ delta →
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      (∀ i, PositiveCyclicNiltest.{u} (s + 2) N ((p + C) ^ C) (A i)) →
      (∀ i j h, (U i j h).UnitIntervalValued) →
      (∀ i j h, (U i j h).ComplexityLE ((p + C) ^ C)) →
      sigma * N ≤ (H.card : ℝ) → (∀ h ∈ H, (S h).UnitIntervalValued) →
      (∀ h ∈ H, ∀ n, ((S h).evalCyclic N (fun _ => n)).re =
        (∑ i, ∑ j, A i n * A j (n + h) * ((U i j h).evalCyclic N (fun _ => n)).re) + err h n) →
      (∀ h ∈ H, (𝔼 n, |err h n|) ≤
        Real.exp ((p + B) ^ B) * Real.exp (-((p + 2) ^ a)) + 3 / N) →
      CyclicNiltestUpperComparison.{u} (s + 2) N ((p + 2) ^ D)
        (Real.exp (-((p + 2) ^ D))) f g →
      (∀ h ∈ H, delta < 𝔼 n, (f n - (1 + epsilon) * g n) * weight (n + h) *
        ((S h).evalCyclic N (fun _ => n)).re) → False := by
  obtain ⟨a, ha, hcontra⟩ := exists_cyclic_partition_expansion_contradiction.{u, v}
    B k c (s + 1) hc hepsilon hepsilon1 hshift
  refine ⟨a, ha, ?_⟩
  intro C
  obtain ⟨D, hD, haD, hcontra⟩ := hcontra C
  refine ⟨D, hD, haD, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D₀ Q N _ I _ p sigma delta
    f g weight A H U S err hp hodd hN hcard hsigma hdelta hf hg hweight hA hU hUc hH hS
    happrox herror hcompare hviolate
  apply hcontra N p sigma delta f g weight A H
    (fun i j h n => ((U i j h).evalCyclic N (fun _ => n)).re)
    (fun h n => ((S h).evalCyclic N (fun _ => n)).re) err
    hp hodd hN hcard hsigma hdelta hf hg hweight hA _ hH _ happrox herror @hcompare hviolate
  · intro i j h
    exact .of_test Q (by omega) (U i j h) (hU i j h) (hUc i j h) (fun _ => rfl)
  · intro h hh n
    exact ((S h).unit_interval_evalCyclic (hS h hh) N (fun _ => n)).2

end Erdos3

end

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

theorem exists_prepared_higher_shift_contradiction (s r b₀ k₀ k c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ Dexp : ℕ, 2 ≤ Dexp ∧ PreparedHigherShiftContradictionSpec s r b₀ k₀ k Dexp epsilon := by
  obtain ⟨B, _, hpartition⟩ := exists_prescribed_partition_expansion s r b₀
  obtain ⟨a, _, hcontra⟩ := exists_native_partition_expansion_contradiction.{0, 0}
    B k c s hc hepsilon hepsilon1 hshift
  obtain ⟨C, _, hpartition⟩ := hpartition k₀ a
  obtain ⟨Dexp, hDexp, _, hcontra⟩ := hcontra C
  refine ⟨Dexp, hDexp, ?_⟩
  dsimp only [PreparedHigherShiftContradictionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E L₀ _ _ d₀ D₀ W dR dQ R Q₀ _ _ _ _ p cost q
    hp hι hκ hD hV hb hE hcost hcostb hbase g g₀ anchor N _ hodd hN
    f₁ f₂ weight sigma delta hsigma hdelta hf₁ hf₂ hweight J₀ freq hfreq S hS hpositive hinvariant
    Hsh gT branch η γ rSq qSq horbit hother hγ hη hnorm hqSq slow middle rat ζ
    hζ hfactor hslow hrat hcoeff hzero hH hcompare hviolate
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let T := optionFactors D₀ Z
  let H := (pi T).filtration.gradedRefiltrationSubalgebra W
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q₀.basis
  have hdata := hpartition D b v hF M hM hin hout E D₀ W R Q₀ q
    hp hι hκ hD hV hb hE hcost hcostb hbase
  let Q' := Classical.choose hdata
  have hQdata := Classical.choose_spec hdata
  obtain ⟨_, _, _, _, hpart⟩ := hQdata
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨hρ, hρ1, hρinv⟩ := partition_expansion_precision_properties hp0 a
  have hpartData := hpart g g₀ anchor N hρ hρ1 (le_of_eq hρinv)
  let I : Type := Classical.choose hpartData
  have hpartI := Classical.choose_spec hpartData
  let inst : Fintype I := Classical.choose hpartI
  have hpartInst := Classical.choose_spec hpartI
  obtain ⟨hcount, A, hA, _, _, hexp⟩ := hpartInst
  let := inst
  have hexpData := hexp freq hfreq S hS hpositive hinvariant (↑Hsh : Set (ZMod N))
    gT branch η γ rSq qSq horbit hother hγ hη hnorm hqSq
    slow middle rat ζ hζ hfactor hslow hrat hcoeff hzero
  let U := Classical.choose hexpData
  have hUdata := Classical.choose_spec hexpData
  obtain ⟨hU, hUc, _, err, heval, hmean⟩ := hUdata
  exact hcontra (T none) Q' N p sigma delta f₁ f₂ weight A Hsh U S err
    hp hodd hN hcount hsigma hdelta hf₁ hf₂ hweight hA hU hUc hH
    (fun h _ => hpositive h) heval (fun h _ => hmean h) @hcompare hviolate

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.PositiveShiftBasis

end OAI

end

theorem solution : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_prepared_higher_shift_contradiction := @OAI.Erdos3.RationalFilteredNilmanifold.exists_prepared_higher_shift_contradiction
