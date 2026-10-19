-- Prove2me | solution 1 for OAI.Erdos3.exists_configuration_centered_counting_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:59:17.861991+00:00
-- url     : https://prove2.me/submissions/e93efbea-c364-4096-9238-01de649ab097

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B198
import Theorems.Thm_OAI_Erdos3_exists_positive_progression_counting_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem centered_product_mean_expansion {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (hS : S.Nonempty) (F : I → X → ℝ) :
    (𝔼 x, ∏ i ∈ S, (F i x - 1)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * ((𝔼 x, ∏ i ∈ S \ U, F i x) - 1) := by
  have hpoint (x : X) : (∏ i ∈ S, (F i x - 1)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i ∈ S \ U, F i x) := by
    simpa only [Finset.prod_const_one, mul_one] using
      Finset.prod_sub (fun i => F i x) (fun _ => (1 : ℝ)) S
  have hzero : (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card) = 0 := by
    have h := (Finset.prod_sub (fun _ : I => (1 : ℝ)) (fun _ => (1 : ℝ)) S).symm
    simpa [hS.ne_empty] using h
  simp only [hpoint, Finset.expect_sum_comm, ← Finset.mul_expect]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hzero, sub_zero]

theorem centered_product_mean_abs_le {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (hS : S.Nonempty) (F : I → X → ℝ) {error : ℝ}
    (hmean : ∀ U ⊆ S, |(𝔼 x, ∏ i ∈ U, F i x) - 1| ≤ error) :
    |𝔼 x, ∏ i ∈ S, (F i x - 1)| ≤ (2 : ℝ) ^ S.card * error := by
  rw [centered_product_mean_expansion S hS F]
  calc
    _ ≤ ∑ U ∈ S.powerset,
        |(-1 : ℝ) ^ U.card * ((𝔼 x, ∏ i ∈ S \ U, F i x) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, error := by
      apply Finset.sum_le_sum
      intro U _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hmean (S \ U) Finset.sdiff_subset
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

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

theorem complement_evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    T.complement.evalCyclic N x = 1 - T.evalCyclic N x := rfl

theorem complement_unitInterval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    T.complement.UnitIntervalValued := by
  intro z
  have hz := hT z
  change (1 - T.observable z).im = 0 ∧ 0 ≤ (1 - T.observable z).re ∧
    (1 - T.observable z).re ≤ 1
  simp only [Complex.sub_im, Complex.one_im, Complex.sub_re, Complex.one_re, hz.1]
  exact ⟨by norm_num, by linarith [hz.2.2], by linarith [hz.2.1]⟩

theorem complement_complexity (T : D.Niltest w) {p : ℝ}
    (hT : T.ComplexityLE p) : T.complement.ComplexityLE (p + 1) := by
  refine ⟨hT.1.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 + (T.normBound : ℝ)) + (T.lipBound : ℝ)) ≤ p + 1
  apply (Real.log_le_iff_le_exp (by positivity)).2
  rw [Real.exp_add]
  have hcap := T.observable_budget hT
  nlinarith [Real.add_one_le_exp (1 : ℝ), T.normBound.coe_nonneg, T.lipBound.coe_nonneg]

end RationalFilteredNilmanifold.Niltest

theorem PositiveCyclicNiltest.complement {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f) :
    PositiveCyclicNiltest.{u} degree N (p + 1) (fun x => 1 - f x) := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  refine .of_test D hs T.complement (T.complement_unitInterval hT)
    (T.complement_complexity hTc) ?_
  intro x
  rw [T.complement_evalCyclic, Complex.sub_re, Complex.one_re, heval]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MaskedComparisonBudget
namespace OAI

section

namespace Erdos3

theorem exists_masked_comparison_budget (a b : ℕ) {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 2 ≤ p →
      let R := (p + 2) ^ (max a b)
      (p + 2) ^ a ≤ R ∧ (p + 2) ^ b ≤ R ∧
      R + 1 ≤ (p + 2) ^ C ∧
      productNiltestBudget (raisedNiltestBudget R) ≤ (p + 2) ^ C ∧
      Real.exp (-((p + 2) ^ C)) ≤ xi := by
  obtain ⟨ell, hell⟩ := exists_nat_ge (-Real.log xi)
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + 2) ^ (max a b)
  let Q := Y + (Y + 2) ^ 2 + 3
  let E := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (E + Y + 1 + Polynomial.C ell)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  have hp0 : 0 ≤ p := by linarith
  have hell0 : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hbase : 1 ≤ p + 2 := by linarith
  have hR0 : 0 ≤ (p + 2) ^ (max a b) := pow_nonneg (by linarith) _
  have hQ0 : 0 ≤ raisedNiltestBudget ((p + 2) ^ (max a b)) :=
    hR0.trans (le_raisedNiltestBudget _)
  have hE0 : 0 ≤ productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) :=
    (sq_nonneg _).trans (productNiltestBudget_geometry hQ0)
  have hsum : productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) +
      (p + 2) ^ (max a b) + 1 + ell ≤ (p + 2) ^ C := by
    simpa [X, Y, Q, E, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbound p hp0
  have hR : (p + 2) ^ (max a b) + 1 ≤ (p + 2) ^ C := by
    linarith
  have hE : productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) ≤
      (p + 2) ^ C := by linarith
  have hellP : (ell : ℝ) ≤ (p + 2) ^ C := by linarith
  refine ⟨pow_le_pow_right₀ hbase (le_max_left _ _),
    pow_le_pow_right₀ hbase (le_max_right _ _), hR, hE, ?_⟩
  calc
    _ ≤ Real.exp (Real.log xi) := Real.exp_le_exp.mpr (by linarith)
    _ = xi := Real.exp_log hxi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexPositiveMasks
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem complexMaskComponent_abs_le (b : Bool) (z : ℂ) :
    |complexMaskComponent b z| ≤ ‖z‖ := by
  cases b
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

theorem complexPositiveMask_bounds (t : Bool × Bool) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ complexPositiveMask t z ∧ complexPositiveMask t z ≤ 1 := by
  have hs : |complexMaskSign t.2| = 1 := by cases t.2 <;> norm_num [complexMaskSign]
  have h : |complexMaskSign t.2 * complexMaskComponent t.1 z| ≤ 1 := by
    rw [abs_mul, hs, one_mul]
    exact (complexMaskComponent_abs_le t.1 z).trans hz
  obtain ⟨hl, hu⟩ := abs_le.mp h
  dsimp [complexPositiveMask]
  constructor <;> linarith

theorem complexPositiveMask_lipschitz (t : Bool × Bool) :
    LipschitzWith 1 (complexPositiveMask t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hs : |complexMaskSign t.2| = 1 := by cases t.2 <;> norm_num [complexMaskSign]
  have hc : complexMaskComponent t.1 (z - w) =
      complexMaskComponent t.1 z - complexMaskComponent t.1 w := by
    cases t.1 <;> rfl
  have he : complexPositiveMask t z - complexPositiveMask t w =
      complexMaskSign t.2 * complexMaskComponent t.1 (z - w) / 2 := by
    rw [hc]
    dsimp [complexPositiveMask]
    ring
  rw [NNReal.coe_one, one_mul, Real.dist_eq, he, abs_div, abs_mul, hs, one_mul]
  norm_num only [show |(2 : ℝ)| = 2 by norm_num]
  rw [dist_eq_norm]
  linarith [complexMaskComponent_abs_le t.1 (z - w), norm_nonneg (z - w)]

theorem complexMaskCoefficient_norm (t : Bool × Bool) : ‖complexMaskCoefficient t‖ = 1 := by
  rcases t with ⟨b, c⟩
  cases b <;> cases c <;> norm_num [complexMaskCoefficient, complexMaskSign]

theorem complexPositiveMask_expansion (z : ℂ) :
    z = ∑ t : Bool × Bool, complexMaskCoefficient t * (complexPositiveMask t z : ℂ) := by
  apply Complex.ext <;>
    simp [Fintype.sum_prod_type, complexMaskCoefficient,
      complexPositiveMask, complexMaskSign, complexMaskComponent] <;> ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductSumEstimate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_expect_product_sum_le {I J X : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype X]
    (c : I → J → ℂ) (A : I → J → X → ℂ) {error : ℝ}
    (hc : ∀ i j, ‖c i j‖ = 1)
    (hA : ∀ choice : I → J, ‖𝔼 x, ∏ i, A i (choice i) x‖ ≤ error) :
    ‖𝔼 x, ∏ i, ∑ j, c i j * A i j x‖ ≤ (Fintype.card J : ℝ) ^ Fintype.card I * error := by
  have he : (𝔼 x, ∏ i, ∑ j, c i j * A i j x) =
      ∑ choice : I → J, (∏ i, c i (choice i)) * (𝔼 x, ∏ i, A i (choice i) x) := by
    simp only [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]
  rw [he]
  calc
    _ ≤ ∑ choice : I → J, ‖(∏ i, c i (choice i)) * (𝔼 x, ∏ i, A i (choice i) x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _choice : I → J, error := by
      apply Finset.sum_le_sum
      intro choice _
      simpa only [norm_mul, norm_prod, hc, Finset.prod_const_one, one_mul] using hA choice
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotStageBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem twoSlopeMap_bijective {R : Type*} [CommRing R] (a b : R) (hab : IsUnit (b - a)) :
    Function.Bijective (fun z : R × R => (z.1 + a * z.2, z.1 + b * z.2)) := by
  obtain ⟨u, hu⟩ := hab
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hd : (u : R) * x.2 = (u : R) * y.2 := by
      rw [hu]
      dsimp at h1 h2
      linear_combination h2 - h1
    have hxy : x.2 = y.2 := u.isUnit.mul_left_cancel hd
    apply Prod.ext
    · dsimp at h1
      rw [hxy] at h1
      exact add_right_cancel h1
    · exact hxy
  · rintro ⟨y, z⟩
    let d := (↑(u⁻¹) : R) * (z - y)
    refine ⟨(y - a * d, d), ?_⟩
    apply Prod.ext
    · dsimp
      ring
    · change y - a * d + b * d = z
      have hd : (b - a) * d = z - y := by
        rw [← hu]
        dsimp [d]
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      linear_combination hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedCenteredCounting
namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

theorem maskedNormalized_bounds {X : Type*} (mu phi : X → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hmu : ∀ x, 0 ≤ mu x ∧ mu x ≤ B) (hphi : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1) (x : X) :
    0 ≤ maskedNormalized mu phi x ∧ maskedNormalized mu phi x ≤ B := by
  have h1 := mul_nonneg (hphi x).1 (hmu x).1
  have h2 := mul_nonneg (hphi x).1 (sub_nonneg.mpr (hmu x).2)
  have h3 := mul_nonneg (sub_nonneg.mpr (hphi x).2) (sub_nonneg.mpr hB)
  dsimp [maskedNormalized]
  constructor <;> nlinarith [(hphi x).2]

theorem maskedNormalized_score_le {X : Type*} (mu phi : X → ℝ) {xi xi' : ℝ}
    (hxi : 0 ≤ xi) (hxi' : xi ≤ xi') (hphi : ∀ x, phi x ≤ 1) (x : X) :
    maskedNormalized mu phi x - (1 + xi') ≤ mu x * phi x - (1 + xi) * phi x := by
  have h := mul_le_mul_of_nonneg_left (hphi x) hxi
  dsimp [maskedNormalized]
  nlinarith

theorem maskedNormalized_mean {X : Type*} [Fintype X] [Nonempty X]
    (mu phi : X → ℝ) {xi error : ℝ} (hxi : 0 ≤ xi)
    (hmean : (𝔼 x, mu x) = 1) (hphi : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hupper : (𝔼 x, (mu x - (1 + xi)) * phi x) ≤ error)
    (hlower : (𝔼 x, (mu x - (1 + xi)) * (1 - phi x)) ≤ error) :
    |(𝔼 x, maskedNormalized mu phi x) - 1| ≤ xi + error := by
  have hphimean : 0 ≤ (𝔼 x, phi x) ∧ (𝔼 x, phi x) ≤ 1 := by
    constructor
    · exact Finset.expect_nonneg (fun x _ => (hphi x).1)
    · exact (Finset.expect_le_expect (fun x _ => (hphi x).2)).trans_eq (Fintype.expect_const 1)
  have he (x : X) : maskedNormalized mu phi x = 1 + (mu x - (1 + xi)) * phi x + xi * phi x := by
    dsimp [maskedNormalized]
    ring
  have hcomp (x : X) : (mu x - (1 + xi)) * (1 - phi x) =
      mu x - (1 + xi) - (mu x - (1 + xi)) * phi x := by ring
  simp only [hcomp, Finset.expect_sub_distrib, Fintype.expect_const, hmean] at hlower
  simp only [he, Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hxi hphimean.1,
    mul_le_mul_of_nonneg_left hphimean.2 hxi]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem CyclicNiltestUpperComparison.masked {degree N : ℕ} [NeZero N]
    {P R error xi xi' : ℝ} {mu phi : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error mu (fun _ => 1 + xi))
    (hphi : PositiveCyclicNiltest.{u} degree N R phi) (hR : 0 ≤ R)
    (hbudget : productNiltestBudget (raisedNiltestBudget R) ≤ P)
    (hxi : 0 ≤ xi) (hxi' : xi ≤ xi') :
    CyclicNiltestUpperComparison.{u} degree N R error
      (maskedNormalized mu phi) (fun _ => 1 + xi') := by
  have h : CyclicNiltestUpperComparison.{u} degree N R error
      (fun x => mu x * phi x) (fun x => (1 + xi) * phi x) :=
    hphi.mul_upperComparison (low := degree) (@hcompare) le_rfl hR hbudget
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  apply le_trans _ (h D hs T hT hTc)
  apply Finset.expect_le_expect
  intro x _
  exact mul_le_mul_of_nonneg_right
    (maskedNormalized_score_le mu phi hxi hxi' (fun y => (hphi.unit_interval y).2) x)
    (T.unit_interval_evalCyclic hT N (fun _ => x)).2.1

theorem CyclicNiltestUpperComparison.masked_mean {degree N : ℕ} [NeZero N]
    {P R error xi : ℝ} {mu phi : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error mu (fun _ => 1 + xi))
    (hphi : PositiveCyclicNiltest.{u} degree N R phi) (hRP : R + 1 ≤ P)
    (hxi : 0 ≤ xi) (hmean : (𝔼 x, mu x) = 1) :
    |(𝔼 x, maskedNormalized mu phi x) - 1| ≤ xi + error :=
  maskedNormalized_mean mu phi hxi hmean hphi.unit_interval
    (hcompare.test_positive hphi (by linarith))
    (hcompare.test_positive hphi.complement hRP)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_masked_positive_counting (s a : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (phi : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i, PositiveCyclicNiltest.{0} s N ((p + 2) ^ a) (phi i)) →
      ∀ T : Finset I, T.card ≤ s + 2 →
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, maskedNormalized mu (phi i) (x + slopes i * d)) - 1| ≤ tau := by
  obtain ⟨B, _, xi, hxi, hcount⟩ := exists_positive_progression_counting_s2 s htau
  obtain ⟨C, hC, hbudget⟩ := exists_masked_comparison_budget a B hxi
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes phi hsep hphi T hT
  obtain ⟨haR, hBR, hRP, hproduct, herror⟩ := hbudget p hp
  let R := (p + 2) ^ (max a B)
  have hR : 0 ≤ R := pow_nonneg (by linarith) _
  have hBP : (p + 2) ^ B ≤ (p + 2) ^ C := by linarith
  have hphiR (i : I) : PositiveCyclicNiltest.{0} s N R (phi i) :=
    (hphi i).mono le_rfl haR
  apply hcount (N := N) (p := p) (xi := xi) hp hxi le_rfl hodd
    ((Real.exp_le_exp.mpr hBP).trans hN) slopes (fun i => maskedNormalized mu (phi i)) hsep
    (fun i x => maskedNormalized_bounds mu (phi i) (Real.one_le_exp (by linarith))
      hmu (hphiR i).unit_interval x) ?_ ?_ T hT
  · intro i
    have h := CyclicNiltestUpperComparison.masked_mean hcompare (hphiR i) hRP hxi.le hmean
    exact h.trans (by linarith)
  · intro i
    exact CyclicNiltestUpperComparison.mono_budget
      (CyclicNiltestUpperComparison.masked hcompare (hphiR i) hR hproduct hxi.le le_rfl)
      hBR (Real.exp_le_exp.mpr (neg_le_neg hBP))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_masked_centered_counting (s a : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (phi : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i, PositiveCyclicNiltest.{0} s N ((p + 2) ^ a) (phi i)) →
      ∀ T : Finset I, T.Nonempty → T.card ≤ s + 2 →
        |𝔼 x, 𝔼 d, ∏ i ∈ T, phi i (x + slopes i * d) * (mu (x + slopes i * d) - 1)| ≤
          epsilon := by
  let tau := epsilon / (2 : ℝ) ^ (s + 2)
  have htau : 0 < tau := by dsimp [tau]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_masked_positive_counting s a htau
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes phi hsep hphi T hT hcard
  let F : I → (ZMod N × ZMod N) → ℝ :=
    fun i z => maskedNormalized mu (phi i) (z.1 + slopes i * z.2)
  have hsub (U : Finset I) (hU : U ⊆ T) : |(𝔼 z, ∏ i ∈ U, F i z) - 1| ≤ tau := by
    dsimp only [F]
    rw [expect_prod_split]
    exact hcount hp hodd hN mu hmu hmean hcompare slopes phi hsep hphi U
      ((Finset.card_le_card hU).trans hcard)
  have h := centered_product_mean_abs_le T hT F hsub
  have heq (i : I) (z : ZMod N × ZMod N) :
      F i z - 1 = phi i (z.1 + slopes i * z.2) * (mu (z.1 + slopes i * z.2) - 1) := by
    dsimp [F, maskedNormalized]
    ring
  simp only [heq] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    (2 : ℝ) ^ T.card * tau ≤ (2 : ℝ) ^ (s + 2) * tau :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) htau.le
    _ = epsilon := by dsimp [tau]; field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCenteredCounting
namespace OAI

section

namespace Erdos3

open scoped TensorProduct NNReal

theorem positiveCyclicNiltest_characterMask {N degree : ℕ} [NeZero N]
    (hdegree : 1 ≤ degree) (chi : AddChar (ZMod N) ℂ) (t : Bool × Bool) :
    PositiveCyclicNiltest.{0} degree N 13 (fun x => complexPositiveMask t (chi x)) := by
  obtain ⟨T, hTnorm, hTc, hTeval⟩ := exists_cyclic_character_niltest chi
  have hbound (z) := complexPositiveMask_bounds t ((T.norm_le z).trans (by exact_mod_cast hTnorm))
  let S : (RationalTorus.nilmanifold 1).Niltest (fun _ : Unit => 1) := {
    orbit := T.orbit
    observable := fun z => (complexPositiveMask t (T.observable z) : ℂ)
    normBound := 1
    lipBound := T.lipBound
    norm_le := fun z => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound z).1, NNReal.coe_one] using (hbound z).2
    lipschitz := by
      let := (RationalTorus.nilmanifold 1).metricSpace
      simpa only [one_mul, Function.comp_def] using
        Complex.isometry_ofReal.lipschitz.comp ((complexPositiveMask_lipschitz t).comp T.lipschitz) }
  have hS : S.UnitIntervalValued := by
    intro z
    exact ⟨rfl, hbound z⟩
  have hSc : S.ComplexityLE 13 := by
    refine ⟨hTc.1.mono _ (by norm_num), ?_⟩
    change Real.log (2 + 1 + (T.lipBound : ℝ)) ≤ 13
    apply (Real.log_le_iff_le_exp (by positivity)).2
    have h := T.observable_budget hTc
    have he : Real.exp 13 = Real.exp 12 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith [T.normBound.coe_nonneg, Real.add_one_le_exp (1 : ℝ), Real.exp_pos (12 : ℝ)]
  refine .of_test (RationalTorus.nilmanifold 1) hdegree S hS hSc ?_
  intro x
  change complexPositiveMask t (chi x) = complexPositiveMask t (T.evalCyclic N (fun _ => x))
  rw [hTeval]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_character_centered_counting (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N) (chi : I → AddChar (ZMod N) ℂ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ‖𝔼 x, 𝔼 d, ∏ i, chi i (x + slopes i * d) * ((mu (x + slopes i * d) - 1 : ℝ) : ℂ)‖ ≤
        epsilon := by
  let delta := epsilon / (4 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_masked_centered_counting s 2 hdelta
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ _ _ hI slopes chi hsep
  let A : I → (Bool × Bool) → (ZMod N × ZMod N) → ℂ := fun i t z =>
    (complexPositiveMask t (chi i (z.1 + slopes i * z.2)) : ℂ) *
      ((mu (z.1 + slopes i * z.2) - 1 : ℝ) : ℂ)
  have hcost : (13 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have hA (choice : I → Bool × Bool) : ‖𝔼 z, ∏ i, A i (choice i) z‖ ≤ delta := by
    let phi : I → ZMod N → ℝ := fun i x => complexPositiveMask (choice i) (chi i x)
    have hphi (i : I) : PositiveCyclicNiltest.{0} s N ((p + 2) ^ 2) (phi i) :=
      (positiveCyclicNiltest_characterMask hs (chi i) (choice i)).mono le_rfl hcost
    have h := hcount hp hodd hN mu hmu hmean hcompare slopes phi hsep hphi
      Finset.univ Finset.univ_nonempty (by simpa using hI)
    have he : (𝔼 z, ∏ i, A i (choice i) z) =
        (((𝔼 x, 𝔼 d, ∏ i, phi i (x + slopes i * d) * (mu (x + slopes i * d) - 1)) : ℝ) : ℂ) := by
      simp only [A, ← Complex.ofReal_mul, ← Complex.ofReal_prod]
      rw [expect_prod_split]
      simp only [phi, Fintype.expect_eq_sum_div_card, Complex.ofReal_div,
        Complex.ofReal_sum, Complex.ofReal_natCast]
    rw [he]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  have h := norm_expect_product_sum_le (fun _ : I => complexMaskCoefficient) A
    (fun _ t => complexMaskCoefficient_norm t) hA
  have he (i : I) (z : ZMod N × ZMod N) :
      (∑ t, complexMaskCoefficient t * A i t z) =
        chi i (z.1 + slopes i * z.2) * ((mu (z.1 + slopes i * z.2) - 1 : ℝ) : ℂ) := by
    dsimp only [A]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    exact (complexPositiveMask_expansion _).symm
  simp only [he, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    ((2 : ℝ) * 2) ^ Fintype.card I * delta ≤ (4 : ℝ) ^ (s + 2) * delta := by
      norm_num only [show (2 : ℝ) * 2 = 4 by norm_num]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hI) hdelta.le
    _ = epsilon := by dsimp [delta]; field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ConfigurationCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_two_slope_characters {R : Type*} [CommRing R]
    (a b : R) (hab : IsUnit (b - a)) (Psi : AddChar (R × R) ℂ) :
    ∃ chi rho : AddChar R ℂ, ∀ x d, Psi (x, d) = chi (x + a * d) * rho (x + b * d) := by
  let e : (R × R) ≃+ (R × R) := AddEquiv.ofBijective (twoSlopeAddHom a b)
    (twoSlopeMap_bijective a b hab)
  let L : R →+ (R × R) := { toFun := fun x => (x, 0), map_zero' := rfl, map_add' := by intros; simp }
  let M : R →+ (R × R) := { toFun := fun y => (0, y), map_zero' := rfl, map_add' := by intros; simp }
  refine ⟨Psi.compAddMonoidHom (e.symm.toAddMonoidHom.comp L),
    Psi.compAddMonoidHom (e.symm.toAddMonoidHom.comp M), ?_⟩
  intro x d
  change Psi (x, d) = Psi (e.symm (x + a * d, 0)) * Psi (e.symm (0, x + b * d))
  have hpair : (x + a * d, 0) + (0, x + b * d) = e (x, d) := by
    change (x + a * d, 0) + (0, x + b * d) = (x + a * d, x + b * d)
    simp
  rw [← AddChar.map_add_eq_mul, ← map_add, hpair, e.symm_apply_apply]

theorem exists_single_slope_characters {R : Type*} [CommRing R]
    (a : R) (Psi : AddChar (R × R) ℂ) :
    ∃ chi rho : AddChar R ℂ, ∀ u d, Psi (u - a * d, d) = chi u * rho d := by
  let L : R →+ (R × R) := { toFun := fun u => (u, 0), map_zero' := rfl, map_add' := by intros; simp }
  let M : R →+ (R × R) := {
    toFun := fun d => (-a * d, d)
    map_zero' := by simp
    map_add' := by intro x y; ext <;> simp [mul_add] }
  refine ⟨Psi.compAddMonoidHom L, Psi.compAddMonoidHom M, ?_⟩
  intro u d
  change Psi (u - a * d, d) = Psi (u, 0) * Psi (-a * d, d)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ext <;> simp [sub_eq_add_neg]

theorem complex_expect_pivot_change {R : Type*} [Ring R] [Fintype R]
    (a : R) (F : R → R → ℂ) :
    (𝔼 x, 𝔼 d, F x d) = 𝔼 u, 𝔼 d, F (u - a * d) d := by
  rw [Finset.expect_comm, Finset.expect_comm (Finset.univ : Finset R) (Finset.univ : Finset R)
    (fun u d => F (u - a * d) d)]
  apply Finset.expect_congr rfl
  intro d _
  symm
  apply Fintype.expect_equiv (Equiv.addRight (-(a * d)))
  intro u
  change F (u - a * d) d = F (u + -(a * d)) d
  rw [sub_eq_add_neg]

theorem exists_single_slope_character_bound {R : Type*} [CommRing R] [Fintype R]
    (a : R) (Psi : AddChar (R × R) ℂ) (f : R → ℂ) :
    ∃ chi : AddChar R ℂ,
      ‖𝔼 x, 𝔼 d, Psi (x, d) * f (x + a * d)‖ ≤ ‖𝔼 u, chi u * f u‖ := by
  obtain ⟨chi, rho, hfactor⟩ := exists_single_slope_characters a Psi
  refine ⟨chi, ?_⟩
  rw [complex_expect_pivot_change a]
  simp only [sub_add_cancel, hfactor]
  have he : (𝔼 u, 𝔼 d, chi u * rho d * f u) =
      (𝔼 u, chi u * f u) * (𝔼 d, rho d) := by
    have hpoint (u d : R) : chi u * rho d * f u = (chi u * f u) * rho d := by ring
    simp only [hpoint, ← Finset.mul_expect, ← Finset.expect_mul]
  rw [he, norm_mul]
  have hrho : ‖𝔼 d, rho d‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    simp only [AddChar.norm_apply, Fintype.expect_const]
    exact le_rfl
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hrho (norm_nonneg _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConfigurationCenteredCounting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_configuration_centered_counting_s2_oai (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N), (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ∀ Psi : AddChar (ZMod N × ZMod N) ℂ,
      ‖𝔼 x, 𝔼 d, Psi (x, d) * (∏ i, ((mu (x + slopes i * d) - 1 : ℝ) : ℂ))‖ ≤ epsilon := by
  classical
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_character_centered_counting s hs hepsilon
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ _ _ hI slopes hsep Psi
  by_cases hsmall : Fintype.card I ≤ 1
  · let : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hsmall
    let i : I := Classical.arbitrary I
    obtain ⟨chi, hchi⟩ := exists_single_slope_character_bound (slopes i) Psi
      (fun u => ((mu u - 1 : ℝ) : ℂ))
    have hsingle := hcount hp hodd hN mu hmu hmean hcompare (I := Unit)
      (by simp) (fun _ => (0 : ZMod N)) (fun _ => chi)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    have hsingle' : ‖𝔼 u, chi u * ((mu u - 1 : ℝ) : ℂ)‖ ≤ epsilon := by
      simpa using hsingle
    have hprod (x d : ZMod N) :
        (∏ j : I, ((mu (x + slopes j * d) - 1 : ℝ) : ℂ)) =
          ((mu (x + slopes i * d) - 1 : ℝ) : ℂ) := Fintype.prod_subsingleton _ i
    simp only [hprod]
    exact hchi.trans hsingle'
  obtain ⟨i, _, j, _, hij⟩ := Finset.one_lt_card.mp
    (show 1 < (Finset.univ : Finset I).card by simpa using (show 1 < Fintype.card I by omega))
  obtain ⟨chi, rho, hfactor⟩ := exists_two_slope_characters (slopes i) (slopes j)
    (hsep j i (Ne.symm hij)) Psi
  let theta : I → AddChar (ZMod N) ℂ := fun k => if k = i then chi else if k = j then rho else 0
  have htheta (x d : ZMod N) :
      (∏ k : I, theta k (x + slopes k * d)) = Psi (x, d) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => theta k (x + slopes k * d)) (Finset.mem_univ i)]
    have hi : theta i (x + slopes i * d) = chi (x + slopes i * d) := by simp [theta]
    have hj : (∏ k ∈ (Finset.univ : Finset I).erase i, theta k (x + slopes k * d)) =
        rho (x + slopes j * d) := by
      rw [Finset.prod_eq_single_of_mem j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
      · simp [theta, Ne.symm hij]
      · intro k hk hkj
        simp [theta, Finset.ne_of_mem_erase hk, hkj]
    rw [hi, hj, ← hfactor]
  have h := hcount hp hodd hN mu hmu hmean hcompare hI slopes theta hsep
  simpa only [Finset.prod_mul_distrib, htheta] using h

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_configuration_centered_counting_s2_oai := @OAI.Erdos3.exists_configuration_centered_counting_s2_oai
