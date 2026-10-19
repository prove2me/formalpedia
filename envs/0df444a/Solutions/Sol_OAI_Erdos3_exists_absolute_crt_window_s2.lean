-- Prove2me | solution 1 for OAI.Erdos3.exists_absolute_crt_window_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:58:22.396006+00:00
-- url     : https://prove2.me/submissions/e58b0db2-9cfc-4558-9334-588ee83efd3a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B110
import Definitions.Def_OAIE3v2B198
import Theorems.Thm_OAI_Erdos3_exists_crt_counting_contradiction_s2
import Theorems.Thm_OAI_Erdos3_exists_localizedRepresentativeWindow_score_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem ofCoordinates_center (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (t : σ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    ((ofCoordinates P hP).slots t).center x i = aeval t (P i) := by
  simp only [slots, ofCoordinates, MvPolynomial.comp_aeval_apply, aeval_X, Sum.elim_inl]

end PolynomialSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AbsoluteIncrementBudgets
namespace OAI

section

namespace Erdos3

theorem absolute_normalization_budget (C : ℕ) {p alpha : ℝ} (hp : 2 ≤ p)
    (halpha : 0 < alpha) (hlower : Real.exp (-p) ≤ alpha) :
    (p + 2) ^ C ≤ (p + 2) ^ (C + 1) ∧
      Real.exp (-((p + 2) ^ (C + 1))) / alpha ≤ Real.exp (-((p + 2) ^ C)) := by
  have hb : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ C := one_le_pow₀ hb
  have hs : (p + 2) ^ C + p ≤ (p + 2) ^ (C + 1) := by
    rw [pow_succ]
    nlinarith [mul_nonneg (by linarith : 0 ≤ p + 1) (sub_nonneg.mpr hpow)]
  refine ⟨by linarith, (div_le_iff₀ halpha).mpr ?_⟩
  calc
    _ ≤ Real.exp (-((p + 2) ^ C) - p) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-((p + 2) ^ C)) * Real.exp (-p) := by rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le

theorem exists_absolute_side_budget (Csc k : ℕ) (hk : 0 < k) {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧ ∀ p : ℝ, 2 ≤ p →
      (p + 2) ^ Csc ≤ (p + 2) ^ C ∧
      (64 * (k : ℝ)) ≤ Real.exp ((p + 2) ^ C) ∧
      100 * (1 + xi) * Real.exp ((p + 2) ^ Csc) ≤ Real.exp ((p + 2) ^ C) := by
  obtain ⟨ell, hell⟩ := exists_nat_ge (Real.log (64 * (k : ℝ)))
  obtain ⟨b, hb⟩ := exists_nat_ge (Real.log (100 * (1 + xi)))
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 2) ^ Csc + Polynomial.C ell + Polynomial.C b)
  let C := max D (Csc + 1)
  refine ⟨C, hD.trans (le_max_left _ _), by dsimp [C]; omega, ?_⟩
  intro p hp
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hpoly : (p + 2) ^ Csc + ell + b ≤ (p + 2) ^ D := by
    simpa [Polynomial.eval₂_pow] using hbound p hp0
  have hDC : (p + 2) ^ D ≤ (p + 2) ^ C := pow_le_pow_right₀ hbase (le_max_left _ _)
  have hsum := hpoly.trans hDC
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hpow0 : 0 ≤ (p + 2) ^ Csc := pow_nonneg (by linarith) _
  have hside : Real.log (64 * (k : ℝ)) ≤ (p + 2) ^ C := by linarith
  have hscore : Real.log (100 * (1 + xi)) + (p + 2) ^ Csc ≤ (p + 2) ^ C := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · calc
      _ = Real.exp (Real.log (64 * (k : ℝ))) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hside
  · calc
      _ = Real.exp (Real.log (100 * (1 + xi)) + (p + 2) ^ Csc) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem representativeWindowCount_pos : 0 < representativeWindowCount := by
  unfold representativeWindowCount intervalSiteCount
  omega

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

theorem patch_term {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ) :
    (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) =
      w.value (aeval t P - (b 0 : ℝ)) := by
  simp only [patch, PolynomialPatch.ofCoordinates, kernel, TriangularSlots.residual,
    PolynomialSlots.ofCoordinates_center, map_sub, aeval_C, Algebra.algebraMap_self_apply]
  congr 1
  ring

theorem patch_value {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) (t : σ → ℝ) :
    (w.patch s hs P hP).value t = w.value (Int.fract (aeval t P)) := by
  change (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
    (((w.patch s hs P hP).form.slots t).residual b)) = _
  simp_rw [w.patch_term s hs P hP t]
  rw [tsum_eq_single (fun _ : Fin 1 => ⌊aeval t P⌋)]
  · rfl
  · intro b hb
    by_contra h
    obtain ⟨h0, h1⟩ := w.interior _ h
    have hfloor : ⌊aeval t P⌋ = b 0 := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    apply hb
    funext i
    fin_cases i
    exact hfloor.symm

end RepresentativeWindow
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtIntegerRepresentative_cast (u : J → ℤ) :
    (crtIntegerRepresentative N hN u : ZMod (∏ j, N j)) =
      (ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j))) := by
  let E := ZMod.prodEquivPi N hN
  have hcoeff (j : J) : (crtIntegerCoefficient N hN j : ZMod (∏ j, N j)) =
      E.symm (Pi.single j (1 : ZMod (N j))) := by
    simp only [crtIntegerCoefficient, Int.cast_natCast, ZMod.natCast_zmod_val, E]
  calc
    _ = ∑ j, E.symm (Pi.single j (1 : ZMod (N j))) * (u j : ZMod (∏ j, N j)) := by
      simp only [crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, hcoeff]
    _ = E.symm (∑ j, Pi.single j (1 : ZMod (N j)) * (u j : (j : J) → ZMod (N j))) := by
      simp only [map_sum, map_mul, map_intCast]
    _ = _ := by
      congr 1
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_eq_same, one_mul]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij.symm, zero_mul]
      · simp

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_eval (u : J → ℤ) :
    aeval (fun j => (u j : ℝ)) (crtRepresentativePolynomial N hN) =
      (crtIntegerRepresentative N hN u : ℝ) / (∏ i, N i : ℕ) := by
  simp only [crtRepresentativePolynomial, map_sum, map_smul, aeval_X,
    smul_eq_mul, crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRepresentativeFraction
namespace OAI

section

namespace Erdos3

theorem integer_fraction_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    Int.fract ((a : ℝ) / N) = (((a : ZMod N).val : ℝ) / N) := by
  rw [Int.fract_div_intCast_eq_div_intCast_mod]
  exact congrArg (fun z : ℤ => (z : ℝ) / N) (ZMod.val_intCast a).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport
namespace OAI

section

namespace Erdos3.RepresentativeWindow

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtPatch_value (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) (u : J → ℤ) :
    (w.crtPatch N hN s hs).value (fun j => (u j : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) := by
  rw [crtPatch, w.patch_value, crtRepresentativePolynomial_eval,
    integer_fraction_eq_zmod_val, crtIntegerRepresentative_cast]

theorem crtPatch_value_residues [∀ j, NeZero (N j)] (w : RepresentativeWindow)
    (s : ℕ) (hs : 1 ≤ s) (u : (j : J) → ZMod (N j)) :
    (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) := by
  have h := w.crtPatch_value N hN s hs (fun j => ((u j).val : ℤ))
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h

end Erdos3.RepresentativeWindow

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTWindowScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
  (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crt_representative_patch_score (s : ℕ) (hs : 1 ≤ s)
    (f : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow) :
    (𝔼 u : (j : J) → ZMod (N j),
      f ((ZMod.prodEquivPi N hN).symm u) *
        (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ))) =
      𝔼 x, f x * w.value ((x.val : ℝ) / (∏ j, N j : ℕ)) := by
  apply Fintype.expect_equiv (ZMod.prodEquivPi N hN).symm.toEquiv
  intro u
  rw [w.crtPatch_value_residues N hN s hs]
  rfl

theorem exists_scored_crt_representative_patch (s : ℕ) (hs : 1 ≤ s)
    (f : ZMod (∏ j, N j) → ℝ) {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (hsize : 1 / ((∏ j, N j : ℕ) : ℝ) ≤ sigma / (100 * M)) :
    ∃ w : RepresentativeWindow,
      (w.lip : ℝ) = 100 * M / sigma + representativeWindowPartitionLip ∧
      3 * sigma / (4 * representativeWindowCount) ≤
        𝔼 u : (j : J) → ZMod (N j),
          f ((ZMod.prodEquivPi N hN).symm u) *
            (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) := by
  let eta : ℝ≥0 := ⟨sigma / (100 * M), by positivity⟩
  have heta : 0 < eta := by change 0 < sigma / (100 * M); positivity
  obtain ⟨i, hi⟩ := exists_localizedRepresentativeWindow_score_s2 f hM hsigma hf hscore
    eta heta le_rfl hsize
  let w := localizedRepresentativeWindow eta heta i
  refine ⟨w, ?_, ?_⟩
  · change (sigma / (100 * M))⁻¹ + (representativeWindowPartitionLip : ℝ) = _
    rw [inv_div]
  · rw [crt_representative_patch_score N hN s hs]
    exact hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RepresentativeWindowBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_representativeWindow_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p M sigma : ℝ, 0 ≤ p → 0 < M → M ≤ Real.exp p →
      Real.exp (-p) ≤ sigma →
      Real.log (2 + 100 * M / sigma + representativeWindowPartitionLip) ≤ (p + 2) ^ C ∧
      Real.exp (-((p + 2) ^ C)) ≤ 3 * sigma / (4 * representativeWindowCount) := by
  obtain ⟨a, ha⟩ := exists_nat_ge
    (Real.log (102 + (representativeWindowPartitionLip : ℝ)))
  obtain ⟨b, hb⟩ := exists_nat_ge (Real.log (4 * (representativeWindowCount : ℝ)))
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (2 * Polynomial.X + Polynomial.C (a + b))
  refine ⟨C, hC, ?_⟩
  intro p M sigma hp hM hMexp hsigma
  have hspos : 0 < sigma := lt_of_lt_of_le (Real.exp_pos _) hsigma
  have hbudget : 2 * p + a + b ≤ (p + 2) ^ C := by
    simpa [Nat.cast_add, add_assoc] using hbound p hp
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hK : 0 ≤ (representativeWindowPartitionLip : ℝ) := NNReal.coe_nonneg _
  have hdiv : M / sigma ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p / Real.exp (-p) :=
        div_le_div₀ (Real.exp_pos _).le hMexp (Real.exp_pos _) hsigma
      _ = Real.exp (2 * p) := by rw [← Real.exp_sub]; congr 1; ring
  have he : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by positivity)
  have hlip : 2 + 100 * M / sigma + representativeWindowPartitionLip ≤
      (102 + (representativeWindowPartitionLip : ℝ)) * Real.exp (2 * p) := by
    have hscaled := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 100)
    have hrest := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 +
      (representativeWindowPartitionLip : ℝ) by positivity)
    rw [mul_div_assoc]
    nlinarith
  have hcount : 0 < (4 * (representativeWindowCount : ℝ)) := by
    have : (0 : ℝ) < representativeWindowCount := by exact_mod_cast representativeWindowCount_pos
    positivity
  constructor
  · apply (Real.log_le_iff_le_exp (by positivity)).mpr
    calc
      _ ≤ (102 + (representativeWindowPartitionLip : ℝ)) * Real.exp (2 * p) := hlip
      _ = Real.exp (Real.log (102 + (representativeWindowPartitionLip : ℝ)) + 2 * p) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ ≤ Real.exp (-p - Real.log (4 * (representativeWindowCount : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-p) / (4 * representativeWindowCount) := by
        rw [Real.exp_sub, Real.exp_log hcount]
      _ ≤ 3 * sigma / (4 * representativeWindowCount) :=
        div_le_div_of_nonneg_right (by linarith) hcount.le

theorem exists_polynomial_scored_crt_representative_patch :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (s : ℕ) (hs : 1 ≤ s)
      (f : ZMod (∏ j, N j) → ℝ) {p M sigma : ℝ},
      0 ≤ p → 0 < M → M ≤ Real.exp p → Real.exp (-p) ≤ sigma →
      (∀ x, |f x| ≤ M) → sigma ≤ (𝔼 x, f x) →
      1 / ((∏ j, N j : ℕ) : ℝ) ≤ sigma / (100 * M) →
      ∃ w : RepresentativeWindow,
        Real.log (2 + ((w.crtPatch N hN s hs).kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤
          𝔼 u : (j : J) → ZMod (N j), f ((ZMod.prodEquivPi N hN).symm u) *
            (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_representativeWindow_budget
  refine ⟨C, hC, ?_⟩
  intro J _ _ N _ _ hN s hs f p M sigma hp hM hMexp hsigma hf hscore hsize
  obtain ⟨w, hw, hws⟩ := exists_scored_crt_representative_patch N hN s hs f hM
    (lt_of_lt_of_le (Real.exp_pos _) hsigma) hf hscore hsize
  have hb := hbudget p M sigma hp hM hMexp hsigma
  refine ⟨w, ?_, hb.2.trans hws⟩
  rw [RepresentativeWindow.crtPatch_lip, hw]
  simpa only [add_assoc] using hb.1

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem density_lower_bound_of_log_inverse {alpha p : ℝ} (halpha : 0 < alpha)
    (hlog : Real.log (1 / alpha) ≤ p) : Real.exp (-p) ≤ alpha := by
  have he : Real.log alpha ≥ -p := by
    rw [Real.log_div (by norm_num) halpha.ne', Real.log_one, zero_sub] at hlog
    linarith
  calc
    _ ≤ Real.exp (Real.log alpha) := Real.exp_le_exp.mpr he
    _ = alpha := Real.exp_log halpha

theorem normalized_density_bounds {X : Type*} (f : X → ℝ) {alpha p : ℝ}
    (halpha : 0 < alpha) (hlower : Real.exp (-p) ≤ alpha)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : X) :
    0 ≤ f x / alpha ∧ f x / alpha ≤ Real.exp p := by
  refine ⟨div_nonneg (hf x).1 halpha.le, ?_⟩
  apply (div_le_iff₀ halpha).mpr
  calc
    f x ≤ 1 := (hf x).2
    _ = Real.exp p * Real.exp (-p) := by rw [← Real.exp_add]; simp
    _ ≤ Real.exp p * alpha := mul_le_mul_of_nonneg_left hlower (Real.exp_pos p).le

theorem normalized_density_mean {X : Type*} [Fintype X] (f : X → ℝ) {alpha : ℝ}
    (halpha : 0 < alpha) (hmean : (𝔼 x, f x) = alpha) :
    (𝔼 x, f x / alpha) = 1 := by
  rw [← Finset.expect_div, hmean, div_self halpha.ne']

theorem support_normalized_density {X : Type*} (f : X → ℝ) {alpha : ℝ}
    (halpha : alpha ≠ 0) : Function.support (fun x => f x / alpha) = Function.support f := by
  ext x
  simp [Function.mem_support, halpha]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveScoreComparison
namespace OAI

section

universe u

namespace Erdos3

open scoped BigOperators TensorProduct

theorem CyclicNiltestUpperComparison.of_positive_scores {degree N : ℕ} [NeZero N]
    {P epsilon : ℝ} {f g : ZMod N → ℝ}
    (h : ∀ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N P T →
      (𝔼 x, (f x - g x) * T x) ≤ epsilon) :
    CyclicNiltestUpperComparison.{u} degree N P epsilon f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  exact h (fun x => (T.evalCyclic N (fun _ => x)).re)
    (.of_test D hs T hT hTc (fun _ => rfl))

theorem exists_positive_score_of_not_upperComparison {degree N : ℕ} [NeZero N]
    {P epsilon : ℝ} {f g : ZMod N → ℝ}
    (h : ¬ CyclicNiltestUpperComparison.{u} degree N P epsilon f g) :
    ∃ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N P T ∧
      epsilon < 𝔼 x, (f x - g x) * T x := by
  by_contra hnone
  apply h
  apply CyclicNiltestUpperComparison.of_positive_scores
  intro T hT
  by_contra he
  exact hnone ⟨T, hT, lt_of_not_ge he⟩

theorem CyclicNiltestUpperComparison.normalize {degree N : ℕ} [NeZero N]
    {P epsilon alpha c : ℝ} {f : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N P epsilon f (fun _ => c * alpha))
    (halpha : 0 < alpha) :
    CyclicNiltestUpperComparison.{u} degree N P (epsilon / alpha)
      (fun x => f x / alpha) (fun _ => c) := by
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  have he (x : ZMod N) : (f x / alpha - c) * (T.evalCyclic N (fun _ => x)).re =
      ((f x - c * alpha) * (T.evalCyclic N (fun _ => x)).re) / alpha := by
    field_simp [halpha.ne']
  simp only [he, ← Finset.expect_div]
  exact div_le_div_of_nonneg_right (h D hs T hT hTc) halpha.le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AbsoluteCRTWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem prime_product_unit_of_lt {J : Type*} [Fintype J] (N : J → ℕ)
    (hprime : ∀ j, (N j).Prime) {a : ℕ} (ha : 0 < a) (hlt : ∀ j, a < N j) :
    IsUnit (a : ZMod (∏ j, N j)) := by
  apply (ZMod.isUnit_iff_coprime a _).mpr
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro j
  exact ((hprime j).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha (hlt j))).symm

theorem modulus_le_product {J : Type*} [Fintype J] (N : J → ℕ)
    (hpos : ∀ j, 0 < N j) (j : J) : N j ≤ ∏ i, N i :=
  Finset.single_le_prod' (fun i _ => hpos i) (Finset.mem_univ j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_absolute_crt_score {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Csc : ℕ, 2 ≤ Csc ∧ ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
      (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
      0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
      (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
      (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
      IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
      let hN := distinct_prime_moduli_coprime N hprime hinj
      ∃ T : ZMod (∏ j, N j) → ℝ,
        PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ Csc) T ∧
        Real.exp (-((p + 2) ^ Csc)) ≤
          (𝔼 x, (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x) ∧
        ((∏ j, N j : ℕ) : ℝ)⁻¹ ≤
          (𝔼 x, (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x) /
            (100 * (1 + xi)) := by
  classical
  obtain ⟨C0, hC0, xi, hxi, hcontra⟩ := exists_crt_counting_contradiction_s2 (J := J) k hk
  let Csc := C0 + 1
  obtain ⟨C, hC, hstrict, hbudget⟩ := exists_absolute_side_budget Csc k (by omega) hxi
  refine ⟨Csc, by dsimp [Csc]; omega, C, hC, hstrict, xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  let hN := distinct_prime_moduli_coprime N hprime hinj
  let original : ZMod (∏ j, N j) → ℝ := fun x => f (ZMod.prodEquivPi N hN x)
  let normalized : ((j : J) → ZMod (N j)) → ℝ := fun u => f u / alpha
  have hlower := density_lower_bound_of_log_inverse halpha hlog
  have hnumb := absolute_normalization_budget C0 hp halpha hlower
  have hb := hbudget p hp
  have hside (j) : 64 * k ≤ N j := by exact_mod_cast hb.2.1.trans (hsize j)
  let j0 : J := Classical.choice inferInstance
  have hprod : (N j0 : ℝ) ≤ (∏ j, N j : ℕ) := by
    exact_mod_cast modulus_le_product N (fun j => (hprime j).pos) j0
  have hlarge : Real.exp ((p + 2) ^ C0) ≤ (∏ j, N j : ℕ) :=
    (Real.exp_le_exp.mpr (hnumb.1.trans hb.1)).trans ((hsize j0).trans hprod)
  have hunit (a : ℕ) (ha : 1 ≤ a) (hak : a < k) : IsUnit (a : ZMod (∏ j, N j)) := by
    apply prime_product_unit_of_lt N hprime ha
    intro j
    have hj := hside j
    omega
  have hodd : Odd (∏ j, N j) := Nat.coprime_two_left.mp
    ((ZMod.isUnit_iff_coprime 2 _).mp (hunit 2 (by omega) (by omega)))
  have horiginal : (𝔼 x, original x) = alpha := by
    calc
      _ = 𝔼 u, f u := Fintype.expect_equiv (ZMod.prodEquivPi N hN).toEquiv _ _ (fun _ => rfl)
      _ = alpha := hmean
  have hnormalized : (𝔼 x : ZMod (∏ j, N j), normalized (ZMod.prodEquivPi N hN x)) = 1 :=
    normalized_density_mean original halpha horiginal
  have hnormfree : IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support normalized) k := by
    dsimp only [normalized]
    rw [support_normalized_density f halpha.ne']
    exact hfree
  have hnot := hcontra N hN hp hodd hlarge hside hunit normalized
    (normalized_density_bounds f halpha hlower hf) hnormalized hnormfree
  have hnotScore : ¬ CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j)
      ((p + 2) ^ Csc) (Real.exp (-((p + 2) ^ Csc))) original (fun _ => (1 + xi) * alpha) := by
    intro hcomp
    have hn : CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j)
        ((p + 2) ^ Csc) (Real.exp (-((p + 2) ^ Csc)) / alpha)
        (fun x => original x / alpha) (fun _ => 1 + xi) :=
      CyclicNiltestUpperComparison.normalize hcomp halpha
    exact hnot (CyclicNiltestUpperComparison.mono_budget hn hnumb.1 hnumb.2)
  obtain ⟨T, hT, hscore⟩ := exists_positive_score_of_not_upperComparison hnotScore
  refine ⟨T, hT, hscore.le, ?_⟩
  have hbig : 100 * (1 + xi) * Real.exp ((p + 2) ^ Csc) ≤ (∏ j, N j : ℕ) :=
    hb.2.2.trans ((hsize j0).trans hprod)
  have hM : 0 < 100 * (1 + xi) := by positivity
  calc
    _ = 1 / ((∏ j, N j : ℕ) : ℝ) := (one_div _).symm
    _ ≤ 1 / (100 * (1 + xi) * Real.exp ((p + 2) ^ Csc)) :=
      one_div_le_one_div_of_le (mul_pos hM (Real.exp_pos _)) hbig
    _ = Real.exp (-((p + 2) ^ Csc)) / (100 * (1 + xi)) := by
      simp [Real.exp_neg, div_eq_mul_inv, mul_comm]
    _ ≤ _ := div_le_div_of_nonneg_right hscore.le hM.le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem density_test_score_abs_le {f T alpha xi : ℝ}
    (hf : 0 ≤ f ∧ f ≤ 1) (hT : 0 ≤ T ∧ T ≤ 1)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1) (hxi : 0 ≤ xi) :
    |(f - (1 + xi) * alpha) * T| ≤ 1 + xi := by
  have hM : 0 ≤ 1 + xi := by positivity
  have hc0 := mul_nonneg hM halpha.1
  have hc1 : (1 + xi) * alpha ≤ 1 + xi :=
    mul_le_of_le_one_right hM halpha.2
  have hdiff : |f - (1 + xi) * alpha| ≤ 1 + xi := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg hT.1]
  exact (mul_le_mul_of_nonneg_right hdiff hT.1).trans (mul_le_of_le_one_right hM hT.2)

theorem exists_absolute_crt_window_s2_oai {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Csc : ℕ, 2 ≤ Csc ∧ ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧
      ∃ Cwindow : ℕ, 2 ≤ Cwindow ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
        (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
        (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
        0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
        IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
        let hN := distinct_prime_moduli_coprime N hprime hinj
        ∃ (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow),
          PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ Csc) T ∧
          Real.log (2 + (w.lip : ℝ)) ≤ (p + 2) ^ Cwindow ∧
          Real.exp (-((p + 2) ^ Cwindow)) ≤
            𝔼 u : (j : J) → ZMod (N j),
              ((f u - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm u)) *
                (w.crtPatch N hN (k - 2) (by omega)).value (fun j => ((u j).val : ℝ)) := by
  obtain ⟨Csc, hCsc, C, hC, hstrict, xi, hxi, habsolute⟩ :=
    exists_absolute_crt_score (J := J) k hk
  obtain ⟨D, hD, hwindow⟩ := exists_polynomial_scored_crt_representative_patch
  obtain ⟨a, ha⟩ := exists_nat_ge (Real.log (1 + xi))
  obtain ⟨Cwindow, hCwindow, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (((Polynomial.X + 2) ^ Csc + Polynomial.C a + 2) ^ D)
  refine ⟨Csc, hCsc, C, hC, hstrict, Cwindow, hCwindow, xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  let hN := distinct_prime_moduli_coprime N hprime hinj
  obtain ⟨T, hT, hscore, hmod⟩ := habsolute N hprime hinj f halpha hp hlog hsize hf hmean hfree
  let F : ZMod (∏ j, N j) → ℝ :=
    fun x => (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x
  let sigma : ℝ := 𝔼 x, F x
  let q : ℝ := (p + 2) ^ Csc + a
  have hp0 : 0 ≤ p := by linarith
  have hpow0 : 0 ≤ (p + 2) ^ Csc := by positivity
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hq : 0 ≤ q := add_nonneg hpow0 ha0
  have hM : 0 < 1 + xi := by positivity
  have hMexp : 1 + xi ≤ Real.exp q := by
    apply (Real.log_le_iff_le_exp hM).mp
    exact ha.trans (by dsimp only [q]; linarith)
  have hsig : Real.exp (-q) ≤ sigma :=
    (Real.exp_le_exp.mpr (show -q ≤ -((p + 2) ^ Csc) by dsimp only [q]; linarith)).trans hscore
  have halpha1 : alpha ≤ 1 := by
    rw [← hmean]
    exact (Finset.expect_le_expect (fun u _ => (hf u).2)).trans_eq (Fintype.expect_const 1)
  have hcap (x : ZMod (∏ j, N j)) : |F x| ≤ 1 + xi :=
    density_test_score_abs_le (hf _) (hT.unit_interval x) ⟨halpha.le, halpha1⟩ hxi.le
  obtain ⟨w, hw, hws⟩ := hwindow N hN (k - 2) (by omega) F hq hM hMexp hsig
    hcap le_rfl (by simpa only [one_div] using hmod)
  have hb : (q + 2) ^ D ≤ (p + 2) ^ Cwindow := by
    simpa [Polynomial.eval₂_pow, q] using hbudget p hp0
  refine ⟨T, w, hT, hw.trans hb, ?_⟩
  have hs := (Real.exp_le_exp.mpr (neg_le_neg hb)).trans hws
  have he (u : (j : J) → ZMod (N j)) :
      F ((ZMod.prodEquivPi N hN).symm u) =
        (f u - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm u) := by
    dsimp only [F]
    rw [RingEquiv.apply_symm_apply]
  simpa only [he] using hs

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.exists_absolute_crt_window_s2_oai.{u_1} := @OAI.Erdos3.exists_absolute_crt_window_s2_oai.{u_1}
