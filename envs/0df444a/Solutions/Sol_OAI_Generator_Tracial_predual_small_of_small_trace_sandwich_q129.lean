-- Prove2me | solution 1 for OAI.Generator.Tracial.predual_small_of_small_trace_sandwich_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:54:24.234725+00:00
-- url     : https://prove2.me/submissions/a4384d0a-418e-4152-9cfa-073f508c6fec

import Mathlib
import Definitions.Def_OAIQ129G008

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/

/-! Operator order bounds are closed in the weak operator topology. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weakOperator_nonneg_isClosed :
    IsClosed {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} := by
  have hi (x : H) : Continuous (fun T : H →WOT[ℂ] H => inner ℂ (T x) x) := by
    simpa only [Function.comp_def, id_eq, inner_conj_symm] using
      (Complex.continuous_conj.comp
        (ContinuousLinearMapWOT.continuous_inner_apply continuous_id x x))
  have he : {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} =
      ⋂ x : H, {T : H →WOT[ℂ] H |
        ((inner ℂ (T x) x).re : ℂ) = inner ℂ (T x) x ∧ 0 ≤ (inner ℂ (T x) x).re} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, ContinuousLinearMap.nonneg_iff_isPositive,
      ContinuousLinearMap.isPositive_iff_complex]
    rfl
  rw [he]
  apply isClosed_iInter
  intro x
  exact (isClosed_eq (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (hi x)))
    (hi x)).inter (isClosed_le continuous_const (Complex.continuous_re.comp (hi x)))

theorem weakOperator_lowerBound_isClosed (a : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | a ≤ T.toCLM} := by
  have h := (weakOperator_nonneg_isClosed (H := H)).preimage
    (continuous_id.sub (continuous_const (y := ContinuousLinearMapWOT.ofCLM a)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext T
  change (a ≤ T.toCLM) ↔ 0 ≤ T.toCLM - a
  exact sub_nonneg.symm

theorem weakOperator_upperBound_isClosed (b : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM ≤ b} := by
  have h := (weakOperator_nonneg_isClosed (H := H)).preimage
    ((continuous_const (y := ContinuousLinearMapWOT.ofCLM b)).sub continuous_id)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext T
  change (T.toCLM ≤ b) ↔ 0 ≤ b - T.toCLM
  exact sub_nonneg.symm

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MonotoneTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129Algebra _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_add _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_smul _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_sub _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Bounded positive monotone nets have actual least upper bounds in M.
Every displayed vector-trace bound passes to the constructed bound. -/
section
open Filter
open scoped Topology
namespace Tracial

section
open UltrapowerBridge
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]

theorem exists_monotone_positive_limit (a : I → M.toStarSubalgebra)
    (hmono : Monotone (fun i => (a i).val))
    (hpos : ∀ i, 0 ≤ (a i).val) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, ‖a i‖ ≤ C) (r : ℝ) (htrace : ∀ i, (τ.trace (a i)).re ≤ r) :
    ∃ b : M.toStarSubalgebra, 0 ≤ b.val ∧ ‖b‖ ≤ C ∧
      (∀ i, (a i).val ≤ b.val) ∧
      (∀ c : M.toStarSubalgebra, (∀ i, (a i).val ≤ c.val) → b.val ≤ c.val) ∧
      (τ.trace b).re ≤ r := by
  let ω : Ultrafilter I := Ultrafilter.of atTop
  obtain ⟨T, hT, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val) C hC hbound
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M a T ht⟩
  have hw : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (a i).val) (ω : Filter I)
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
  refine ⟨b, ?_, hT, ?_, ?_, ?_⟩
  · exact weakOperator_nonneg_isClosed.mem_of_tendsto hw (Eventually.of_forall hpos)
  · intro i
    apply (weakOperator_lowerBound_isClosed (a i).val).mem_of_tendsto hw
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact hmono hj
  · intro c hc
    exact (weakOperator_upperBound_isClosed c.val).mem_of_tendsto hw (Eventually.of_forall hc)
  · exact le_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (ht τ.vector τ.vector))
      (Eventually.of_forall htrace)

end

/-! Positivity, order, and faithfulness of the actual vector trace, using
ambient operator order throughout. No identification with subtype spectral
order is needed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem ambient_trace_nonneg (a : M.toStarSubalgebra) (ha : 0 ≤ a.val) :
    0 ≤ (τ.trace a).re :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mp ha |>.re_inner_nonneg_right τ.vector

theorem ambient_trace_mono {a b : M.toStarSubalgebra} (hab : a.val ≤ b.val) :
    (τ.trace a).re ≤ (τ.trace b).re := by
  have h := ambient_trace_nonneg τ (b-a) (sub_nonneg.mpr hab)
  change 0 ≤ (inner ℂ τ.vector (b.val τ.vector - a.val τ.vector)).re at h
  simpa only [TracialRepresentation.trace, inner_sub_right, Complex.sub_re, sub_nonneg] using h

theorem ambient_eq_zero_of_trace_zero (a : M.toStarSubalgebra)
    (ha : 0 ≤ a.val) (ht : (τ.trace a).re = 0) : a = 0 := by
  let s : M.toStarSubalgebra := ⟨CFC.sqrt a.val, ambient_sqrt_mem a ha⟩
  have hs : star s * s = a := by
    apply Subtype.ext
    change star (CFC.sqrt a.val) * CFC.sqrt a.val = a.val
    rw [(CFC.sqrt_nonneg a.val).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a.val ha]
  have h := congrArg Complex.re (τ.trace_star_mul s)
  rw [hs, ht] at h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at h
  have hz : τ.norm₂ s = 0 := by nlinarith [sq_nonneg (τ.norm₂ s)]
  have sz := (τ.norm₂_eq_zero_iff s).mp hz
  simpa only [sz, star_zero, mul_zero] using hs.symm

/-- Any lower bound of a uniformly bounded positive sequence whose traces
tend to zero is nonpositive. The sequence need not itself be monotone. -/
theorem ambient_lowerBound_nonpos_of_trace_tendsto_zero
    (b : ℕ → M.toStarSubalgebra) (hpos : ∀ n, 0 ≤ (b n).val)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖b n‖ ≤ C)
    (ht : Tendsto (fun n => (τ.trace (b n)).re) atTop (𝓝 0))
    (c : M.toStarSubalgebra) (hc : ∀ n, c.val ≤ (b n).val) : c.val ≤ 0 := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T, _, hT⟩ := exists_weak_operator_ultralimit ω (fun n => (b n).val) C hC hbound
  let d : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M b T hT⟩
  have hw : Tendsto (fun n => ContinuousLinearMapWOT.ofCLM (b n).val) (ω : Filter ℕ)
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr hT
  have hd : 0 ≤ d.val := weakOperator_nonneg_isClosed.mem_of_tendsto hw
    (Eventually.of_forall hpos)
  have hz : (τ.trace d).re = 0 := tendsto_nhds_unique
    (Complex.continuous_re.tendsto _ |>.comp (hT τ.vector τ.vector))
    (ht.mono_left (Ultrafilter.of_le atTop))
  have hcd : c.val ≤ d.val := (weakOperator_lowerBound_isClosed c.val).mem_of_tendsto hw
    (Eventually.of_forall hc)
  simpa only [ambient_eq_zero_of_trace_zero τ d hd hz, ZeroMemClass.coe_zero] using hcd

end Tracial

end

/-! Absolute values in the represented algebra, with ambient order bounds
and the actual trace two-norm. -/

/-! The bounded monotone transform a ↦ 1 - (1+a)⁻¹ of positive operators.
Its bounds prepare a construction of decreasing order majorants from small
trace tails. No tail majorant or predual continuity is asserted here. -/
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveResolvent_continuousOn (a : A) (ha : 0 ≤ a) :
    ContinuousOn (fun t : ℝ => 1 - (1 + t)⁻¹) (spectrum ℝ a) := by
  apply continuousOn_const.sub
  apply (continuousOn_const.add continuousOn_id).inv₀
  intro t ht
  have := spectrum_nonneg_of_nonneg ha ht
  change 1 + t ≠ 0
  linarith

theorem positiveResolvent_eq (a : A) (ha : 0 ≤ a) :
    positiveResolvent a = 1 - Ring.inverse (1 + a) := by
  have hn (t : ℝ) (ht : t ∈ spectrum ℝ a) : 1 + t ≠ 0 := by
    have := spectrum_nonneg_of_nonneg ha ht
    positivity
  have hi : ContinuousOn (fun t : ℝ => (1 + t)⁻¹) (spectrum ℝ a) :=
    (continuousOn_const.add continuousOn_id).inv₀ hn
  rw [positiveResolvent, cfc_sub (fun _ : ℝ => 1) (fun t => (1 + t)⁻¹) a
    continuousOn_const hi,
    cfc_const_one ℝ a, cfc_inv (fun t : ℝ => 1 + t) a hn,
    cfc_const_add (1 : ℝ) (fun t : ℝ => t) a continuousOn_id ha.isSelfAdjoint,
    cfc_id' ℝ a ha.isSelfAdjoint]
  simp only [map_one]

theorem positiveResolvent_nonneg (a : A) (ha : 0 ≤ a) : 0 ≤ positiveResolvent a := by
  apply cfc_nonneg
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  have hi : (1 + t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  linarith

theorem positiveResolvent_le_one (a : A) (ha : 0 ≤ a) : positiveResolvent a ≤ 1 := by
  apply cfc_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  exact sub_le_self _ (inv_nonneg.mpr (by linarith))

theorem positiveResolvent_mono {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) :
    positiveResolvent a ≤ positiveResolvent b := by
  rw [positiveResolvent_eq a ha, positiveResolvent_eq b (ha.trans hab)]
  apply sub_le_sub_left
  exact CStarAlgebra.ringInverse_le_ringInverse (add_le_add le_rfl hab)
    (isStrictlyPositive_one.add_nonneg ha)

theorem positiveResolvent_le_self (a : A) (ha : 0 ≤ a) : positiveResolvent a ≤ a := by
  calc
    positiveResolvent a ≤ cfc (fun t : ℝ => t) a := by
      apply cfc_mono (hf := positiveResolvent_continuousOn a ha) (hg := continuousOn_id)
      intro t ht
      have ht0 := spectrum_nonneg_of_nonneg ha ht
      have hp : 0 < 1 + t := by linarith
      have hi : 1 - t ≤ (1 + t)⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ hp).mpr
        nlinarith [sq_nonneg t]
      change 1 - (1 + t)⁻¹ ≤ t
      linarith
    _ = a := cfc_id' ℝ a ha.isSelfAdjoint

theorem half_le_positiveResolvent (a : A) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 / 2 : ℝ) • a ≤ positiveResolvent a := by
  rw [← cfc_const_mul_id (1 / 2 : ℝ) a ha.isSelfAdjoint]
  apply cfc_mono (hf := by fun_prop) (hg := positiveResolvent_continuousOn a ha)
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  have ht1 : t ≤ 1 := (CFC.le_one_iff (R := ℝ) a ha.isSelfAdjoint).mp ha1 t ht
  have hp : 0 < 1 + t := by linarith
  have hi : (1 + t)⁻¹ ≤ 1 - t / 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith

theorem positiveResolvent_norm_le_one (a : A) (ha : 0 ≤ a) : ‖positiveResolvent a‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (positiveResolvent_nonneg a ha)).mpr
    (positiveResolvent_le_one a ha)

end

/-! Decreasing positive order majorants for positive contractions with
summable trace. The finite-tail resolvents and their least upper bounds are
constructed in the actual algebra. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem ambient_trace_finset_sum {ι : Type*} (s : Finset ι)
    (a : ι → M.toStarSubalgebra) :
    (τ.trace (∑ k ∈ s, a k)).re = ∑ k ∈ s, (τ.trace (a k)).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [TracialRepresentation.trace]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih]
    change (inner ℂ τ.vector ((a k).val τ.vector + (∑ i ∈ s, a i).val τ.vector)).re = _
    rw [inner_add_right, Complex.add_re]
    rfl

theorem ambient_trace_real_smul (r : ℝ) (a : M.toStarSubalgebra) :
    (τ.trace (r • a)).re = r * (τ.trace a).re := by
  change (inner ℂ τ.vector ((r : ℂ) • a.val τ.vector)).re = _
  simp only [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rfl

theorem exists_positive_trace_tail_majorants (a : ℕ → M.toStarSubalgebra)
    (hpos : ∀ n, 0 ≤ (a n).val) (hbound : ∀ n, ‖a n‖ ≤ 1)
    (hsum : Summable (fun n => (τ.trace (a n)).re)) :
    ∃ b : ℕ → M.toStarSubalgebra,
      (∀ n, 0 ≤ (b n).val) ∧ (∀ n, ‖b n‖ ≤ 2) ∧
      Antitone (fun n => (b n).val) ∧ (∀ n, (a n).val ≤ (b n).val) ∧
      (∀ n, (τ.trace (b n)).re ≤ 2 * ∑' k, (τ.trace (a (n+k))).re) ∧
      (∀ c : M.toStarSubalgebra, (∀ n, c.val ≤ (b n).val) → c.val ≤ 0) := by
  classical
  let s (n m : ℕ) : M.toStarSubalgebra := ∑ k ∈ Finset.Ico n m, a k
  have hsval (n m : ℕ) : (s n m).val = ∑ k ∈ Finset.Ico n m, (a k).val := by
    exact map_sum M.toStarSubalgebra.subtype _ _
  have hspos (n m : ℕ) : 0 ≤ (s n m).val := by
    rw [hsval]
    exact Finset.sum_nonneg (fun k _ => hpos k)
  have hsmono (n : ℕ) : Monotone (fun m => (s n m).val) := by
    intro i j hij
    change (s n i).val ≤ (s n j).val
    rw [hsval, hsval]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hij)
      (fun k _ _ => hpos k)
  have hsanti (m : ℕ) : Antitone (fun n => (s n m).val) := by
    intro i j hij
    change (s j m).val ≤ (s i m).val
    rw [hsval, hsval]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico hij le_rfl)
      (fun k _ _ => hpos k)
  let u (n m : ℕ) := algebraPositiveResolvent (s n m)
  have hup (n m : ℕ) : 0 ≤ (u n m).val := positiveResolvent_nonneg _ (hspos n m)
  have huone (n m : ℕ) : (u n m).val ≤ 1 := positiveResolvent_le_one _ (hspos n m)
  have humono (n : ℕ) : Monotone (fun m => (u n m).val) :=
    fun i j hij => positiveResolvent_mono (hspos n i) (hsmono n hij)
  have hut (n m : ℕ) : (τ.trace (u n m)).re ≤ ∑' k, (τ.trace (a (n+k))).re := by
    calc
      (τ.trace (u n m)).re ≤ (τ.trace (s n m)).re :=
        ambient_trace_mono τ (positiveResolvent_le_self _ (hspos n m))
      _ = ∑ k ∈ Finset.range (m-n), (τ.trace (a (n+k))).re := by
        rw [ambient_trace_finset_sum, Finset.sum_Ico_eq_sum_range]
      _ ≤ ∑' k, (τ.trace (a (n+k))).re :=
        Summable.sum_le_tsum _ (fun k _ => ambient_trace_nonneg τ _ (hpos _))
          (by simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hsum)
  have hc (n : ℕ) := exists_monotone_positive_limit τ (u n) (humono n) (hup n)
    1 zero_le_one (fun m => positiveResolvent_norm_le_one _ (hspos n m))
    (∑' k, (τ.trace (a (n+k))).re) (hut n)
  choose c hcp hcn hcu hcl hct using hc
  have hcanti : Antitone (fun n => (c n).val) := by
    intro i j hij
    apply hcl j
    intro m
    exact (positiveResolvent_mono (hspos j m) (hsanti m hij)).trans (hcu i m)
  let b (n : ℕ) : M.toStarSubalgebra := (2 : ℝ) • c n
  have hbp (n : ℕ) : 0 ≤ (b n).val := by
    change 0 ≤ (2 : ℝ) • (c n).val
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hcp n)
  have hbn (n : ℕ) : ‖b n‖ ≤ 2 := by
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left (hcn n) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
      (mul_one 2)
  have hbt (n : ℕ) : (τ.trace (b n)).re ≤ 2 * ∑' k, (τ.trace (a (n+k))).re := by
    rw [ambient_trace_real_smul]
    exact mul_le_mul_of_nonneg_left (hct n) (by norm_num)
  refine ⟨b, hbp, hbn, ?_, ?_, hbt, ?_⟩
  · intro i j hij
    change (2 : ℝ) • (c j).val ≤ (2 : ℝ) • (c i).val
    exact smul_le_smul_of_nonneg_left (hcanti hij) (by norm_num : (0 : ℝ) ≤ 2)
  · intro n
    change (a n).val ≤ (2 : ℝ) • (c n).val
    have ha1 : (a n).val ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpos n)).mp (hbound n)
    have hn : s n (n+1) = a n := by simp [s]
    have hv := hcu n (n+1)
    change positiveResolvent (s n (n+1)).val ≤ (c n).val at hv
    rw [hn] at hv
    have hh : (1/2 : ℝ) • (a n).val ≤ (c n).val :=
      (half_le_positiveResolvent _ (hpos n) ha1).trans hv
    have hd := smul_le_smul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul] using hd
  · apply ambient_lowerBound_nonpos_of_trace_tendsto_zero τ b hbp 2 (by norm_num) hbn
    apply squeeze_zero (fun n => ambient_trace_nonneg τ _ (hbp n)) hbt
    simpa only [Nat.add_comm, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_sum_nat_add (fun n => (τ.trace (a n)).re)) :
        Tendsto (fun n => 2 * ∑' k, (τ.trace (a (k+n))).re) atTop (𝓝 (2*0)))

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualOrder
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Operator norm geometry for the original existential Banach-predual gap.
These statements use only concrete Hilbert operators. They do not identify
any predual or prove trace-orbit separability. -/
section
open scoped ComplexConjugate
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_imaginary_shift_apply_sq (A : H →L[ℂ] H) (t : ℝ) (x : H) :
    ‖(A + ((t : ℂ)*Complex.I) • 1) x‖^2 =
      ‖A x‖^2 - 2*t*(inner ℂ (A x) x).im + t^2*‖x‖^2 := by
  change ‖A x + ((t : ℂ)*Complex.I) • x‖^2 = _
  rw [norm_add_sq (𝕜 := ℂ),inner_smul_right]
  change ‖A x‖^2 + 2*((t : ℂ)*Complex.I*inner ℂ (A x) x).re +
    ‖((t : ℂ)*Complex.I) • x‖^2 = _
  simp only [
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,mul_one,
    norm_smul,norm_mul,Complex.norm_real,Complex.norm_I,mul_pow,
    Real.norm_eq_abs,sq_abs]
  ring

variable [CompleteSpace H]

/-- Self-adjointness and a norm bound are characterized by translated norm balls. -/
theorem selfAdjoint_norm_le_iff_imaginary_shifts (A : H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) :
    (IsSelfAdjoint A ∧ ‖A‖ ≤ C) ↔
      ∀ t : ℝ, ‖A + ((t : ℂ)*Complex.I) • 1‖ ≤ Real.sqrt (C^2+t^2) := by
  constructor
  · rintro ⟨ha,hn⟩ t
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hi : (inner ℂ (A x) x).im = 0 := by
      have h := congrArg Complex.im
        ((LinearMap.isSymmetric_iff_inner_map_self_real A.toLinearMap).mp ha.isSymmetric x)
      simp only [Complex.conj_im,ContinuousLinearMap.coe_coe] at h
      linarith
    have hx := (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg x))
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mpr hx
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
    rw [norm_imaginary_shift_apply_sq,hi,mul_zero,sub_zero,mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ C^2+t^2)]
    nlinarith
  · intro h
    have hn : ‖A‖ ≤ C := by
      simpa only [Complex.ofReal_zero,zero_mul,zero_smul,add_zero,zero_pow (by decide : 2 ≠ 0),
        Real.sqrt_sq hC] using h 0
    refine ⟨?_,hn⟩
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    apply (LinearMap.isSymmetric_iff_inner_map_self_real A.toLinearMap).mpr
    intro x
    have hb (t : ℝ) : -2*t*(inner ℂ (A x) x).im ≤ C^2*‖x‖^2 := by
      have hx := ((A + ((t : ℂ)*Complex.I) • 1).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (h t) (norm_nonneg x))
      have hs := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mpr hx
      rw [norm_imaginary_shift_apply_sq,mul_pow,
        Real.sq_sqrt (by positivity : 0 ≤ C^2+t^2)] at hs
      nlinarith [sq_nonneg ‖A x‖]
    have hi : (inner ℂ (A x) x).im = 0 := by
      by_contra hi
      have ht := hb ((C^2*‖x‖^2+1)/(-2*(inner ℂ (A x) x).im))
      have he : -2*((C^2*‖x‖^2+1)/(-2*(inner ℂ (A x) x).im)) *
          (inner ℂ (A x) x).im = C^2*‖x‖^2+1 := by
        field_simp [hi]
      rw [he] at ht
      linarith
    apply Complex.ext
    · rfl
    · simp only [Complex.conj_im,ContinuousLinearMap.coe_coe,hi,neg_zero]

end

/-! Bounded self-adjoint sets are weak-star compact for the actual Banach
predual isometry. No predual uniqueness or WOT compatibility is assumed. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S) (C : ℝ) (hC : 0 ≤ C)

include hC

/-- The self-adjoint ball pulled back to the given weak-star dual is closed. -/
theorem predual_selfAdjointBall_isClosed :
    IsClosed {φ : WeakDual ℂ X |
      IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧ ‖e (WeakDual.toStrongDual φ)‖ ≤ C} := by
  have he : {φ : WeakDual ℂ X |
      IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧ ‖e (WeakDual.toStrongDual φ)‖ ≤ C} =
      ⋂ t : ℝ, WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (-e.symm (((t : ℂ)*Complex.I) • (1 : S))) (Real.sqrt (C^2+t^2)) := by
    ext φ
    simp only [Set.mem_iInter,Set.mem_preimage,Metric.mem_closedBall,dist_eq_norm,sub_neg_eq_add]
    change (IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧
      ‖(e (WeakDual.toStrongDual φ)).val‖ ≤ C) ↔ _
    rw [selfAdjoint_norm_le_iff_imaginary_shifts _ C hC]
    apply forall_congr'
    intro t
    rw [← e.norm_map (WeakDual.toStrongDual φ + e.symm (((t : ℂ)*Complex.I) • (1 : S))),
      map_add,e.apply_symm_apply]
    rfl
  rw [he]
  exact isClosed_iInter (fun t => WeakDual.isClosed_closedBall _ _)

end

/-! Positive operator balls are compact in the weak-star topology of the
given Banach predual. The isometry is not assumed weak-operator continuous. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Positivity on a bounded self-adjoint ball is one more translated norm bound. -/
theorem positive_norm_le_iff_real_shift (A : H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) :
    (A.IsPositive ∧ ‖A‖ ≤ C) ↔
      (IsSelfAdjoint A ∧ ‖A‖ ≤ C ∧ ‖A - (C : ℂ) • 1‖ ≤ C) := by
  have hc : algebraMap ℝ (H →L[ℂ] H) C = (C : ℂ) • 1 := by
    ext x
    simp
  have hsa : IsSelfAdjoint (algebraMap ℝ (H →L[ℂ] H) C) :=
    (isSelfAdjoint_iff.mpr (star_trivial C)).algebraMap _
  constructor
  · rintro ⟨hp, hn⟩
    have ha := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp
    have hupper := (CStarAlgebra.norm_le_iff_le_algebraMap A hC ha).mp hn
    have hdiff : 0 ≤ algebraMap ℝ (H →L[ℂ] H) C - A := sub_nonneg.mpr hupper
    refine ⟨IsSelfAdjoint.of_nonneg ha, hn, ?_⟩
    rw [← hc, norm_sub_rev]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hC hdiff).mpr
      (sub_le_self _ ha)
  · rintro ⟨ha, hn, hd⟩
    rw [← hc] at hd
    have hlo := (ha.sub hsa).neg_algebraMap_norm_le_self
    have hm := neg_le_neg (algebraMap_mono (H →L[ℂ] H) hd)
    have h : -(algebraMap ℝ (H →L[ℂ] H) C) ≤
        A - algebraMap ℝ (H →L[ℂ] H) C := hm.trans hlo
    refine ⟨(ContinuousLinearMap.nonneg_iff_isPositive _).mp ?_, hn⟩
    simpa only [neg_add_cancel, sub_add_cancel, add_neg_cancel,
      ← add_sub_assoc, add_sub_cancel_left] using
      add_le_add_right h (algebraMap ℝ (H →L[ℂ] H) C)

variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S) (C : ℝ) (hC : 0 ≤ C)

include hC

/-- Positive balls are weak-star closed for the actual given predual. -/
theorem predual_positiveBall_isClosed :
    IsClosed {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ C} := by
  have he : {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ C} =
      {φ : WeakDual ℂ X |
        IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧
        ‖e (WeakDual.toStrongDual φ)‖ ≤ C} ∩
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (e.symm ((C : ℂ) • (1 : S))) C) := by
    ext φ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Metric.mem_closedBall, dist_eq_norm]
    rw [← e.norm_map (WeakDual.toStrongDual φ - e.symm ((C : ℂ) • (1 : S))),
      map_sub, e.apply_symm_apply]
    change (_ ∧ ‖(e (WeakDual.toStrongDual φ)).val‖ ≤ C) ↔ _
    rw [positive_norm_le_iff_real_shift _ C hC]
    exact and_assoc.symm
  rw [he]
  exact (predual_selfAdjointBall_isClosed S e C hC).inter
    (WeakDual.isClosed_closedBall _ _)

end

/-! Closed and compact order intervals for the given Banach predual.
All inequalities are the concrete operator Loewner order. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- A positive order interval is the intersection of two translated positive balls. -/
theorem predual_zeroInterval_eq (b : S) :
    {φ : WeakDual ℂ X | 0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} =
    {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ ‖b‖} ∩
    (fun φ : WeakDual ℂ X => StrongDual.toWeakDual (e.symm b) - φ) ⁻¹'
    {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ ‖b‖} := by
  ext φ
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, map_sub,
    StrongDual.toStrongDual_toWeakDual, e.apply_symm_apply]
  change (0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val) ↔
    ((e (WeakDual.toStrongDual φ)).val.IsPositive ∧
      ‖(e (WeakDual.toStrongDual φ)).val‖ ≤ ‖b.val‖) ∧
    (b.val - (e (WeakDual.toStrongDual φ)).val).IsPositive ∧
      ‖b.val - (e (WeakDual.toStrongDual φ)).val‖ ≤ ‖b.val‖
  simp only [← ContinuousLinearMap.nonneg_iff_isPositive]
  constructor
  · rintro ⟨ha, hab⟩
    have hd := sub_nonneg.mpr hab
    exact ⟨⟨ha, CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha⟩,
      hd, CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self _ ha) hd⟩
  · rintro ⟨⟨ha, _⟩, hd, _⟩
    exact ⟨ha, sub_nonneg.mp hd⟩

theorem predual_zeroInterval_isClosed (b : S) :
    IsClosed {φ : WeakDual ℂ X | 0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} := by
  rw [predual_zeroInterval_eq S e b]
  exact (predual_positiveBall_isClosed S e ‖b‖ (norm_nonneg b)).inter
    ((predual_positiveBall_isClosed S e ‖b‖ (norm_nonneg b)).preimage
      (continuous_const.sub continuous_id))

/-- Translate an arbitrary interval to one with lower endpoint zero. -/
theorem predual_orderInterval_eq (a b : S) :
    {φ : WeakDual ℂ X | a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} =
    (fun φ : WeakDual ℂ X => φ - StrongDual.toWeakDual (e.symm a)) ⁻¹'
    {φ : WeakDual ℂ X | 0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ (b-a).val} := by
  ext φ
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_sub,
    StrongDual.toStrongDual_toWeakDual, e.apply_symm_apply]
  change (a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
    (e (WeakDual.toStrongDual φ)).val ≤ b.val) ↔
    (0 ≤ (e (WeakDual.toStrongDual φ)).val - a.val ∧
    (e (WeakDual.toStrongDual φ)).val - a.val ≤ b.val - a.val)
  rw [sub_nonneg, sub_le_sub_iff_right]

theorem predual_orderInterval_isClosed (a b : S) :
    IsClosed {φ : WeakDual ℂ X | a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} := by
  rw [predual_orderInterval_eq S e a b]
  exact (predual_zeroInterval_isClosed S e (b-a)).preimage
    (continuous_id.sub continuous_const)

theorem predual_orderInterval_isCompact (a b : S) :
    IsCompact {φ : WeakDual ℂ X | a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X)
    (‖b-a‖+‖a‖)).of_isClosed_subset (predual_orderInterval_isClosed S e a b)
  intro φ hφ
  change dist (WeakDual.toStrongDual φ) 0 ≤ ‖b-a‖+‖a‖
  rw [dist_zero_right, ← e.norm_map]
  have hd : ‖(e (WeakDual.toStrongDual φ)).val-a.val‖ ≤ ‖b.val-a.val‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_sub_right hφ.2 a.val)
      (sub_nonneg.mpr hφ.1)
  calc
    ‖e (WeakDual.toStrongDual φ)‖ =
        ‖((e (WeakDual.toStrongDual φ)).val-a.val)+a.val‖ := by rw [sub_add_cancel]; rfl
    _ ≤ ‖(e (WeakDual.toStrongDual φ)).val-a.val‖+‖a.val‖ := norm_add_le _ _
    _ ≤ ‖b-a‖+‖a‖ := add_le_add hd le_rfl

end

/-! Monotone order limits in the algebra converge for the actual given
Banach predual. Greatest/least bounds are tested only against members of S,
not against all ambient operators. -/

/-! The actual given predual embeds isometrically into the norm dual of S.
Conjugation accounts for the conjugate-linear predual isometry. These
functionals preserve monotone order limits. No canonical-predual membership
or weak-operator continuity is assumed. -/

/-! An arbitrary net squeezed into shrinking operator order intervals
converges in the topology of the given Banach predual. The net itself need
not be monotone. No normal-functional decomposition is used. -/
open Filter
open scoped Topology
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)
variable [Preorder I] [Nonempty I]

theorem predual_order_squeeze_tendsto_zero (a b : I → S)
    (hanti : Antitone (fun i => (b i).val))
    (hgreatest : ∀ c : S, (∀ i, c.val ≤ (b i).val) → c.val ≤ 0)
    (hlower : ∀ i, -(b i).val ≤ (a i).val)
    (hupper : ∀ i, (a i).val ≤ (b i).val) :
    Tendsto (fun i => StrongDual.toWeakDual (e.symm (a i))) atTop (𝓝 0) := by
  let u : I → WeakDual ℂ X := fun i => StrongDual.toWeakDual (e.symm (a i))
  have hu (i : I) : ∀ᶠ j in atTop,
      u j ∈ {φ : WeakDual ℂ X | -(b i).val ≤ (e (WeakDual.toStrongDual φ)).val ∧
        (e (WeakDual.toStrongDual φ)).val ≤ (b i).val} := by
    filter_upwards [eventually_ge_atTop i] with j hj
    simpa only [u, Set.mem_ofPred_eq, StrongDual.toStrongDual_toWeakDual,
      e.apply_symm_apply] using
      And.intro ((neg_le_neg (hanti hj)).trans (hlower j)) ((hupper j).trans (hanti hj))
  inhabit I
  apply (predual_orderInterval_isCompact S e (-b default) (b default)).tendsto_nhds_of_unique_mapClusterPt
    (hu default)
  intro φ _ hc
  have hb (i : I) := (predual_orderInterval_isClosed S e (-b i) (b i)).mem_of_mapClusterPt
    hc (hu i)
  have hn : (e (WeakDual.toStrongDual φ)).val ≤ 0 :=
    hgreatest _ (fun i => (hb i).2)
  have hp : 0 ≤ (e (WeakDual.toStrongDual φ)).val := by
    have h := hgreatest (-e (WeakDual.toStrongDual φ)) (fun i => by
      change -(e (WeakDual.toStrongDual φ)).val ≤ (b i).val
      have hi : -(b i).val ≤ (e (WeakDual.toStrongDual φ)).val := (hb i).1
      simpa only [neg_neg] using neg_le_neg hi)
    exact neg_nonpos.mp h
  apply WeakDual.toStrongDual.injective
  apply e.injective
  apply Subtype.ext
  simpa using le_antisymm hn hp

theorem predualFunctional_order_squeeze_tendsto_zero (x : X) (a b : I → S)
    (hanti : Antitone (fun i => (b i).val))
    (hgreatest : ∀ c : S, (∀ i, c.val ≤ (b i).val) → c.val ≤ 0)
    (hlower : ∀ i, -(b i).val ≤ (a i).val)
    (hupper : ∀ i, (a i).val ≤ (b i).val) :
    Tendsto (fun i => predualFunctional S e x (a i)) atTop (𝓝 0) := by
  have h := (Complex.continuous_conj.tendsto _).comp
    ((WeakDual.eval_continuous x).tendsto _ |>.comp
      (predual_order_squeeze_tendsto_zero S e a b hanti hgreatest hlower hupper))
  have hz : (0 : WeakDual ℂ X) x = 0 := rfl
  simpa [Function.comp_def, predualFunctional, hz] using h

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualContinuity
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
attribute [-simp] _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Given-predual evaluations are uniformly small on operator order
intervals bounded by positive contractions with small trace. This is derived
from the constructed tail majorants, without assuming predual normality. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

theorem predual_summable_trace_sandwich (x : X) (a p : ℕ → M.toStarSubalgebra)
    (hp : ∀ n, 0 ≤ (p n).val) (hpn : ∀ n, ‖p n‖ ≤ 1)
    (hpt : Summable (fun n => (τ.trace (p n)).re))
    (hal : ∀ n, -(p n).val ≤ (a n).val) (hau : ∀ n, (a n).val ≤ (p n).val) :
    Tendsto (fun n => predualFunctional M.toStarSubalgebra e x (a n)) atTop (𝓝 0) := by
  obtain ⟨b, _, _, hbanti, hpb, _, hbg⟩ := exists_positive_trace_tail_majorants τ p hp hpn hpt
  exact predualFunctional_order_squeeze_tendsto_zero M.toStarSubalgebra e x a b hbanti hbg
    (fun n => (neg_le_neg (hpb n)).trans (hal n)) (fun n => (hau n).trans (hpb n))

theorem predual_small_of_small_trace_sandwich_q129_oai (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a p : M.toStarSubalgebra,
      0 ≤ p.val → ‖p‖ ≤ 1 → (τ.trace p).re < δ →
      -p.val ≤ a.val → a.val ≤ p.val →
      ‖predualFunctional M.toStarSubalgebra e x a‖ < ε := by
  by_contra h
  push Not at h
  have hseq (n : ℕ) := h ((1/2 : ℝ)^n) (pow_pos (by norm_num) n)
  choose a p hp hpn hpt hal hau hbad using hseq
  have hsum : Summable (fun n => (τ.trace (p n)).re) :=
    Summable.of_nonneg_of_le (fun n => ambient_trace_nonneg τ _ (hp n))
      (fun n => (hpt n).le) (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))
  have ht := predual_summable_trace_sandwich τ e x a p hp hpn hsum hal hau
  have he := Metric.tendsto_nhds.mp ht ε hε
  obtain ⟨n, hn⟩ := he.exists
  exact (not_lt_of_ge (hbad n)) (by simpa only [dist_zero_right] using hn)

/-! Given-predual evaluation is uniformly trace-two-norm continuous on every
operator-norm bounded ball. No WOT continuity premise is used. -/

end

/-! Every evaluation from the given Banach predual belongs to the constructed
cyclic predual. In particular, the original separable-predual hypothesis
supplies trace-orbit separability without an additional continuity premise. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Generator.Tracial.predual_small_of_small_trace_sandwich_q129_oai.{u_1, u_2} := @OAI.Generator.Tracial.predual_small_of_small_trace_sandwich_q129_oai.{u_1, u_2}
