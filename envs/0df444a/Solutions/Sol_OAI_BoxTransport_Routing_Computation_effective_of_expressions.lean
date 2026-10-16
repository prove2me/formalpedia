-- Prove2me | solution 1 for OAI.BoxTransport.Routing.Computation.effective_of_expressions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:51:59.380733+00:00
-- url     : https://prove2.me/submissions/7316aaf3-a8db-4845-8250-9fd33dbab95f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Expressions.lean:L733-L773
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.Computation.effective_of_expressions. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_evalE_error
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_value_bound

-- ---- from OAI.Analysis.BoxTransport.Computation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Computable rational arithmetic and exponential/flat-function approximation. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace BoxTransport.Routing.Computation

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem Qval_bound (q : QCode) : |Qval q| ≤ qBound q := by
  rw [Qval, abs_div, abs_of_pos (by positivity : (0 : ℚ) < q.2.2 + 1)]
  have h : |(q.1 : ℚ) - q.2.1| ≤ (q.1 : ℚ) + q.2.1 := by
    simpa only [Nat.abs_cast] using abs_sub (q.1 : ℚ) q.2.1
  apply le_trans (div_le_self (abs_nonneg _) (by norm_cast; omega))
  simpa [qBound] using h

end BoxTransport.Routing.Computation

end

end OAI

-- ---- from OAI.Analysis.BoxTransport.Expressions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Smooth expression calculus and effective mixed derivatives. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

theorem coord_le_norm (j : Axis) (p : SpaceTime) :
    |value (varE j) p| ≤ ‖p‖ := by
  cases j with
  | none => exact norm_fst_le p
  | some j =>
    simpa using (norm_le_pi_norm p.2 j).trans (norm_snd_le p)

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

attribute [fun_prop] Primrec Computable
attribute [fun_prop] Primrec.const Primrec.id Primrec.fst Primrec.snd Primrec.comp Primrec.pair Primrec.succ Primrec.encode Primrec.ofNat
attribute [fun_prop] Computable.const Computable.id Computable.fst Computable.snd Computable.comp Computable.pair

attribute [fun_prop] Code.primrec_rfind' primrec_qNat primrec_qBound primrec_qInv primrec_qAbs primrec_qNeg primrec_factorial

attribute [fun_prop] Primrec.to_comp computable_qFlat

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

theorem norm_code_le (q : RationalPointCode) : ‖codeSpaceTime q‖ ≤ pointBound q := by
  have h0 : |(Qval q.1 : ℝ)| ≤ (qBound q.1 : ℝ) := by exact_mod_cast Qval_bound q.1
  have h1 : |(Qval q.2.1 : ℝ)| ≤ (qBound q.2.1 : ℝ) := by exact_mod_cast Qval_bound q.2.1
  have h2 : |(Qval q.2.2.1 : ℝ)| ≤ (qBound q.2.2.1 : ℝ) := by exact_mod_cast Qval_bound q.2.2.1
  have h3 : |(Qval q.2.2.2 : ℝ)| ≤ (qBound q.2.2.2 : ℝ) := by exact_mod_cast Qval_bound q.2.2.2
  rw [Prod.norm_def, max_le_iff]
  constructor
  · change |(Qval q.1 : ℝ)| ≤ _
    unfold pointBound; push_cast; have := Nat.cast_nonneg (α := ℝ) (qBound q.2.1 + qBound q.2.2.1 + qBound q.2.2.2)
    push_cast at this; linarith
  · apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2
    intro j
    fin_cases j <;> change |(Qval _ : ℝ)| ≤ _
    all_goals unfold pointBound; push_cast
    all_goals linarith [Nat.cast_nonneg (α := ℝ) (qBound q.1), Nat.cast_nonneg (α := ℝ) (qBound q.2.1),
      Nat.cast_nonneg (α := ℝ) (qBound q.2.2.1), Nat.cast_nonneg (α := ℝ) (qBound q.2.2.2)]

theorem amplification_precision (A N : ℕ) :
    (A : ℝ) * (((((N + 1) * (A + 1) : ℕ) : ℝ) + 1)⁻¹) ≤ ((N : ℝ) + 1)⁻¹ := by
  push_cast
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have hn : (0 : ℝ) < N + 1 := by positivity
  apply (mul_le_mul_iff_right₀ hn).mp
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem evalPrecise_error {e : Expr} (he : Valid e) (q : RationalPointCode) (N : ℕ) :
    |value e (codeSpaceTime q) - (Qval (evalPrecise e q N) : ℝ)| ≤ ((N : ℝ) + 1)⁻¹ :=
  (evalE_error he q _ _ (norm_code_le q)).trans (amplification_precision _ N)

theorem valid_mixedE {e : Expr} (he : Valid e) (ds : List Axis) : Valid (mixedE ds e) := by
  induction ds with
  | nil => exact he
  | cons j ds ih => exact valid_diff ih j

theorem smooth_mixedDerivative {U : Field} (hU : ContDiff ℝ ∞ U) (ds : List Axis) :
    ContDiff ℝ ∞ (mixedDerivative ds U) := by
  induction ds with
  | nil => exact hU
  | cons j ds ih => exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem mixedDerivative_component {U : Field} (hU : ContDiff ℝ ∞ U)
    {es : Fin 3 → Expr} (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j)
    (ds : List Axis) (p : SpaceTime) (j : Fin 3) :
    value (mixedE ds (es j)) p = mixedDerivative ds U p j := by
  induction ds generalizing p with
  | nil => exact hval p j
  | cons d ds ih =>
    rw [mixedE_cons, value_diff (valid_mixedE (he j) ds)]
    have hv : value (mixedE ds (es j)) = fun p => mixedDerivative ds U p j := by
      funext p
      exact ih p
    rw [hv, fderiv_apply ((smooth_mixedDerivative hU ds).differentiable (by simp) p)]
    rfl

theorem tsupport_mixedDerivative_subset (U : Field) (ds : List Axis) :
    tsupport (mixedDerivative ds U) ⊆ tsupport U := by
  induction ds with
  | nil => exact Set.Subset.rfl
  | cons j ds ih => exact (tsupport_fderiv_apply_subset ℝ (coordinateDirection j)).trans ih

theorem exists_supportRadius {U : Field} (hU : HasCompactSupport U) :
    ∃ R : ℕ, ∀ p ∈ tsupport U, ‖p‖ ≤ R := by
  obtain ⟨r, hr⟩ := hU.isCompact.isBounded.subset_closedBall (0 : SpaceTime)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  refine ⟨R, fun p hp => ?_⟩
  have hp' : ‖p‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hr hp
  exact hp'.trans hR

theorem boundE_le_familyBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) (j : Fin 3) :
    boundE R (mixedE ds (es j)) ≤ familyBound R es ds := by
  fin_cases j <;> simp only [familyBound, Fin.reduceFinMk] <;> omega

theorem uniform_mixed_bound {U : Field} (hU : ContDiff ℝ ∞ U)
    {es : Fin 3 → Expr} (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j)
    (R : ℕ) (hR : ∀ p ∈ tsupport U, ‖p‖ ≤ R) (ds : List Axis) (p : SpaceTime) (j : Fin 3) :
    |mixedDerivative ds U p j| ≤ familyBound R es ds := by
  by_cases hp : p ∈ tsupport U
  · rw [← mixedDerivative_component hU he hval]
    exact (value_bound (valid_mixedE (he j) ds) R (hR p hp)).trans
      (Nat.cast_le.mpr (boundE_le_familyBound R es ds j))
  · have hx : mixedDerivative ds U p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_mixedDerivative_subset U ds h))
    rw [hx]; simp only [Pi.zero_apply, abs_zero]; positivity

theorem spacetime_decomposition (p : SpaceTime) :
    p = ∑ j : Axis, value (varE j) p • coordinateDirection j := by
  simp only [Fintype.sum_option, Fin.sum_univ_three, value_varE]
  apply Prod.ext
  · simp [coordinateDirection]
  · funext j
    fin_cases j <;> simp [coordinateDirection, coordinateVector]

theorem opnorm_from_coordinates (L : SpaceTime →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hL : ∀ j : Axis, |L (coordinateDirection j)| ≤ M) : ‖L‖ ≤ 4 * M := by
  apply L.opNorm_le_bound (by positivity)
  intro p
  calc
    ‖L p‖ = ‖∑ j : Axis, value (varE j) p • L (coordinateDirection j)‖ := by
      conv_lhs => rw [spacetime_decomposition p]
      simp only [map_sum, map_smul]
    _ ≤ ∑ j : Axis, ‖value (varE j) p • L (coordinateDirection j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Axis, ‖p‖ * M := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (coord_le_norm j p) (hL j) (abs_nonneg _) (norm_nonneg _)
    _ = (4 * M) * ‖p‖ := by simp [Fintype.card_option]; ring

theorem familyBound_le_gradientBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) (d : Axis) :
    familyBound R es (d :: ds) ≤ gradientBound R es ds := by
  cases d with
  | none => unfold gradientBound; omega
  | some j => fin_cases j <;> simp only [gradientBound, Fin.reduceFinMk] <;> omega

theorem mixed_component_lipschitz {U : Field} (hU : ContDiff ℝ ∞ U)
    {es : Fin 3 → Expr} (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j)
    (R : ℕ) (hR : ∀ p ∈ tsupport U, ‖p‖ ≤ R) (ds : List Axis) (j : Fin 3) :
    LipschitzWith (4 * gradientBound R es ds) (fun p => mixedDerivative ds U p j) := by
  have hs := smooth_mixedDerivative hU ds
  apply lipschitzWith_of_nnnorm_fderiv_le ((contDiff_pi.mp hs j).differentiable (by simp))
  intro p
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
  apply opnorm_from_coordinates _ (Nat.cast_nonneg _)
  intro d
  rw [fderiv_apply (hs.differentiable (by simp) p)]
  change |mixedDerivative (d :: ds) U p j| ≤ _
  exact (uniform_mixed_bound hU he hval R hR (d :: ds) p j).trans
    (Nat.cast_le.mpr (familyBound_le_gradientBound R es ds d))

theorem effective_of_expressions {U : Field} (hU : ContDiff ℝ ∞ U) (hc : HasCompactSupport U)
    (es : Fin 3 → Expr) (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j) :
    Effective U := by
  obtain ⟨R, hR⟩ := exists_supportRadius hc
  let ev : EvaluationRequest → RationalCode := fun r =>
    evalPrecise (mixedE r.1 (es r.2.2.2)) r.2.1 (2 * r.2.2.1 + 1)
  let md : List Axis × ℕ → ℕ := fun r =>
    ((2 * r.2 + 1) + 1) * (4 * gradientBound R es r.1 + 1)
  have hes : Primrec es := Primrec.dom_finite _
  have hev : Computable ev := by
    unfold ev
    have hs : Primrec (fun r : EvaluationRequest => es r.2.2.2) :=
      hes.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hm : Primrec (fun r : EvaluationRequest => mixedE r.1 (es r.2.2.2)) :=
      primrec_mixedE.comp (Primrec.fst.pair hs)
    have hp : Primrec (fun r : EvaluationRequest => 2 * r.2.2.1 + 1) := by fun_prop
    have hq : Primrec (fun r : EvaluationRequest => r.2.1) := Primrec.fst.comp Primrec.snd
    have hreq : Computable (fun r : EvaluationRequest => (mixedE r.1 (es r.2.2.2), r.2.1, 2 * r.2.2.1 + 1)) :=
      (hm.pair (hq.pair hp)).to_comp
    have h := computable_evalPrecise.comp hreq
    exact h
  have hmd : Computable md := by unfold md; fun_prop
  refine ⟨ev, md, familyBound R es, hev, hmd, (primrec_familyBound R es).to_comp, ?_, ?_⟩
  · intro ds q N p hp j
    have hl := (mixed_component_lipschitz hU he hval R hR ds j).dist_le_mul p (codeSpaceTime q)
    simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast] at hl
    have heval := evalPrecise_error (valid_mixedE (he j) ds) q (2 * N + 1)
    rw [mixedDerivative_component hU he hval ds (codeSpaceTime q) j] at heval
    change |mixedDerivative ds U p j - (Qval (evalPrecise (mixedE ds (es j)) q (2 * N + 1)) : ℝ)| ≤ _
    calc
      _ ≤ |mixedDerivative ds U p j - mixedDerivative ds U (codeSpaceTime q) j| +
          |mixedDerivative ds U (codeSpaceTime q) j - (Qval (evalPrecise (mixedE ds (es j)) q (2 * N + 1)) : ℝ)| := abs_sub_le _ _ _
      _ ≤ (4 * (gradientBound R es ds : ℝ)) * ((md (ds, N) : ℝ) + 1)⁻¹ +
          (((2 * N + 1 : ℕ) : ℝ) + 1)⁻¹ := by
        apply add_le_add _ heval
        exact hl.trans (mul_le_mul_of_nonneg_left hp (by positivity))
      _ ≤ (((2 * N + 1 : ℕ) : ℝ) + 1)⁻¹ + (((2 * N + 1 : ℕ) : ℝ) + 1)⁻¹ := by
        apply add_le_add _ le_rfl
        simpa only [md, Nat.cast_mul, Nat.cast_ofNat] using amplification_precision (4 * gradientBound R es ds) (2 * N + 1)
      _ = ((N : ℝ) + 1)⁻¹ := by push_cast; field_simp; ring
  · exact uniform_mixed_bound hU he hval R hR

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

attribute [fun_prop] Representable

namespace Representable

end Representable

end BoxTransport.Routing.Computation

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing OAI.BoxTransport.Routing.Computation
open scoped Topology
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.Computation.effective_of_expressions := @_root_.OAI.BoxTransport.Routing.Computation.effective_of_expressions
