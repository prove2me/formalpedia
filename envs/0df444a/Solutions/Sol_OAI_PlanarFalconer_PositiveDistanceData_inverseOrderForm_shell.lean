-- Prove2me | solution 1 for OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:03:25.356015+00:00
-- url     : https://prove2.me/submissions/cf43bf71-7b44-4c9c-b0aa-6cedfc6efac5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskPeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem thickening_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (r x : ℝ) :
    x+T ∈ thickening r G ↔ x ∈ thickening r G := by
  constructor
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    refine mem_thickening_iff.mpr ⟨z-T,?_,?_⟩
    · exact (hG (z-T)).mp (by simpa using hz)
    · simpa only [Real.dist_eq] using (show |x-(z-T)| < r by
        convert hd using 1; simp only [Real.dist_eq]; congr 1; ring)
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    exact mem_thickening_iff.mpr ⟨z+T,(hG z).mpr hz,by simpa using hd⟩

theorem thickenedIndicator_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) :
    Function.Periodic (thickenedIndicator G η) T := by
  intro x
  classical
  simp only [thickenedIndicator,Set.indicator_apply,thickening_periodic hG]

theorem smoothAngleMask_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) (hη : 0 < η) :
    Function.Periodic (smoothAngleMask G η hη) T := by
  intro x
  unfold smoothAngleMask
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp := thickenedIndicator_periodic hG η (x-t)
  rw [show x+T-t = (x-t)+T by ring,hp]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleBumpScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function
open scoped ContDiff Topology

theorem angleBump_scale (η : ℝ) (hη : 0 < η) (x : ℝ) :
    angleBump η hη x = angleBump 1 zero_lt_one (η⁻¹*x) := by
  rw [ContDiffBump.apply,ContDiffBump.apply]
  simp only [angleBump,smul_eq_mul,sub_zero]
  congr 1 <;> field_simp

theorem angleBump_integral_scale (η : ℝ) (hη : 0 < η) :
    (∫ x : ℝ, angleBump η hη x) = η*(∫ x : ℝ, angleBump 1 zero_lt_one x) := by
  simp_rw [angleBump_scale η hη]
  rw [Measure.integral_comp_mul_left]
  simp [abs_of_pos hη,smul_eq_mul]

theorem angleBump_normed_scale (η : ℝ) (hη : 0 < η) (x : ℝ) :
    (angleBump η hη).normed volume x =
      η⁻¹*(angleBump 1 zero_lt_one).normed volume (η⁻¹*x) := by
  rw [ContDiffBump.normed_def,angleBump_scale,angleBump_integral_scale,ContDiffBump.normed_def]
  ring

theorem angleBump_normed_iteratedDeriv (η : ℝ) (hη : 0 < η) (j : ℕ) (x : ℝ) :
    iteratedDeriv j ((angleBump η hη).normed volume) x =
      η⁻¹*(η⁻¹)^j*iteratedDeriv j ((angleBump 1 zero_lt_one).normed volume) (η⁻¹*x) := by
  have he : (angleBump η hη).normed volume = fun x =>
      η⁻¹*(angleBump 1 zero_lt_one).normed volume (η⁻¹*x) := funext (angleBump_normed_scale η hη)
  rw [he,iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (angleBump 1 zero_lt_one).contDiff_normed]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem compactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem iteratedDeriv_convolution_left {f g : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) (hg : LocallyIntegrable g volume)
    (j : ℕ) :
    iteratedDeriv j (f ⋆[lsmul ℝ ℝ,volume] g) =
      iteratedDeriv j f ⋆[lsmul ℝ ℝ,volume] g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]
    have hd : ContDiff ℝ 1 (iteratedDeriv j f) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp
        (hf.of_le (by exact_mod_cast (le_top : (j+1:ℕ∞) ≤ ⊤)) : ContDiff ℝ (j+1:ℕ) f)).2
    funext x
    simpa only [iteratedDeriv_succ] using
      ((compactSupport_iteratedDeriv hfc j).hasDerivAt_convolution_left
        (lsmul ℝ ℝ) hd hg x).deriv

theorem angleDerivativeConstant_nonneg (j : ℕ) : 0 ≤ angleDerivativeConstant j :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem angleBump_derivative_L1 (η : ℝ) (hη : 0 < η) (j : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv j ((angleBump η hη).normed volume) x‖) =
      (η⁻¹)^j*angleDerivativeConstant j := by
  simp_rw [angleBump_normed_iteratedDeriv η hη j,norm_mul,Real.norm_eq_abs,abs_pow,
    abs_inv,abs_of_pos hη]
  rw [integral_const_mul,Measure.integral_comp_inv_mul_left
    (fun y : ℝ => |iteratedDeriv j ((angleBump 1 zero_lt_one).normed volume) y|) η]
  simp only [abs_of_pos hη,smul_eq_mul,angleDerivativeConstant,Real.norm_eq_abs]
  field_simp

theorem smoothAngleMask_derivative_bound (G : Set ℝ) (η : ℝ) (hη : 0 < η) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (smoothAngleMask G η hη) x‖ ≤
      (η⁻¹)^j*angleDerivativeConstant j := by
  rw [smoothAngleMask,iteratedDeriv_convolution_left
    (angleBump η hη).hasCompactSupport_normed (angleBump η hη).contDiff_normed
    (thickenedIndicator_locallyIntegrable G η),← angleBump_derivative_L1 η hη j]
  apply norm_integral_le_of_norm_le
  · exact (ContDiff.continuous_iteratedDeriv' j (angleBump η hη).contDiff_normed).integrable_of_hasCompactSupport
      (compactSupport_iteratedDeriv (angleBump η hη).hasCompactSupport_normed j) |>.norm
  · filter_upwards [] with t
    simp only [lsmul_apply,smul_eq_mul,norm_mul]
    have hb := thickenedIndicator_bounds G η (x-t)
    simp only [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)).trans_eq (mul_one _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngleMasks
attribute [-instance] _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_derivatives (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (sourceTestMask G d hd) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(d⁻¹)^j := by
  apply (smoothAngleMask_derivative_bound _ _ _ _ _).trans_eq
  rw [inv_div,div_eq_mul_inv,mul_pow]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

namespace AngularDifferentialExpr

theorem sum_order_le (ps : List AngularDifferentialExpr) (n : ℕ)
    (h : ∀ p ∈ ps, p.order ≤ n) : (sum ps).order ≤ n := by
  induction ps with
  | nil => exact Nat.zero_le n
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SymbolProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

 theorem iteratedDeriv_product_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) (c : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (J : ℕ) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ n ≤ J, ∀ x, ‖iteratedDeriv n (f i) x‖ ≤ c i * d^n) :
    ∀ j ≤ J, ∀ x, ‖iteratedDeriv j (fun x => ∏ i ∈ S, f i x) x‖ ≤
      (∏ i ∈ S, c i) * ((S.card:ℝ)*d)^j := by
  induction S using Finset.induction_on with
  | empty =>
    intro j hj x
    cases j with
    | zero => simp
    | succ j => simp [iteratedDeriv_const]
  | @insert a S ha ih =>
    have hcS : ∀ i ∈ S, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hfS : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbS := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih := ih hcS hfS hbS
    intro j hj x
    have hfa : ContDiffAt ℝ j (f a) x :=
      ((hf a (Finset.mem_insert_self _ _)).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    have hfp : ContDiffAt ℝ j (fun x => ∏ i ∈ S, f i x) x :=
      ((contDiff_prod fun i hi => hfS i hi).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    rw [iteratedDeriv_fun_mul hfa hfp]
    calc
      _ ≤ ∑ k ∈ Finset.range (j+1),
          (j.choose k:ℝ) * (c a*d^k) * ((∏ i ∈ S, c i)*((S.card:ℝ)*d)^(j-k)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp only [norm_mul, Real.norm_natCast]
        have hca := hc a (Finset.mem_insert_self _ _)
        gcongr
        · exact hb a (Finset.mem_insert_self _ _) k (hk.trans hj) x
        · exact ih (j-k) ((Nat.sub_le _ _).trans hj) x
      _ = (c a * ∏ i ∈ S, c i) * (d+(S.card:ℝ)*d)^j := by
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by congr 2; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_periodic (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Function.Periodic (sourceTestMask G d hd) (2*Real.pi) := by
  apply smoothAngleMask_periodic
  intro θ
  have he : sourceUnitDirection (θ+2*Real.pi) = sourceUnitDirection θ := by
    apply Subtype.ext
    simp only [sourceUnitDirection,sourceDirection,Real.cos_add_two_pi,Real.sin_add_two_pi]
  simp only [mem_preimage,he]

theorem circleTestMask_comp (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    circleTestMask G d hd (sourceUnitDirection θ) = sourceTestMask G d hd θ := by
  unfold circleTestMask
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := (sourceTestMask_periodic G d hd).int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

theorem circleTestMask_angular_contDiff (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (fun θ => circleTestMask G d hd (sourceUnitDirection θ)) := by
  simpa only [circleTestMask_comp] using sourceTestMask_contDiff G d hd

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialAnchorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem spatialAnchorMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection θ)) := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx] using circleTestMask_angular_contDiff (G P) d hd
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx]
    exact contDiff_const

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

theorem policy_move_length (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    let p := policyDepth A N q a t
    let l := min (p-a) (t-p)
    q ≤ l ∧ a ≤ p-l ∧ p+l ≤ t := by
  have hh := policyDepth_interior A hq hne
  dsimp only
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) :
    0 < descriptorLength d ∧ b ≤ descriptorAnchor d-descriptorLength d ∧
      descriptorAnchor d+descriptorLength d ≤ u := by
  have hne := policyBlocks_nonempty hq huN hwide
  have hp := policyDepth_interior A hq hne
  have hl := policy_move_length A hq hne
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
    have hg := Finset.mem_Ico.mp hg
    dsimp only [descriptorLength,descriptorAnchor] at *
    omega
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d
      dsimp only [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMaskSymmetry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem spatialAnchorMask_derivative_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection φ)) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(d⁻¹)^j := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx,circleTestMask_comp] using
      sourceTestMask_derivatives (G P) d hd j θ
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx,iteratedDeriv_fun_const_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (angleDerivativeConstant_nonneg j)) (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_NormalizedSymbolFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem symbolDerivativeConstant_one_le (B : ℕ) : 1 ≤ symbolDerivativeConstant B := by
  have : 0 ≤ ∑ n ∈ Finset.range (B+1), (100:ℝ)^n * angleDerivativeConstant n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (angleDerivativeConstant_nonneg n)
  unfold symbolDerivativeConstant
  linarith

theorem symbolDerivativeConstant_dominates {B n : ℕ} (hn : n ≤ B) :
    (100:ℝ)^n * angleDerivativeConstant n ≤ symbolDerivativeConstant B := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (B+1)) =>
      mul_nonneg (by positivity : 0 ≤ (100:ℝ)^i) (angleDerivativeConstant_nonneg i))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  unfold symbolDerivativeConstant
  linarith

theorem iteratedDeriv_shift (f : ℝ → ℝ) (j k : ℕ) :
    iteratedDeriv j (iteratedDeriv k f) = iteratedDeriv (j+k) f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ,ih,Nat.succ_add,iteratedDeriv_succ]

theorem smooth_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

 theorem normalizedMaskFactor_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (d : ℝ) (k : ℕ) : ContDiff ℝ ∞ (normalizedMaskFactor w d k) :=
  contDiff_const.mul (smooth_iteratedDeriv hw k)

 theorem normalizedMaskFactor_derivative_bound {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ, ‖w θ‖ ≤ 1)
    (hall : ∀ n θ, ‖iteratedDeriv n w θ‖ ≤
      ((100:ℝ)^n*angleDerivativeConstant n)*(d⁻¹)^n)
    {B k j : ℕ} (hkj : k+j ≤ B) (θ : ℝ) :
    ‖iteratedDeriv j (normalizedMaskFactor w d k) θ‖ ≤
      (symbolDerivativeConstant B)^k * (symbolDerivativeConstant B*d⁻¹)^j := by
  have hA := symbolDerivativeConstant_one_le B
  have hA0 : 0 ≤ symbolDerivativeConstant B := le_trans zero_le_one hA
  unfold normalizedMaskFactor
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_shift]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_pos hd]
  by_cases hz : j+k = 0
  · have hj : j = 0 := by omega
    have hk : k = 0 := by omega
    subst j; subst k
    simpa only [Nat.zero_add,pow_zero,one_mul,mul_one,iteratedDeriv_zero,Real.norm_eq_abs] using hzero θ
  · have hbudget : j+k ≤ B := by omega
    have hC : (100:ℝ)^(j+k)*angleDerivativeConstant (j+k) ≤
        symbolDerivativeConstant B^(j+k) := by
      apply (symbolDerivativeConstant_dominates hbudget).trans
      exact le_self_pow₀ hA (by omega)
    calc
      _ ≤ d^k * (((100:ℝ)^(j+k)*angleDerivativeConstant (j+k))*(d⁻¹)^(j+k)) :=
        mul_le_mul_of_nonneg_left (hall (j+k) θ) (by positivity)
      _ ≤ d^k * (symbolDerivativeConstant B^(j+k)*(d⁻¹)^(j+k)) := by gcongr
      _ = _ := by
        rw [pow_add,pow_add,mul_pow]
        have he : d^k*(d⁻¹)^k = 1 := by rw [← mul_pow,mul_inv_cancel₀ hd.ne',one_pow]
        calc
          _ = (d^k*(d⁻¹)^k) * (symbolDerivativeConstant B)^k *
              (symbolDerivativeConstant B)^j * (d⁻¹)^j := by ring
          _ = _ := by rw [he]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedAngularSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem descriptorAngleMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) :
    ContDiff ℝ ∞ (descriptorAngleMask Q ρ m N lam sig J i b x) :=
  spatialAnchorMask_contDiff Q hQ _ _ _ _ _ _

 theorem descriptorAngleMask_norm_le_one (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (θ : ℝ) :
    ‖descriptorAngleMask Q ρ m N lam sig J i b x θ‖ ≤ 1 := by
  have hb := descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x (sourceUnitDirection θ)
  simpa only [descriptorAngleMask,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

 theorem descriptorAngleMask_derivatives (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (descriptorAngleMask Q ρ m N lam sig J i b x) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(sourceAngularRadius N sig (descriptorLength b))⁻¹^j :=
  spatialAnchorMask_derivative_bound Q hQ _ _ _ _ _ _ _ _

 theorem inheritedMaskProduct_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane)
    (K j : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (D : ℝ) (hD : 0 ≤ D)
    (hscale : ∀ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹ ≤ D)
    (θ : ℝ) :
    ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤
      symbolDerivativeConstant (K+j)^(K+j) * ((S.card:ℝ)*D)^j := by
  let A := symbolDerivativeConstant (K+j)
  have hA : 1 ≤ A := symbolDerivativeConstant_one_le _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hk (a : ι) (ha : a ∈ S) : k a ≤ K :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha).trans hK
  have hh := iteratedDeriv_product_bound S
    (fun a => normalizedMaskFactor (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a))
      (sourceAngularRadius N sig (descriptorLength (b a))) (k a))
    (fun a => A^(k a)) (A*D) (mul_nonneg hA0 hD) j
    (fun _ _ => pow_nonneg hA0 _) (fun a _ => normalizedMaskFactor_contDiff
      (descriptorAngleMask_contDiff Q hQ ρ m N lam sig J i (b a) (x a)) _ _)
    (fun a ha n hn θ => (normalizedMaskFactor_derivative_bound (sourceAngularRadius_pos _ _ _)
      (descriptorAngleMask_norm_le_one Q hQ ρ m N lam sig J i (b a) (x a))
      (descriptorAngleMask_derivatives Q hQ ρ m N lam sig J i (b a) (x a))
      (Nat.add_le_add (hk a ha) hn) θ).trans (by
        change A^(k a)*(A*_ )^n ≤ _
        have hp := sourceAngularRadius_pos N sig (descriptorLength (b a))
        gcongr
        exact hscale a ha)) j le_rfl θ
  change ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤ _ at hh
  apply hh.trans
  rw [Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ A^K * ((S.card:ℝ)*(A*D))^j := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hK) (by positivity)
    _ = A^(K+j)*((S.card:ℝ)*D)^j := by rw [pow_add,mul_pow,mul_pow]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_AnchorSymbolDropping
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem inheritedMaskProduct_zero_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (θ : ℝ) :
    ‖inheritedMaskProduct S b k Q ρ m N lam sig J i x θ‖ ≤ symbolDerivativeConstant K^K := by
  let D := ∑ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹
  have hp a : 0 ≤ (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹ :=
    inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hp a)
  have hh := inheritedMaskProduct_bound S b k Q hQ ρ m N lam sig J i x K 0 hK D hD
    (fun a ha => Finset.single_le_sum (fun a _ => hp a) ha) θ
  simpa using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_UniformSymbolScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem sourceAngularRadius_inv (N : ℕ) (sig : ℝ) (l : ℕ) :
    (sourceAngularRadius N sig l)⁻¹ = max 1 ((2:ℝ)^l*((2:ℝ)^N)^(-50*sig)) := by
  have hp : 0 < 1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig) := by positivity
  have he : (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig))⁻¹ =
      (2:ℝ)^l*((2:ℝ)^N)^(-50*sig) := by
    rw [mul_inv_rev,inv_div,div_one,show -50*sig = -(50*sig) by ring,Real.rpow_neg (by positivity)]
    ring
  unfold sourceAngularRadius
  rcases le_total 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig)) with h | h
  · rw [min_eq_left h,inv_one,← he,max_eq_left (by simpa using inv_anti₀ zero_lt_one h)]
  · rw [min_eq_right h,he,← he,max_eq_right (by simpa using inv_anti₀ hp h)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem stationaryJet_order {n k : ℕ} (_hk : k ∈ Finset.range (n+1))
    (c : OrderedFinpartition (n-k)) : c.length ≤ n := by
  exact c.length_le.trans (Nat.sub_le _ _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem angularFiniteSum_order {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (n : ℕ) (h : ∀ a ∈ s, (p a).order ≤ n) :
    (angularFiniteSum s p).order ≤ n := by
  apply AngularDifferentialExpr.sum_order_le
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact h a (Finset.mem_toList.mp ha)

theorem stationaryJetExpr_order (n : ℕ) : (stationaryJetExpr n).order ≤ n := by
  apply angularFiniteSum_order
  intro k hk
  apply angularFiniteSum_order
  intro c _
  exact stationaryJet_order hk c

theorem directStationaryExpr_order (j : ℕ) : (directStationaryExpr j).order ≤ 2*j := by
  simpa [directStationaryExpr, AngularDifferentialExpr.order] using stationaryJetExpr_order (2*j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseStationaryExpr_order (n : ℕ) : (inverseStationaryExpr n).order ≤ 2*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [inverseStationaryExpr, AngularDifferentialExpr.order]
    | succ n =>
      simp only [inverseStationaryExpr, AngularDifferentialExpr.order, zero_add]
      apply angularFiniteSum_order
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hi := ih (n-k) (by omega)
      have hd := directStationaryExpr_order (k+1)
      change (directStationaryExpr (k+1)).order + (inverseStationaryExpr (n-k)).order ≤ _
      omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OrderedLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem orderedDerivAssignments_budget {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (n : ℕ) {k : ι → ℕ} (hk : k ∈ orderedDerivAssignments S n) :
    ∑ i ∈ S, k i = n := by
  induction n generalizing k with
  | zero => simp only [orderedDerivAssignments,List.mem_singleton] at hk; subst k; simp
  | succ n ih =>
    obtain ⟨l,hl,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    have hi : i ∈ S := Finset.mem_toList.mp hi
    rw [Finset.sum_update_of_mem hi,Finset.sdiff_singleton_eq_erase]
    have he := Finset.add_sum_erase S l hi
    rw [ih hl] at he
    omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOperatorTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff
namespace AngularDifferentialExpr

theorem terms_order (p : AngularDifferentialExpr) {a : ℂ × ℕ} (ha : a ∈ p.terms) :
    a.2 ≤ p.order := by
  induction p generalizing a with
  | term c k =>
    have he : a = (c,k) := List.mem_singleton.mp ha
    subst a
    exact le_rfl
  | add p q hp hq =>
    obtain ha | ha := List.mem_append.mp ha
    · exact (hp ha).trans (le_max_left _ _)
    · exact (hq ha).trans (le_max_right _ _)
  | comp p q hp hq =>
    obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    exact Nat.add_le_add (hp hb) (hq hc)

end AngularDifferentialExpr

theorem inverseStationaryOperator_terms_order (j : ℕ) {a : ℂ × ℕ}
    (ha : a ∈ (inverseStationaryExpr j).terms) : a.2 ≤ 2*j :=
  ((inverseStationaryExpr j).terms_order ha).trans (inverseStationaryExpr_order j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransformSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angular_integrand_norm (r : ℝ) (ω : UnitCircle) (x : Plane)
    (b : Plane → UnitCircle → ℂ) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω‖ =
      ‖b x ω‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem sourceAngularTransform_norm_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (M : ℝ) (hM : 0 < M) (b : Plane → UnitCircle → ℂ)
    (C : ℝ) (hC : ∀ x ∈ X, ∀ ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    ‖sourceAngularTransform ρ X M b r ω‖ ≤ C * (ρ X).toReal / M := by
  unfold sourceAngularTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_setIntegral_le_of_norm_le_const (measure_lt_top ρ X)
    (fun x hx => (angular_integrand_norm r ω x b).trans_le (hC x hx ω))
  calc
    _ ≤ M⁻¹ * (C * (ρ X).toReal) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_InheritedSymbolMeasurability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped ContDiff Topology

 theorem spatialAnchorMask_derivative_formula (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection φ)) θ =
      ∑ P ∈ occupiedAnchorPaths Q ρ n,
        if x ∈ (Q.descendant P).carrier then iteratedDeriv j (sourceTestMask (G P) d hd) θ else 0 := by
  classical
  unfold spatialAnchorMask
  simp only [circleTestMask_comp]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro P _
    by_cases hx : x ∈ (Q.descendant P).carrier <;> simp [hx]
  · intro P _
    by_cases hx : x ∈ (Q.descendant P).carrier
    · simp only [hx, ↓reduceIte]
      exact ((sourceTestMask_contDiff (G P) d hd).of_le
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    · simp only [hx, ↓reduceIte]
      exact contDiffAt_const

 theorem measurable_spatialAnchorMask_derivative (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (j : ℕ) :
    Measurable (fun z : Plane × UnitCircle =>
      iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd z.1 (sourceUnitDirection φ)) (sourceAngle z.2)) := by
  simp only [spatialAnchorMask_derivative_formula]
  apply Finset.measurable_sum
  intro P _
  apply Measurable.ite ((Q.descendant P).measurable.preimage measurable_fst) _ measurable_const
  exact ((smooth_iteratedDeriv (sourceTestMask_contDiff (G P) d hd) j).continuous.measurable.comp
    measurable_sourceAngle).comp measurable_snd

 theorem measurable_inheritedCircleSymbol {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (hh : Measurable h) :
    Measurable (fun z : Plane × UnitCircle => inheritedCircleSymbol S b k Q ρ m N lam sig J i h z.1 z.2) := by
  unfold inheritedCircleSymbol
  apply (hh.comp measurable_fst).mul
  apply Complex.measurable_ofReal.comp
  apply Finset.measurable_prod
  intro a _
  apply measurable_const.mul
  exact measurable_spatialAnchorMask_derivative Q ρ _ _ _ _ (k a)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ENNReal

theorem sourcePlaneWave_norm (r : ℝ) (ω : UnitCircle) (x : Plane) :
    ‖sourcePlaneWave r ω x‖ = 1 := by
  simpa only [sourcePlaneWave, mul_one, norm_one] using angular_integrand_norm r ω x (fun _ _ => 1)

theorem sourcePlaneWave_sub (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    sourcePlaneWave r ω x * conj (sourcePlaneWave r ω y) =
      sourcePlaneWave r ω (x-y) := by
  simp only [sourcePlaneWave, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_add, inner_sub_right, Complex.ofReal_sub]
  congr 1
  ring

theorem sourceAngularTransform_product (ρ ν : Measure Plane) (X Y : Set Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ X M₁ b₁ r ω *
      conj (sourceAngularTransform ν Y M₂ b₂ r ω) =
    (M₁*M₂)⁻¹ • (∫ x in X, ∫ y in Y,
      sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω)) ∂ν ∂ρ) := by
  have he (x y : Plane) :
      sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω)) =
      (sourcePlaneWave r ω x * b₁ x ω) * conj (sourcePlaneWave r ω y * b₂ y ω) := by
    rw [← sourcePlaneWave_sub, map_mul]
    ring
  simp_rw [he, integral_const_mul, integral_mul_const, integral_conj]
  simp only [sourceAngularTransform, sourcePlaneWave, Complex.real_smul,
    map_mul, Complex.conj_ofReal, mul_inv_rev, Complex.ofReal_mul]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceFormFubini
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem finite_three_integral_swap {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (τ : Measure γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure τ]
    (f : α → β → γ → ℂ)
    (hf : Measurable (fun z : (α × β) × γ => f z.1.1 z.1.2 z.2))
    (C : ℝ) (hC : ∀ a b c, ‖f a b c‖ ≤ C) :
    (∫ a, ∫ b, ∫ c, f a b c ∂τ ∂ν ∂μ) =
      ∫ b, ∫ c, ∫ a, f a b c ∂μ ∂τ ∂ν := by
  have hi : Integrable (fun z : (α × β) × γ => f z.1.1 z.1.2 z.2)
      ((μ.prod ν).prod τ) :=
    (integrable_const C).mono hf.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun point =>
        (hC point.1.1 point.1.2 point.2).trans (le_abs_self C)))
  rw [integral_integral_swap hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards with b
  apply integral_integral_swap
  apply (integrable_const C).mono
  · exact (hf.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aestronglyMeasurable
  · filter_upwards with z
    exact (hC z.1 b z.2).trans (le_abs_self C)

theorem measurable_distance_integrand (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) (r : ℝ) :
    Measurable (fun z : (UnitCircle × Plane) × Plane =>
      sourcePlaneWave r z.1.1 (z.1.2-z.2) *
        (ψ z.1.1 * b₁ z.1.2 z.1.1 * conj (b₂ z.2 z.1.1))) := by
  apply Measurable.mul
  · unfold sourcePlaneWave
    fun_prop
  · exact ((hψ.comp (measurable_fst.comp measurable_fst)).mul
      (h₁.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)))).mul
      (Complex.continuous_conj.measurable.comp
        (h₂.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))))

theorem distance_integrand_norm_le (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {P B₁ B₂ : ℝ}
    (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (_ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    ‖sourcePlaneWave r ω (x-y) * (ψ ω * b₁ x ω * conj (b₂ y ω))‖ ≤ P*B₁*B₂ := by
  simp only [norm_mul, sourcePlaneWave_norm, Complex.norm_conj, one_mul]
  exact mul_le_mul (mul_le_mul (hp ω) (hb₁ x ω) (norm_nonneg _) hP)
    (hb₂ y ω) (norm_nonneg _) (mul_nonneg hP hB₁)

theorem sourceDistanceF_endpoint_integral (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    sourceDistanceF ψ (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2) r =
      (M₁*M₂)⁻¹ • (∫ x in X, ∫ y in Y, sourceDistanceKernel ψ b₁ b₂ r x y ∂ν ∂ρ) := by
  unfold sourceDistanceF
  simp_rw [mul_assoc, sourceAngularTransform_product, mul_smul_comm,
    ← integral_const_mul]
  have he (ω : UnitCircle) (x y : Plane) :
      ψ ω * (sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω))) =
        sourcePlaneWave r ω (x-y) * (ψ ω * b₁ x ω * conj (b₂ y ω)) := by ring
  simp_rw [he]
  rw [integral_smul]
  congr 1
  exact finite_three_integral_swap sourceArcLength (ρ.restrict X) (ν.restrict Y) _
    (measurable_distance_integrand ψ b₁ b₂ hψ h₁ h₂ r) (P*B₁*B₂)
    (distance_integrand_norm_le ψ b₁ b₂ hP hB₁ hB₂ hp hb₁ hb₂ r)

theorem sourceDistanceF_norm_le (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (_ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ∈ X, ∀ ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ∈ Y, ∀ ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    ‖sourceDistanceF ψ (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2) r‖ ≤
      (P*B₁*B₂*sourceArcLength.real univ) *
        ((ρ X).toReal/M₁) * ((ν Y).toReal/M₂) := by
  have hh := norm_integral_le_of_norm_le_const (μ := sourceArcLength)
    (f := fun ω => ψ ω * sourceAngularTransform ρ X M₁ b₁ r ω *
      conj (sourceAngularTransform ν Y M₂ b₂ r ω))
    (C := P*(B₁*(ρ X).toReal/M₁)*(B₂*(ν Y).toReal/M₂))
    (Filter.Eventually.of_forall (fun ω => by
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul
        (mul_le_mul (hp ω) (sourceAngularTransform_norm_le ρ X M₁ hM₁ b₁ B₁ hb₁ r ω)
          (norm_nonneg _) hP)
        (sourceAngularTransform_norm_le ν Y M₂ hM₂ b₂ B₂ hb₂ r ω)
        (norm_nonneg _) (by positivity)))
  apply hh.trans_eq
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphConeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem graphConeCutoff_contDiff : ContDiff ℝ ∞ graphConeCutoff :=
  Complex.ofRealCLM.contDiff.comp graphConeBump.contDiff

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedConeKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

theorem measurable_sourceConeCircle (axis : ℝ) : Measurable (sourceConeCircle axis) :=
  graphConeCutoff_contDiff.continuous.measurable.comp
    (measurable_sourceAngle.comp (sourceCircleRotate_isometry (-axis)).continuous.measurable)

theorem sourceConeCircle_norm_le (axis : ℝ) (dir : UnitCircle) :
    ‖sourceConeCircle axis dir‖ ≤ 1 := by
  simp only [sourceConeCircle, graphConeCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg graphConeBump.nonneg]
  exact graphConeBump.le_one

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_InverseLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseLeibnizTerms_budget {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι)
    {a : ℂ × (ι → ℕ)} (ha : a ∈ inverseLeibnizTerms j S) :
    ∑ i ∈ S, a.2 i ≤ 2*j := by
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  rw [orderedDerivAssignments_budget S b.2 hk]
  exact inverseStationaryOperator_terms_order j hb

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceKernelSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem measurable_sourceDistanceKernel (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) :
    Measurable (fun z : ℝ × (Plane × Plane) => sourceDistanceKernel ψ b₁ b₂ z.1 z.2.1 z.2.2) := by
  have hf : Measurable (fun z : (ℝ × (Plane × Plane)) × UnitCircle =>
      sourcePlaneWave z.1.1 z.2 (z.1.2.1-z.1.2.2) *
        (ψ z.2 * b₁ z.1.2.1 z.2 * conj (b₂ z.1.2.2 z.2))) := by
    apply Measurable.mul
    · unfold sourcePlaneWave
      fun_prop
    · exact (((hψ.comp measurable_snd).mul
        (h₁.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))).mul
        (Complex.continuous_conj.measurable.comp
          (h₂.comp ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

theorem sourceDistanceKernel_norm_le (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {P B₁ B₂ : ℝ}
    (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) (x y : Plane) :
    ‖sourceDistanceKernel ψ b₁ b₂ r x y‖ ≤ P*B₁*B₂*sourceArcLength.real univ :=
  norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun dir =>
    distance_integrand_norm_le ψ b₁ b₂ hP hB₁ hB₂ hp hb₁ hb₂ r dir x y))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialFourierSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

theorem spatialFourierCost_nonneg (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 0 ≤ spatialFourierCost δ L hδ hL j :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem spatialFourierPhase_norm (s : ℝ) (ξ x : Plane) :
    ‖spatialFourierPhase s ξ x‖ = 1 := by
  simp [spatialFourierPhase, Complex.norm_exp, Complex.mul_re]

theorem spatialFourierCoeff_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : Integrable (spatialFourierCoeff δ L hδ hL j) :=
  (spatialFourierCoeff δ L hδ hL j).integrable

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialPhasedSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate

theorem spatialPhasedSymbol_norm (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ) (x : Plane) (ω : UnitCircle) :
    ‖spatialPhasedSymbol s ξ b x ω‖ = ‖b x ω‖ := by
  simp [spatialPhasedSymbol, spatialFourierPhase_norm]

theorem spatialPhasedSymbol_measurable (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2)) :
    Measurable (fun z : Plane × UnitCircle => spatialPhasedSymbol s ξ b z.1 z.2) := by
  apply Measurable.mul _ hb
  unfold spatialFourierPhase
  fun_prop

theorem sourceDistanceKernel_phased (s : ℝ) (ξ : Plane) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) (x y : Plane) :
    sourceDistanceKernel ψ (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r x y =
      spatialPairPhase s ξ (x,y) * sourceDistanceKernel ψ b₁ b₂ r x y := by
  simp only [sourceDistanceKernel, spatialPhasedSymbol, spatialPairPhase, map_mul,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialPhasedDistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

 theorem spatialPhasedDistanceF_formula (s : ℝ) (ξ : Plane)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    sourceDistanceF ψ
      (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s ξ b₁) z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s ξ b₂) z.1 z.2) r =
      (M₁*M₂)⁻¹ • (∫ z, spatialPairPhase s ξ z * sourceDistanceKernel ψ b₁ b₂ r z.1 z.2
        ∂((ρ.restrict X).prod (ν.restrict Y))) := by
  have hm₁ := spatialPhasedSymbol_measurable s ξ b₁ h₁
  have hm₂ := spatialPhasedSymbol_measurable s ξ b₂ h₂
  have hb₁' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₁ x ω‖ ≤ B₁ := by
    intro x ω; rw [spatialPhasedSymbol_norm]; exact hb₁ x ω
  have hb₂' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₂ x ω‖ ≤ B₂ := by
    intro x ω; rw [spatialPhasedSymbol_norm]; exact hb₂ x ω
  rw [sourceDistanceF_endpoint_integral ρ ν X Y M₁ M₂ ψ _ _ hψ hm₁ hm₂
    hP hB₁ hB₂ hp hb₁' hb₂']
  have hm : Measurable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2) :=
    (measurable_sourceDistanceKernel ψ _ _ hψ hm₁ hm₂).comp (f := fun z : Plane × Plane => (r,z))
      (show Measurable (fun z : Plane × Plane => (r,z)) from measurable_const.prodMk measurable_id)
  have hi : Integrable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2)
      ((ρ.restrict X).prod (ν.restrict Y)) :=
    Integrable.of_bound hm.aestronglyMeasurable (P*B₁*B₂*sourceArcLength.real univ)
      (Eventually.of_forall (fun z => sourceDistanceKernel_norm_le ψ _ _ hP hB₁ hB₂
        hp hb₁' hb₂' r z.1 z.2))
  rw [← integral_prod _ hi]
  simp_rw [sourceDistanceKernel_phased]

 theorem spatialPhasedDistanceF_joint_measurable (s : ℝ)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) :
    Measurable (fun p : Plane × ℝ => sourceDistanceF ψ
      (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s p.1 b₁) z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s p.1 b₂) z.1 z.2) p.2) := by
  simp_rw [spatialPhasedDistanceF_formula s _ ρ ν X Y M₁ M₂ ψ b₁ b₂ hψ h₁ h₂
    hP hB₁ hB₂ hp hb₁ hb₂]
  have hphase : Measurable (fun p : (Plane × ℝ) × (Plane × Plane) =>
      spatialPairPhase s p.1.1 p.2) :=
    (spatialPairPhase_continuous s).measurable.comp (f := fun p : (Plane × ℝ) × (Plane × Plane) => (p.1.1,p.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hkernel : Measurable (fun p : (Plane × ℝ) × (Plane × Plane) =>
      sourceDistanceKernel ψ b₁ b₂ p.1.2 p.2.1 p.2.2) :=
    (measurable_sourceDistanceKernel ψ b₁ b₂ hψ h₁ h₂).comp (f := fun p : (Plane × ℝ) × (Plane × Plane) => (p.1.2,p.2))
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : Plane × ℝ =>
      ∫ z, spatialPairPhase s p.1 z * sourceDistanceKernel ψ b₁ b₂ p.2 z.1 z.2
        ∂((ρ.restrict X).prod (ν.restrict Y))) :=
    (hphase.mul hkernel).stronglyMeasurable.integral_prod_right'.measurable
  exact hm.const_smul ((M₁*M₂)⁻¹ : ℝ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphKernelBounds
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem inheritedCircleSymbol_norm_le {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Plane → ℂ) (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K)
    (x : Plane) (hx : ‖h x‖ ≤ 1) (ω : UnitCircle) :
    ‖inheritedCircleSymbol S b k Q ρ m N lam sig J i h x ω‖ ≤
      symbolDerivativeConstant K^K := by
  classical
  simp only [inheritedCircleSymbol, norm_mul, Complex.norm_real]
  exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
    (by simpa using (inheritedMaskProduct_zero_bound S b k Q hQ ρ m N lam sig J i
      (fun _ => x) K hK (sourceAngle ω)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_WeightedIntegralSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem weighted_integral_square {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hiw : Integrable w μ)
    (hif : Integrable (fun x => w x * f x) μ)
    (hif₂ : Integrable (fun x => w x * (f x)^2) μ) :
    (∫ x, w x * f x ∂μ)^2 ≤ (∫ x, w x ∂μ) * (∫ x, w x * (f x)^2 ∂μ) := by
  let W := ∫ x, w x ∂μ
  let V := ∫ x, w x * f x ∂μ
  let U := ∫ x, w x * (f x)^2 ∂μ
  have hW : 0 ≤ W := integral_nonneg hw
  by_cases hz : W = 0
  · have hwz : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hw hiw).mp hz
    have hvz : V = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hwz] with x hx
      simp [hx]
    change V^2 ≤ W*U
    simp [hvz,hz]
  · have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
    have hn : 0 ≤ ∫ x, w x * (f x - V/W)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
    have he (x : α) : w x * (f x - V/W)^2 =
        w x*(f x)^2 - (2*(V/W))*(w x*f x) + (V/W)^2*w x := by ring
    simp_rw [he] at hn
    have hiSub : Integrable (fun x => w x*(f x)^2 - (2*(V/W))*(w x*f x)) μ :=
      hif₂.sub (hif.const_mul (2*(V/W)))
    rw [integral_add hiSub (hiw.const_mul ((V/W)^2)),
      integral_sub hif₂ (hif.const_mul (2*(V/W))), integral_const_mul, integral_const_mul] at hn
    change 0 ≤ U - (2*(V/W))*V + (V/W)^2*W at hn
    have hc : U - (2*(V/W))*V + (V/W)^2*W = U - V^2/W := by
      field_simp
      ring
    rw [hc] at hn
    change V^2 ≤ W*U
    have hh := (div_le_iff₀ hWp).mp (show V^2/W ≤ U by linarith)
    nlinarith

theorem norm_integral_coeff_square {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c F : α → ℂ) (hic : Integrable c μ)
    (hi₁ : Integrable (fun x => ‖c x‖ * ‖F x‖) μ)
    (hi₂ : Integrable (fun x => ‖c x‖ * ‖F x‖^2) μ) :
    ‖∫ x, c x * F x ∂μ‖^2 ≤
      (∫ x, ‖c x‖ ∂μ) * (∫ x, ‖c x‖ * ‖F x‖^2 ∂μ) := by
  have hn : ‖∫ x, c x * F x ∂μ‖ ≤ ∫ x, ‖c x‖ * ‖F x‖ ∂μ := by
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun x => c x * F x)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (weighted_integral_square μ (fun x => ‖c x‖) (fun x => ‖F x‖)
      (fun x => norm_nonneg _) hic.norm hi₁ hi₂)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_MinimalDescriptorLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length_le_anchor (A : ℕ → ℝ) {N q b u : ℕ}
    {d : PolicyDescriptor} (hd : d ∈ originDescriptors A N q b u) :
    descriptorLength d ≤ descriptorAnchor d := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.sub_le _ _
  · split_ifs at hd with h
    · obtain rfl := Finset.mem_singleton.mp hd
      dsimp [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem policyDescriptor_twice_length (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    a + 2*descriptorLength d ≤ t := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,ht,hw⟩ := Finset.mem_filter.mp hz
  have hu := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hl := originDescriptor_length A hq hu hw hd
  have hp := originDescriptor_length_le_anchor A hd
  omega

theorem policyDescriptor_real_length (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    2*(descriptorLength d:ℝ) ≤ (t:ℝ)-(a:ℝ) := by
  have h : (a:ℝ)+2*(descriptorLength d:ℝ) ≤ (t:ℝ) := by
    exact_mod_cast policyDescriptor_twice_length A hq hd
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ContinuousCoefficientShell
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

 theorem integrable_coeff_norm_power {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c F : α → ℂ) (hic : Integrable c μ) (hF : Measurable F)
    {C : ℝ} (_ : 0 ≤ C) (hb : ∀ x, ‖F x‖ ≤ C) (n : ℕ) :
    Integrable (fun x => ‖c x‖ * ‖F x‖^n) μ := by
  apply (hic.norm.mul_const (C^n)).mono'
    (hic.aestronglyMeasurable.norm.mul (hF.aestronglyMeasurable.norm.pow n))
  filter_upwards with x
  change ‖‖c x‖ * ‖F x‖^n‖ ≤ ‖c x‖ * C^n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb x) n) (norm_nonneg _)

 theorem continuous_coefficient_shell_square (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : Plane → ℂ) (hc : Measurable c) (hic : Integrable c)
    (F : Plane × ℝ → ℂ) (hF : Measurable F)
    {C B : ℝ} (hC : 0 ≤ C) (hb : ∀ p, ‖F p‖ ≤ C)
    (hB : ∀ ξ, (∫ r, ‖F (ξ,r)‖^2 ∂μ) ≤ B) :
    (∫ r, ‖∫ ξ, c ξ * F (ξ,r)‖^2 ∂μ) ≤ (∫ ξ, ‖c ξ‖)^2 * B := by
  let W := ∫ ξ, ‖c ξ‖
  have hW : 0 ≤ W := integral_nonneg (fun _ => norm_nonneg _)
  have hiJoint : Integrable (fun p : Plane × ℝ => ‖c p.1‖ * ‖F p‖^2)
      (volume.prod μ) := by
    apply ((hic.norm.comp_fst μ).mul_const (C^2)).mono'
      ((hic.aestronglyMeasurable.norm.comp_fst).mul (hF.aestronglyMeasurable.norm.pow 2))
    filter_upwards with p
    change ‖‖c p.1‖ * ‖F p‖^2‖ ≤ ‖c p.1‖ * C^2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb p) 2) (norm_nonneg _)
  have hPoint (r : ℝ) : ‖∫ ξ, c ξ * F (ξ,r)‖^2 ≤
      W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2) := by
    have hmF : Measurable (fun ξ => F (ξ,r)) := hF.comp (measurable_id.prodMk measurable_const)
    have hi₁ := integrable_coeff_norm_power volume c (fun ξ => F (ξ,r)) hic hmF hC (fun ξ => hb (ξ,r)) 1
    have hi₂ := integrable_coeff_norm_power volume c (fun ξ => F (ξ,r)) hic hmF hC (fun ξ => hb (ξ,r)) 2
    exact norm_integral_coeff_square volume c (fun ξ => F (ξ,r)) hic
      (by simpa only [pow_one] using hi₁) hi₂
  have hm : Measurable (fun r => ∫ ξ, c ξ * F (ξ,r)) :=
    ((hc.comp measurable_fst).mul hF).stronglyMeasurable.integral_prod_left'.measurable
  have hiBound : Integrable (fun r => W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2)) μ :=
    hiJoint.integral_prod_right.const_mul W
  have hiMix : Integrable (fun r => ‖∫ ξ, c ξ * F (ξ,r)‖^2) μ :=
    hiBound.mono' (hm.norm.pow_const 2).aestronglyMeasurable (by
      filter_upwards with r
      change ‖‖∫ ξ, c ξ * F (ξ,r)‖^2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖∫ ξ, c ξ * F (ξ,r)‖))]
      exact hPoint r)
  calc
    _ ≤ ∫ r, W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2) ∂μ :=
      integral_mono hiMix hiBound hPoint
    _ = W * (∫ ξ, ‖c ξ‖ * (∫ r, ‖F (ξ,r)‖^2 ∂μ)) := by
      rw [integral_const_mul, ← integral_integral_swap
        (f := fun ξ r => ‖c ξ‖ * ‖F (ξ,r)‖^2) hiJoint]
      simp_rw [integral_const_mul]
    _ ≤ W * (∫ ξ, ‖c ξ‖ * B) := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply integral_mono
      · simpa only [integral_const_mul] using hiJoint.integral_prod_left
      · exact hic.norm.mul_const B
      · intro ξ
        exact mul_le_mul_of_nonneg_left (hB ξ) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; dsimp [W]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_FiniteWeightedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem finite_weighted_shell_square {ι : Type*} (s : Finset ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hi : ∀ i ∈ s, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖∑ i ∈ s, F i r‖^2 ∂μ) ≤ (∑ i ∈ s, w i)^2*B := by
  classical
  have hz (i : ι) (his : i ∈ s) (hwi : w i = 0) :
      ∀ᵐ r ∂μ, F i r = 0 := by
    have he : (∫ r, ‖F i r‖^2 ∂μ) = 0 :=
      le_antisymm (by simpa [hwi] using hB i his)
        (integral_nonneg (fun _ => sq_nonneg _))
    have hh := (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg (‖F i r‖)) (hi i his)).mp he
    filter_upwards [hh] with r hr
    simpa using hr
  have hae : ∀ᵐ r ∂μ, ∀ i ∈ s, w i = 0 → F i r = 0 := by
    exact (eventually_all_finset s).mpr (fun i his =>
      (ae_all_iff).mpr (fun hwi => hz i his hwi))
  let G : ℝ → ℝ := fun r => ∑ i ∈ s, ‖F i r‖^2 / w i
  let W : ℝ := ∑ i ∈ s, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hgi : Integrable G μ := integrable_finsetSum s
    (fun i his => (hi i his).div_const (w i))
  have hpoint : ∀ᵐ r ∂μ, ‖∑ i ∈ s, F i r‖^2 ≤ W*G r := by
    filter_upwards [hae] with r hr
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i his => div_nonneg (sq_nonneg _) (hw i his))
    intro i his
    by_cases hwi : w i = 0
    · simp [hwi,hr i his hwi]
    · rw [mul_div_cancel₀ _ hwi]
  have hsi : Integrable (fun r => ‖∑ i ∈ s, F i r‖^2) μ := by
    have hsm : AEStronglyMeasurable (fun r => ∑ i ∈ s, F i r) μ := by
      convert Finset.aestronglyMeasurable_sum s hm using 1
      all_goals try with_reducible_and_instances rfl
      ext r
      simp
    apply (hgi.const_mul W).mono' (hsm.norm.pow 2)
    filter_upwards [hpoint] with r hr
    change ‖‖∑ i ∈ s, F i r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  have hBi (i : ι) (his : i ∈ s) :
      (∫ r, ‖F i r‖^2 ∂μ) / w i ≤ w i*B := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · apply (div_le_iff₀ (lt_of_le_of_ne (hw i his) (Ne.symm hwi))).mpr
      nlinarith [hB i his]
  calc
    _ ≤ ∫ r, W*G r ∂μ := integral_mono_ae hsi (hgi.const_mul W) hpoint
    _ = W * ∑ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) / w i := by
      rw [integral_const_mul,integral_finsetSum s (fun i his => (hi i his).div_const (w i))]
      simp only [integral_div]
    _ ≤ W * ∑ i ∈ s, w i*B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hBi) hW
    _ = _ := by rw [← Finset.sum_mul]; dsimp [W]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellStationaryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem high_shell_gap {sig : ℝ} {N q a t : ℕ} {v : ℝ}
    (hq : sig*(N:ℝ) ≤ (q:ℝ)) (hw : a+100*q < t)
    (hv : (t:ℝ)-sig*N ≤ v) : 99*sig*N ≤ v-a := by
  have hw' : (a:ℝ)+100*(q:ℝ) < (t:ℝ) := by exact_mod_cast hw
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem high_shell_descriptor_scale {sig v : ℝ} (hsig : 0 ≤ sig)
    (N l a t : ℕ) (hl : 2*(l:ℝ) ≤ (t:ℝ)-a)
    (hgap : 0 ≤ v-a) (hv : (t:ℝ)-sig*N ≤ v) :
    (sourceAngularRadius N sig l)⁻¹ ≤ (2:ℝ)^((v-a)/2) := by
  rw [sourceAngularRadius_inv]
  apply max_le
  · exact Real.one_le_rpow (by norm_num) (by linarith)
  · rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [mul_nonneg (Nat.cast_nonneg N) hsig]

theorem high_shell_extracted_scale {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) {sig v : ℝ}
    (hsig : 0 ≤ sig) (N a t j : ℕ)
    (hl : ∀ i ∈ S, 2*(descriptorLength (b i):ℝ) ≤ (t:ℝ)-a)
    (hgap : 0 ≤ v-a) (hv : (t:ℝ)-sig*N ≤ v) (hk : ∑ i ∈ S, k i ≤ 2*j) :
    (∏ i ∈ S, ((sourceAngularRadius N sig (descriptorLength (b i)))⁻¹)^(k i)) ≤
      (2:ℝ)^((j:ℝ)*(v-a)) := by
  calc
    _ ≤ ∏ i ∈ S, ((2:ℝ)^((v-a)/2))^(k i) := by
      apply Finset.prod_le_prod (fun index _ =>
        pow_nonneg (inv_nonneg.mpr (sourceAngularRadius_pos N sig (descriptorLength (b index))).le) _)
      intro i hi
      exact pow_le_pow_left₀ (inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le)
        (high_shell_descriptor_scale hsig N _ a t (hl i hi) hgap hv) _
    _ = ((2:ℝ)^((v-a)/2))^(∑ i ∈ S, k i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ ((2:ℝ)^((v-a)/2))^(2*j) :=
      pow_le_pow_right₀ (Real.one_le_rpow (by norm_num) (by linarith)) hk
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem pair_assignment_endpoint_budget (S : Finset PolicyDescriptor) (k : PairMaskIndex → ℕ)
    (K : ℕ) (hk : ∑ a ∈ pairMaskIndices S, k a ≤ K) (l : Fin 2) :
    ∑ b ∈ S, k (b,l) ≤ K := by
  apply le_trans _ hk
  change (∑ b ∈ S, k (b,l)) ≤ ∑ a ∈ S.product (Finset.univ : Finset (Fin 2)), k a
  rw [Finset.product_eq_sprod,Finset.sum_product S (Finset.univ : Finset (Fin 2)) k]
  apply Finset.sum_le_sum
  intro b hb
  exact Finset.single_le_sum (f := fun y : Fin 2 => k (b,y)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem minimal_assignment_scale (A : ℕ → ℝ) {N q a t j : ℕ} {sig v : ℝ}
    (hsig : 0 ≤ sig) (hq : 0 < q) (hqscale : sig*N ≤ (q:ℝ))
    (hw : a+100*q < t) (hv : (t:ℝ)-sig*N ≤ v)
    {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))) :
    assignmentScale (policyDescriptorList A N q a t) N sig b.2 ≤
      (2:ℝ)^((j:ℝ)*(v-a)) := by
  apply high_shell_extracted_scale _ Prod.fst b.2 hsig N a t j
  · intro c hc
    exact policyDescriptor_real_length A hq (Finset.mem_product.mp hc).1
  · have hg := high_shell_gap hqscale hw hv
    have hn : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig (Nat.cast_nonneg _)
    linarith
  · exact hv
  · exact inverseLeibnizTerms_budget j _ hb

theorem minimal_assignment_scale_absorbed (A : ℕ → ℝ) {N q a t j : ℕ} {sig v : ℝ}
    (hsig : 0 ≤ sig) (hq : 0 < q) (hqscale : sig*N ≤ (q:ℝ))
    (hw : a+100*q < t) (hv : (t:ℝ)-sig*N ≤ v)
    {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))) :
    0 ≤ (2:ℝ)^(-(j:ℝ)*(v-a))*assignmentScale (policyDescriptorList A N q a t) N sig b.2 ∧
    (2:ℝ)^(-(j:ℝ)*(v-a))*assignmentScale (policyDescriptorList A N q a t) N sig b.2 ≤ 1 := by
  have hpos : 0 ≤ assignmentScale (policyDescriptorList A N q a t) N sig b.2 :=
    Finset.prod_nonneg (fun c _ => pow_nonneg (inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le) _)
  refine ⟨mul_nonneg (by positivity) hpos,?_⟩
  apply (mul_le_mul_of_nonneg_left (minimal_assignment_scale A hsig hq hqscale hw hv hb)
    (by positivity : 0 ≤ (2:ℝ)^(-(j:ℝ)*(v-a)))).trans_eq
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  convert Real.rpow_zero 2 using 2
  all_goals try with_reducible_and_instances rfl
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellEndpointTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate
namespace PositiveDistanceData

 theorem inverseEndpointSymbol_measurable (d : PositiveDistanceData) (k : PairMaskIndex → ℕ)
    (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => d.inverseEndpointSymbol k l z.1 z.2) :=
  measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ measurable_const

 theorem inverseEndpointSymbol_norm (d : PositiveDistanceData) (hQ : 0 < d.Q.side) (j : ℕ)
    {b : ℂ × (PairMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (l : Fin 2) (x : Plane) (dir : UnitCircle) :
    ‖d.inverseEndpointSymbol b.2 l x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) := by
  exact inheritedCircleSymbol_norm_le _ _ _ _ hQ _ _ _ _ _ _ _ _ (2*j)
    (pair_assignment_endpoint_budget _ _ _ (inverseLeibnizTerms_budget j _ hb) l) x (by simp) dir

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_NormalizedHighShellKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
namespace PositiveDistanceData

 theorem absorbedInverseCoefficient_norm (d : PositiveDistanceData)
    (hsig : 0 ≤ d.sig) (hq : 0 < d.q) (hqs : d.sig*d.N ≤ (d.q:ℝ))
    (hw : d.a+100*d.q < d.t) {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (j : ℕ)
    {b : ℂ × (PairMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)) :
    ‖d.absorbedInverseCoefficient j v b‖ ≤ ‖b.1‖ := by
  have he := minimal_assignment_scale_absorbed (fun n => d.mass n-(n:ℝ)/(d.N:ℝ))
    hsig hq hqs hw hv hb
  rw [absorbedInverseCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  simp only [inverseDescriptorList]
  rw [abs_of_nonneg he.1]
  exact (mul_le_mul_of_nonneg_left he.2 (norm_nonneg _)).trans_eq (mul_one _)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ListWeightedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem list_weighted_shell_square {ι : Type*} (L : List ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ L, 0 ≤ w i)
    (hi : ∀ i ∈ L, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ L, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ L, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖(L.map (fun i => F i r)).sum‖^2 ∂μ) ≤ (L.map w).sum^2*B := by
  have hh := finite_weighted_shell_square (Finset.univ : Finset (Fin L.length)) μ
    (fun i => F L[i]) (fun i => w L[i])
    (fun i _ => hw _ (List.getElem_mem i.isLt))
    (fun i _ => hi _ (List.getElem_mem i.isLt))
    (fun i _ => hm _ (List.getElem_mem i.isLt))
    (fun i _ => hB _ (List.getElem_mem i.isLt))
  have he (f : ι → ℂ) : (∑ i : Fin L.length, f L[i]) = (L.map f).sum := by
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map L f
  have hw' : (∑ i : Fin L.length, w L[i]) = (L.map w).sum := by
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map L w
  simp_rw [show ∀ r, (∑ i : Fin L.length, F L[i] r) =
    (L.map (fun i => F i r)).sum from fun r => he (fun i => F i r),hw'] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellMultipliers
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem shell_multiplier_square (μ : Measure ℝ) (u F : ℝ → ℂ)
    (hu : Measurable u) (hF : Measurable F)
    (hi : Integrable (fun r => ‖F r‖^2) μ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ r ∂μ, ‖u r‖ ≤ A) :
    Integrable (fun r => ‖u r*F r‖^2) μ ∧
      (∫ r, ‖u r*F r‖^2 ∂μ) ≤ A^2*(∫ r, ‖F r‖^2 ∂μ) := by
  have hp : ∀ᵐ r ∂μ, ‖u r*F r‖^2 ≤ A^2*‖F r‖^2 := by
    filter_upwards [hb] with r hr
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hA).mpr hr) (sq_nonneg _)
  have hi' : Integrable (fun r => ‖u r*F r‖^2) μ := by
    apply (hi.const_mul (A^2)).mono' ((hu.mul hF).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with r hr
    change ‖‖u r*F r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  exact ⟨hi', (integral_mono_ae hi' (hi.const_mul (A^2)) hp).trans_eq (integral_const_mul _ _)⟩

theorem continuous_shell_mixture_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : Plane → ℂ) (hc : Measurable c) (hic : Integrable c)
    (F : Plane × ℝ → ℂ) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p, ‖F p‖ ≤ C) :
    Measurable (fun r => ∫ ξ, c ξ*F (ξ,r)) ∧
    (∀ r, ‖∫ ξ, c ξ*F (ξ,r)‖ ≤ (∫ ξ, ‖c ξ‖)*C) ∧
    Integrable (fun r => ‖∫ ξ, c ξ*F (ξ,r)‖^2) μ := by
  have hm : Measurable (fun r => ∫ ξ, c ξ*F (ξ,r)) :=
    ((hc.comp measurable_fst).mul hF).stronglyMeasurable.integral_prod_left'.measurable
  have hn (r : ℝ) : ‖∫ ξ, c ξ*F (ξ,r)‖ ≤ (∫ ξ, ‖c ξ‖)*C := by
    apply (norm_integral_le_integral_norm _).trans
    simp only [norm_mul]
    have hi := integrable_coeff_norm_power volume c (fun ξ => F (ξ,r)) hic
      (hF.comp (measurable_id.prodMk measurable_const)) hC (fun ξ => hb (ξ,r)) 1
    apply (integral_mono (by simpa using hi) (hic.norm.mul_const C)
      (fun ξ => mul_le_mul_of_nonneg_left (hb (ξ,r)) (norm_nonneg _))).trans_eq
    exact integral_mul_const _ _
  refine ⟨hm,hn,?_⟩
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable
    (((∫ ξ, ‖c ξ‖)*C)^2)
  filter_upwards with r
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hn r) 2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem inversePhasedBound_nonneg (d : PositiveDistanceData) (j : ℕ) :
    0 ≤ d.inversePhasedBound j := by
  have hC := zero_le_one.trans (symbolDerivativeConstant_one_le (2*j))
  unfold inversePhasedBound levelMass
  positivity

theorem inversePhasedForm_data (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)) :
    Measurable (fun p : Plane × ℝ => d.inversePhasedForm b.2 p.1 p.2) ∧
      ∀ p : Plane × ℝ, ‖d.inversePhasedForm b.2 p.1 p.2‖ ≤ d.inversePhasedBound j := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  constructor
  · exact spatialPhasedDistanceF_joint_measurable _ d.ρ d.ρ _ _ d.levelMass d.levelMass
      _ _ _ (measurable_sourceConeCircle _) (d.inverseEndpointSymbol_measurable b.2 0)
      (d.inverseEndpointSymbol_measurable b.2 1) (by norm_num) hC hC
      (sourceConeCircle_norm_le _) (d.inverseEndpointSymbol_norm hQ j hb 0)
      (d.inverseEndpointSymbol_norm hQ j hb 1)
  · intro p
    apply sourceDistanceF_norm_le d.ρ d.ρ _ _
      (show 0 < d.levelMass by unfold levelMass; positivity)
      (show 0 < d.levelMass by unfold levelMass; positivity)
      _ _ _ (by norm_num) hC hC (sourceConeCircle_norm_le _)
    · intro x hx ω
      rw [spatialPhasedSymbol_norm]
      exact d.inverseEndpointSymbol_norm hQ j hb 0 x ω
    · intro y hy ω
      rw [spatialPhasedSymbol_norm]
      exact d.inverseEndpointSymbol_norm hQ j hb 1 y ω

theorem inverseSpatialMixture_data (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (d.inverseSpatialMixture j b.2) ∧
    (∀ r, ‖d.inverseSpatialMixture j b.2 r‖ ≤
      spatialFourierCost 96 2004 (by norm_num) (by norm_num) j*d.inversePhasedBound j) ∧
    Integrable (fun r => ‖d.inverseSpatialMixture j b.2 r‖^2) μ := by
  have hd := d.inversePhasedForm_data hQ j hb
  exact continuous_shell_mixture_bound μ _
    (spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j).continuous.measurable
    (spatialFourierCoeff_integrable _ _ _ _ _) _ hd.1 (d.inversePhasedBound_nonneg j) hd.2

theorem inverseSpatialMixture_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ}
    (hB : ∀ ξ, (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseSpatialMixture j b.2 r‖^2 ∂μ) ≤
      (spatialFourierCost 96 2004 (by norm_num) (by norm_num) j)^2*B := by
  have hd := d.inversePhasedForm_data hQ j hb
  exact continuous_coefficient_shell_square μ _
    (spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j).continuous.measurable
    (spatialFourierCoeff_integrable _ _ _ _ _) _ hd.1 (d.inversePhasedBound_nonneg j) hd.2 hB

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellOrderForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

theorem inverseOrderForm_shell_oai (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hsig : 0 ≤ d.sig) (hq : 0 < d.q)
    (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (j : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
      (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseOrderForm j v r‖^2 ∂μ) ≤
      (spatialFourierCost 96 2004 (by norm_num) (by norm_num) j *
        ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b => ‖b.1‖)).sum)^2*B := by
  let C := spatialFourierCost 96 2004 (by norm_num) (by norm_num) j
  have hC : 0 ≤ C := spatialFourierCost_nonneg ..
  let L := inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)
  let F := fun b : ℂ × (PairMaskIndex → ℕ) =>
    fun r => d.absorbedInverseCoefficient j v b*d.inverseSpatialMixture j b.2 r
  have ht (b : ℂ × (PairMaskIndex → ℕ)) (hb : b ∈ L) :
      Measurable (F b) ∧ Integrable (fun r => ‖F b r‖^2) μ ∧
        (∫ r, ‖F b r‖^2 ∂μ) ≤ (‖b.1‖*C)^2*B := by
    have hd := d.inverseSpatialMixture_data hQ j hb μ
    have hcoeff := d.absorbedInverseCoefficient_norm hsig hq hqs hw hv j hb
    have hm := shell_multiplier_square μ (fun _ => d.absorbedInverseCoefficient j v b)
      (d.inverseSpatialMixture j b.2) measurable_const hd.1 hd.2.2 (norm_nonneg b.1)
      (Eventually.of_forall (fun _ => hcoeff))
    refine ⟨hd.1.const_mul _,hm.1,?_⟩
    apply hm.2.trans
    apply (mul_le_mul_of_nonneg_left (d.inverseSpatialMixture_shell hQ j hb μ (hB b hb))
      (sq_nonneg ‖b.1‖)).trans_eq
    dsimp [C]
    ring
  have hh := list_weighted_shell_square L μ F (fun b => ‖b.1‖*C)
    (fun b _ => mul_nonneg (norm_nonneg _) hC)
    (fun b hb => (ht b hb).2.1) (fun b hb => (ht b hb).1.aestronglyMeasurable)
    (fun b hb => (ht b hb).2.2)
  have he : (L.map (fun b => ‖b.1‖*C)).sum = C*(L.map (fun b => ‖b.1‖)).sum := by
    rw [List.sum_map_mul_right]
    ring
  rw [he] at hh
  exact hh

end PositiveDistanceData

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell_oai := @OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell_oai
