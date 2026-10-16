-- Prove2me | solution 1 for OAI.DiagonalForms.System.comparison_resolvent_average
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:17:58.477215+00:00
-- url     : https://prove2.me/submissions/30174dc5-54f3-4fc8-9b37-f247ded656b2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L782-L817
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.comparison_resolvent_average. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Theorems.Thm_OAI_DiagonalForms_System_comparison_harmonic_sum_nonneg
import Theorems.Thm_OAI_DiagonalForms_System_comparison_inverse_integral
import Theorems.Thm_OAI_DiagonalForms_System_comparison_parallel
import Theorems.Thm_OAI_DiagonalForms_System_integral_comp_simpleFunc
import Theorems.Thm_OAI_DiagonalForms_System_integral_compactApprox_tendsto

-- ---- from OAI.Analysis.DiagonalForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
end DiagonalForms.System

namespace QuantumCalculus
end QuantumCalculus

namespace DiagonalForms.System
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

end DiagonalForms.System

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace DiagonalForms

namespace System

variable {P I J : Type*} (D : System P I J)

theorem source_summable (w : P → ℝ) (z : D.tests) :
    Summable (fun i => w (D.sourceParam i) * Complex.normSq (z.val i)) := by
  classical
  obtain ⟨s, hs⟩ := D.finite_values z
  let B : ℝ := ∑ p ∈ s, |w p|
  apply Summable.of_norm_bounded ((D.mass_summable z).mul_left B)
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
  by_cases hz : z.val i = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun p _ => abs_nonneg (w p)) (hs i hz)) (Complex.normSq_nonneg _)

theorem comparison_add {v w : P → ℝ} (hv : D.Comparison v) (hw : D.Comparison w) :
    D.Comparison (fun p => v p + w p) := by
  intro z s
  simp only [add_mul, Finset.sum_add_distrib]
  simp only [sourceForm, add_mul]
  rw [(D.source_summable v z).tsum_add (D.source_summable w z)]
  exact add_le_add (hv z s) (hw z s)

theorem comparison_smul {w : P → ℝ} (hw : D.Comparison w) {a : ℝ} (ha : 0 ≤ a) :
    D.Comparison (fun p => a * w p) := by
  intro z s
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [sourceForm, mul_assoc, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hw z s) ha

theorem sourceForm_finite (z : D.tests) :
    ∃ (s : Finset P) (c : P → ℝ), ∀ w : P → ℝ,
      D.sourceForm w z = ∑ p ∈ s, w p * c p := by
  classical
  obtain ⟨s, hs⟩ := D.finite_values z
  let c (p : P) : ℝ := ∑' i, if p = D.sourceParam i then Complex.normSq (z.val i) else 0
  refine ⟨s, c, ?_⟩
  intro w
  have hsum (p : P) : Summable (fun i => if p = D.sourceParam i then Complex.normSq (z.val i) else 0) := by
    apply Summable.of_nonneg_of_le _ _ (D.mass_summable z)
    · intro i
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl
    · intro i
      split_ifs
      · exact le_rfl
      · exact Complex.normSq_nonneg _
  simp only [c, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun p _ => (hsum p).mul_left (w p))]
  apply tsum_congr
  intro i
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hz : z.val i = 0
  · simp [hz]
  · simp [hs i hz]

theorem sourceForm_tendsto {α : Type*} {l : Filter α} {w : α → P → ℝ} {v : P → ℝ}
    (h : ∀ p, Tendsto (fun a => w a p) l (𝓝 (v p))) (z : D.tests) :
    Tendsto (fun a => D.sourceForm (w a) z) l (𝓝 (D.sourceForm v z)) := by
  obtain ⟨s, c, hc⟩ := D.sourceForm_finite z
  simp_rw [hc]
  exact tendsto_finsetSum s (fun p _ => (h p).mul_const (c p))

theorem comparison_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {w : α → P → ℝ} {v : P → ℝ} (hw : ∀ a, D.Comparison (w a))
    (hlim : ∀ p, Tendsto (fun a => w a p) l (𝓝 (v p))) : D.Comparison v := by
  intro z s
  exact le_of_tendsto_of_tendsto
    (tendsto_finsetSum s (fun j _ => (hlim _).mul_const _))
    (D.sourceForm_tendsto hlim z) (Eventually.of_forall (fun a => hw a z s))

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem parallel_inv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    parallel x⁻¹ y⁻¹ = (x + y)⁻¹ := by
  unfold parallel
  field_simp
  ring

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem comparison_harmonic_sum_add {K : Type*} (s : Finset K)
    {v : P → ℝ} {w : K → P → ℝ} {c : K → ℝ}
    (hv : D.Comparison v) (hvp : ∀ p, 0 < v p)
    (hc : ∀ k ∈ s, 0 ≤ c k) (hwp : ∀ k ∈ s, ∀ p, 0 < w k p)
    (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => ((v p)⁻¹ + ∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert k s hk ih =>
    have hcs : ∀ j ∈ s, 0 ≤ c j := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    have hws : ∀ j ∈ s, ∀ p, 0 < w j p := fun j hj => hwp j (Finset.mem_insert_of_mem hj)
    have hcomp := ih hcs hws (fun j hj => hw j (Finset.mem_insert_of_mem hj))
    have hk0 := hc k (Finset.mem_insert_self k s)
    rcases eq_or_lt_of_le hk0 with he | hp
    · simpa only [Finset.sum_insert hk, ← he, zero_div, zero_add] using hcomp
    · have hsmall := D.comparison_smul (hw k (Finset.mem_insert_self k s))
        (le_of_lt (inv_pos.mpr hp))
      have hsmall' : D.Comparison (fun p => (c k / w k p)⁻¹) := by
        simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm] using hsmall
      have hsum (p : P) : 0 < (v p)⁻¹ + ∑ j ∈ s, c j / w j p :=
        add_pos_of_pos_of_nonneg (inv_pos.mpr (hvp p))
          (Finset.sum_nonneg (fun j hj => div_nonneg (hcs j hj) (hws j hj p).le))
      have hkp (p : P) : 0 < c k / w k p :=
        div_pos hp (hwp k (Finset.mem_insert_self k s) p)
      have h := D.comparison_parallel hsmall' hcomp
        (fun p => inv_pos.mpr (hkp p)) (fun p => inv_pos.mpr (hsum p))
      simpa only [parallel_inv (hkp _) (hsum _), Finset.sum_insert hk, add_left_comm] using h

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

include k₀ in
theorem comparison_inverse_integral_add {v : P → ℝ} {w : K → P → ℝ}
    (hv : D.Comparison v) (hvp : ∀ p, 0 < v p)
    (hcont : ∀ p, Continuous (fun k => w k p)) (hwp : ∀ k p, 0 < w k p)
    (hw : ∀ k, D.Comparison (w k)) :
    D.Comparison (fun p => ((v p)⁻¹ + ∫ k, (w k p)⁻¹ ∂μ)⁻¹) := by
  apply D.comparison_tendsto (l := atTop)
    (w := fun n p => ((v p)⁻¹ + ∫ k, (w (compactApprox k₀ n k) p)⁻¹ ∂μ)⁻¹)
  · intro n
    have he (p : P) := integral_comp_simpleFunc μ (compactApprox k₀ n) (fun k => (w k p)⁻¹)
    simp_rw [he]
    simpa only [div_eq_mul_inv, Measure.real] using D.comparison_harmonic_sum_add
      (compactApprox k₀ n).range hv hvp (fun _ _ => ENNReal.toReal_nonneg)
      (fun k _ => hwp k) (fun k _ => hw k)
  · intro p
    apply Tendsto.inv₀
    · exact tendsto_const_nhds.add (integral_compactApprox_tendsto μ k₀
        ((hcont p).inv₀ (fun k => (hwp k p).ne')))
    · exact ne_of_gt (add_pos_of_pos_of_nonneg (inv_pos.mpr (hvp p))
        (integral_nonneg (fun k => inv_nonneg.mpr (hwp k p).le)))

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
theorem unitInterval_volume : (volume : Measure UnitInterval) Set.univ = 1 := by
  simp [UnitInterval]

theorem affine_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (t : UnitInterval) :
    0 < (1 - t.val) * X + t.val * Y := by
  rcases t.property.1.eq_or_lt with ht | ht
  · simp [← ht, hX]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) hX.le) (mul_pos ht hY)
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

theorem resolvent_kernel_pos {q r : ℝ} (hq : 0 < q) (hr : r ∈ Icc 0 1) :
    0 < 1+(q-1)*r := by
  have h := affine_pos (X := 1) (Y := q) (by norm_num) hq ⟨r, hr⟩
  dsimp at h
  nlinarith

include k₀ in
theorem comparison_resolvent {m q : P → ℝ} {c : ℝ} (hc : 0 ≤ c)
    {r : K → ℝ} (hrc : Continuous r) (hr : ∀ k, r k ∈ Icc 0 1)
    (hm : ∀ p, 0 < m p) (hq : ∀ p, 0 < q p)
    (hmcomp : D.Comparison m) (hqcomp : D.Comparison (fun p => m p*q p)) :
    D.Comparison (fun p => m p / resolventWeight μ c r (q p)) := by
  let v (p : P) := ((m p*q p)⁻¹+c/(m p))⁻¹
  have hv : D.Comparison v := by
    have h := D.comparison_harmonic_sum_nonneg (Finset.univ : Finset (Fin 2))
      (w := fun i p => if i = 0 then m p*q p else m p)
      (c := fun i => if i = 0 then 1 else c)
      (by intro i _; split_ifs; norm_num; exact hc)
      (by intro i _ p; split_ifs; exact mul_pos (hm p) (hq p); exact hm p)
      (by intro i _; split_ifs; exact hqcomp; exact hmcomp)
    simpa [v, Fin.sum_univ_two] using h
  have hvp (p : P) : 0 < v p := inv_pos.mpr
    (add_pos_of_pos_of_nonneg (inv_pos.mpr (mul_pos (hm p) (hq p)))
      (div_nonneg hc (hm p).le))
  let w (k : K) (p : P) := m p*(1+(q p-1)*r k)
  have hwp (k : K) (p : P) : 0 < w k p :=
    mul_pos (hm p) (resolvent_kernel_pos (hq p) (hr k))
  have hw (k : K) : D.Comparison (w k) := by
    have h := D.comparison_add (D.comparison_smul hmcomp (sub_nonneg.mpr (hr k).2))
      (D.comparison_smul hqcomp (hr k).1)
    convert h using 1
    funext p
    dsimp [w]
    ring
  have hwc (p : P) : Continuous (fun k => w k p) := by
    dsimp [w]
    fun_prop
  have h := D.comparison_inverse_integral_add μ k₀ hv hvp hwc hwp hw
  convert h using 1
  funext p
  dsimp [v, w, resolventWeight]
  simp only [inv_inv, mul_inv_rev]
  rw [integral_mul_const]
  simp only [div_eq_mul_inv]
  rw [show (q p)⁻¹ * (m p)⁻¹ + c*(m p)⁻¹ +
      (∫ k, (1+(q p-1)*r k)⁻¹ ∂μ)*(m p)⁻¹ =
      ((q p)⁻¹+c+∫ k, (1+(q p-1)*r k)⁻¹ ∂μ)*(m p)⁻¹ by ring]
  simp only [mul_inv_rev, inv_inv]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure μ] in
theorem resolventWeight_pos {c : ℝ} (hc : 0 ≤ c) {r : K → ℝ}
    (hr : ∀ k, r k ∈ Icc 0 1) {q : ℝ} (hq : 0 < q) :
    0 < resolventWeight μ c r q := by
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (inv_pos.mpr hq) hc)
    (integral_nonneg (fun k => inv_nonneg.mpr (resolvent_kernel_pos hq (hr k)).le))

theorem continuous_resolvent_affine {c : ℝ} {r : K → ℝ} (hrc : Continuous r)
    (hr : ∀ k, r k ∈ Icc 0 1) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Continuous (fun θ : UnitInterval =>
      resolventWeight μ c r ((1-θ.val)*s+θ.val*t)) := by
  have hk : Continuous (fun z : UnitInterval × K =>
      (1+(((1-z.1.val)*s+z.1.val*t)-1)*r z.2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro z
      exact (resolvent_kernel_pos (affine_pos hs ht z.1) (hr z.2)).ne'
  have hi : Continuous (fun θ : UnitInterval =>
      ∫ k, (1+(((1-θ.val)*s+θ.val*t)-1)*r k)⁻¹ ∂μ) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := μ) hk isCompact_univ)
  exact ((by fun_prop : Continuous (fun θ : UnitInterval => (1-θ.val)*s+θ.val*t)).inv₀
    (fun θ => (affine_pos hs ht θ).ne') |>.add continuous_const).add hi

theorem comparison_resolvent_average (k₀ : K) {m s t : P → ℝ} {c : ℝ} (hc : 0 ≤ c)
    {r : K → ℝ} (hrc : Continuous r) (hr : ∀ k, r k ∈ Icc 0 1)
    (hm : ∀ p, 0 < m p) (hs : ∀ p, 0 < s p) (ht : ∀ p, 0 < t p)
    (hmc : D.Comparison m) (hsc : D.Comparison (fun p => m p*s p))
    (htc : D.Comparison (fun p => m p*t p)) :
    D.Comparison (fun p => m p / ∫ θ : UnitInterval,
      resolventWeight μ c r ((1-θ.val)*s p+θ.val*t p)) := by
  let q (θ : UnitInterval) (p : P) := (1-θ.val)*s p+θ.val*t p
  have hqc (θ : UnitInterval) : D.Comparison (fun p => m p*q θ p) := by
    have h := D.comparison_add (D.comparison_smul hsc (sub_nonneg.mpr θ.property.2))
      (D.comparison_smul htc θ.property.1)
    convert h using 1
    funext p
    dsimp [q]
    ring
  have hqp (θ : UnitInterval) (p : P) : 0 < q θ p := affine_pos (hs p) (ht p) θ
  have hw (θ : UnitInterval) :
      D.Comparison (fun p => m p / resolventWeight μ c r (q θ p)) :=
    D.comparison_resolvent μ k₀ hc hrc hr hm (hqp θ) hmc (hqc θ)
  have hwp (θ : UnitInterval) (p : P) :
      0 < m p / resolventWeight μ c r (q θ p) :=
    div_pos (hm p) (resolventWeight_pos μ hc hr (hqp θ p))
  have hcont (p : P) : Continuous (fun θ : UnitInterval =>
      m p / resolventWeight μ c r (q θ p)) := by
    exact continuous_const.div (continuous_resolvent_affine μ hrc hr (hs p) (ht p))
      (fun θ => (resolventWeight_pos μ hc hr (hqp θ p)).ne')
  have hμ : (volume : Measure UnitInterval) ≠ 0 := by
    intro h
    have h1 := unitInterval_volume
    rw [h] at h1
    simp at h1
  have h := D.comparison_inverse_integral volume ⟨0, by norm_num⟩ hμ hcont hwp hw
  convert h using 1
  funext p
  dsimp [q]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, integral_mul_const]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalForms OAI.DiagonalForms.System
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open MeasureTheory Set


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.comparison_resolvent_average := @_root_.OAI.DiagonalForms.System.comparison_resolvent_average
