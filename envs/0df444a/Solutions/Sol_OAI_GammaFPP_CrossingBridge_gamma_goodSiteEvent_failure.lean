-- Prove2me | solution 1 for OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:57:07.173836+00:00
-- url     : https://prove2.me/submissions/f2c31db3-9a94-4bf5-9b07-8b4723d173e9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000
import Theorems.Thm_OAI_GammaFPP_IntervalTravelBridge_gamma_moving_goodOrigin_failure_tendsto

section
-- module Solutions.OAIW2_GammaFPP.Compat
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ProbabilityFoundations
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem measurableSet_strict_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds < bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_lt (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

theorem measurableSet_bounded_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds ≤ bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_le (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_CoordinateTails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem straightEdge_injective (p : Vertex) (d : Step) :
    Function.Injective (straightEdge p d) := by
  intro i j h
  cases d <;> simp [straightEdge, Step.edge, Step.delta, Prod.ext_iff] at h <;> omega

theorem pathCost_replicate (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ i ∈ range n, w (straightEdge p d i) := by
  induction n generalizing p with
  | zero => simp [pathCost]
  | succ n ih =>
    rw [List.replicate_succ, pathCost, ih, sum_range_succ']
    simp [straightEdge, Nat.cast_add, add_smul, add_assoc, add_comm]

theorem pathCost_replicate_edgeSet (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ e ∈ (range n).image (straightEdge p d), w e := by
  rw [sum_image (fun i _ j _ hij => straightEdge_injective p d hij)]
  exact pathCost_replicate w p d n

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ExtremeSlopes
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem extreme_slopes_ordered (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    leftSlope φ ≤ rightSlope φ :=
  hφ.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

theorem subgradient_of_between_slopes (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (a : ℝ) (hleft : leftSlope φ ≤ a) (hright : a ≤ rightSlope φ) :
    ∀ t, φ 0 + a * t ≤ φ t := by
  intro t
  rcases lt_trichotomy 0 t with ht | rfl | ht
  · have hbound := hφ.rightDeriv_le_slope_of_mem_interior (by simp) (by simp) ht
    have ha : a ≤ (φ t - φ 0) / t := by
      exact le_trans hright (by simpa [rightSlope, slope_def_field] using hbound)
    have := (le_div_iff₀ ht).mp ha
    linarith
  · simp
  · have hbound := hφ.slope_le_leftDeriv_of_mem_interior (by simp) (by simp) ht
    have ha : (φ 0 - φ t) / (0 - t) ≤ a := by
      exact le_trans (by simpa [leftSlope, slope_def_field] using hbound) hleft
    have := (div_le_iff₀ (show 0 < 0 - t by linarith)).mp ha
    linarith

theorem extreme_subgradients (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    (∀ t, φ 0 + leftSlope φ * t ≤ φ t) ∧
    (∀ t, φ 0 + rightSlope φ * t ≤ φ t) := by
  have horder := extreme_slopes_ordered φ hφ
  exact ⟨subgradient_of_between_slopes φ hφ _ le_rfl horder,
    subgradient_of_between_slopes φ hφ _ horder le_rfl⟩

theorem extreme_slopes_contact (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    HasDerivWithinAt φ (leftSlope φ) (Iio 0) 0 ∧
    HasDerivWithinAt φ (rightSlope φ) (Ioi 0) 0 := by
  exact ⟨hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp),
    hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)⟩

theorem convex_transverse_profile {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z) :
    ConvexOn ℝ univ (fun t : ℝ => μ (u + t • e)) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  simp only [smul_eq_mul]
  have heq : u + (a * v + b * w) • e = a • (u + v • e) + b • (u + w • e) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm,
      ← add_smul, hab, one_smul, ← add_smul]
  rw [heq]
  exact (hadd _ _).trans_eq (by rw [hhom a ha, hhom b hb])

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_PlaneGeometry
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem plane_reconstruction (b : ℝ) (z : Plane) :
    z = xCoord z • direction b + rCoord b z • transverseUnit := by
  ext i
  fin_cases i <;> simp [direction, transverseUnit, PiLp.add_apply, PiLp.smul_apply]
  ring

theorem norm_positive_homogeneous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z := by
  intro t ht z
  rw [hμ.homogeneous, abs_of_nonneg ht]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_SpatialModulus
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

theorem latticeBox_card (n : ℕ) : (latticeBox n).card = (2*n+1)^2 := by
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [latticeBox, hi, pow_two]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem summable_box_connection_bound {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => (2*(n : ℝ)+1)^4 * (2 * Real.exp (-ε*n/4))) := by
  have hs (k : ℕ) := Real.summable_pow_mul_exp_neg_nat_mul k
    (show 0 < ε/4 by linarith)
  have ht := (((((hs 4).mul_left 32).add ((hs 3).mul_left 64)).add
    ((hs 2).mul_left 48)).add ((hs 1).mul_left 16)).add ((hs 0).mul_left 2)
  apply ht.congr
  intro n
  simp only [pow_one, pow_zero]
  have he : -(ε/4)*(n : ℝ) = -ε*n/4 := by ring
  rw [he]
  ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_SupportContactEstimate
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

theorem derivative_remainder_radius (φ : ℝ → ℝ) (a : ℝ) (S : Set ℝ)
    (ha : HasDerivWithinAt φ a S 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ S, |t| ≤ r → |φ t-φ 0-a*t| ≤ ε*|t| := by
  have hh := ha.isLittleO.bound hε
  simp only [sub_zero,smul_eq_mul,Real.norm_eq_abs] at hh
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhdsWithin_iff.mp hh
  refine ⟨r/2,by linarith,?_⟩
  intro t ht htr
  have hball : t ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    linarith
  simpa only [mem_ofPred_eq,mul_comm t a] using hh ⟨hball,ht⟩

theorem norm_extreme_support_contact (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (plus : Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ contactSide plus, |t| ≤ r →
      0 ≤ μ (direction b+t • transverseUnit)-μ (direction b)-extremeSlope μ b plus*t ∧
      μ (direction b+t • transverseUnit)-μ (direction b)-extremeSlope μ b plus*t ≤ ε*|t| := by
  let φ := fun t : ℝ => μ (direction b+t • transverseUnit)
  have hφ := convex_transverse_profile μ (direction b) transverseUnit
    hμ.triangle (norm_positive_homogeneous μ hμ)
  have hc := extreme_slopes_contact φ hφ
  have hs := extreme_subgradients φ hφ
  have hd : HasDerivWithinAt φ (extremeSlope μ b plus) (contactSide plus) 0 := by
    cases plus <;> simp only [extremeSlope,contactSide,Bool.false_eq_true,ite_false,ite_true]
    · exact hc.1
    · exact hc.2
  obtain ⟨r,hr,hh⟩ := derivative_remainder_radius φ (extremeSlope μ b plus)
    (contactSide plus) hd ε hε
  refine ⟨r,hr,?_⟩
  intro t ht htr
  have he := (le_abs_self _).trans (hh t ht htr)
  have hl : φ 0+extremeSlope μ b plus*t ≤ φ t := by
    cases plus
    · exact hs.1 t
    · exact hs.2 t
  simp only [φ,zero_smul,add_zero] at he hl
  exact ⟨by linarith,he⟩

theorem connector_support_gap (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (plus : Bool) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      D0*s ≤ xCoord z → rCoord b z ∈ contactSide plus → |rCoord b z| ≤ 3*C*s →
      μ z-(μ (direction b)*xCoord z+extremeSlope μ b plus*rCoord b z) ≤ ε*s/4 := by
  obtain ⟨r,hr,hcontact⟩ := norm_extreme_support_contact μ hμ b plus
    (ε/(12*C)) (by positivity)
  let D0 := max 1 (3*C/r)
  have hD : 1 ≤ D0 := le_max_left _ _
  have hCr : 3*C ≤ D0*r := (div_le_iff₀ hr).mp (le_max_right _ _)
  refine ⟨D0,hD,?_⟩
  intro s hs z hz hside htrans
  have hx : 0 < xCoord z := by nlinarith
  have hratio : rCoord b z / xCoord z ∈ contactSide plus := by
    cases plus <;> simp only [contactSide,Bool.false_eq_true,ite_false,ite_true,
      mem_Iio,mem_Ioi] at hside ⊢
    · exact div_neg_of_neg_of_pos hside hx
    · exact div_pos hside hx
  have hsmall : |rCoord b z/xCoord z| ≤ r := by
    rw [abs_div,abs_of_pos hx]
    apply (div_le_iff₀ hx).mpr
    have h1 := mul_le_mul_of_nonneg_right hCr hs.le
    have h2 := mul_le_mul_of_nonneg_left hz hr.le
    nlinarith
  have hg := (hcontact _ hratio hsmall).2
  have hrepr : z = xCoord z • (direction b+(rCoord b z/xCoord z) • transverseUnit) := by
    rw [smul_add,smul_smul]
    have he : xCoord z*(rCoord b z/xCoord z)=rCoord b z := by field_simp
    rw [he]
    exact plane_reconstruction b z
  have hnorm : μ z = xCoord z*μ (direction b+(rCoord b z/xCoord z) • transverseUnit) := by
    conv_lhs => rw [hrepr]
    rw [hμ.homogeneous,abs_of_pos hx]
  calc
    _ = xCoord z*(μ (direction b+(rCoord b z/xCoord z) • transverseUnit)-
        μ (direction b)-extremeSlope μ b plus*(rCoord b z/xCoord z)) := by
      rw [hnorm]
      field_simp
      ring
    _ ≤ xCoord z*(ε/(12*C)*|rCoord b z/xCoord z|) :=
      mul_le_mul_of_nonneg_left hg hx.le
    _ = ε/(12*C)*|rCoord b z| := by
      rw [abs_div,abs_of_pos hx]
      field_simp
    _ ≤ ε/(12*C)*(3*C*s) := mul_le_mul_of_nonneg_left htrans (by positivity)
    _ = ε*s/4 := by field_simp; ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Stationarity
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {ν : Measure ℝ}

/-- Every measurable configuration observable has translation-invariant law. -/
theorem IidEnvironment.translated_event_probability
    (h : IidEnvironment ν P τ) (a : Vertex)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) :
    P {ω | (fun e => τ (shiftEdge a e) ω) ∈ A} =
      P {ω | (fun e => τ e ω) ∈ A} := by
  have he := congrArg (fun Q : Measure (Edge → ℝ) => Q A)
    ((h.translate a).jointLaw.trans h.jointLaw.symm)
  rw [Measure.map_apply (Measurable.of_eval (fun e => h.measurable _)) hA,
    Measure.map_apply (Measurable.of_eval h.measurable) hA] at he
  exact he

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MGF
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Exponential weighting changes the Gamma rate from `rate` to `rate - theta`. -/
lemma gamma_weighted_density {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (exp (theta * x)) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) *
        gammaPDF shape (rate - theta) x := by
  have hs : 0 < rate - theta := sub_pos.mpr htheta
  have hc : 0 ≤ (rate / (rate - theta)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hrate hs) shape).le
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
    congr 1
    have hexp : exp (-(rate * x)) * exp (theta * x) =
        exp (-((rate - theta) * x)) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) *
          exp (theta * x) =
          rate ^ shape / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (theta * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x)) := by rw [hexp]
      _ = (rate / (rate - theta)) ^ shape *
          ((rate - theta) ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x))) := by
        rw [Real.div_rpow hrate.le hs.le]
        have hpow : (rate - theta) ^ shape ≠ 0 :=
          (Real.rpow_pos_of_pos hs shape).ne'
        have hgamma : Gamma shape ≠ 0 := (Real.Gamma_pos_of_pos hshape).ne'
        field_simp [hpow, hgamma]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- The nonnegative exponential moment from the normalized density with shifted rate. -/
theorem gamma_lintegral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x)) ∂gammaMeasure shape rate) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x))
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_weighted_density hshape hrate htheta]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one hshape (sub_pos.mpr htheta), mul_one]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

lemma IidEnvironment.measurable_edgeSum (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) : Measurable (edgeSum S τ) :=
  Finset.measurable_sum S (fun e _ => h.measurable e)

variable {shape rate theta : ℝ}

/-- The nonnegative exponential moment of a finite iid Gamma edge sum. -/
theorem GammaEnvironment.lintegral_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) =
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card := by
  classical
  let X : PlanarFPP.Edge → Ω → ℝ≥0∞ :=
    fun e ω => ENNReal.ofReal (Real.exp (theta * τ e ω))
  have hX : ∀ e, Measurable (X e) := by
    intro e
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable e)))
  have hXi : iIndepFun X P := h.independent.comp
    (fun _ (x : ℝ) => ENNReal.ofReal (Real.exp (theta * x))) (fun _ => by fun_prop)
  have hpoint (ω : Ω) : ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) =
      ∏ e ∈ S, X e ω := by
    rw [edgeSum, Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun e _ => (Real.exp_pos _).le)
  have hm (e : PlanarFPP.Edge) :
      (∫⁻ ω, X e ω ∂P) = ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
    change (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * τ e ω)) ∂P) = _
    rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (Real.exp (theta * x)))
      (by fun_prop) (h.measurable e), h.marginal e]
    exact gamma_lintegral_exp hshape hrate htheta
  simp_rw [hpoint]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun S X hXi hX]
  simp only [hm, Finset.prod_const]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate theta : ℝ}

/-- Exponential Markov bound for a real parameter `theta` and an arbitrary real threshold. -/
theorem GammaEnvironment.exponential_markov_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable_edgeSum S)))
  calc
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
        P {ω | ENNReal.ofReal (Real.exp (theta * a)) ≤
          ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) /
        ENNReal.ofReal (Real.exp (theta * a)) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ = _ := by rw [h.lintegral_exp_edgeSum hshape hrate htheta S]

/-- Gamma Chernoff upper-tail estimate for `0 < theta < rate`. -/
theorem GammaEnvironment.upper_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_pos : 0 < theta) (htheta : theta < rate)
    (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | a ≤ edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate htheta S a)
  intro ω hω
  exact mul_le_mul_of_nonneg_left hω htheta_pos.le

/-- Gamma Chernoff lower-tail estimate for `theta < 0`. -/
theorem GammaEnvironment.lower_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_neg : theta < 0) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | edgeSum S τ ω ≤ a} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate (htheta_neg.trans hrate) S a)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω htheta_neg.le

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPath
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

lemma trace_edge_length (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).length = ds.length := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simpa only [trace, List.map_cons, List.length_cons] using
      (congrArg Nat.succ (ih (p + d.delta)))

lemma pathCost_trace_edge_sum (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds = (((trace p ds).map traversalEdge).map w).sum := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [pathCost, trace, List.map_cons, List.sum_cons,
      traversalEdge, ih]

/-- Only a trail's traversal sum can be replaced by its distinct-edge set sum. -/
lemma pathCost_eq_distinct_edgeSum (w : Edge → ℝ) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w p ds = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, w e := by
  classical
  rw [pathCost_trace_edge_sum]
  exact (List.sum_toFinset w hn).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Genuine Gamma lower tail for any fixed trail, with arbitrary real threshold.
The positive parameter s uses the native MGF at theta=-s. -/
theorem GammaEnvironment.cheap_path_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) (t : ℝ) :
    P {ω | pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ ds.length /
        ENNReal.ofReal (Real.exp (-s * t)) := by
  classical
  have hc : ((trace p ds).map traversalEdge).toFinset.card = ds.length := by
    rw [List.toFinset_card_of_nodup hn, trace_edge_length]
  have he (ω : Ω) : edgeSum ((trace p ds).map traversalEdge).toFinset τ ω =
      pathCost (fun e => τ e ω) p ds := by
    exact (pathCost_eq_distinct_edgeSum (fun e => τ e ω) p ds hn).symm
  have hb := h.lower_tail_edgeSum hs hr (neg_neg_of_pos hsp)
    ((trace p ds).map traversalEdge).toFinset t
  simpa only [he, hc, sub_neg_eq_add] using hb

/-- The probability that a finite family contains a cheap trail is bounded by
its cardinality times the single-trail estimate. -/
theorem GammaEnvironment.cheap_path_family_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (F : Finset (List Step)) (n : ℕ)
    (hF : ∀ ds ∈ F, ((trace p ds).map traversalEdge).Nodup ∧ ds.length = n)
    (t : ℝ) :
    P {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (F.card : ℝ≥0∞) * ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
  classical
  have he : {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} =
      ⋃ ds ∈ F, {ω | pathCost (fun e => τ e ω) p ds ≤ t} := by
    ext ω
    simp
  rw [he]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _ds ∈ F, ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
      apply Finset.sum_le_sum
      intro ds hds
      simpa only [(hF ds hds).2] using
        h.cheap_path_probability hs hr s hsp p ds (hF ds hds).1 t
    _ = _ := by simp

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathCounting
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

attribute [local instance] OAI.GammaFPP.cheapStepFintype
private lemma cheapStep_card : Fintype.card Step = 4 := by decide

lemma card_fixedStepLists_le (n : ℕ) : (fixedStepLists n).card ≤ 4 ^ n := by
  classical
  calc
    (fixedStepLists n).card ≤ (Finset.univ : Finset (Fin n → Step)).card :=
      Finset.card_image_le
    _ = 4 ^ n := by rw [Finset.card_univ, Fintype.card_fun, cheapStep_card, Fintype.card_fin]

lemma card_fixedTrailLists_le (p : Vertex) (n : ℕ) :
    (fixedTrailLists p n).card ≤ 4 ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_fixedStepLists_le n)

/-- Exact event equality; there is no hidden restriction to a selected optimizer. -/
lemma fixedTrail_event_eq {Ω : Type*} (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) (t : ℝ) :
    {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} =
    {ω | ∃ ds ∈ fixedTrailLists p n, pathCost (fun e => τ e ω) p ds ≤ t} := by
  ext ω
  simp only [Set.mem_ofPred_eq, mem_fixedTrailLists]
  constructor
  · rintro ⟨ds, hl, hn, hc⟩
    exact ⟨ds, ⟨hl, hn⟩, hc⟩
  · rintro ⟨ds, ⟨hl, hn⟩, hc⟩
    exact ⟨ds, hl, hn, hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual fixed-length trails, with a proved four-way exponential count. -/
theorem GammaEnvironment.cheap_fixed_length_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (n : ℕ) (t : ℝ) :
    P {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} ≤
      ((4 ^ n : ℕ) : ℝ≥0∞) *
        ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
          ENNReal.ofReal (Real.exp (-s * t))) := by
  rw [fixedTrail_event_eq]
  have hb := h.cheap_path_family_probability hs hr s hsp p (fixedTrailLists p n) n
    (fun ds hds => ((mem_fixedTrailLists p n ds).mp hds).symm) t
  refine hb.trans (mul_le_mul_left ?_ _)
  exact_mod_cast card_fixedTrailLists_le p n

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathDecay
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP
open scoped ENNReal

lemma cheapChernoff_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapChernoff shape rate := by
  have hl : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos hr (sub_pos.mpr (Real.one_lt_exp_iff.mpr (div_pos hl hs)))

lemma cheapSlope_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapSlope shape rate :=
  div_pos (Real.log_pos (by norm_num)) (cheapChernoff_pos hs hr)

/-- The exact native Gamma Laplace factor is 1/16 at the chosen parameter. -/
lemma cheapChernoff_factor {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    (rate / (rate + cheapChernoff shape rate)) ^ shape = (1 / 16 : ℝ) := by
  have hd : rate + cheapChernoff shape rate =
      rate * Real.exp (Real.log 16 / shape) := by
    unfold cheapChernoff
    ring
  have hratio : rate / (rate + cheapChernoff shape rate) =
      Real.exp (-(Real.log 16 / shape)) := by
    rw [hd, Real.exp_neg]
    field_simp [hr.ne', Real.exp_ne_zero]
  rw [hratio, ← Real.exp_mul]
  have he : -(Real.log 16 / shape) * shape = -Real.log 16 := by
    field_simp [hs.ne']
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  norm_num

lemma cheapChernoff_mul_slope {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    cheapChernoff shape rate * cheapSlope shape rate = Real.log 2 := by
  unfold cheapSlope
  field_simp [(cheapChernoff_pos hs hr).ne']

/-- Exact cancellation of counting, Laplace factor and linear threshold. -/
lemma cheap_count_bound_eq {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (n : ℕ) :
    (4 : ℝ)^n * (((rate / (rate + cheapChernoff shape rate)) ^ shape)^n /
      Real.exp (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) =
        (1 / 2 : ℝ)^n := by
  rw [cheapChernoff_factor hs hr]
  have he : -cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)) =
      (n : ℝ) * (-Real.log 2) := by
    have hc := cheapChernoff_mul_slope hs hr
    calc
      _ = -(cheapChernoff shape rate * cheapSlope shape rate) * (n : ℝ) := by ring
      _ = _ := by rw [hc]; ring
  rw [he, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← div_pow, ← mul_pow]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual trails of n steps from p are exponentially unlikely to cost at
most c*n. This includes n=0, where the empty path has probability one. -/
theorem GammaEnvironment.cheap_fixed_length_decay_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (n : ℕ) :
    P.real {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧
        pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)} ≤
      (1 / 2 : ℝ)^n := by
  have hsp := cheapChernoff_pos hs hr
  have hbase : 0 ≤ (rate / (rate + cheapChernoff shape rate)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hr (add_pos hr hsp)) shape).le
  have hden : ENNReal.ofReal (Real.exp
      (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfin : ((4 ^ n : ℕ) : ℝ≥0∞) *
      ((ENNReal.ofReal ((rate / (rate + cheapChernoff shape rate)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp
          (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ))))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp)
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden)
  have hb := ENNReal.toReal_mono hfin
    (h.cheap_fixed_length_probability hs hr (cheapChernoff shape rate) hsp p n
      (cheapSlope shape rate * (n : ℝ)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_pow, Nat.cast_ofNat] at hb
  change P.real _ ≤ _ at hb
  rw [cheap_count_bound_eq hs hr n] at hb
  exact hb

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapLongTrails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Exponential decay is summable, including the nonempty bad event at n=0. -/
theorem GammaEnvironment.summable_cheapTrailEvent_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) : Summable (fun n => P.real (cheapTrailEvent shape rate τ p n)) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact hg.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun n => h.cheap_fixed_length_decay_real hs hr p n)

/-- At each fixed start, almost surely all sufficiently long trails have
strictly positive linear cost. No independence across lengths is used. -/
theorem GammaEnvironment.ae_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  let := h.probability
  have hsum : (∑' n, P (cheapTrailEvent shape rate τ p n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (h.summable_cheapTrailEvent_real hs hr p).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, ?_⟩
  intro ds hlen htrail
  by_contra hc
  exact hN ds.length hlen ⟨ds, rfl, htrail, le_of_not_gt hc⟩

/-- Countably many lattice starts may share one event; the length cutoff can
depend on both the environment and the start. -/
theorem GammaEnvironment.ae_all_starts_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  rw [ae_all_iff]
  intro p
  exact h.ae_long_trails_cost hs hr p

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PassageLowerBound
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Filter

/-- Each original nearest-neighbor step contributes at most one L1 unit. -/
lemma displacement_natAbs_sum_le_length (ds : List Step) :
    (displacement ds).1.natAbs + (displacement ds).2.natAbs ≤ ds.length := by
  induction ds with
  | nil => simp [displacement]
  | cons d ds ih =>
      have h₁ := Int.natAbs_add_le d.delta.1 (displacement ds).1
      have h₂ := Int.natAbs_add_le d.delta.2 (displacement ds).2
      have hd : d.delta.1.natAbs + d.delta.2.natAbs = 1 := by
        cases d <;> norm_num [Step.delta]
      simp only [displacement_cons, List.length_cons]
      change (d.delta.1 + (displacement ds).1).natAbs +
        (d.delta.2 + (displacement ds).2).natAbs ≤ ds.length + 1
      omega

/-- Literal latticeDistance, not the product max norm. -/
lemma latticeDistance_endpoint_le_length (p : Vertex) (ds : List Step) :
    latticeDistance p (p + displacement ds) ≤ ds.length := by
  simpa only [latticeDistance, Prod.fst_add, Prod.snd_add, add_sub_cancel_left] using
    displacement_natAbs_sum_le_length ds

/-- Erasure preserves the endpoint, so every sufficiently distant arbitrary
path inherits the long-trail lower bound, even if it repeats edges. -/
lemma pathCost_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) (ds : List Step)
    (hend : p + displacement ds = q) :
    c * (latticeDistance p q : ℝ) < pathCost w p ds := by
  obtain ⟨es, he, hn, hcost⟩ := LoopErase.erase_path_loops w hw p ds
  have hend' : p + displacement es = q := by rw [he, hend]
  have hdist : latticeDistance p q ≤ es.length := by
    simpa only [hend'] using latticeDistance_endpoint_le_length p es
  have hdistR : (latticeDistance p q : ℝ) ≤ (es.length : ℝ) := by
    exact_mod_cast hdist
  exact (mul_le_mul_of_nonneg_left hdistR hc).trans_lt
    ((hN es (hq.trans hdist) hn).trans_le hcost)

/-- Taking the infimum of path costs preserves the non-strict lower bound,
without requiring the existence of a minimizing path. -/
lemma passageTime_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) :
    c * (latticeDistance p q : ℝ) ≤ passageTime w p q := by
  apply le_csInf (path_costs_nonempty w p q)
  rintro t ⟨ds, hend, rfl⟩
  exact (pathCost_lower_of_long_trails w hw c hc p N hN q hq ds hend).le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- On one probability-one event, every lattice start has an eventual metric
lower bound for all distant endpoints. The cutoff may depend on start/sample. -/
theorem GammaEnvironment.ae_all_starts_passageTime_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ q : Vertex,
      N ≤ latticeDistance p q →
        cheapSlope shape rate * (latticeDistance p q : ℝ) ≤
          passageTime (fun e => τ e ω) p q := by
  filter_upwards [h.ae_positive, h.ae_all_starts_long_trails_cost hs hr] with ω hpos hlong
  intro p
  obtain ⟨N, hN⟩ := hlong p
  refine ⟨N, ?_⟩
  intro q hq
  exact passageTime_lower_of_long_trails (fun e => τ e ω) (fun e => (hpos e).le)
    (cheapSlope shape rate) (cheapSlope_pos hs hr).le p N hN q hq

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanPositive
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped Topology ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fatou needs only eventual lower bounds, not samplewise convergence. -/
lemma lower_le_limit_integral_of_ae_eventually [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (a m : ℝ)
    (hX : ∀ n, Measurable (X n)) (hI : ∀ n, Integrable (X n) P)
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω)
    (hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, a ≤ X n ω)
    (hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 m)) (hm : 0 ≤ m) :
    a ≤ m := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (X n ω)
  have hmeas : ∀ n, Measurable (F n) := fun n => (hX n).ennreal_ofReal
  have hpoint : ∀ᵐ ω ∂P, ENNReal.ofReal a ≤ liminf (fun n => F n ω) atTop := by
    filter_upwards [hlower] with ω hω
    exact le_liminf_of_le (h := hω.mono fun n hn => ENNReal.ofReal_le_ofReal hn)
  have hlow : ENNReal.ofReal a ≤ ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P := by
    simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hpoint
  have hfatou := lintegral_liminf_le (μ := P) (u := atTop) hmeas
  have hint (n : ℕ) : (∫⁻ ω, F n ω ∂P) = ENNReal.ofReal (∫ ω, X n ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hI n) (hpos n)).symm
  have ht : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 (ENNReal.ofReal m)) := by
    simpa only [hint] using ENNReal.tendsto_ofReal hlimit
  have hb : ENNReal.ofReal a ≤ ENNReal.ofReal m := by
    simpa only [ht.liminf_eq] using hlow.trans hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hm).mp hb

/-- Literal lattice L1 distance scales under natural multiplication. -/
lemma latticeDistance_zero_nsmul (z : Vertex) (n : ℕ) :
    latticeDistance 0 (n • z) = n * latticeDistance 0 z := by
  simp [latticeDistance, nsmul_eq_mul, Int.natAbs_mul, Nat.mul_add]

variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The actual Fekete mean limit has the same positive linear lower bound as
the eventual path metric. The zero direction is treated before division. -/
theorem GammaEnvironment.directionalMeanConstant_linear_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ directionalMeanConstant h hs hr z := by
  by_cases hz : z = 0
  · subst z
    simp [latticeDistance, h.directionalMeanConstant_zero hs hr]
  let : IsProbabilityMeasure P := h.probability
  have hd : 0 < latticeDistance 0 z := by
    by_contra hn
    have hd0 : latticeDistance 0 z = 0 := Nat.eq_zero_of_not_pos hn
    have hxy : z.1 = 0 ∧ z.2 = 0 := by simpa [latticeDistance] using hd0
    exact hz (Prod.ext hxy.1 hxy.2)
  let X : ℕ → Ω → ℝ := fun n ω => passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
  have hX : ∀ n, Measurable (X n) := fun n =>
    (h.measurable_passageTime 0 (n • z)).div_const (n : ℝ)
  have hI : ∀ n, Integrable (X n) P := fun n =>
    (h.integrable_passageTime hs hr 0 (n • z)).div_const (n : ℝ)
  have hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω := by
    intro n
    filter_upwards [h.ae_positive] with ω hω
    exact div_nonneg (passageTime_nonneg _ (fun e => (hω e).le) 0 (n • z))
      (Nat.cast_nonneg n)
  have hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ X n ω := by
    filter_upwards [h.ae_all_starts_passageTime_lower hs hr] with ω hω
    obtain ⟨N, hN⟩ := hω 0
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hnd : N ≤ latticeDistance 0 (n • z) := by
      rw [latticeDistance_zero_nsmul]
      nlinarith
    have hb := hN (n • z) hnd
    rw [latticeDistance_zero_nsmul, Nat.cast_mul] at hb
    change cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤
      passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop
      (𝓝 (directionalMeanConstant h hs hr z)) := by
    simpa only [X, integral_div, meanPassageSequence] using h.meanPassageSequence_tendsto hs hr z
  exact lower_le_limit_integral_of_ae_eventually X _ _ hX hI hpos hlower hlimit
    (h.directionalMeanConstant_nonneg hs hr z)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanNorm
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Topology

/-- Positive denominators transport a lattice coercivity bound to rationals. -/
lemma rationalMean_lower (m : Vertex → ℝ) (c : ℝ)
    (hm : ∀ x, c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|) ≤ m x)
    (q : ℚ × ℚ) :
    c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ rationalMean m q := by
  let x := rationalNumerator q
  let n := rationalDenominator q
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (rationalDenominator_pos q)
  have he := rationalLatticePoint_numerator_denominator q
  have h₁ : (x.1 : ℝ) / (n : ℝ) = (q.1 : ℝ) := by
    have hq : (x.1 : ℚ) / (n : ℚ) = q.1 := by
      simpa only [rationalLatticePoint] using congrArg Prod.fst he
    exact_mod_cast hq
  have h₂ : (x.2 : ℝ) / (n : ℝ) = (q.2 : ℝ) := by
    have hq : (x.2 : ℚ) / (n : ℚ) = q.2 := by
      simpa only [rationalLatticePoint] using congrArg Prod.snd he
    exact_mod_cast hq
  change _ ≤ m x / (n : ℝ)
  rw [← h₁, ← h₂, abs_div, abs_div, abs_of_pos hn]
  simpa only [← add_div, ← mul_div_assoc] using
    div_le_div_of_nonneg_right (hm x) hn.le

/-- A closed inequality on the rational image holds on its real closure. -/
lemma realMeanExtension_lower {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (c : ℝ) (hl : ∀ q, c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ f q)
    (v : ℝ × ℝ) : c * (|v.1| + |v.2|) ≤ realMeanExtension f v := by
  apply isClosed_property rationalPairCast_dense
    (p := fun v => c * (|v.1| + |v.2|) ≤ realMeanExtension f v) ?_ ?_ v
  · exact isClosed_le
      (continuous_const.mul (continuous_fst.abs.add continuous_snd.abs))
      (realMeanExtension_uniformContinuous hf).continuous
  · intro q
    rw [realMeanExtension_on_rat hf]
    exact hl q

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanPairSeminorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : ℝ × ℝ) :
    cheapSlope shape rate * (|v.1| + |v.2|) ≤ gammaMeanPairSeminorm h hs hr v := by
  change _ ≤ realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v
  have hlip := rationalMean_l1 (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)
  apply realMeanExtension_lower
    (rational_l1_lipschitz _ ⟨shape/rate, (div_pos hs hr).le⟩ hlip).uniformContinuous
  intro q
  apply rationalMean_lower
  intro z
  simpa [latticeDistance] using h.directionalMeanConstant_linear_lower hs hr z

lemma gammaMeanNorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : Plane) : cheapSlope shape rate * (|v 0| + |v 1|) ≤ gammaMeanNorm h hs hr v :=
  gammaMeanPairSeminorm_lower h hs hr (v 0, v 1)

/-- The real extension of the Gamma directional mean constants is a norm. -/
theorem gammaMeanNorm_laws
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    TimeConstantNorm (gammaMeanNorm h hs hr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    exact apply_nonneg (gammaMeanPairSeminorm h hs hr) (v 0, v 1)
  · intro v
    constructor
    · intro hv
      have hb := gammaMeanNorm_lower h hs hr v
      have hc := cheapSlope_pos hs hr
      rw [hv] at hb
      have h₀ : v 0 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      have h₁ : v 1 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      ext i
      fin_cases i
      · exact h₀
      · exact h₁
    · rintro rfl
      change gammaMeanPairSeminorm h hs hr 0 = 0
      exact map_zero _
  · intro v w
    change gammaMeanPairSeminorm h hs hr ((v 0, v 1) + (w 0, w 1)) ≤ _
    exact map_add_le_add (gammaMeanPairSeminorm h hs hr) _ _
  · intro a v
    change gammaMeanPairSeminorm h hs hr (a • (v 0, v 1)) = _
    simpa only [Real.norm_eq_abs, gammaMeanNorm] using map_smul_eq_mul (gammaMeanPairSeminorm h hs hr) a (v 0, v 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealDirectionGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem plane_norm_le_coordinates (v : Plane) : ‖v‖ ≤ |v 0| + |v 1| := by
  let x : Plane := PiLp.single 2 0 (v 0)
  let y : Plane := PiLp.single 2 1 (v 1)
  have hv : v = x+y := by
    ext i
    fin_cases i <;> simp [x,y]
  have hx : ‖x‖ = |v 0| := by simp [x]
  have hy : ‖y‖ = |v 1| := by simp [y]
  calc
    ‖v‖ = ‖x+y‖ := congrArg norm hv
    _ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    _ = _ := by rw [hx,hy]

theorem latticeDistance_le_norm (p q : Vertex) :
    (latticeDistance p q : ℝ) ≤ 2 * ‖latticeEmbed q - latticeEmbed p‖ := by
  have h0 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 0
  have h1 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 1
  have hc (a : ℤ) : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [latticeDistance, Nat.cast_add, hc, Int.cast_sub]
  simpa only [latticeEmbed, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, two_mul] using add_le_add h0 h1

theorem latticeFloor_error (v : Plane) : ‖latticeEmbed (latticeFloor v) - v‖ ≤ 2 := by
  have hi (i : Fin 2) : |(latticeEmbed (latticeFloor v) - v) i| ≤ 1 := by
    have hle := Int.floor_le (v i)
    have hlt := Int.lt_floor_add_one (v i)
    have he : (latticeEmbed (latticeFloor v) - v) i = (⌊v i⌋ : ℝ) - v i := by
      fin_cases i <;> rfl
    rw [he, abs_of_nonpos (by linarith)]
    linarith
  exact (plane_norm_le_coordinates _).trans (by linarith [hi 0, hi 1])

theorem timeConstantNorm_lipschitz_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v w, |μ v - μ w| ≤ B * ‖v-w‖ := by
  let e0 : Plane := PiLp.single 2 0 1
  let e1 : Plane := PiLp.single 2 1 1
  let B := μ e0 + μ e1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [hμ.nonneg e0, hμ.nonneg e1]
  have hu (v : Plane) : μ v ≤ B * ‖v‖ := by
    have he : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    have ht := hμ.triangle (v 0 • e0) (v 1 • e1)
    rw [← he, hμ.homogeneous, hμ.homogeneous] at ht
    have h0 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 0) (hμ.nonneg e0)
    have h1 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 1) (hμ.nonneg e1)
    dsimp [B]
    nlinarith [norm_nonneg v]
  refine ⟨B, hB, ?_⟩
  intro v w
  apply abs_le.mpr
  have h1 := hμ.triangle (v-w) w
  have h2 := hμ.triangle (w-v) v
  simp only [sub_add_cancel] at h1 h2
  have hu1 := hu (v-w)
  have hu2 := hu (w-v)
  rw [norm_sub_rev] at hu2
  constructor <;> linarith

end GammaFPP.RealDirectionBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CoordinateTails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma coordinateAllowance_pos (hs : 0 < shape) (hr : 0 < rate) :
    0 < coordinateAllowance shape rate := by
  unfold coordinateAllowance
  positivity

/-- Exponential upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp ((rate / 2) * t)) := by
  have hp : 0 < rate / 2 := by positivity
  have hl : rate / 2 < rate := by linarith
  have he : rate / (rate - rate / 2) = 2 := by
    have hd : rate - rate / 2 ≠ 0 := (sub_pos.mpr hl).ne'
    field_simp [hd]; ring
  have hb := h.upper_tail_edgeSum hs hr hp hl
    ((range n).image (straightEdge p d)) t
  simpa only [edgeSum, pathCost_replicate_edgeSet, he,
    card_image_of_injective _ (straightEdge_injective p d), card_range] using hb

/-- The real-valued upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      ((2 : ℝ) ^ shape) ^ n * Real.exp (-(rate / 2) * t) := by
  have hbase : 0 ≤ (2 : ℝ) ^ shape := (Real.rpow_pos_of_pos (by norm_num) shape).le
  have hden : ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hn : (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
      ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden
  have hb := ENNReal.toReal_mono hn (h.costly_straight_probability hs hr p d n t)
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hbase, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hb
  change P.real _ ≤ _ at hb
  rw [show -(rate / 2) * t = -((rate / 2) * t) by ring, Real.exp_neg]
  simpa only [div_eq_mul_inv] using hb

lemma gamma_half_rate_mgf_bound (hs : 0 < shape) :
    (2 : ℝ) ^ shape ≤ Real.exp (shape + 1) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hb ⊢
    exact hb
  nlinarith

/-- Exponential tail above the linear allowance, for every real excess `t`. -/
theorem GammaEnvironment.costly_straight_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (n : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      Real.exp (-(rate / 2) * t) := by
  refine (h.costly_straight_probability_real hs hr p d n
    (coordinateAllowance shape rate * n + t)).trans ?_
  have hp : ((2 : ℝ) ^ shape) ^ n ≤ Real.exp ((n : ℝ) * (shape + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) shape).le
      (gamma_half_rate_mgf_bound hs) n
  calc
    ((2 : ℝ) ^ shape) ^ n *
        Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) ≤
        Real.exp ((n : ℝ) * (shape + 1)) *
          Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-(rate / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      unfold coordinateAllowance
      field_simp [hr.ne']; ring

theorem GammaEnvironment.costly_horizontal_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (horizontal a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.east a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.west (-a).toNat t

theorem GammaEnvironment.costly_vertical_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (vertical a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.north a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.south (-a).toNat t

/-- A union bound for the two coordinate legs, counting every edge traversal. -/
theorem GammaEnvironment.costly_coordinatePath_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ≤
      2 * Real.exp (-(rate / 4) * t) := by
  let := h.probability
  let A := {ω | coordinateAllowance shape rate * ((q.1-p.1).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) p (horizontal (q.1-p.1))}
  let B := {ω | coordinateAllowance shape rate * ((q.2-p.2).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) (p + displacement (horizontal (q.1-p.1)))
      (vertical (q.2-p.2))}
  have hsub : {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ⊆ A ∪ B := by
    intro ω hω
    change _ ∨ _
    by_contra hn
    push Not at hn
    simp only [Set.mem_ofPred_eq, coordinatePath, pathCost_append, latticeDistance,
      Nat.cast_add] at hω
    simp only [A, B, Set.mem_ofPred_eq, not_le] at hn
    linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le A B).trans ?_)
  have ha := h.costly_horizontal_excess_probability_real hs hr p (q.1-p.1) (t/2)
  have hb := h.costly_vertical_excess_probability_real hs hr
    (p + displacement (horizontal (q.1-p.1))) (q.2-p.2) (t/2)
  change P.real A + P.real B ≤ _
  change P.real A ≤ _ at ha
  change P.real B ≤ _ at hb
  have he : -(rate / 2) * (t / 2) = -(rate / 4) * t := by ring
  rw [he] at ha hb
  linarith

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialModulus
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory PlanarFPP Finset Filter Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Finite union bound over all ordered pairs, without independence of path events. -/
theorem GammaEnvironment.gammaBadConnections_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (ε : ℝ) (n : ℕ) :
    P.real (gammaBadConnections shape rate τ ε n) ≤
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n))) := by
  let := h.probability
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _pq ∈ (latticeBox n) ×ˢ (latticeBox n),
        2 * Real.exp (-(rate / 4) * (ε * n)) :=
      sum_le_sum (fun pq _ => h.costly_coordinatePath_probability_real hs hr pq.1 pq.2 (ε * n))
    _ = _ := by simp [latticeBox_card]; ring

/-- The only summability requirement is positive rate times positive epsilon. -/
theorem summable_gamma_box_connection_bound {rate ε : ℝ}
    (hr : 0 < rate) (hε : 0 < ε) :
    Summable (fun n : ℕ =>
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n)))) := by
  apply (PlanarFPP.summable_box_connection_bound (mul_pos hr hε)).congr
  intro n
  have he : -(rate * ε) * (n : ℝ) / 4 = -(rate / 4) * (ε * n) := by ring
  rw [he]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OriginEscape
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.UniformShapeBridge
open MeasureTheory Filter Set
open scoped Topology

theorem pathCost_take_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (i : ℕ) :
    pathCost w p (ds.take i) ≤ pathCost w p ds := by
  have he := pathCost_append w p (ds.take i) (ds.drop i)
  rw [List.take_append_drop] at he
  have hn := pathCost_nonneg hw (p+displacement (ds.take i)) (ds.drop i)
  linarith

theorem path_confined_of_escape (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (R a : ℝ)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hcost : pathCost w p ds < a) :
    PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  intro i _
  change ‖latticeEmbed (p+displacement (ds.take i)-p)‖ < R
  by_contra hn
  have he := hescape (p+displacement (ds.take i)) (le_of_not_gt hn)
  have hp := passageTime_le_cost w hw p (p+displacement (ds.take i)) (ds.take i) rfl
  have ht := pathCost_take_le w hw p ds i
  linarith

/-- Approximate passage-time minimizers with any positive error bound control
the cost of escaping a ball. -/
theorem exists_confined_near_optimal (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R a ε : ℝ) (hε : 0 < ε)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hshort : passageTime w p q + ε ≤ a) :
    ∃ ds, p+displacement ds=q ∧ pathCost w p ds < passageTime w p q+ε ∧
      PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  exact ⟨ds,hend,hcost,path_confined_of_escape w hw p ds R a hescape (hcost.trans_le hshort)⟩

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MovingOrigin
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem measurableSet_goodOrigin (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ) :
    MeasurableSet {w | GoodOrigin μ α C η δ n w} := by
  unfold GoodOrigin
  simp only [ofPred_and, ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun e => ?_) ?_
  · exact measurableSet_le measurable_const (measurable_pi_apply e)
  refine MeasurableSet.inter (MeasurableSet.iInter fun z => ?_)
    (MeasurableSet.iInter fun z => ?_)
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (continuous_abs.measurable.comp ((measurable_passageTime measurable_pi_apply 0 z).sub_const _))
      measurable_const
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le measurable_const (measurable_passageTime measurable_pi_apply 0 z)

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteWaypoints
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- A location-uniform finite union estimate. The common shape-test error is
at the fixed origin, while every tested location may be different. -/
theorem gamma_finite_waypoint_failure_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ι : Type*} (J : Finset ι) (a : ι → Vertex) (C n : ℕ) (η δ : ℝ) :
    P.real {ω | ∃ j ∈ J, ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)} ≤
      (J.card : ℝ) * P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C η δ n (fun e => τ e ω)} := by
  classical
  let := h.probability
  let A (j : ι) := {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
    (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)}
  have hevent : {ω | ∃ j ∈ J, ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)} =
      ⋃ j ∈ J, A j := by
    ext ω
    constructor
    · rintro ⟨j, hj, hω⟩
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hω⟩⟩
    · intro hω
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hω
      obtain ⟨hJ, hgood⟩ := Set.mem_iUnion.mp hj
      exact ⟨j, hJ, hgood⟩
  rw [hevent]
  have he (j : ι) : P.real (A j) =
      P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C η δ n (fun e => τ e ω)} := by
    exact congrArg ENNReal.toReal (h.translated_event_probability (a j)
      {w | ¬GoodOrigin (gammaMeanNorm h hs hr) (cheapSlope shape rate) C η δ n w}
      (measurableSet_goodOrigin _ _ _ _ _ n).compl)
  calc
    _ ≤ ∑ j ∈ J, P.real (A j) := measureReal_biUnion_finset_le J A
    _ = _ := by simp only [he, sum_const, nsmul_eq_mul]

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathChain
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

/-- Concatenating a finite list of connections preserves vertex localization and adds traversal costs. -/
theorem exists_path_chain (w : Edge → ℝ) (p : ℕ → Vertex) (S : Set Vertex)
    (a : ℕ → ℝ) (n : ℕ) (hp : p 0 ∈ S)
    (h : ∀ i < n, ∃ ds, p i+displacement ds=p (i+1) ∧
      pathCost w (p i) ds ≤ a i ∧ PathIn (p i) ds S) :
    ∃ ds, p 0+displacement ds=p n ∧
      pathCost w (p 0) ds ≤ ∑ i ∈ range n, a i ∧ PathIn (p 0) ds S := by
  induction n with
  | zero =>
    refine ⟨[],by simp,by simp [pathCost],?_⟩
    intro i hi
    simpa using hp
  | succ n ih =>
    obtain ⟨ds,hd,hcostd,hind⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨es,he,hcoste,hine⟩ := h n (Nat.lt_succ_self n)
    refine ⟨ds++es,?_,?_,?_⟩
    · rw [displacement_append, ← add_assoc, hd]
      exact he
    · rw [pathCost_append, hd, sum_range_succ]
      exact add_le_add hcostd hcoste
    · apply pathIn_append _ _ _ _ hind
      simpa only [hd] using hine

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Waypoints
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem waypoint_end (p q : Vertex) (B : ℕ) (hB : 0 < B) : waypoint p q B B=q := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  simp [waypoint,segmentPoint,hb]

theorem waypoint_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)‖ ≤ 2 :=
  latticeFloor_error _

theorem waypoint_displacement_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p)‖ ≤ 4 := by
  have he : latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p) =
      (latticeEmbed (waypoint p q B (j+1))-segmentPoint p q (((j+1 : ℕ) : ℝ)/B)) -
      (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)) := by
    rw [latticeEmbed_sub,latticeEmbed_sub]
    unfold segmentPoint
    ext i
    simp [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [waypoint_error p q B (j+1),waypoint_error p q B j])

theorem waypoint_displacement_norm (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)‖ ≤
      ‖latticeEmbed (q-p)‖/(B : ℝ)+4 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hn := norm_add_le
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)-(1/(B : ℝ)) • latticeEmbed (q-p))
    ((1/(B : ℝ)) • latticeEmbed (q-p))
  rw [sub_add_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hb)] at hn
  have he := waypoint_displacement_error p q B j
  have hid : (1/(B : ℝ))*‖latticeEmbed (q-p)‖=‖latticeEmbed (q-p)‖/(B : ℝ) := by ring
  rw [hid] at hn
  linarith

theorem waypoint_cost_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v w, |μ v-μ w| ≤ β*‖v-w‖)
    (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    μ (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)) ≤
      μ (latticeEmbed (q-p))/(B : ℝ)+4*β := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have ht := (le_abs_self _).trans (hlip
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j))
    ((1/(B : ℝ)) • latticeEmbed (q-p)))
  have he := mul_le_mul_of_nonneg_left (waypoint_displacement_error p q B j) hβ
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hb)] at ht
  have hid : (1/(B : ℝ))*μ (latticeEmbed (q-p))=μ (latticeEmbed (q-p))/(B : ℝ) := by ring
  rw [hid] at ht
  linarith

theorem waypoint_ball_in_tube (p q : Vertex) (B j : ℕ) (hB : 0 < B) (hj : j ≤ B)
    (R : ℝ) (z : Vertex) (hz : ‖latticeEmbed (z-waypoint p q B j)‖ ≤ R) :
    z ∈ SegmentTube p q (R+2) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  refine ⟨(j : ℝ)/B,div_nonneg (Nat.cast_nonneg _) hb.le,?_,?_⟩
  · exact (div_le_one hb).mpr (by exact_mod_cast hj)
  have he := waypoint_error p q B j
  have ht := norm_add_le (latticeEmbed z-latticeEmbed (waypoint p q B j))
    (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B))
  rw [sub_add_sub_cancel] at ht
  rw [latticeEmbed_sub] at hz
  linarith

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TubeDeterministic
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem localTravel_of_waypoint_tests (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (α D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n)
    (hgood : ∀ j < B, GoodOrigin μ α C κ δ n
      (fun e => w (shiftEdge (waypoint p q B j) e))) :
    LocalTravel μ η δ n p q w := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    have ht := (hgood 0 hB).1 (e.1-p,e.2)
    simpa [waypoint_zero,shiftEdge] using ht
  have hμzero : μ 0=0 := (hμ.zero_iff 0).mpr rfl
  have hwhole : μ (latticeEmbed (q-p)) ≤ β*(D*n) := by
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q-p)) 0)
    simp only [hμzero,sub_zero] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hdist hβ)
  let a := μ (latticeEmbed (q-p))/(B : ℝ)+4*β+κ*n+1
  have hpiece (j : ℕ) (hj : j < B) : ∃ ds,
      waypoint p q B j+displacement ds=waypoint p q B (j+1) ∧
      pathCost w (waypoint p q B j) ds ≤ a ∧
      PathIn (waypoint p q B j) ds (SegmentTube p q (δ*n)) := by
    let x := waypoint p q B j
    let y := waypoint p q B (j+1)
    have hg := hgood j hj
    have hlength : ‖latticeEmbed (y-x)‖ ≤ (C : ℝ)*n := by
      have ht := waypoint_displacement_norm p q B j hB
      exact (ht.trans (add_le_add ((div_le_div_iff_of_pos_right hb).mpr hdist) le_rfl)).trans hshortdist
    have herror := (abs_le.mp (hg.2.1 (y-x) hlength)).2
    have hpassage : passageTime w x y ≤ μ (latticeEmbed (y-x))+κ*n := by
      have hxy : waypoint p q B j+(y-x)=y := by dsimp [x]; abel
      simp only [passageTime_translate,add_zero,hxy] at herror
      linarith
    have hstepμ := waypoint_cost_bound μ hμ β hβ hlip p q B j hB
    have hshort : passageTime w x y+1 ≤ α*δ*n/6 := by
      have hd := (div_le_div_iff_of_pos_right hb).mpr hwhole
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    have hescape (z : Vertex) (hz : δ*n/3 ≤ ‖latticeEmbed (z-x)‖) :
        α*δ*n/6 ≤ passageTime w x z := by
      have hxz : waypoint p q B j+(z-x)=z := by dsimp [x]; abel
      simpa only [passageTime_translate,add_zero,hxz] using hg.2.2 (z-x) hz
    obtain ⟨ds,hend,hcost,hlocal⟩ := exists_confined_near_optimal w hw x y
      (δ*n/3) (α*δ*n/6) 1 (by norm_num) hescape hshort
    refine ⟨ds,hend,?_,?_⟩
    · change pathCost w x ds ≤ a
      dsimp [a]
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    · intro i hi
      obtain ⟨t,ht0,ht1,hbound⟩ := waypoint_ball_in_tube p q B j hB hj.le
        (δ*n/3) (x+displacement (ds.take i)) (hlocal i hi).le
      exact ⟨t,ht0,ht1,hbound.trans htube⟩
  have hp : waypoint p q B 0 ∈ SegmentTube p q (δ*n) := by
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hn : 0 ≤ δ*n := by linarith
    simpa [segmentPoint] using hn
  obtain ⟨ds,hend,hcost,hlocal⟩ := exists_path_chain w (waypoint p q B)
    (SegmentTube p q (δ*n)) (fun _ => a) B hp hpiece
  refine ⟨ds,by simpa [waypoint_end p q B hB] using hend,?_,by simpa using hlocal⟩
  have hid : (B : ℝ)*a=μ (latticeEmbed (q-p))+(B : ℝ)*(4*β+κ*n+1) := by
    dsimp [a]
    field_simp; ring
  simp only [sum_const,card_range,nsmul_eq_mul] at hcost
  rw [hid] at hcost
  simpa only [waypoint_zero] using hcost.trans (add_le_add le_rfl htotal)

theorem localTravel_parameters (α β D η δ : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ B C : ℕ, ∃ κ : ℝ, 0 < B ∧ 0 < C ∧ 0 < κ ∧
      ∀ᶠ n : ℕ in atTop,
        D*n/(B : ℝ)+4 ≤ (C : ℝ)*n ∧
        β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6 ∧
        (B : ℝ)*(4*β+κ*n+1) ≤ η*n ∧ δ*n/3+2 ≤ δ*n := by
  have had : 0 < α*δ := mul_pos hα hδ
  obtain ⟨B,hB⟩ := exists_nat_gt (max 1 (24*β*D/(α*δ)))
  have hb1 : (1 : ℝ) < B := (le_max_left _ _).trans_lt hB
  have hbpos : (0 : ℝ) < B := by linarith
  have hb : 0 < B := by exact_mod_cast hbpos
  have hbchoose := (div_lt_iff₀ had).mp ((le_max_right _ _).trans_lt hB)
  have hbase : β*D/(B : ℝ) ≤ α*δ/24 :=
    (div_le_iff₀ hbpos).mpr (by nlinarith)
  obtain ⟨C,hC⟩ := exists_nat_gt (D+4)
  have hc : 0 < C := by
    have : (0 : ℝ) < C := by linarith
    exact_mod_cast this
  let κ := min (η/(4*(B : ℝ))) (α*δ/24)
  have hk : 0 < κ := lt_min (div_pos hη (by linarith)) (div_pos had (by norm_num))
  have hkcost : κ ≤ α*δ/24 := min_le_right _ _
  have hktotal : (B : ℝ)*κ ≤ η/4 := by
    have ht := (le_div_iff₀ (by linarith : 0 < 4*(B : ℝ))).mp (min_le_left _ _ : κ ≤ η/(4*(B : ℝ)))
    nlinarith
  refine ⟨B,C,κ,hb,hc,hk,?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (12*(4*β+1)/(α*δ))),
    hlim.eventually (eventually_ge_atTop (2*(B : ℝ)*(4*β+1)/η)),
    hlim.eventually (eventually_ge_atTop (3/δ))] with n hn hn1 hn2 hn3
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1' := (div_le_iff₀ had).mp hn1
  have hn2' := (div_le_iff₀ hη).mp hn2
  have hn3' := (div_le_iff₀ hδ).mp hn3
  have hbase' := mul_le_mul_of_nonneg_right hbase hn0
  have hkcost' := mul_le_mul_of_nonneg_right hkcost hn0
  have hktotal' := mul_le_mul_of_nonneg_right hktotal hn0
  have hdiv : D*(n : ℝ)/(B : ℝ) ≤ D*n := by
    apply (div_le_iff₀ hbpos).mpr
    have ht := mul_le_mul_of_nonneg_left hb1.le (mul_nonneg hD.le hn0)
    simpa using ht
  have hc' := mul_le_mul_of_nonneg_right hC.le hn0
  have hid : β*(D*n)/(B : ℝ) = (β*D/(B : ℝ))*n := by ring
  rw [hid]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TubeTravel
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_tube_failure_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |gammaMeanNorm h hs hr v-gammaMeanNorm h hs hr u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ cheapSlope shape rate*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n) :
    P.real {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} ≤
      (B : ℝ)*P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C κ δ n (fun e => τ e ω)} := by
  let := h.probability
  have hsub : {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} ⊆
      {ω | ∃ j ∈ range B, ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C κ δ n (fun e => τ (shiftEdge (waypoint p q B j) e) ω)} := by
    intro ω hω
    by_contra hn
    apply hω
    apply localTravel_of_waypoint_tests _ _ (gammaMeanNorm_laws h hs hr) β hβ hlip
      p q B C n hB (cheapSlope shape rate) D η δ κ hdist hshortdist hshortcost htotal htube
    intro j hj
    by_contra hjbad
    exact hn ⟨j, mem_range.mpr hj, hjbad⟩
  refine (measureReal_mono hsub).trans ?_
  simpa only [card_range] using gamma_finite_waypoint_failure_bound h hs hr
    (range B) (waypoint p q B) C n κ δ

/-- Uniform probability statement for all deterministic endpoint pairs at each
large integer scale. It is NOT one event of simultaneous success for all pairs. -/
theorem gamma_tube_travel_nat
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ p q : Vertex,
      ‖latticeEmbed (q-p)‖ ≤ D*n →
      P.real {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} < ε := by
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound _ (gammaMeanNorm_laws h hs hr)
  obtain ⟨B,C,κ,hB,hC,hκ,hparams⟩ := localTravel_parameters
    (cheapSlope shape rate) β D η δ (cheapSlope_pos hs hr) hβ.le hD hη hδ
  have ht := gamma_moving_goodOrigin_failure_tendsto h hs hr C hC κ δ hκ hδ
    (fun _ => (0 : Vertex))
  have ht' : Tendsto (fun n => (B : ℝ)*P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C κ δ n (fun e => τ e ω)}) atTop (𝓝 0) := by
    simpa only [shiftEdge, zero_add, mul_zero] using ht.const_mul (B : ℝ)
  intro ε hε
  filter_upwards [hparams, ht'.eventually (gt_mem_nhds hε)] with n hn hprob
  intro p q hpq
  exact (gamma_tube_failure_bound h hs hr β hβ.le hlip p q B C n hB D η δ κ hpq
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans_lt hprob

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointNet
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

theorem step_embed_norm_le (d : Step) : ‖latticeEmbed d.delta‖ ≤ 1 := by
  have h := plane_norm_le_coordinates (latticeEmbed d.delta)
  cases d <;> simpa [Step.delta, latticeEmbed] using h

theorem displacement_norm_le_length (ds : List Step) :
    ‖latticeEmbed (displacement ds)‖ ≤ (ds.length : ℝ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [displacement_cons, latticeEmbed_add]
    have ht := norm_add_le (latticeEmbed d.delta) (latticeEmbed (displacement ds))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [step_embed_norm_le d]

theorem coordinatePath_length (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

theorem coordinatePath_prefix_bound (p q : Vertex) (i : ℕ) :
    ‖latticeEmbed (p+displacement ((coordinatePath p q).take i)-p)‖ ≤
      (latticeDistance p q : ℝ) := by
  simp only [add_sub_cancel_left]
  exact (displacement_norm_le_length _).trans (by
    exact_mod_cast (show ((coordinatePath p q).take i).length ≤ latticeDistance p q by
      rw [List.length_take, coordinatePath_length]; exact min_le_right _ _))

theorem segmentPoint_perturbation (p q p' q' : Vertex) (r t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    ‖segmentPoint p' q' t-segmentPoint p q t‖ ≤ r := by
  have he : segmentPoint p' q' t-segmentPoint p q t =
      (1-t) • latticeEmbed (p'-p)+t • latticeEmbed (q'-q) := by
    simp only [segmentPoint,latticeEmbed_sub]
    ext i
    simp [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  have hn := norm_add_le ((1-t) • latticeEmbed (p'-p)) (t • latticeEmbed (q'-q))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1-t),abs_of_nonneg ht0] at hn
  have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-t by linarith)
  have h2 := mul_le_mul_of_nonneg_left hq ht0
  nlinarith

theorem segmentTube_perturbation (p q p' q' : Vertex) (r R : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    SegmentTube p' q' R ⊆ SegmentTube p q (R+r) := by
  rintro z ⟨t,ht0,ht1,ht⟩
  refine ⟨t,ht0,ht1,?_⟩
  have hb := segmentPoint_perturbation p q p' q' r t ht0 ht1 hp hq
  have hn := norm_add_le (latticeEmbed z-segmentPoint p' q' t)
    (segmentPoint p' q' t-segmentPoint p q t)
  rw [sub_add_sub_cancel] at hn
  linarith

/-- Concatenates two explicit coordinate attachments and a net connection.
Every traversal is charged and every vertex is retained in the tube. -/
theorem localTravel_attach (μ : Plane → ℝ) (w : Edge → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q p' q' : Vertex) (r a η δ s : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r)
    (hleft : pathCost w p (coordinatePath p p') ≤ a)
    (hright : pathCost w q' (coordinatePath q' q) ≤ a)
    (hmid : LocalTravel μ η δ s p' q' w) :
    ∃ ds, p+displacement ds=q ∧
        pathCost w p ds ≤ μ (latticeEmbed (q-p))+η*s+2*a+2*β*r ∧
        PathIn p ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
  obtain ⟨ds,hd,hcost,hin⟩ := hmid
  let l := coordinatePath p p'
  let v := coordinatePath q' q
  have hl : p+displacement l=p' := coordinatePath_endpoint p p'
  have hv : q'+displacement v=q := coordinatePath_endpoint q' q
  have hμdiff : μ (latticeEmbed (q'-p')) ≤ μ (latticeEmbed (q-p))+2*β*r := by
    have he : latticeEmbed (q'-p')-latticeEmbed (q-p) =
        latticeEmbed (q'-q)-latticeEmbed (p'-p) := by
      simp only [latticeEmbed_sub]; abel
    have hn : ‖latticeEmbed (q'-p')-latticeEmbed (q-p)‖ ≤ 2*r := by
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q'-p')) (latticeEmbed (q-p)))
    have hb := mul_le_mul_of_nonneg_left hn hβ
    linarith
  have hll : PathIn p l (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound p p' i
    have hdist := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hdist
    have hr : 0 ≤ r := (norm_nonneg _).trans hp
    simp only [segmentPoint,zero_smul,add_zero]
    rw [← latticeEmbed_sub]
    exact hb.trans ((hdist.trans (by linarith)).trans (le_max_left _ _))
  have hrr : PathIn q' v (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨1,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound q' q i
    have hdist := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hdist
    have hn := norm_add_le
      (latticeEmbed (q'+displacement (v.take i))-latticeEmbed q')
      (latticeEmbed q'-latticeEmbed q)
    rw [sub_add_sub_cancel,← latticeEmbed_sub,← latticeEmbed_sub,← latticeEmbed_sub] at hn
    simp only [segmentPoint,one_smul,add_sub_cancel]
    rw [← latticeEmbed_sub]
    exact (hn.trans (by dsimp [v] at *; linarith)).trans (le_max_left _ _)
  have hmm : PathIn p' ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i hi
    obtain ⟨t,ht0,ht1,ht⟩ := segmentTube_perturbation p q p' q' r (δ*s) hp hq (hin i hi)
    exact ⟨t,ht0,ht1,ht.trans (le_max_right _ _)⟩
  refine ⟨l++ds++v,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc,hl,hd,hv]
  · rw [pathCost_append,pathCost_append,displacement_append,← add_assoc,hl,hd]
    dsimp [l,v]
    linarith
  · apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hll (by simpa [hl] using hmm))
    simpa only [displacement_append,← add_assoc,hl,hd] using hrr

/-- A fixed finite Euclidean net; its cardinality is independent of scale. -/
theorem finite_ball_net (D γ : ℝ) (hγ : 0 < γ) :
    ∃ S : Finset {v : Plane // ‖v‖ ≤ D},
      ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ := by
  classical
  have hc : closedBall (0 : Plane) D ⊆
      ⋃ u : {v : Plane // ‖v‖ ≤ D}, ball u.val γ := by
    intro v hv
    have hv' : ‖v‖ ≤ D := by simpa using hv
    exact mem_iUnion.mpr ⟨⟨v,hv'⟩,by simpa using hγ⟩
  obtain ⟨S,hS⟩ := (isCompact_closedBall (0 : Plane) D).elim_finite_subcover
    (fun u : {v : Plane // ‖v‖ ≤ D} => ball u.val γ) (fun _ => isOpen_ball) hc
  refine ⟨S,?_⟩
  intro v hv
  obtain ⟨u,hu,hvu⟩ := mem_iUnion₂.mp (hS (by simpa using hv))
  exact ⟨u,hu,hvu⟩

theorem lattice_mem_box_of_norm (p : Vertex) (n : ℕ)
    (hp : ‖latticeEmbed p‖ ≤ (n : ℝ)) : p ∈ latticeBox n := by
  have h0 := (plane_coordinate_le_norm (latticeEmbed p) 0).trans hp
  have h1 := (plane_coordinate_le_norm (latticeEmbed p) 1).trans hp
  simp only [latticeEmbed,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hh0 : -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n := by exact_mod_cast abs_le.mp h0
  have hh1 : -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n := by exact_mod_cast abs_le.mp h1
  simpa only [latticeBox,Finset.mem_product,Finset.mem_Icc] using And.intro hh0 hh1

theorem scaled_net_norm (D : ℝ) (u : {v : Plane // ‖v‖ ≤ D}) (n : ℕ) :
    ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val))‖ ≤ D*n+2 := by
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val)
  rw [sub_add_cancel,norm_smul,Real.norm_natCast] at ht
  have hu := mul_le_mul_of_nonneg_left u.property (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

theorem scaled_net_approximates (D γ : ℝ)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (n : ℕ) (hn : 0 < n) (p : Vertex) (hp : ‖latticeEmbed p‖ ≤ D*n) :
    ∃ u ∈ S, ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val)-p)‖ ≤ γ*n+2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let v := (1/(n : ℝ)) • latticeEmbed p
  have hv : ‖v‖ ≤ D := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hn')]
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hn').mpr (by nlinarith)
  obtain ⟨u,hu,hvu⟩ := hS v hv
  refine ⟨u,hu,?_⟩
  have he : (n : ℝ) • v = latticeEmbed p := by
    dsimp [v]; rw [smul_smul]; simp [hn'.ne']
  have hd : ‖(n : ℝ) • u.val-latticeEmbed p‖ ≤ γ*n := by
    rw [← he,← smul_sub,norm_smul,Real.norm_natCast,norm_sub_rev]
    nlinarith
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val-latticeEmbed p)
  rw [sub_add_sub_cancel,← latticeEmbed_sub] at ht
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BallTravelGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

theorem ballTravel_of_net (μ : Plane → ℝ) (w : Edge → ℝ)
    (D γ β η δ κ A : ℝ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (C n : ℕ) (hn : 0 < n) (hbox : D*n+2 ≤ (C*n : ℕ))
    (hcost : η/4*n+2*((2*A)*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n)
    (htube : max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n)
    (hc : ∀ p ∈ latticeBox (C*n), ∀ q ∈ latticeBox (C*n),
      pathCost w p (coordinatePath p q) < A*(latticeDistance p q : ℝ)+κ*(C*n : ℕ))
    (hm : ∀ u ∈ S, ∀ v ∈ S, LocalTravel μ (η/4) (δ/2) n
      (latticeFloor ((n : ℝ) • u.val)) (latticeFloor ((n : ℝ) • v.val)) w) :
    BallTravel μ D η δ n w := by
  intro p q hp hq
  obtain ⟨u,hu,hpu⟩ := scaled_net_approximates D γ S hS n hn p hp
  obtain ⟨v,hv,hqv⟩ := scaled_net_approximates D γ S hS n hn q hq
  let p' := latticeFloor ((n : ℝ) • u.val)
  let q' := latticeFloor ((n : ℝ) • v.val)
  have hpbox : p ∈ latticeBox (C*n) := lattice_mem_box_of_norm p (C*n) (hp.trans (by linarith))
  have hqbox : q ∈ latticeBox (C*n) := lattice_mem_box_of_norm q (C*n) (hq.trans (by linarith))
  have hp'box : p' ∈ latticeBox (C*n) := lattice_mem_box_of_norm p' (C*n)
    ((scaled_net_norm D u n).trans hbox)
  have hq'box : q' ∈ latticeBox (C*n) := lattice_mem_box_of_norm q' (C*n)
    ((scaled_net_norm D v n).trans hbox)
  have hleft : pathCost w p (coordinatePath p p') ≤ (2*A)*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hd
    have hh := hc p hpbox p' hp'box
    dsimp [p'] at *
    have hd' := mul_le_mul_of_nonneg_left hd hA.le
    have hp' := mul_le_mul_of_nonneg_left hpu hA.le
    nlinarith
  have hright : pathCost w q' (coordinatePath q' q) ≤ (2*A)*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hd
    have hh := hc q' hq'box q hqbox
    dsimp [q'] at *
    have hd' := mul_le_mul_of_nonneg_left hd hA.le
    have hq' := mul_le_mul_of_nonneg_left hqv hA.le
    nlinarith
  obtain ⟨ds,hend,hc',ht'⟩ := localTravel_attach μ w β hβ hlip p q p' q'
    (γ*n+2) ((2*A)*(γ*n+2)+κ*(C*n : ℕ)) (η/4) (δ/2) n hpu hqv hleft hright (hm u hu v hv)
  refine ⟨ds,hend,hc'.trans (by linarith),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := ht' i hi
  exact ⟨t,ht0,ht1,hbound.trans htube⟩

theorem ballTravel_parameters (D β η δ A : ℝ)
    (hA : 0 < A)
    (hD : 0 < D) (hβ : 0 ≤ β) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ γ κ : ℝ, ∃ C : ℕ, 0 < γ ∧ 0 < κ ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        0 < n ∧ D*n+2 ≤ (C*n : ℕ) ∧
        η/4*n+2*((2*A)*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n ∧
        max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n := by
  obtain ⟨C,hC⟩ := exists_nat_gt (D+2)
  have hc : (0 : ℝ) < C := by linarith
  have hc' : 0 < C := by exact_mod_cast hc
  let γ := min (η/(8*(4*A+2*β))) (δ/12)
  let κ := η/(16*(C : ℝ))
  have hγ : 0 < γ := lt_min (div_pos hη (by positivity)) (by positivity)
  have hκ : 0 < κ := div_pos hη (by positivity)
  have hgη : (4*A+2*β)*γ ≤ η/8 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 8*(4*A+2*β))).mp (min_le_left _ _ : γ ≤ _)
    nlinarith
  have hgδ : γ ≤ δ/12 := min_le_right _ _
  have hk : κ*(C : ℝ)=η/16 := by dsimp [κ]; field_simp
  refine ⟨γ,κ,C,hγ,hκ,hc',?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (4*(8*A+4*β)/η)),
    hlim.eventually (eventually_ge_atTop (24/δ))] with n hn hnη hnδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hhη := (div_le_iff₀ hη).mp hnη
  have hhδ := (div_le_iff₀ hδ).mp hnδ
  have hge := mul_le_mul_of_nonneg_right hgη hn0
  have hgd := mul_le_mul_of_nonneg_right hgδ hn0
  have hcb := mul_le_mul_of_nonneg_right hC.le hn0
  simp only [Nat.cast_mul]
  refine ⟨by omega,by nlinarith,?_,?_⟩
  · have he : κ*((C : ℝ)*n)=(η/16)*n := by rw [← mul_assoc,hk]
    rw [he]
    nlinarith
  · apply max_le <;> nlinarith

theorem localTravel_mono (μ : Plane → ℝ) (w : Edge → ℝ) (p q : Vertex)
    {η δ s η' δ' s' : ℝ} (hη : η*s ≤ η'*s') (hδ : δ*s ≤ δ'*s')
    (h : LocalTravel μ η δ s p q w) : LocalTravel μ η' δ' s' p q w := by
  obtain ⟨ds,hend,hcost,htube⟩ := h
  refine ⟨ds,hend,hcost.trans (add_le_add le_rfl hη),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := htube i hi
  exact ⟨t,ht0,ht1,hbound.trans hδ⟩

theorem measurableSet_localTravel (μ : Plane → ℝ) (η δ s : ℝ) (p q : Vertex) :
    MeasurableSet {w | LocalTravel μ η δ s p q w} := by
  have hm := measurableSet_bounded_path_event (τ := fun e (w : Edge → ℝ) => w e)
    measurable_pi_apply
    (fun x ds => x=p ∧ x+displacement ds=q ∧ PathIn x ds (SegmentTube p q (δ*s)))
    (fun _ _ => μ (latticeEmbed (q-p))+η*s)
  convert hm using 1
  ext w
  constructor
  · rintro ⟨ds,hend,hcost,htube⟩
    exact ⟨p,ds,⟨rfl,hend,htube⟩,hcost⟩
  · rintro ⟨x,ds,⟨rfl,hend,htube⟩,hcost⟩
    exact ⟨ds,hend,hcost,htube⟩

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BallTravel
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_badConnections_tendsto_zero
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => P.real (gammaBadConnections shape rate τ κ n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (h.gammaBadConnections_probability hs hr κ)
  exact (summable_gamma_box_connection_bound hr hκ).tendsto_atTop_zero

theorem gamma_ball_travel_nat (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by
  classical
  let μ := gammaMeanNorm h hs hr
  have hμ := gammaMeanNorm_laws h hs hr
  let _ := h.probability
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  obtain ⟨γ,κ,C,hγ,hκ,hC,hparams⟩ := ballTravel_parameters D β η δ (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr) hD hβ.le hη hδ
  obtain ⟨S,hS⟩ := finite_ball_net D γ hγ
  let A (n : ℕ) := ⋃ uv ∈ S ×ˢ S, {ω | ¬LocalTravel μ (η/4) (δ/2) n
    (latticeFloor ((n : ℝ) • uv.1.val)) (latticeFloor ((n : ℝ) • uv.2.val)) (fun e => τ e ω)}
  have hA : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    apply (tendsto_order.2 ⟨?_,?_⟩)
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
    · intro ε hε
      have hden : 0 < ((S ×ˢ S).card : ℝ)+1 := by positivity
      filter_upwards [eventually_ge_atTop 1,
        gamma_tube_travel_nat h hs hr (2*D+4) (η/4) (δ/2)
          (by linarith) (by linarith) (by linarith)
          (ε/(((S ×ˢ S).card : ℝ)+1)) (div_pos hε hden)] with n hn hh
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hbound : P.real (A n) ≤ ((S ×ˢ S).card : ℝ)*(ε/(((S ×ˢ S).card : ℝ)+1)) := by
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        calc
          _ ≤ ∑ _uv ∈ S ×ˢ S, ε/(((S ×ˢ S).card : ℝ)+1) := by
            apply sum_le_sum
            intro uv huv
            apply (hh _ _ ?_).le
            rw [latticeEmbed_sub]
            exact (norm_sub_le _ _).trans (by
              have h1 := scaled_net_norm D uv.1 n
              have h2 := scaled_net_norm D uv.2 n
              nlinarith)
          _ = _ := by simp
      apply hbound.trans_lt
      have he := (div_pos hε hden)
      have hid : ((((S ×ˢ S).card : ℝ)+1))*(ε/(((S ×ˢ S).card : ℝ)+1))=ε := by field_simp
      nlinarith
  have hCn : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left n hC)
  have hB := (gamma_badConnections_tendsto_zero h hs hr κ hκ).comp hCn
  have hbound : ∀ᶠ n : ℕ in atTop,
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)} ≤
        P.real (gammaBadConnections shape rate τ κ (C*n))+P.real (A n) := by
    filter_upwards [hparams] with n hn
    have hsub : {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)} ⊆
        gammaBadConnections shape rate τ κ (C*n) ∪ A n := by
      intro ω hω
      by_contra hb
      have hc : ω ∉ gammaBadConnections shape rate τ κ (C*n) := fun hc => hb (Or.inl hc)
      have hm : ω ∉ A n := fun hm => hb (Or.inr hm)
      apply hω
      apply ballTravel_of_net μ _ D γ β η δ κ (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr) hβ.le hlip S hS C n
        hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      · intro p hp q hq
        by_contra hh
        exact hc (mem_iUnion₂.mpr ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,le_of_not_gt hh⟩)
      · intro u hu v hv
        by_contra hh
        exact hm (mem_iUnion₂.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,hh⟩)
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hbound
    (by simpa using hB.add hA)

theorem segmentTube_translate_iff (a p q z : Vertex) (R : ℝ) :
    a+z ∈ SegmentTube (a+p) (a+q) R ↔ z ∈ SegmentTube p q R := by
  simp only [SegmentTube,mem_ofPred_eq,segmentPoint,latticeEmbed_add,
    add_sub_add_left_eq_sub]
  have he (t : ℝ) : latticeEmbed a+latticeEmbed z-
      (latticeEmbed a+latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)) =
      latticeEmbed z-(latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)) := by abel
  simp only [he]

theorem localTravel_translate_iff (μ : Plane → ℝ) (w : Edge → ℝ)
    (a p q : Vertex) (η δ s : ℝ) :
    LocalTravel μ η δ s p q (fun e => w (shiftEdge a e)) ↔
      LocalTravel μ η δ s (a+p) (a+q) w := by
  constructor
  · rintro ⟨ds,hd,hc,hin⟩
    refine ⟨ds,by rw [add_assoc,hd],?_,?_⟩
    · simpa only [pathCost_translate,add_sub_add_left_eq_sub] using hc
    · intro i hi
      rw [add_assoc,segmentTube_translate_iff]
      exact hin i hi
  · rintro ⟨ds,hd,hc,hin⟩
    refine ⟨ds,by simpa only [add_assoc,add_left_cancel_iff] using hd,?_,?_⟩
    · simpa only [pathCost_translate,add_sub_add_left_eq_sub] using hc
    · intro i hi
      have ht := hin i hi
      rw [add_assoc,segmentTube_translate_iff] at ht
      exact ht

theorem measurableSet_ballTravel (μ : Plane → ℝ) (D η δ s : ℝ) :
    MeasurableSet {w | BallTravel μ D η δ s w} := by
  simp only [BallTravel,ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun q =>
    MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_localTravel μ η δ s p q))))

theorem gamma_ball_travel (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ a : Vertex,
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} < ε := by
  let _ := h.probability
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((gamma_ball_travel_nat h hs hr D (η/2) (δ/2) hD (by linarith) (by linarith)).eventually
      (gt_mem_nhds hε))
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hscale
  intro a
  have he := h.translated_event_probability a
    {w | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s w} (measurableSet_ballTravel (gammaMeanNorm h hs hr) D η δ s).compl
  rw [show P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} =
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ e ω)} from congrArg ENNReal.toReal he]
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hscale
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hscale).trans hsn
  have hnupper : (n : ℝ) ≤ 2*s := by
    have hh : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hη' : (η/2)*(n : ℝ) ≤ η*s := by nlinarith
  have hδ' : (δ/2)*(n : ℝ) ≤ δ*s := by nlinarith
  refine (measureReal_mono (show {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ e ω)} ⊆
      {ω | ¬BallTravel (gammaMeanNorm h hs hr) D (η/2) (δ/2) n (fun e => τ e ω)} from ?_)).trans_lt (hN n hnN)
  intro ω hb hg
  apply hb
  intro p q hp hq
  apply localTravel_mono (gammaMeanNorm h hs hr) _ p q hη' hδ'
  apply hg p q <;> nlinarith

/-- Simultaneous travel for arbitrary deterministic lattice endpoint sets of
bounded combined diameter. This stronger statement includes vertical intervals. -/
theorem gamma_set_travel (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ I J : Set Vertex,
      (∀ p ∈ I ∪ J, ∀ q ∈ I ∪ J, ‖latticeEmbed (q-p)‖ ≤ D*s) →
      P.real {ω | ¬∀ p ∈ I, ∀ q ∈ J,
        LocalTravel (gammaMeanNorm h hs hr) η δ s p q (fun e => τ e ω)} < ε := by
  let _ := h.probability
  intro ε hε
  filter_upwards [gamma_ball_travel h hs hr D η δ hD hη hδ ε hε] with s hscale
  intro I J hdiam
  by_cases hI : I.Nonempty
  · obtain ⟨a,ha⟩ := hI
    refine (measureReal_mono (show {ω | ¬∀ p ∈ I, ∀ q ∈ J, LocalTravel (gammaMeanNorm h hs hr) η δ s p q (fun e => τ e ω)} ⊆
        {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} from ?_)).trans_lt (hscale a)
    intro ω hb hg
    apply hb
    intro p hp q hq
    have hgood := hg (p-a) (q-a) (hdiam a (Or.inl ha) p (Or.inl hp))
      (hdiam a (Or.inl ha) q (Or.inr hq))
    have hh := (localTravel_translate_iff (gammaMeanNorm h hs hr) (fun e => τ e ω) a (p-a) (q-a) η δ s).mp hgood
    simpa only [add_sub_cancel] using hh
  · have he : I=∅ := Set.not_nonempty_iff_eq_empty.mp hI
    simpa [he] using hε

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConnectorContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP MeasureTheory Set
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_connector_support_gap
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (b : ℝ) (plus : Bool) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      D0*s ≤ xCoord z → rCoord b z ∈ contactSide plus → |rCoord b z| ≤ 3*C*s →
      gammaMeanNorm h hs hr z -
        (gammaMeanNorm h hs hr (direction b)*xCoord z +
          extremeSlope (gammaMeanNorm h hs hr) b plus*rCoord b z) ≤ ε*s/4 :=
  connector_support_gap _ (gammaMeanNorm_laws h hs hr) b plus ε C hε hC

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridIndependence
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint independence for finite families of tests on disjoint edge sets. -/
namespace GammaFPP.Grid
open PlanarFPP MeasureTheory ProbabilityTheory Set Finset

theorem measurable_extendEdgeWeights (S : Finset Edge) : Measurable (extendEdgeWeights S) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ S
  · simpa only [extendEdgeWeights,dite_eq_left he] using (measurable_pi_apply (⟨e,he⟩ : S))
  · simp only [extendEdgeWeights,dite_eq_right he]
    exact measurable_const

theorem DependsOnEdges.restriction_iff {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    extendEdgeWeights S (fun e : S => w e) ∈ A ↔ w ∈ A := by
  apply hA
  intro e he
  simp [extendEdgeWeights,he]

theorem DependsOnEdges.compl {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) : DependsOnEdges Aᶜ S := by
  intro w w' hh
  exact not_congr (hA w w' hh)

theorem dependsOnEdges_biInter {ι : Type*} (t : Finset ι)
    (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, DependsOnEdges (A i) (S i)) :
    DependsOnEdges (⋂ i ∈ t, A i) (t.biUnion S) := by
  classical
  intro w w' hh
  simp only [mem_iInter]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact hA i hi w w' (fun e he => hh e (mem_biUnion.mpr ⟨i,hi,he⟩))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem disjoint_edge_events_independent (h : GammaEnvironment shape rate P τ)
    (A B : Set (Edge → ℝ)) (S T : Finset Edge)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : DependsOnEdges A S) (hBT : DependsOnEdges B T) (hST : Disjoint S T) :
    IndepSet {ω | (fun e => τ e ω) ∈ A} {ω | (fun e => τ e ω) ∈ B} P := by
  let _ := h.probability
  have hf := h.independent.indepFun_finset S T hST h.measurable
  have hs : Measurable (fun ω (e : S) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have ht : Measurable (fun ω (e : T) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have hi := (indepFun_iff_indepSet_preimage hs ht).mp hf
    ((extendEdgeWeights S) ⁻¹' A) ((extendEdgeWeights T) ⁻¹' B)
    (hA.preimage (measurable_extendEdgeWeights S)) (hB.preimage (measurable_extendEdgeWeights T))
  have heA : (fun ω (e : S) => τ e ω) ⁻¹' ((extendEdgeWeights S) ⁻¹' A) =
      {ω | (fun e => τ e ω) ∈ A} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hAS.restriction_iff (fun e => τ e ω)
  have heB : (fun ω (e : T) => τ e ω) ⁻¹' ((extendEdgeWeights T) ⁻¹' B) =
      {ω | (fun e => τ e ω) ∈ B} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hBT.restriction_iff (fun e => τ e ω)
  simpa only [heA,heB] using hi

theorem disjoint_edge_events_inter_probability (h : GammaEnvironment shape rate P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j))) :
    P {ω | ∀ i ∈ t, (fun e => τ e ω) ∈ A i} =
      ∏ i ∈ t, P {ω | (fun e => τ e ω) ∈ A i} := by
  classical
  let _ := h.probability
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hAt : ∀ i ∈ t, MeasurableSet (A i) := fun i hi => hA i (mem_insert_of_mem hi)
    have hSt : ∀ i ∈ t, DependsOnEdges (A i) (S i) := fun i hi => hAS i (mem_insert_of_mem hi)
    have hd : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)) := by
      intro i hi j hj hij
      exact hdis (mem_insert_of_mem hi) (mem_insert_of_mem hj) hij
    have hdunion : Disjoint (S a) (t.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hi) (by intro he; exact ha (he ▸ hi))
    have hm : MeasurableSet (⋂ i ∈ t, A i) := MeasurableSet.biInter (t.countable_toSet) hAt
    have hi := disjoint_edge_events_independent h (A a) (⋂ i ∈ t, A i) (S a) (t.biUnion S)
      (hA a (mem_insert_self _ _)) hm (hAS a (mem_insert_self _ _))
      (dependsOnEdges_biInter t A S hSt) hdunion
    have hprob := hi.measure_inter_eq_mul
    have he : {ω | ∀ i ∈ insert a t, (fun e => τ e ω) ∈ A i} =
        {ω | (fun e => τ e ω) ∈ A a} ∩ {ω | (fun e => τ e ω) ∈ ⋂ i ∈ t, A i} := by
      ext ω; simp
    rw [he,hprob,Finset.prod_insert ha]
    congr 1
    simpa only [mem_iInter] using ih hAt hSt hd

/-- The amplification step in cr:rare-fast: M disjoint trials with individual
success probability at least p have joint failure probability at most (1-p)^M. -/
theorem disjoint_trials_failure_bound (h : GammaEnvironment shape rate P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)))
    (p : ℝ)
    (hprob : ∀ i ∈ t, p ≤ P.real {ω | (fun e => τ e ω) ∈ A i}) :
    P.real {ω | ∀ i ∈ t, (fun e => τ e ω) ∉ A i} ≤ (1-p)^t.card := by
  classical
  let _ := h.probability
  have he := disjoint_edge_events_inter_probability h t (fun i => (A i)ᶜ) S
    (fun i hi => (hA i hi).compl) (fun i hi => (hAS i hi).compl) hdis
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_prod] at her
  change P.real _ = ∏ i ∈ t, P.real {ω | (fun e => τ e ω) ∉ A i} at her
  simp only [mem_compl_iff] at her
  rw [her]
  calc
    _ ≤ ∏ _i ∈ t, (1-p) := by
      apply Finset.prod_le_prod
      · intro i _; exact measureReal_nonneg
      · intro i hi
        have hm := (hA i hi).preimage (Measurable.of_eval h.measurable)
        have hc := measureReal_compl (μ := P) hm
        simp only [Set.preimage] at hc
        change P.real ({ω | (fun e => τ e ω) ∈ A i}ᶜ) ≤ _
        rw [hc]
        simpa using sub_le_sub_left (hprob i hi) 1
    _ = _ := by simp

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingLocalized
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem internalEdges_disjoint {V W : Finset Vertex} (h : Disjoint V W) :
    Disjoint (internalEdges V) (internalEdges W) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h (mem_internalEdges e V |>.mp he).1
    (mem_internalEdges e W |>.mp hf).1

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges,he]))]

theorem measurableSet_strictLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (strictLocalizedEvent V family bound) := by
  simpa only [strictLocalizedEvent,and_assoc] using
    measurableSet_strict_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem strictLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (strictLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem strip_vertices_disjoint (V W : Finset Vertex) (b y z R : ℝ)
    (hV : ∀ v ∈ V, |transverse b v-y| ≤ R)
    (hW : ∀ v ∈ W, |transverse b v-z| ≤ R)
    (hsep : 2*R < |y-z|) : Disjoint V W := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have ht := abs_add_le (y-transverse b v) (transverse b v-z)
  rw [sub_add_sub_cancel,abs_sub_comm y (transverse b v)] at ht
  have h1 := hV v hv
  have h2 := hW v hw
  linarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConnectorEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge
open GammaFPP.IntervalTravelBridge Set MeasureTheory Filter
open scoped Topology

theorem mem_allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) (w : Edge → ℝ) :
    w ∈ allPairsRegionEvent V I J bound ↔
      ∀ p ∈ I, ∀ q ∈ J, ∃ ds, p+displacement ds=q ∧
        PathIn p ds (V : Set Vertex) ∧ pathCost w p ds ≤ bound p q := by
  simp [allPairsRegionEvent,boundedLocalizedEvent]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

/-- Uniform connection estimates for finite-region endpoint tests from
diameter, support-cost, and tube-containment bounds. -/
theorem gamma_allPairsRegionEvent (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ (V : Finset Vertex) (I J : Set Vertex)
      (bound : Vertex → Vertex → ℝ),
      (∀ p ∈ I ∪ J, ∀ q ∈ I ∪ J, ‖latticeEmbed (q-p)‖ ≤ D*s) →
      (∀ p ∈ I, ∀ q ∈ J, gammaMeanNorm h hshape hrate (latticeEmbed (q-p))+η*s ≤ bound p q) →
      (∀ p ∈ I, ∀ q ∈ J, SegmentTube p q (δ*s) ⊆ (V : Set Vertex)) →
      P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent V I J bound} < ε := by
  let _ := h.probability
  intro ε hε
  filter_upwards [gamma_set_travel h hshape hrate D η δ hD hη hδ ε hε] with s hs
  intro V I J bound hdiam hcost hregion
  refine (measureReal_mono (show {ω | (fun e => τ e ω) ∉ allPairsRegionEvent V I J bound} ⊆
    {ω | ¬∀ p ∈ I, ∀ q ∈ J, LocalTravel (gammaMeanNorm h hshape hrate) η δ s p q (fun e => τ e ω)} from ?_)).trans_lt
      (hs I J hdiam)
  intro ω hbad htravel
  apply hbad
  rw [mem_allPairsRegionEvent]
  intro p hp q hq
  obtain ⟨ds,hd,hc,hin⟩ := htravel p hp q hq
  refine ⟨ds,hd,?_,hc.trans (hcost p hp q hq)⟩
  intro i hi
  exact hregion p hp q hq (hin i hi)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RareFastEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem mem_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ rareFastEvent b m a A R ε s n t ↔
      ∃ p ds, p.1=t.1 ∧ (p+displacement ds).1=t.1+n ∧
        PathIn p ds (rareFastRegion b A R s n t) ∧ defect w b m a p ds < -ε*s := by
  simp only [rareFastEvent,strictLocalizedEvent,mem_ofPred_eq,defect]
  have hV : (rareFastVertices b A R s n t : Set Vertex)=rareFastRegion b A R s n t := by
    ext p; simp
  rw [hV]
  constructor
  · rintro ⟨p,ds,⟨hp,hq⟩,hin,hc⟩
    exact ⟨p,ds,hp,hq,hin,by linarith⟩
  · rintro ⟨p,ds,hp,hq,hin,hc⟩
    exact ⟨p,ds,⟨hp,hq⟩,hin,by linarith⟩

theorem measurableSet_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (rareFastEvent b m a A R ε s n t) :=
  measurableSet_strictLocalizedEvent _ _ _

theorem rareFastEvent_depends (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    DependsOnEdges (rareFastEvent b m a A R ε s n t)
      (internalEdges (rareFastVertices b A R s n t)) :=
  strictLocalizedEvent_depends _ _ _

/-- Translating weights is exactly equivalent to translating all path vertices;
the supporting functional is evaluated on the unchanged displacement. -/
theorem rareFastEvent_translate (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    (fun e => w (shiftEdge t e)) ∈ rareFastEvent b m a A R ε s n 0 ↔
      w ∈ rareFastEvent b m a A R ε s n t := by
  rw [mem_rareFastEvent,mem_rareFastEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m a p ds =
      defect w b m a (t+p) ds := by simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨t+p,ds,by simpa using hp,by simpa [add_assoc] using hq,?_,?_⟩
    · intro i hi
      have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
      change _ ∈ rareFastRegion b A R s n t
      simpa only [rareFastRegion,mem_ofPred_eq,he,sub_zero] using hin i hi
    · rwa [← hc]
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨p-t,ds,by simpa using sub_eq_zero.mpr hp,?_,?_,?_⟩
    · simp only [Prod.fst_add,Prod.fst_sub,Prod.fst_zero] at *
      omega
    · intro i hi
      have he : p-t+displacement (ds.take i)=(p+displacement (ds.take i))-t := by abel
      rw [he]
      simpa [rareFastRegion] using hin i hi
    · have he : t + (p-t) = p := by abel
      rw [hc,he]
      exact hcost

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

theorem rareFastEvent_probability_translate (h : GammaEnvironment shape rate P τ)
    (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} =
      P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0} := by
  have he : {ω | (fun e => τ (shiftEdge t e) ω) ∈ rareFastEvent b m a A R ε s n 0} =
      {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} := by
    ext ω
    exact rareFastEvent_translate b m a A R ε s n t (fun e => τ e ω)
  rw [← he]
  exact h.translated_event_probability t _ (measurableSet_rareFastEvent ..)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConnectorGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set

theorem connector_transverse_displacement (b : ℝ) (X d : ℤ) (Y S σ a : ℝ)
    (hS : 0 ≤ S) (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex) (hp : p ∈ connectorWindow b X Y S)
    (hq : q ∈ connectorWindow b (X+d) (Y+σ*a*S) S) :
    S/2 ≤ σ*(transverse b q-transverse b p) ∧
      σ*(transverse b q-transverse b p) ≤ 5*S/2 := by
  have hsq : σ*σ=1 := by nlinarith [sq_abs σ]
  have hep := hp.2
  have heq := hq.2
  have hp' : |σ*(transverse b p-Y)| ≤ S/4 := by simpa [abs_mul,hσ] using hep
  have hq' : |σ*(transverse b q-(Y+σ*a*S))| ≤ S/4 := by simpa [abs_mul,hσ] using heq
  have he : σ*(transverse b q-transverse b p) =
      σ*(transverse b q-(Y+σ*a*S))-σ*(transverse b p-Y)+a*S := by
    calc
      _ = σ*(transverse b q-(Y+σ*a*S))-σ*(transverse b p-Y)+(σ*σ)*(a*S) := by ring
      _ = _ := by rw [hsq]; ring
  rw [he]
  obtain ⟨hp₀,hp₁⟩ := abs_le.mp hp'
  obtain ⟨hq₀,hq₁⟩ := abs_le.mp hq'
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right ha.1 hS,
    mul_le_mul_of_nonneg_right ha.2 hS]

theorem connector_window_bounds (b : ℝ) (X d : ℤ) (Y S σ a : ℝ)
    (hd : 0 ≤ d) (hS : 0 ≤ S) (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p : Vertex) (hp : p ∈ connectorWindow b X Y S ∪
      connectorWindow b (X+d) (Y+σ*a*S) S) :
    (X : ℝ) ≤ p.1 ∧ (p.1 : ℝ) ≤ (X : ℝ)+d ∧
      |transverse b p-Y| ≤ 9*S/4 := by
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  rcases hp with hp | hp
  · refine ⟨by simp [hp.1],?_,?_⟩
    · simp only [hp.1]; linarith
    · linarith [hp.2]
  · refine ⟨?_,by simp [hp.1],?_⟩
    · simp only [hp.1,Int.cast_add]; linarith
    · have hh := abs_add_le (transverse b p-(Y+σ*a*S)) (σ*a*S)
      have he : transverse b p-(Y+σ*a*S)+σ*a*S=transverse b p-Y := by ring
      rw [he,abs_mul,abs_mul,hσ,one_mul,abs_of_nonneg (by linarith : 0 ≤ a),abs_of_nonneg hS] at hh
      nlinarith [hp.2,mul_le_mul_of_nonneg_right ha.2 hS]

theorem transverse_plane_lipschitz (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    |rCoord b z| ≤ 2*‖z‖ := by
  have hh := abs_sub_le (z 1) 0 (b*z 0)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at hh
  have hc₀ := plane_coordinate_le_norm z 0
  have hc₁ := plane_coordinate_le_norm z 1
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  change |z 1-b*z 0| ≤ _
  nlinarith

theorem plane_norm_le_shear (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    ‖z‖ ≤ 2*|xCoord z|+|rCoord b z| := by
  have hh := abs_add_le (rCoord b z) (b*z 0)
  have he : rCoord b z+b*z 0=z 1 := by simp [rCoord_apply]
  rw [he,abs_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  have hn := plane_norm_le_coordinates z
  change ‖z‖ ≤ 2*|z 0|+|rCoord b z|
  linarith

theorem connector_union_diameter (b : ℝ) (hb : |b| ≤ 1)
    (X d : ℤ) (Y S σ a : ℝ) (hd : 0 ≤ d) (hS : 0 ≤ S)
    (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex)
    (hp : p ∈ connectorWindow b X Y S ∪ connectorWindow b (X+d) (Y+σ*a*S) S)
    (hq : q ∈ connectorWindow b X Y S ∪ connectorWindow b (X+d) (Y+σ*a*S) S) :
    ‖latticeEmbed (q-p)‖ ≤ 2*(d : ℝ)+9*S/2 := by
  obtain ⟨hp₀,hp₁,hp₂⟩ := connector_window_bounds b X d Y S σ a hd hS hσ ha p hp
  obtain ⟨hq₀,hq₁,hq₂⟩ := connector_window_bounds b X d Y S σ a hd hS hσ ha q hq
  have hx : |xCoord (latticeEmbed (q-p))| ≤ (d : ℝ) := by
    change |((q-p).1 : ℝ)| ≤ _
    simp only [Prod.fst_sub,Int.cast_sub]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hr : |rCoord b (latticeEmbed (q-p))| ≤ 9*S/2 := by
    have hh := abs_sub_le (transverse b q-Y) 0 (transverse b p-Y)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have he : rCoord b (latticeEmbed (q-p))=(transverse b q-Y)-(transverse b p-Y) := by
      simp [rCoord_apply,latticeEmbed,transverse]; ring
    rw [he]
    linarith
  exact (plane_norm_le_shear b hb _).trans (by linarith)

theorem connector_tube_containment (b : ℝ) (hb : |b| ≤ 1)
    (X d : ℤ) (Y S s σ a : ℝ) (hd : 0 ≤ d) (hs : 0 ≤ s) (hS : s ≤ S)
    (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex) (hp : p ∈ connectorWindow b X Y S)
    (hq : q ∈ connectorWindow b (X+d) (Y+σ*a*S) S) :
    SegmentTube p q (s/2) ⊆ (connectorVertices b X d Y S s : Set Vertex) := by
  have hS0 : 0 ≤ S := hs.trans hS
  obtain ⟨hp₀,hp₁,hp₂⟩ := connector_window_bounds b X d Y S σ a hd hS0 hσ ha p (Or.inl hp)
  obtain ⟨hq₀,hq₁,hq₂⟩ := connector_window_bounds b X d Y S σ a hd hS0 hσ ha q (Or.inr hq)
  intro z hz
  obtain ⟨t,ht₀,ht₁,ht⟩ := hz
  have hsegx : xCoord (segmentPoint p q t)=(1-t)*(p.1 : ℝ)+t*(q.1 : ℝ) := by
    simp [segmentPoint,latticeEmbed,xCoord_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hsegr : rCoord b (segmentPoint p q t)-Y=
      (1-t)*(transverse b p-Y)+t*(transverse b q-Y) := by
    simp [segmentPoint,latticeEmbed,rCoord_apply,transverse,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hseg₀ : (X : ℝ) ≤ xCoord (segmentPoint p q t) := by
    rw [hsegx]
    nlinarith [mul_le_mul_of_nonneg_left hp₀ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₀ ht₀]
  have hseg₁ : xCoord (segmentPoint p q t) ≤ (X : ℝ)+d := by
    rw [hsegx]
    nlinarith [mul_le_mul_of_nonneg_left hp₁ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₁ ht₀]
  have hseg₂ : |rCoord b (segmentPoint p q t)-Y| ≤ 9*S/4 := by
    rw [hsegr]
    have hh := abs_add_le ((1-t)*(transverse b p-Y)) (t*(transverse b q-Y))
    rw [abs_mul,abs_mul,abs_of_nonneg ht₀,abs_of_nonneg (by linarith : 0 ≤ 1-t)] at hh
    nlinarith [mul_le_mul_of_nonneg_left hp₂ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₂ ht₀]
  have hx := (plane_coordinate_le_norm (latticeEmbed z-segmentPoint p q t) 0).trans ht
  have hr := (transverse_plane_lipschitz b hb (latticeEmbed z-segmentPoint p q t)).trans
    (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2))
  have hx' : |(z.1 : ℝ)-xCoord (segmentPoint p q t)| ≤ s/2 := by
    simpa [latticeEmbed,PiLp.sub_apply] using hx
  have hr' : |transverse b z-rCoord b (segmentPoint p q t)| ≤ s := by
    have he : 2*(s/2)=s := by ring
    simpa [map_sub,rCoord_apply,latticeEmbed,transverse,he] using hr
  change z ∈ connectorVertices b X d Y S s
  rw [mem_connectorVertices]
  refine ⟨?_,?_,?_⟩
  · linarith [(abs_le.mp hx').1]
  · linarith [(abs_le.mp hx').2]
  · have hh := abs_add_le (transverse b z-rCoord b (segmentPoint p q t))
      (rCoord b (segmentPoint p q t)-Y)
    rw [sub_add_sub_cancel] at hh
    linarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SourceConnector
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology

theorem contactSide_of_sign (plus : Bool) (r : ℝ) (hr : 0 < contactSign plus*r) :
    r ∈ contactSide plus := by
  cases plus <;> simpa [contactSign,contactSide] using hr

theorem trialWindow_scale_bounds (M : ℕ) (hM : 0 < M) (R s : ℝ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    s ≤ trialWindow M R s ∧ trialWindow M R s ≤ (200*M*(R+1))*s := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc := Nat.le_ceil s
  have hc' := Nat.ceil_lt_add_one (by linarith : 0 ≤ s)
  have hbase : s ≤ (R+1)*(⌈s⌉₊ : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hM' (by positivity : 0 ≤ (R+1)*(⌈s⌉₊ : ℝ))
  have hupper := mul_le_mul_of_nonneg_left (show (⌈s⌉₊ : ℝ) ≤ 2*s by linarith)
    (show 0 ≤ 100*(M : ℝ)*(R+1) by positivity)
  unfold trialWindow trialSpacing
  constructor <;> nlinarith

/-- The two source tests correspond to a=1 and a=2. D0 is fixed after M;
the probability estimate is uniform over every column X and transverse
phase Y. No geometric premise or connector-probability premise remains. -/
theorem gamma_source_connector_test {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ} (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ X : ℤ, ∀ Y a : ℝ, 1 ≤ a → a ≤ 2 →
      P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent
        (connectorVertices b X ⌈D0*s⌉ Y (trialWindow M R s) s)
        (connectorWindow b X Y (trialWindow M R s))
        (connectorWindow b (X+⌈D0*s⌉)
          (Y+contactSign plus*a*trialWindow M R s) (trialWindow M R s))
        (sourceSupportCost (gammaMeanNorm h hshape hrate) b plus ε s)} < κ := by
  let C : ℝ := 200*M*(R+1)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨D0,hD0,hgap⟩ := gamma_connector_support_gap h hshape hrate b plus ε C hε hC
  let D := 2*(D0+1)+9*C/2
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D0,hD0,?_⟩
  intro κ hκ
  filter_upwards [gamma_allPairsRegionEvent h hshape hrate D (ε/4) (1/2)
    hD (by positivity) (by norm_num) κ hκ,eventually_ge_atTop (1 : ℝ)] with s hs hs1
  intro X Y a ha₀ ha₁
  let S := trialWindow M R s
  let d : ℤ := ⌈D0*s⌉
  have hs0 : 0 < s := by linarith
  have hSb := trialWindow_scale_bounds M hM R s hR hs1
  have hS : s ≤ S := hSb.1
  have hSC : S ≤ C*s := hSb.2
  have hS0 : 0 < S := hs0.trans_le hS
  have hdlo : D0*s ≤ (d : ℝ) := Int.le_ceil _
  have hdhi : (d : ℝ) ≤ (D0+1)*s := by
    have hh : (d : ℝ) < D0*s+1 := Int.ceil_lt_add_one _
    nlinarith
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) ≤ d := by nlinarith
    exact_mod_cast this
  apply hs
  · intro p hp q hq
    exact (connector_union_diameter b hb X d Y S (contactSign plus) a hd0 hS0.le
      (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq).trans (by dsimp [D]; nlinarith)
  · intro p hp q hq
    have hx : xCoord (latticeEmbed (q-p))=(d : ℝ) := by
      change ((q-p).1 : ℝ)=_
      rw [Prod.fst_sub,hp.1,hq.1]
      congr 1
      omega
    have hr : rCoord b (latticeEmbed (q-p))=transverse b q-transverse b p := by
      simp [rCoord_apply,latticeEmbed,transverse]; ring
    have htrans := connector_transverse_displacement b X d Y S (contactSign plus) a
      hS0.le (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq
    have hpos : 0 < contactSign plus*rCoord b (latticeEmbed (q-p)) := by
      rw [hr]; linarith [htrans.1]
    have habs : |rCoord b (latticeEmbed (q-p))| ≤ 3*C*s := by
      have he : |rCoord b (latticeEmbed (q-p))| =
          contactSign plus*rCoord b (latticeEmbed (q-p)) := by
        calc
          _ = |contactSign plus*rCoord b (latticeEmbed (q-p))| := by simp [abs_mul]
          _ = _ := abs_of_pos hpos
      rw [he,hr]
      nlinarith [htrans.2]
    have hg := hgap s hs0 (latticeEmbed (q-p)) (by rw [hx]; exact hdlo)
      (contactSide_of_sign plus _ hpos) habs
    unfold sourceSupportCost
    linarith
  · intro p hp q hq
    simpa only [one_div,mul_comm (2⁻¹ : ℝ) s,← div_eq_mul_inv] using
      connector_tube_containment b hb X d Y S s (contactSign plus) a hd0 hs0.le hS
        (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem nearest_integer_error (t : ℝ) : |(⌊t+1/2⌋ : ℝ)-t| ≤ 1/2 := by
  have hlo := Int.floor_le (t+1/2)
  have hhi := Int.lt_floor_add_one (t+1/2)
  apply abs_le.mpr
  constructor <;> linarith

theorem trialTranslate_error (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) :
    |transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)| ≤ 1/2 := by
  have hh := nearest_integer_error (b*X+Y+trialOffset M R s j)
  convert hh using 1
  simp [trialTranslate,transverse]
  congr 1
  ring

theorem trialSpacing_bounds (R s : ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    1 ≤ trialSpacing R s ∧ R*s ≤ trialSpacing R s := by
  have hc := Nat.le_ceil s
  have hn : (1 : ℝ) ≤ (⌈s⌉₊ : ℝ) := by linarith
  unfold trialSpacing
  constructor
  · nlinarith
  · nlinarith

/-- Distinct trials have strictly disjoint transverse strips, uniformly in
both the longitudinal column and the real transverse phase. -/
theorem trial_centers_separated (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j l : Fin M) (hjl : j ≠ l) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    2*R*s < |transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l)| := by
  have hB := trialSpacing_bounds R s hR hs
  have he := trialTranslate_error b X Y M R s j
  have hf := trialTranslate_error b X Y M R s l
  have he' := abs_le.mp he
  have hf' := abs_le.mp hf
  have hdiff : trialOffset M R s j-trialOffset M R s l =
      6*((j.val : ℝ)-(l.val : ℝ))*trialSpacing R s := by unfold trialOffset; ring
  have hne : j.val ≠ l.val := fun hh => hjl (Fin.ext hh)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : (j.val : ℝ)+1 ≤ l.val := by exact_mod_cast hlt
    have ha := neg_le_abs (transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l))
    nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ trialSpacing R s)]
  · have hn : (l.val : ℝ)+1 ≤ j.val := by exact_mod_cast hgt
    have ha := le_abs_self (transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l))
    nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ trialSpacing R s)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

theorem rareFastTrials_disjoint (b A R s : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    Pairwise (fun j l : Fin M => Disjoint
      (rareFastVertices b A R s n (trialTranslate b X Y M R s j))
      (rareFastVertices b A R s n (trialTranslate b X Y M R s l))) := by
  intro j l hjl
  apply strip_vertices_disjoint _ _ b
    (transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s l)) (R*s)
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · simpa only [mul_assoc] using trial_centers_separated b X Y M R s j l hjl hR hs

/-- Disjoint translated trials amplify the original crossing success
probability. -/
theorem rareFastTrials_failure_bound (h : GammaEnvironment shape rate P τ)
    (b m a A R ε s p0 : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hp0 : p0 ≤ P.real {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0}) :
    P.real {ω | ∀ j : Fin M, (fun e => τ e ω) ∉ rareFastEvent b m a A R ε s n
      (trialTranslate b X Y M R s j)} ≤ (1-p0)^M := by
  have hh := Grid.disjoint_trials_failure_bound h (Finset.univ : Finset (Fin M))
    (fun j => rareFastEvent b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun j => internalEdges (rareFastVertices b A R s n (trialTranslate b X Y M R s j)))
    (fun _ _ => measurableSet_rareFastEvent ..) (fun j _ => rareFastEvent_depends b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun _ _ _ _ hij => internalEdges_disjoint (rareFastTrials_disjoint b A R s n X Y M hR hs hij))
    p0 (fun j _ => ?_)
  · simpa using hh
  · unfold Measure.real
    rw [rareFastEvent_probability_translate h]
    exact hp0

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem goodSiteEvent_failure_bound (h : GammaEnvironment shape rate P τ)
    (μ : Plane → ℝ) (b A R ε s p0 : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ) (v : Vertex)
    (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hp0 : p0 ≤ P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n 0}) :
    P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent μ b A R ε s plus n d M v} ≤
      (1-p0)^M + P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 1} +
        P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 2} := by
  let _ := h.probability
  let F := {ω | ∀ j : Fin M, (fun e => τ e ω) ∉ siteTrial μ b A R ε s plus n d M v j}
  let C₁ := {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 1}
  let C₂ := {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 2}
  have hsub : {ω | (fun e => τ e ω) ∉ goodSiteEvent μ b A R ε s plus n d M v} ⊆
      (F ∪ C₁) ∪ C₂ := by
    intro ω hh
    simp only [goodSiteEvent,mem_ofPred_eq,not_and_or,not_exists] at hh
    rcases hh with hf | hc | hc
    · exact Or.inl (Or.inl hf)
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  have hf : P.real F ≤ (1-p0)^M := rareFastTrials_failure_bound h b (μ (direction b))
    (extremeSlope μ b plus) A R ε s p0 n (blockX n d v)
    (blockY (contactSign plus) (trialWindow M R s) v) M hR hs hp0
  calc
    _ ≤ P.real ((F ∪ C₁) ∪ C₂) := measureReal_mono hsub
    _ ≤ P.real (F ∪ C₁)+P.real C₂ := measureReal_union_le _ _
    _ ≤ (P.real F+P.real C₁)+P.real C₂ := by linarith [measureReal_union_le (μ := P) F C₁]
    _ ≤ _ := by dsimp [C₁,C₂]; linarith

/-- Choosing the separation after the trial count gives an error uniform
in both the site and the longitudinal scale. -/
theorem gamma_goodSiteEvent_failure_oai (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ (n : ℤ) (v : Vertex) (p0 : ℝ),
      p0 ≤ P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} →
      P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v} <
        (1-p0)^M+κ := by
  obtain ⟨D0,hD0,hc⟩ := gamma_source_connector_test h hshape hrate b hb plus M hM R ε hR hε
  refine ⟨D0,hD0,?_⟩
  intro κ hκ
  filter_upwards [hc (κ/2) (by positivity),eventually_ge_atTop (1 : ℝ)] with s hcs hs
  intro n v p0 hp0
  have h1 := hcs (blockX n ⌈D0*s⌉ v+n)
    (blockY (contactSign plus) (trialWindow M R s) v) 1 (by norm_num) (by norm_num)
  have h2 := hcs (blockX n ⌈D0*s⌉ v+n)
    (blockY (contactSign plus) (trialWindow M R s) v) 2 (by norm_num) (by norm_num)
  have hh := goodSiteEvent_failure_bound h (gammaMeanNorm h hshape hrate) b A R ε s p0 plus n ⌈D0*s⌉ M v hR hs hp0
  change P.real {ω | (fun e => τ e ω) ∉ siteConnector (gammaMeanNorm h hshape hrate) b R ε s plus n ⌈D0*s⌉ M v 1} < κ/2 at h1
  change P.real {ω | (fun e => τ e ω) ∉ siteConnector (gammaMeanNorm h hshape hrate) b R ε s plus n ⌈D0*s⌉ M v 2} < κ/2 at h2
  linarith

end GammaFPP.CrossingBridge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure_oai.{u_1} := @OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure_oai.{u_1}
