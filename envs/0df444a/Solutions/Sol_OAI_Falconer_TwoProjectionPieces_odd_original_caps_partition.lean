-- Prove2me | solution 1 for OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:02:12.626826+00:00
-- url     : https://prove2.me/submissions/27316e8f-3b4a-44fb-88b2-ed9a14d49595

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_Regularization_endpoint_one_scale_gain
import Theorems.Thm_OAI_Falconer_Regularization_nonendpoint_one_scale_gain

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularBootstrap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Endpoint of the thin-tube bootstrap

This is the order-theoretic step in Proposition `prep:thin-upgrade`.
Its hypotheses describe the closed set of available exponents inside
`[k - 1, k - 1 / 2]`, with strict improvement below the endpoint.
-/

namespace Falconer
open Set

/-- A closed family of available exponents containing the integer starting
exponent and admitting a strict improvement below the desired endpoint
contains the half-integer endpoint. -/
theorem thin_tube_bootstrap_endpoint (k : ℕ) (A : Set ℝ)
    (hclosed : IsClosed A) (hstart : (k : ℝ) - 1 ∈ A)
    (hupper : ∀ q ∈ A, q ≤ (k : ℝ) - 1 / 2)
    (himprove : ∀ q ∈ A, q < (k : ℝ) - 1 / 2 → ∃ q' ∈ A, q < q') :
    (k : ℝ) - 1 / 2 ∈ A := by
  have hnonempty : A.Nonempty := ⟨_, hstart⟩
  have hbounded : BddAbove A := ⟨(k : ℝ) - 1 / 2, hupper⟩
  have hsup : sSup A ∈ A := hclosed.csSup_mem hnonempty hbounded
  have hsup_upper : sSup A ≤ (k : ℝ) - 1 / 2 := hupper _ hsup
  by_cases heq : sSup A = (k : ℝ) - 1 / 2
  · exact heq ▸ hsup
  · obtain ⟨q, hq, hlt⟩ := himprove _ hsup (lt_of_le_of_ne hsup_upper heq)
    exact False.elim ((not_lt_of_ge (le_csSup hbounded hq)) hlt)

/-- At resolution `R⁻¹`, increasing the cap exponent by at most `e` costs
only the allowed factor `R ^ e`. This is the quantitative inequality used
when closing the set of available exponents in `prep:thin-upgrade`. -/
theorem cap_exponent_loss_transfer {R u q q' e : ℝ}
    (hR : 1 ≤ R) (hu : R⁻¹ ≤ u) (hqq : q ≤ q') (hgap : q' - q ≤ e) :
    u ^ q ≤ R ^ e * u ^ q' := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hupos : 0 < u := (inv_pos.mpr hRpos).trans_le hu
  have hcompare : u ^ (q - q') ≤ R ^ e := by
    calc
      u ^ (q - q') ≤ (R⁻¹) ^ (q - q') :=
        Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hRpos) hu (sub_nonpos.mpr hqq)
      _ = R ^ (q' - q) := by
        rw [← Real.rpow_neg_eq_inv_rpow]
        congr 1
        ring
      _ ≤ R ^ e := Real.rpow_le_rpow_of_exponent_le hR hgap
  calc
    u ^ q = u ^ (q - q') * u ^ q' := by
      rw [← Real.rpow_add hupos]
      congr 1
      ring
    _ ≤ R ^ e * u ^ q' := mul_le_mul_of_nonneg_right hcompare (Real.rpow_nonneg hupos.le _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_perpendicularPart_sq {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖^2 = ‖v‖^2-(inner ℝ w v)^2 := by
  have h := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right,real_inner_comm v w,norm_smul,hw,
    mul_one,Real.norm_eq_abs,sq_abs] at h
  dsimp only [perpendicularPart]
  rw [real_inner_comm v w]
  nlinarith

theorem unit_close_of_perpendicular {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hinner : 0 ≤ inner ℝ w u) :
    ‖w-u‖ ≤ 2*‖perpendicularPart w u‖ := by
  have hsq := norm_sub_sq_real w u
  have hp := norm_perpendicularPart_sq hw u
  have ha : inner ℝ w u ≤ 1 := by
    have h := (le_abs_self (inner ℝ w u)).trans (abs_real_inner_le_norm w u)
    simpa only [hw,hu,mul_one] using h
  rw [hw,hu] at hsq
  rw [hu] at hp
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 4*inner ℝ w u+2 by linarith)
  nlinarith [norm_nonneg (w-u),norm_nonneg (perpendicularPart w u)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ProjectedDirections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lifting auxiliary radial directions

The integer-cap argument in `prep:integer-caps` uses the map
`w ↦ P w / ‖P w‖` only where projected separation bounds `‖P w‖`
away from zero. These elementary facts keep the auxiliary direction
map separate from the original Euclidean distance map.
-/

namespace Falconer
open NormedSpace

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalization is Lipschitz on vectors whose norms are bounded below. -/
theorem normalize_dist_le {v w : E} {c : ℝ} (hc : 0 < c)
    (hv : c ≤ ‖v‖) (hw : c ≤ ‖w‖) :
    dist (normalize v) (normalize w) ≤ (2 / c) * dist v w := by
  have hvpos : 0 < ‖v‖ := hc.trans_le hv
  have hwne : w ≠ 0 := norm_pos_iff.mp (hc.trans_le hw)
  have hscale : ‖v‖ * dist (normalize v) (normalize w) ≤ 2 * dist v w := by
    calc
      ‖v‖ * dist (normalize v) (normalize w) =
          dist (‖v‖ • normalize v) (‖v‖ • normalize w) := by
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ dist (‖v‖ • normalize v) (‖w‖ • normalize w) +
          dist (‖w‖ • normalize w) (‖v‖ • normalize w) := dist_triangle _ _ _
      _ = dist v w + |‖w‖ - ‖v‖| := by
        have he : dist (‖w‖ • normalize w) (‖v‖ • normalize w) = |‖w‖ - ‖v‖| := by
          rw [dist_eq_norm, ← sub_smul, norm_smul, norm_normalize hwne,
            Real.norm_eq_abs, mul_one]
        rw [he, norm_smul_normalize, norm_smul_normalize]
      _ ≤ dist v w + dist w v :=
        add_le_add le_rfl (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le w v)
      _ = 2 * dist v w := by rw [dist_comm w v]; ring
  calc
    dist (normalize v) (normalize w) ≤ (2 * dist v w) / ‖v‖ := by
      apply (le_div_iff₀ hvpos).mpr
      simpa only [mul_comm] using hscale
    _ ≤ (2 * dist v w) / c :=
      div_le_div_of_nonneg_left (by positivity) hc hv
    _ = (2 / c) * dist v w := by ring

/-- A linear map commutes with radial directions after re-normalization. -/
theorem normalize_map_radial (P : E →L[ℝ] F) {x y : E} (hxy : y ≠ x) :
    normalize (P (normalize (y - x))) = normalize (P y - P x) := by
  change normalize (P (‖y - x‖⁻¹ • (y - x))) = _
  rw [map_smul, normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))), map_sub]

/-- The auxiliary normalized projection has a uniform Lipschitz bound on the
part of the sphere on which projected separation is available. -/
theorem normalized_projection_dist_le (P : E →L[ℝ] F) {c : ℝ} (hc : 0 < c)
    (hP : ‖P‖ ≤ 1) {v w : E} (hv : c ≤ ‖P v‖) (hw : c ≤ ‖P w‖) :
    dist (normalize (P v)) (normalize (P w)) ≤ (2 / c) * dist v w := by
  apply (normalize_dist_le hc hv hw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    dist (P v) (P w) ≤ ‖P‖ * dist v w := by
      simpa only [dist_eq_norm, map_sub] using P.le_opNorm (v - w)
    _ ≤ 1 * dist v w := mul_le_mul_of_nonneg_right hP dist_nonneg
    _ = dist v w := one_mul _

end
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Availability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Available radial exponents in the original product measure

These definitions record `prep:availability`. A bad set is a measurable
set of original pairs, and each remaining radial fiber is measured using
the original opposite marginal. No fiber is renormalized.
The closure and bootstrap express parts of `prep:thin-upgrade`.
-/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

private theorem cap_power_change {R u q q' a : ℝ}
    (hR : 1 ≤ R) (hu : R⁻¹ ≤ u) (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (hgap : q' - q ≤ a) : u ^ q ≤ R ^ a * u ^ q' := by
  by_cases hqq : q ≤ q'
  · exact cap_exponent_loss_transfer hR hu hqq hgap
  · have hupos : 0 < u := (inv_pos.mpr (zero_lt_one.trans_le hR)).trans_le hu
    have hp := Real.rpow_le_rpow_of_exponent_ge hupos hu1 (not_le.mp hqq).le
    exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hupos.le _) (Real.one_le_rpow hR ha))

private theorem cap_bound_change {R u q q' e a : ℝ}
    (hR : 1 ≤ R) (hu : R⁻¹ ≤ u) (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (hgap : q' - q ≤ a) :
    R ^ e * u ^ q ≤ R ^ (e + a) * u ^ q' := by
  calc
    R ^ e * u ^ q ≤ R ^ e * (R ^ a * u ^ q') :=
      mul_le_mul_of_nonneg_left (cap_power_change hR hu hu1 ha hgap) (Real.rpow_nonneg (by linarith) _)
    _ = R ^ (e + a) * u ^ q' := by
      rw [Real.rpow_add (zero_lt_one.trans_le hR)]
      ring

theorem RadialCapBound.change_exponent {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {e q q' a : ℝ}
    (h : RadialCapBound μ ν G N e q) (ha : 0 ≤ a) (hgap : q' - q ≤ a) :
    RadialCapBound μ ν G N (e + a) q' := by
  have hR : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  constructor
  · intro x hx w hw u hu hu1
    exact (h.1 x hx w hw u hu hu1).trans
      (ENNReal.ofReal_le_ofReal (cap_bound_change hR hu hu1 ha hgap))
  · intro y hy w hw u hu hu1
    exact (h.2 y hy w hw u hu hu1).trans
      (ENNReal.ofReal_le_ofReal (cap_bound_change hR hu hu1 ha hgap))

/-- Restricting a pair relation can only decrease each original radial fiber. -/
theorem RadialCapBound.mono {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G H : Set (Space d × Space d)} {e q : ℝ}
    (h : RadialCapBound μ ν G N e q) (hHG : H ⊆ G) :
    RadialCapBound μ ν H N e q := by
  constructor
  · intro x hx w hw u hu hu1
    have hsets : {y | (x, y) ∈ H ∧ dist (radialDirection x y) w < u} ⊆
        {y | (x, y) ∈ G ∧ dist (radialDirection x y) w < u} := by
      rintro y ⟨hy, hd⟩
      exact ⟨hHG hy, hd⟩
    exact (measure_mono hsets).trans (h.1 x hx w hw u hu hu1)
  · intro y hy w hw u hu hu1
    have hsets : {x | (x, y) ∈ H ∧ dist (radialDirection y x) w < u} ⊆
        {x | (x, y) ∈ G ∧ dist (radialDirection y x) w < u} := by
      rintro x ⟨hx, hd⟩
      exact ⟨hHG hx, hd⟩
    exact (measure_mono hsets).trans (h.2 y hy w hw u hu hu1)

/-- Integer cap bounds continue to hold after the coarse pair filters of
`prep:coarse-filter` are imposed. Only the original bad pairs still lying
inside the new filter need to be deleted. -/
theorem CapAvailable.restrict {d : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {Γ Γ' : ℕ → Set (Space d × Space d)} {q : ℝ}
    (hq : CapAvailable μ ν Γ q) (hΓ' : ∀ N, MeasurableSet (Γ' N))
    (hsub : ∀ N, Γ' N ⊆ Γ N) : CapAvailable μ ν Γ' q := by
  intro e he
  obtain ⟨c, C, hc, hC, K, hK⟩ := hq e he
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  obtain ⟨B, hB, _, hmass, hcap⟩ := hK N hN
  refine ⟨B ∩ Γ' N, hB.inter (hΓ' N), inter_subset_right,
    (measure_mono inter_subset_left).trans hmass, hcap.mono ?_⟩
  intro z hz
  exact ⟨hsub N hz.1, fun hb => hz.2 ⟨hb, hz.1⟩⟩

/-- Decreasing the requested cap exponent needs no additional deletion. -/
theorem CapAvailable.mono {d : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {Γ : ℕ → Set (Space d × Space d)} {q q' : ℝ}
    (hq : CapAvailable μ ν Γ q) (hqq : q' ≤ q) : CapAvailable μ ν Γ q' := by
  intro e he
  obtain ⟨c, C, hc, hC, K, hK⟩ := hq e he
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  obtain ⟨B, hB, hsub, hmass, hcap⟩ := hK N hN
  refine ⟨B, hB, hsub, hmass, ?_⟩
  simpa using hcap.change_exponent (le_refl (0 : ℝ)) (sub_nonpos.mpr hqq)

/-- The allowance of every positive scale loss makes availability closed in
the exponent. The same original bad sets and deletion rates work after the
small exponent change. -/
theorem isClosed_capAvailable {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) :
    IsClosed {q : ℝ | CapAvailable μ ν Γ q} := by
  apply isClosed_of_closure_subset
  intro q hq e he
  obtain ⟨q₀, hq₀, hdist⟩ := Metric.mem_closure_iff.1 hq (e / 2) (by linarith)
  obtain ⟨c, C, hc, hC, K, hK⟩ := hq₀ (e / 2) (by linarith)
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  obtain ⟨B, hB, hsub, hmass, hcap⟩ := hK N hN
  refine ⟨B, hB, hsub, hmass, ?_⟩
  have hgap : q - q₀ ≤ e / 2 := by
    rw [Real.dist_eq] at hdist
    exact le_of_lt ((le_abs_self _).trans_lt hdist)
  convert hcap.change_exponent (by linarith : (0 : ℝ) ≤ e / 2) hgap using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The thin-tube endpoint follows from the integer starting exponent and
the one-scale strict improvement, using closure of cap availability. -/
theorem capAvailable_half_integer {d : ℕ} (k : ℕ)
    (μ ν : ProbabilityMeasure (Space d)) (Γ : ℕ → Set (Space d × Space d))
    (hstart : CapAvailable μ ν Γ ((k : ℝ) - 1))
    (himprove : ∀ q : ℝ, (k : ℝ) - 1 ≤ q → q < (k : ℝ) - 1 / 2 →
      CapAvailable μ ν Γ q →
      ∃ q' : ℝ, q < q' ∧ q' ≤ (k : ℝ) - 1 / 2 ∧ CapAvailable μ ν Γ q') :
    CapAvailable μ ν Γ ((k : ℝ) - 1 / 2) := by
  let A := Set.Icc ((k : ℝ) - 1) ((k : ℝ) - 1 / 2) ∩
    {q : ℝ | CapAvailable μ ν Γ q}
  have hclosed : IsClosed A := isClosed_Icc.inter (isClosed_capAvailable μ ν Γ)
  have hfirst : (k : ℝ) - 1 ∈ A := ⟨⟨le_rfl, by linarith⟩, hstart⟩
  have hstep : ∀ q ∈ A, q < (k : ℝ) - 1 / 2 → ∃ q' ∈ A, q < q' := by
    intro q hq hqlt
    obtain ⟨q', hqq', hq'upper, hq'available⟩ := himprove q hq.1.1 hqlt hq.2
    exact ⟨q', ⟨⟨hq.1.1.trans hqq'.le, hq'upper⟩, hq'available⟩, hqq'⟩
  exact (thin_tube_bootstrap_endpoint k A hclosed hfirst (fun q hq => hq.1.2) hstep).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of cap bounds from auxiliary projections

The fixed factor in the cap radius can be absorbed in an arbitrarily small
power of the resolution. The center of an original cap need not be in the
domain where normalized projection is Lipschitz; we choose an actual
source direction in a nonempty cap, and double its radius before projecting.
This is the lifting step of `prep:integer-caps`.
-/

namespace Falconer
open Set MeasureTheory Filter NormedSpace
open scoped ENNReal Topology

private theorem radial_ne_diagonal {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    y ≠ x := by
  intro heq
  subst y
  simp [radialDirection] at h
  linarith

private theorem projected_radial_identity {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    NormedSpace.normalize (P (radialDirection x y)) = radialDirection (P x) (P y) := by
  simpa only [radialDirection, NormedSpace.normalize] using
    normalize_map_radial P (radial_ne_diagonal P hc h)

private theorem projected_radial_norm {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    ‖radialDirection (P x) (P y)‖ = 1 := by
  rw [← projected_radial_identity P hc h]
  exact norm_normalize (norm_pos_iff.mp (hc.trans_le h))

/-- Every actual direction in an original radius-`u` cap maps into a radius
`max 1 (4/c) * u` cap about any chosen actual direction in the first cap. -/
theorem projected_radial_cap {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y y₀ w : Space d} {c u : ℝ} (hc : 0 < c) (hP : ‖P‖ ≤ 1)
    (hy : c ≤ ‖P (radialDirection x y)‖)
    (hy₀ : c ≤ ‖P (radialDirection x y₀)‖)
    (hcap : dist (radialDirection x y) w < u)
    (hcap₀ : dist (radialDirection x y₀) w < u) :
    dist (radialDirection (P x) (P y)) (radialDirection (P x) (P y₀)) <
      max 1 (4 / c) * u := by
  have hu : 0 < u := dist_nonneg.trans_lt hcap
  have hL : 0 < 2 / c := div_pos (by norm_num) hc
  have hdist : dist (radialDirection x y) (radialDirection x y₀) < 2 * u := by
    have ht := dist_triangle (radialDirection x y) w (radialDirection x y₀)
    rw [dist_comm w (radialDirection x y₀)] at ht
    linarith
  calc
    dist (radialDirection (P x) (P y)) (radialDirection (P x) (P y₀)) =
        dist (NormedSpace.normalize (P (radialDirection x y))) (NormedSpace.normalize (P (radialDirection x y₀))) := by
      rw [projected_radial_identity P hc hy, projected_radial_identity P hc hy₀]
    _ ≤ (2 / c) * dist (radialDirection x y) (radialDirection x y₀) :=
      normalized_projection_dist_le P hc hP hy hy₀
    _ < (2 / c) * (2 * u) := mul_lt_mul_of_pos_left hdist hL
    _ = (4 / c) * u := by ring
    _ ≤ max 1 (4 / c) * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le

/-- A fixed radius enlargement is absorbed into the permitted scale loss. -/
theorem eventually_radius_factor_absorbed {K q a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, K ^ q ≤ ((2 : ℝ) ^ N) ^ a := by
  have ht : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact ht.eventually (eventually_ge_atTop (K ^ q))

private theorem enlarged_cap_scalar {R K u e a q : ℝ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hu : 0 ≤ u) (hconstant : K ^ q ≤ R ^ a) :
    R ^ e * (K * u) ^ q ≤ R ^ (e + a) * u ^ q := by
  rw [Real.mul_rpow hK hu, Real.rpow_add (zero_lt_one.trans_le hR)]
  calc
    R ^ e * (K ^ q * u ^ q) = (R ^ e * u ^ q) * K ^ q := by ring
    _ ≤ (R ^ e * u ^ q) * R ^ a := mul_le_mul_of_nonneg_left hconstant
      (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hR).le e) (Real.rpow_nonneg hu q))
    _ = R ^ e * R ^ a * u ^ q := by ring

/-- A cap estimate for the projected source law bounds a fiber of the
original law. Source labels remain distinct even when their images coincide. -/
theorem projected_fiber_cap_bound {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (ν : ProbabilityMeasure (Space d)) (H : Set (Space d)) (J : Set (Space k))
    (x : Space d) {R c e a q : ℝ}
    (hR : 1 ≤ R) (hc : 0 < c) (hP : ‖P‖ ≤ 1) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hconstant : (max 1 (4 / c)) ^ q ≤ R ^ a)
    (himage : ∀ y ∈ H, P y ∈ J)
    (hlower : ∀ y ∈ H, c ≤ ‖P (radialDirection x y)‖)
    (hcap : ∀ w : Space k, ‖w‖ = 1 → ∀ u : ℝ, R⁻¹ ≤ u → u ≤ 1 →
      ((ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure (Space k)) : Measure (Space k))
        {y | y ∈ J ∧ dist (radialDirection (P x) y) w < u} ≤
          ENNReal.ofReal (R ^ e * u ^ q)) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, R⁻¹ ≤ u → u ≤ 1 →
      (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ (e + a) * u ^ q) := by
  intro w _ u hu _
  have hupos : 0 < u := (inv_pos.mpr (zero_lt_one.trans_le hR)).trans_le hu
  let K : ℝ := max 1 (4 / c)
  have hK : 1 ≤ K := le_max_left _ _
  have hscalar := enlarged_cap_scalar (e := e) hR (zero_le_one.trans hK) hupos.le hconstant
  by_cases hsmall : K * u ≤ 1
  · by_cases hex : Set.Nonempty {y | y ∈ H ∧ dist (radialDirection x y) w < u}
    · obtain ⟨y₀, hy₀, hcap₀⟩ := hex
      have hset : {y | y ∈ H ∧ dist (radialDirection x y) w < u} ⊆
          P ⁻¹' {y | y ∈ J ∧ dist (radialDirection (P x) y)
            (radialDirection (P x) (P y₀)) < K * u} := by
        rintro y ⟨hy, hycap⟩
        exact ⟨himage y hy, projected_radial_cap P hc hP (hlower y hy)
          (hlower y₀ hy₀) hycap hcap₀⟩
      have hpre := (measure_mono (μ := (ν : Measure (Space d))) hset).trans
        (Measure.le_map_apply P.continuous.measurable.aemeasurable _)
      have hrad : R⁻¹ ≤ K * u := hu.trans (le_mul_of_one_le_left hupos.le hK)
      exact hpre.trans ((hcap _ (projected_radial_norm P hc (hlower y₀ hy₀))
        _ hrad hsmall).trans (ENNReal.ofReal_le_ofReal hscalar))
    · simp only [Set.not_nonempty_iff_eq_empty.mp hex, measure_empty]
      exact bot_le
  · have hmass : (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤ 1 := by
      exact (measure_mono (subset_univ _)).trans_eq (measure_univ : (ν : Measure (Space d)) univ = 1)
    have hpow : 1 ≤ (K * u) ^ q := Real.one_le_rpow (le_of_not_ge hsmall) hq
    have hepow : 1 ≤ R ^ e := Real.one_le_rpow hR he
    have hone : 1 ≤ R ^ (e + a) * u ^ q := by
      have : 1 ≤ R ^ e * (K * u) ^ q := by nlinarith
      exact this.trans hscalar
    exact hmass.trans (by simpa using (ENNReal.ofReal_le_ofReal hone))

private theorem map_mem_support {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (μ : ProbabilityMeasure (Space d)) {x : Space d}
    (hx : x ∈ (μ : Measure (Space d)).support) :
    P x ∈ ((μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure (Space k)) : Measure (Space k)).support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  have hpre : P ⁻¹' U ∈ 𝓝 x := P.continuous.continuousAt.preimage_mem_nhds hU
  exact ((Measure.mem_support_iff_forall _).mp hx _ hpre).trans_le
    (Measure.le_map_apply P.continuous.measurable.aemeasurable U)

/-- Pull back both cap estimates through a fixed auxiliary projection. -/
theorem RadialCapBound.pullback {d k N : ℕ} (P : Space d →L[ℝ] Space k)
    (μ ν : ProbabilityMeasure (Space d))
    {G : Set (Space d × Space d)} {G' : Set (Space k × Space k)} {c e a q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hconstant : (max 1 (4 / c)) ^ q ≤ ((2 : ℝ) ^ N) ^ a)
    (hG : G ⊆ Prod.map P P ⁻¹' G')
    (hlower : ∀ z ∈ G, c ≤ ‖P (radialDirection z.1 z.2)‖ ∧
      c ≤ ‖P (radialDirection z.2 z.1)‖)
    (hcap : RadialCapBound (μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) G' N e q) :
    RadialCapBound μ ν G N (e + a) q := by
  have hR : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  constructor
  · intro x hx
    exact projected_fiber_cap_bound P ν {y | (x, y) ∈ G} {y | (P x, y) ∈ G'} x
      hR hc hP he hq hconstant
      (fun y hy => hG hy) (fun y hy => (hlower (x, y) hy).1)
      (hcap.1 (P x) (map_mem_support P μ hx))
  · intro y hy
    exact projected_fiber_cap_bound P μ {x | (x, y) ∈ G} {x | (x, P y) ∈ G'} y
      hR hc hP he hq hconstant
      (fun x hx => hG hx) (fun x hx => (hlower (x, y) hx).2)
      (hcap.2 (P y) (map_mem_support P ν hy))

/-- Auxiliary projected cap estimates lift to the original pair law.
The deletion is the preimage of the projected bad set intersected with the
original pair filter; its mass is bounded by the projected product mass. -/
theorem CapAvailable.pullback {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (μ ν : ProbabilityMeasure (Space d))
    {Γ : ℕ → Set (Space d × Space d)} {Γ' : ℕ → Set (Space k × Space k)} {c q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (hq : 0 ≤ q)
    (hΓ : ∀ N, MeasurableSet (Γ N))
    (hΓsub : ∀ N, Γ N ⊆ Prod.map P P ⁻¹' Γ' N)
    (hlower : ∀ N, ∀ z ∈ Γ N, c ≤ ‖P (radialDirection z.1 z.2)‖ ∧
      c ≤ ‖P (radialDirection z.2 z.1)‖)
    (hcap : CapAvailable (μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Γ' q) :
    CapAvailable μ ν Γ q := by
  intro e he
  obtain ⟨c₀, C, hc₀, hC, N₀, hN₀⟩ := hcap (e / 2) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (eventually_radius_factor_absorbed (K := max 1 (4 / c)) (q := q)
      (by linarith : (0 : ℝ) < e / 2))
  refine ⟨c₀, C, hc₀, hC, max N₀ N₁, ?_⟩
  intro N hN
  obtain ⟨B', hB', hB'sub, hmass, hgood⟩ := hN₀ N ((le_max_left _ _).trans hN)
  let B := Γ N ∩ Prod.map P P ⁻¹' B'
  have hPmeas : Measurable (P : Space d → Space k) := P.continuous.measurable
  have hB : MeasurableSet B := (hΓ N).inter (hB'.preimage (hPmeas.prodMap hPmeas))
  have hpre := Measure.le_map_apply
    (μ := (μ : Measure (Space d)).prod (ν : Measure (Space d)))
    (hPmeas.prodMap hPmeas).aemeasurable B'
  rw [← Measure.map_prod_map _ _ hPmeas hPmeas] at hpre
  have hmassB : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ N) ^ (-c₀)) :=
    (measure_mono inter_subset_right).trans (hpre.trans hmass)
  refine ⟨B, hB, inter_subset_left, hmassB, ?_⟩
  have hgoodsub : Γ N \ B ⊆ Prod.map P P ⁻¹' (Γ' N \ B') := by
    intro z hz
    exact ⟨hΓsub N hz.1, fun hb => hz.2 ⟨hz.1, hb⟩⟩
  have hbound := hgood.pullback P μ ν hc hP (by linarith) hq
    (hN₁ N ((le_max_right _ _).trans hN)) hgoodsub
    (fun z hz => hlower N z hz.1)
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectedSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated projected supports give the directional lower bound for cap lifting -/
namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem projected_direction_lower_of_dist (P : Space d →L[ℝ] Space m)
    (x y : Space d) {a b : ℝ} (ha : 0 < a)
    (hprojected : a ≤ dist (P x) (P y)) (hsource : dist x y ≤ b) :
    a/b ≤ ‖P (radialDirection x y)‖ := by
  have hne : x ≠ y := by
    intro h
    rw [h,dist_self] at hprojected
    exact (not_le_of_gt ha) hprojected
  have hd : 0 < dist x y := dist_pos.mpr hne
  have hid : ‖P (radialDirection x y)‖ = dist (P x) (P y) / dist x y := by
    rw [radialDirection,map_smul,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_norm]
    rw [map_sub,← dist_eq_norm,← dist_eq_norm,dist_comm y x,dist_comm (P y) (P x)]
    rw [div_eq_mul_inv,mul_comm]
  rw [hid]
  calc
    a/b ≤ a/dist x y := div_le_div_of_nonneg_left ha.le hd hsource
    _ ≤ dist (P x) (P y) / dist x y := (div_le_div_iff_of_pos_right hd).mpr hprojected

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_DirectionDistance
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact distance ratio for a projected original direction -/
namespace Falconer
open NormedSpace
variable {d m k : ℕ}

theorem norm_projected_radialDirection (P : Space d →L[ℝ] Space m) (x y : Space d) :
    ‖P (radialDirection x y)‖ = dist (P x) (P y) / dist x y := by
  rw [radialDirection,map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
    map_sub,← dist_eq_norm,← dist_eq_norm,dist_comm y x,dist_comm (P y) (P x)]
  rw [div_eq_mul_inv,mul_comm]

theorem projected_distance_lower (P : Space d →L[ℝ] Space m) (x y : Space d)
    {r c : ℝ} (hc : 0 ≤ c) (hr : 0 < r) (hxy : r ≤ dist x y)
    (hlower : c ≤ ‖P (radialDirection x y)‖) : c*r ≤ dist (P x) (P y) := by
  rw [norm_projected_radialDirection] at hlower
  have hd : 0 < dist x y := hr.trans_le hxy
  exact (mul_le_mul_of_nonneg_left hxy hc).trans ((le_div_iff₀ hd).mp hlower)

theorem contractive_distance_le (P : Space d →L[ℝ] Space m) (hP : ‖P‖ ≤ 1)
    (x y : Space d) : dist (P x) (P y) ≤ dist x y := by
  exact (P.dist_le_opNorm x y).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (dist_nonneg : 0 ≤ dist x y))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DensityTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncation of radial densities

The integer-cap step `prep:integer-caps` deletes pairs on which either
radial density exceeds a threshold. These lemmas estimate the deleted
original product mass by the Lp moments and bound every remaining fiber
by the threshold times the angular reference measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

private theorem ennreal_le_threshold_tail {t T : ℝ≥0∞} {p : ℝ}
    (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) (ht : T ≤ t) :
    t ≤ T ^ (1 - p) * t ^ p := by
  have hpow := ENNReal.rpow_le_rpow ht (by linarith : 0 ≤ p - 1)
  have hprod : T ^ (p - 1) * t ≤ t ^ p := by
    calc
      T ^ (p - 1) * t ≤ t ^ (p - 1) * t := mul_le_mul_left hpow t
      _ = t ^ ((p - 1) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
      _ = t ^ p := by congr 1; ring
  have hcancel : T ^ (1 - p) * T ^ (p - 1) = 1 := by
    rw [← ENNReal.rpow_add _ _ hT.ne' hTtop]
    convert (ENNReal.rpow_zero : T ^ (0 : ℝ) = 1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  calc
    t = (T ^ (1 - p) * T ^ (p - 1)) * t := by rw [hcancel, one_mul]
    _ = T ^ (1 - p) * (T ^ (p - 1) * t) := mul_assoc _ _ _
    _ ≤ T ^ (1 - p) * t ^ p := mul_le_mul_right hprod _

/-- The density mass above `T` is bounded by `T^(1-p)` times its pth moment. -/
theorem density_tail_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (σ.withDensity f) {a | T < f a} ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ := by
  have hS : MeasurableSet {a | T < f a} := measurableSet_lt measurable_const hf
  rw [withDensity_apply _ hS]
  calc
    (∫⁻ a in {a | T < f a}, f a ∂σ) ≤
        ∫⁻ a in {a | T < f a}, T ^ (1 - p) * f a ^ p ∂σ := by
      apply setLIntegral_mono' hS
      intro a ha
      exact ennreal_le_threshold_tail hT hTtop hp ha.le
    _ = T ^ (1 - p) * ∫⁻ a in {a | T < f a}, f a ^ p ∂σ :=
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)
    _ ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ :=
      mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- Truncation leaves a density bounded by the threshold on every cap. -/
theorem truncated_density_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    (T : ℝ≥0∞) (S : Set A) (hS : MeasurableSet S) :
    (σ.withDensity f) (S ∩ {a | f a ≤ T}) ≤ T * σ S := by
  have hlow : MeasurableSet {a | f a ≤ T} := measurableSet_le hf measurable_const
  rw [withDensity_apply _ (hS.inter hlow)]
  calc
    (∫⁻ a in S ∩ {a | f a ≤ T}, f a ∂σ) ≤
        ∫⁻ _ in S ∩ {a | f a ≤ T}, T ∂σ := by
      apply setLIntegral_mono' (hS.inter hlow)
      intro a ha
      exact ha.2
    _ = T * σ (S ∩ {a | f a ≤ T}) := by simp
    _ ≤ T * σ S := mul_le_mul_right (measure_mono inter_subset_left) T

theorem measurableSet_densityFailure {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    {f : X × A → ℝ≥0∞} {r : X × Y → A} (hf : Measurable f) (hr : Measurable r)
    (T : ℝ≥0∞) : MeasurableSet (densityFailure f r T) :=
  measurableSet_lt measurable_const (hf.comp (measurable_fst.prodMk hr))

/-- Fubini measures failure using the original source marginal and the
original pin marginal. There is no normalization of individual fibers. -/
theorem density_failure_product_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (hf : Measurable f) (hr : Measurable r)
    (hdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T) ≤
      T ^ (1 - p) * ∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
  rw [Measure.prod_apply (measurableSet_densityFailure hf hr T)]
  calc
    (∫⁻ x, ν (Prod.mk x ⁻¹' densityFailure f r T) ∂μ) ≤
        ∫⁻ x, T ^ (1 - p) * ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hdensity] with x hx
      have hfx : Measurable (fun a => f (x, a)) := hf.comp (measurable_const.prodMk measurable_id)
      have hrx : Measurable (fun y => r (x, y)) := hr.comp (measurable_const.prodMk measurable_id)
      change ν ((fun y => r (x, y)) ⁻¹' {a | T < f (x, a)}) ≤ _
      rw [← Measure.map_apply hrx (measurableSet_lt measurable_const hfx), hx]
      exact density_tail_mass σ _ hfx hT hTtop hp
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)

/-- Any additional pair restriction preserves the truncated fiber bound. -/
theorem truncated_radial_fiber {Y A : Type*} [MeasurableSpace Y] [MeasurableSpace A]
    (ν : Measure Y) (σ : Measure A) (f : A → ℝ≥0∞) (r : Y → A)
    (hf : Measurable f) (hr : Measurable r) (hdensity : ν.map r = σ.withDensity f)
    (T : ℝ≥0∞) (H : Set Y) (hH : ∀ y ∈ H, f (r y) ≤ T)
    (S : Set A) (hS : MeasurableSet S) :
    ν (H ∩ r ⁻¹' S) ≤ T * σ S := by
  have hset : H ∩ r ⁻¹' S ⊆ r ⁻¹' (S ∩ {a | f a ≤ T}) := by
    rintro y ⟨hy, hSy⟩
    exact ⟨hSy, hH y hy⟩
  calc
    ν (H ∩ r ⁻¹' S) ≤ ν (r ⁻¹' (S ∩ {a | f a ≤ T})) := measure_mono hset
    _ = (σ.withDensity f) (S ∩ {a | f a ≤ T}) := by
      rw [← hdensity, Measure.map_apply hr (hS.inter (measurableSet_le hf measurable_const))]
    _ ≤ T * σ S := truncated_density_mass σ f hf T S hS

/-- Deleting the failures in both orientations costs the sum of the two
integrated radial pth moments. -/
theorem bilateral_density_failure_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (g : Y × A → ℝ≥0∞) (s : Y × X → A)
    (hf : Measurable f) (hr : Measurable r) (hg : Measurable g) (hs : Measurable s)
    (hfdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂ν, μ.map (fun x => s (y, x)) = σ.withDensity (fun a => g (y, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T ∪ Prod.swap ⁻¹' densityFailure g s T) ≤
      T ^ (1 - p) * ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν) := by
  have hswap : (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) =
      (ν.prod μ) (densityFailure g s T) := by
    rw [← Measure.map_apply measurable_swap (measurableSet_densityFailure hg hs T), Measure.prod_swap]
  calc
    _ ≤ (μ.prod ν) (densityFailure f r T) + (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) :=
      measure_union_le _ _
    _ = (μ.prod ν) (densityFailure f r T) + (ν.prod μ) (densityFailure g s T) := by rw [hswap]
    _ ≤ T ^ (1 - p) * (∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        T ^ (1 - p) * ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν :=
      add_le_add (density_failure_product_mass μ ν σ f r hf hr hfdensity hT hTtop hp)
        (density_failure_product_mass ν μ σ g s hg hs hgdensity hT hTtop hp)
    _ = _ := (mul_add _ _ _).symm

/-- The threshold `R^(e/2)` gives a positive power saving in deleted mass
for every `p > 1`; its exponent is exactly `e * (p - 1) / 2`. -/
theorem exists_density_tail_power_bound (M : ℝ≥0∞) (hM : M ≠ ∞)
    {e p : ℝ} (he : 0 < e) (hp : 1 < p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ R : ℝ, 0 < R →
      (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M ≤
        ENNReal.ofReal (C * R ^ (-c)) := by
  refine ⟨e * (p - 1) / 2, M.toReal + 1, by positivity, by positivity, ?_⟩
  intro R hR
  have hpow : (e / 2) * (1 - p) = -(e * (p - 1) / 2) := by ring
  calc
    (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M =
        ENNReal.ofReal (M.toReal * R ^ (-(e * (p - 1) / 2))) := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hR _),
        ← Real.rpow_mul hR.le, hpow]
      conv_lhs => rw [← ENNReal.ofReal_toReal hM]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((M.toReal + 1) * R ^ (-(e * (p - 1) / 2))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hR.le _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_IntegerCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer cap availability from radial densities

This is the measure-theoretic truncation step of `prep:integer-caps`.
An angular reference measure with cap exponent `q` and integrable radial
`p`th density moments give availability of `q` for the original pair law.
The radial density hypothesis is the input supplied by the radial
projection theorem.
-/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

private theorem density_threshold_cap_scalar {R A e q u : ℝ}
    (hR : 0 < R) (hu : 0 < u) (hconstant : A ≤ R ^ (e / 2)) :
    R ^ (e / 2) * (A * u ^ q) ≤ R ^ e * u ^ q := by
  calc
    R ^ (e / 2) * (A * u ^ q) = A * (R ^ (e / 2) * u ^ q) := by ring
    _ ≤ R ^ (e / 2) * (R ^ (e / 2) * u ^ q) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = R ^ e * u ^ q := by
      rw [← mul_assoc, ← Real.rpow_add hR]
      congr 2
      ring

private theorem truncated_radial_cap_of_density {d : ℕ}
    (ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f : Space d → ℝ≥0∞) (x : Space d) (hf : Measurable f)
    (hdensity : (ν : Measure (Space d)).map (radialDirection x) = σ.withDensity f)
    {R A e q : ℝ} (hR : 0 < R) (_hA : 0 < A)
    (hconstant : A ≤ R ^ (e / 2))
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (H : Set (Space d))
    (hH : ∀ y ∈ H, f (radialDirection x y) ≤ ENNReal.ofReal (R ^ (e / 2))) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ e * u ^ q) := by
  intro w hw u hu hu1
  have hr : Measurable (radialDirection x) := by
    unfold radialDirection
    fun_prop
  have htrunc := truncated_radial_fiber (ν : Measure (Space d)) σ f
    (radialDirection x) hf hr hdensity (ENNReal.ofReal (R ^ (e / 2))) H hH
    (Metric.ball w u) measurableSet_ball
  calc
    (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ (e / 2)) * σ (Metric.ball w u) := by
      exact htrunc
    _ ≤ ENNReal.ofReal (R ^ (e / 2)) * ENNReal.ofReal (A * u ^ q) :=
      mul_le_mul_right (hσ w hw u hu hu1) _
    _ = ENNReal.ofReal (R ^ (e / 2) * (A * u ^ q)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    _ ≤ ENNReal.ofReal (R ^ e * u ^ q) :=
      ENNReal.ofReal_le_ofReal (density_threshold_cap_scalar hR hu hconstant)

/-- Bilateral radial densities with finite integrated `p`th moments make
the reference cap exponent available in the original product measure.
The deleted mass has a positive power saving for every requested loss.
Null strips of exceptional pins make the resulting bounds valid at every
support pin, although the radial density identities hold only almost everywhere. -/
theorem capAvailable_of_bilateral_radial_densities {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f g : Space d × Space d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfdensity : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) =
        σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) =
        σ.withDensity (fun a => g (y, a)))
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂(ν : Measure (Space d))) ≠ ∞) :
    CapAvailable μ ν (fun _ => Set.univ) q := by
  obtain ⟨Xbad, hXsub, hXm, hXnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hfdensity)
  obtain ⟨Ybad, hYsub, hYm, hYnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hgdensity)
  intro e he
  obtain ⟨c, C, hc, hC, htail⟩ := exists_density_tail_power_bound _ hmoment he hp
  have hconstant : ∀ᶠ N : ℕ in atTop, A ≤ ((2 : ℝ) ^ N) ^ (e / 2) := by
    simpa using (eventually_radius_factor_absorbed (K := A) (q := 1)
      (a := e / 2) (by linarith))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hconstant
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  let R : ℝ := (2 : ℝ) ^ N
  let T : ℝ≥0∞ := ENNReal.ofReal (R ^ (e / 2))
  let r : Space d × Space d → Space d := fun z => radialDirection z.1 z.2
  let B₀ : Set (Space d × Space d) := densityFailure f r T ∪
    Prod.swap ⁻¹' densityFailure g r T
  let Z : Set (Space d × Space d) := (Xbad ×ˢ Set.univ) ∪ (Set.univ ×ˢ Ybad)
  let B : Set (Space d × Space d) := B₀ ∪ Z
  have hR : 0 < R := by dsimp [R]; positivity
  have hT : 0 < T := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR _)
  have hTtop : T ≠ ∞ := ENNReal.ofReal_ne_top
  have hB₀ : MeasurableSet B₀ :=
    (measurableSet_densityFailure hf measurable_radialDirection_joint T).union
      ((measurableSet_densityFailure hg measurable_radialDirection_joint T).preimage
        measurable_swap)
  have hZ : MeasurableSet Z :=
    (hXm.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hYm)
  have hZnull : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) Z = 0 := by
    apply measure_union_null <;> simp only [Measure.prod_prod, hXnull, hYnull, zero_mul, mul_zero]
  have hB : MeasurableSet B := hB₀.union hZ
  refine ⟨B, hB, subset_univ _, ?_, ?_⟩
  · calc
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
          ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B₀ +
          ((μ : Measure (Space d)).prod (ν : Measure (Space d))) Z := measure_union_le _ _
      _ = ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B₀ := by rw [hZnull, add_zero]
      _ ≤ ENNReal.ofReal (C * R ^ (-c)) :=
        (bilateral_density_failure_mass (μ : Measure (Space d))
          (ν : Measure (Space d)) σ f r g r hf measurable_radialDirection_joint hg
          measurable_radialDirection_joint hfdensity hgdensity hT hTtop hp).trans (htail R hR)
  · constructor
    · intro x _ w hw u hu hu1
      by_cases hxb : x ∈ Xbad
      · have hempty : {y | (x, y) ∈ Set.univ \ B ∧
              dist (radialDirection x y) w < u} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro y hy
          exact hy.1.2 (Or.inr (Or.inl ⟨hxb, Set.mem_univ y⟩))
        rw [hempty, measure_empty]
        exact bot_le
      have hdensity : (ν : Measure (Space d)).map (radialDirection x) =
          σ.withDensity (fun a => f (x, a)) := by
        by_contra h
        exact hxb (hXsub h)
      have hupos : 0 < u := (inv_pos.mpr hR).trans_le hu
      have hlow : ∀ y ∈ {y | (x, y) ∈ Set.univ \ B},
          f (x, radialDirection x y) ≤ T := by
        intro y hy
        by_contra h
        have hbad : (x, y) ∈ B := Or.inl (Or.inl (lt_of_not_ge h))
        exact hy.2 hbad
      exact truncated_radial_cap_of_density ν σ (fun a => f (x, a)) x
        (hf.comp (measurable_const.prodMk measurable_id)) hdensity hR hA
        (hK N hN) hσ {y | (x, y) ∈ Set.univ \ B} hlow w hw u hupos hu1
    · intro y _ w hw u hu hu1
      by_cases hyb : y ∈ Ybad
      · have hempty : {x | (x, y) ∈ Set.univ \ B ∧
              dist (radialDirection y x) w < u} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro x hx
          exact hx.1.2 (Or.inr (Or.inr ⟨Set.mem_univ x, hyb⟩))
        rw [hempty, measure_empty]
        exact bot_le
      have hdensity : (μ : Measure (Space d)).map (radialDirection y) =
          σ.withDensity (fun a => g (y, a)) := by
        by_contra h
        exact hyb (hYsub h)
      have hupos : 0 < u := (inv_pos.mpr hR).trans_le hu
      have hlow : ∀ x ∈ {x | (x, y) ∈ Set.univ \ B},
          g (y, radialDirection y x) ≤ T := by
        intro x hx
        by_contra h
        have hbad : (x, y) ∈ B := Or.inl (Or.inr (lt_of_not_ge h))
        exact hx.2 hbad
      exact truncated_radial_cap_of_density μ σ (fun a => g (y, a)) y
        (hg.comp (measurable_const.prodMk measurable_id)) hdensity hR hA
        (hK N hN) hσ {x | (x, y) ∈ Set.univ \ B} hlow w hw u hupos hu1

/-- The same density truncation works inside every measurable coarse pair
filter; its fibers continue to use the original source marginals. -/
theorem capAvailable_of_bilateral_radial_densities_restrict {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f g : Space d × Space d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfdensity : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) =
        σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) =
        σ.withDensity (fun a => g (y, a)))
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂(ν : Measure (Space d))) ≠ ∞)
    (Γ : ℕ → Set (Space d × Space d)) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ q :=
  (capAvailable_of_bilateral_radial_densities μ ν σ f g hf hg hfdensity hgdensity hp
    hA hσ hmoment).restrict hΓ (fun _ => subset_univ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereRotations
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem sphereMap_cone_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (s : Set (Sphere d)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereMap e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨r,hr,e w,⟨sphereMap e w,hw,rfl⟩,by simp⟩
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,heq⟩
    refine ⟨r,hr,e.symm w,⟨sphereMap e.symm w,?_,rfl⟩,?_⟩
    · change sphereMap e (sphereMap e.symm w) ∈ s
      convert hw using 1
      all_goals try with_reducible_and_instances rfl
      apply Subtype.ext
      simp [sphereMap]
    · have hh := congrArg e.symm heq
      simpa using hh

theorem sphereMap_measurePreserving {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving (sphereMap e) (sphereMeasure d) (sphereMeasure d) := by
  have hm := (continuous_sphereMap e).measurable
  refine ⟨hm,Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs]
  unfold sphereMeasure
  rw [Measure.toSphere_apply' _ (hm hs),Measure.toSphere_apply' _ hs,sphereMap_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_Energy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem energyScale_pos (n : ℕ) : 0 < energyScale n := by
  unfold energyScale
  positivity

theorem energy_scale_identity (n : ℕ) (u s C : ℝ) :
    (energyScale n/2)^(-u) * (C*(2*energyScale n)^s) =
      ((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n := by
  have ha : (0 : ℝ) < 1/2 := by norm_num
  have hn := energyScale_pos n
  have hadd : (energyScale n)^(-u)*(energyScale n)^s = (energyScale n)^(s-u) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hpow : (energyScale n)^(s-u) = ((1/2 : ℝ)^(s-u))^n := by
    rw [energyScale, ← Real.rpow_natCast_mul ha.le, mul_comm,
      Real.rpow_mul_natCast ha.le]
  rw [show energyScale n/2 = energyScale n*(1/2) by ring,
    Real.mul_rpow hn.le ha.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le]
  calc
    _ = ((1/2 : ℝ)^(-u)*C*2^s) * ((energyScale n)^(-u)*(energyScale n)^s) := by ring
    _ = _ := by rw [hadd,hpow]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_radius_bracket {m : ℕ} {r : ℝ}
    (hmin : 1/(2:ℝ)^m ≤ r) (hmax : r ≤ 1) :
    ∃ j ≤ m, r ≤ 1/(2:ℝ)^j ∧ 1/(2:ℝ)^j ≤ 2*r := by
  induction m with
  | zero =>
    refine ⟨0,le_rfl,?_,?_⟩
    · simpa using hmax
    · norm_num at hmin ⊢
      linarith
  | succ m ih =>
    by_cases hcoarse : 1/(2:ℝ)^m ≤ r
    · obtain ⟨j,hj,hr,hjr⟩ := ih hcoarse
      exact ⟨j,hj.trans (Nat.le_succ m),hr,hjr⟩
    · refine ⟨m,Nat.le_succ m,(lt_of_not_ge hcoarse).le,?_⟩
      have he : 1/(2:ℝ)^m = 2*(1/(2:ℝ)^(m+1)) := by rw [pow_succ]; field_simp
      rw [he]
      linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rectangular bound for the cone under a spherical cap -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

theorem mem_northCapBox {n : ℕ} {r : ℝ} {z : Space (n+1)} :
    z ∈ northCapBox n r ↔ |z 0| ≤ 1 ∧ ∀ i : Fin n, |z i.succ| ≤ r := by
  simp only [northCapBox,mem_preimage,mem_Icc,Pi.le_def,Fin.forall_fin_succ,
    Fin.cons_zero,Fin.cons_succ,abs_le]
  aesop

theorem northCapBox_volume (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space (n+1))) (northCapBox n r) =
      ENNReal.ofReal (2*(2*r)^n) := by
  unfold northCapBox
  rw [← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin (n+1))).measurable measurableSet_Icc,
    (PiLp.volume_preserving_ofLp (Fin (n+1))).map_eq,Real.volume_Icc_pi,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,sub_neg_eq_add,← two_mul,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hr),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem north_cap_cone_subset {n : ℕ} {r : ℝ} :
    Ioo (0:ℝ) 1 • ((↑) '' (ball (gnomonicChart (0 : Space n)) r)) ⊆ northCapBox n r := by
  rintro z ⟨t,ht,y,⟨w,hw,rfl⟩,rfl⟩
  rw [mem_northCapBox]
  have hw0 : |(w:Space (n+1)) 0| ≤ 1 := by
    simpa only [sphere_norm,Real.norm_eq_abs] using PiLp.norm_apply_le (w:Space (n+1)) 0
  constructor
  · change |t*(w:Space (n+1)) 0| ≤ 1
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_mul_of_nonneg_left hw0 ht.1.le).trans (by simpa only [mul_one] using ht.2.le)
  · intro i
    have hd : ‖(w:Space (n+1))-northLift (0:Space n)‖ < r := by
      simpa only [mem_ball,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
    have hi : |(w:Space (n+1)) i.succ| < r := by
      have hh := (PiLp.norm_apply_le ((w:Space (n+1))-northLift (0:Space n)) i.succ).trans_lt hd
      simpa [northLift] using hh
    change |t*(w:Space (n+1)) i.succ| ≤ r
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hi.le

theorem north_sphere_cap_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball (gnomonicChart (0:Space n)) r) ≤
      ENNReal.ofReal (((n+1:ℕ):ℝ)*2*(2*r)^n) := by
  rw [sphereMeasure,Measure.toSphere_apply' _ measurableSet_ball]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  apply (mul_le_mul_right (measure_mono north_cap_cone_subset) _).trans_eq
  rw [northCapBox_volume n hr,← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedLaws
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation transport of the original point and direction laws -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

theorem sphereMap_distance (e : Space d ≃ₗᵢ[ℝ] Space d) (v w : Sphere d) :
    dist (sphereMap e v) (sphereMap e w) = dist v w := e.dist_map v w

theorem sphereMap_symm_apply (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e (sphereMap e.symm w) = w := by
  apply Subtype.ext
  exact e.apply_symm_apply w

theorem sphereMap_apply_symm (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e.symm (sphereMap e w) = w := by
  apply Subtype.ext
  exact e.symm_apply_apply w

theorem sphereMap_ball_preimage (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    sphereMap e ⁻¹' ball w r = ball (sphereMap e.symm w) r := by
  rw [← sphereMap_symm_apply e w]
  ext v
  simp only [mem_preimage,mem_ball,sphereMap_distance]
  rw [sphereMap_apply_symm e]

theorem rotated_direction_ball (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) (ball w r) = ν (ball (sphereMap e.symm w) r) := by
  rw [Measure.map_apply (continuous_sphereMap e).measurable measurableSet_ball,
    sphereMap_ball_preimage]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual spherical surface measure has its dimensional cap bound -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem sphere_cap_bound (n : ℕ) (w : Sphere (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball w r) ≤
      ENNReal.ofReal ((((n+1:ℕ):ℝ)*(2:ℝ)^(n+1))*r^n) := by
  let north := gnomonicChart (0 : Space n)
  let e := (ℝ ∙ ((north:Space (n+1))-(w:Space (n+1))))ᗮ.reflection
  have he : e (north:Space (n+1)) = (w:Space (n+1)) :=
    Submodule.reflection_sub ((sphere_norm north).trans (sphere_norm w).symm)
  have he' : sphereMap e north = w := Subtype.ext he
  have hrw := rotated_direction_ball (sphereMeasure (n+1)) e w r
  rw [(sphereMap_measurePreserving e).map_eq] at hrw
  have hn : sphereMap e.symm w = north := by rw [← he',sphereMap_apply_symm]
  rw [hn] at hrw
  rw [hrw]
  apply (north_sphere_cap_bound n hr).trans_eq
  congr 1
  rw [mul_pow,pow_succ]
  ring

theorem surfaceMeasure_ball_bound (n : ℕ) (w : Space (n+1)) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    surfaceMeasure (n+1) (ball w r) ≤
      ENNReal.ofReal ((((n+1:ℕ):ℝ)*(2:ℝ)^(n+1))*r^n) := by
  let w' : Sphere (n+1) := ⟨w,by simpa only [mem_sphere,dist_zero_right] using hw⟩
  rw [surfaceMeasure,Measure.map_apply measurable_subtype_coe measurableSet_ball]
  exact sphere_cap_bound n w' hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_StartingMeasures
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Starting measures in all dimensions

The published input is Frostman's lemma, Mattila, *Geometry of Sets and
Measures in Euclidean Spaces* (Cambridge, 1995), Theorem 8.8, p. 112.
Only compact sets above the critical half-dimensional threshold are used.
Selecting an exponent strictly between the threshold and the Hausdorff
dimension, and normalizing the nonzero finite measure, gives the exact
specialization below, stated as a hypothesis for the conditional argument.

The separation and restriction arguments are proved here in the original
ambient dimension. They do not use a projection of the distance set.
-/

namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem noAtoms_of_frostman {d : ℕ} (μ : Measure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hb : FrostmanBallBound (μ : Measure (Space d)) s C) : NullSingletonClass μ := by
  constructor
  intro x
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r^s)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa only [Real.zero_rpow hs.ne', mul_zero, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb x r hr)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanRieszEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Riesz energies from the original all-dimensional Frostman bounds

The dyadic potential argument and its scalar scale identity are dimension
independent.
-/

namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

theorem euclidean_riesz_kernel_majorant (x y : Space d) {u : ℝ} (hu : 0 < u) (hxy : x ≠ y) :
    (edist x y)^(-u) ≤ 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have heq : (edist x y)^(-u) = ENNReal.ofReal ((dist x y)^(-u)) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_pos hd]
  rw [heq]
  by_cases hlarge : 1 ≤ dist x y
  · have hle : (dist x y)^(-u) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        hlarge (neg_nonpos.mpr hu.le)
    exact (show ENNReal.ofReal ((dist x y)^(-u)) ≤ 1 by
      simpa using ENNReal.ofReal_le_ofReal hle).trans (le_add_right le_rfl)
  · obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hd (le_of_not_ge hlarge)
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    have hlo' : energyScale n/2 < dist x y := by
      simpa [energyScale,pow_succ,div_eq_mul_inv] using hlo
    have hball : y ∈ ball x (2*energyScale n) := by
      rw [mem_ball, dist_comm]
      have hpos := energyScale_pos n
      change dist x y ≤ energyScale n at hhi
      linarith
    have hpoint : (edist x y)^(-u) ≤ euclideanEnergyMajorant x u n y := by
      rw [heq, euclideanEnergyMajorant, indicator_of_mem hball]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
        (div_pos (energyScale_pos n) (by norm_num)) hlo'.le (by linarith))
    rw [heq] at hpoint
    exact hpoint.trans ((ENNReal.le_tsum (f := fun index : ℕ =>
      euclideanEnergyMajorant x u index y) n).trans (le_add_left le_rfl))

theorem euclidean_energy_term_integral_le (μ : Measure (Space d)) {s C : ℝ}
    (hb : FrostmanBallBound μ s C) (x : Space d) (u : ℝ) (n : ℕ) :
    (∫⁻ y, euclideanEnergyMajorant x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [euclideanEnergyMajorant, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb x _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem euclidean_riesz_potential_uniform_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : FrostmanBallBound μ s C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, euclideanRieszPotential μ u x ≤ B := by
  let := noAtoms_of_frostman μ (hu.trans hus) hb
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have ha : a < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  have hsum : (∑' n : ℕ, a^n) < ∞ := tsum_geometric_lt_top.mpr ha
  refine ⟨μ univ + D * ∑' n : ℕ, a^n,
    ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum⟩,?_⟩
  intro x
  have hm (n : ℕ) : Measurable (euclideanEnergyMajorant x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simp
  calc
    euclideanRieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact euclidean_riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, euclideanEnergyMajorant x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => euclidean_energy_term_integral_le μ hb x u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left]

theorem rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : FrostmanBallBound μ s C) :
    PlanarFalconer.rieszEnergyOn μ u < ∞ := by
  obtain ⟨B,hB,hpot⟩ := euclidean_riesz_potential_uniform_bound μ hu hus hb
  rw [PlanarFalconer.rieszEnergyOn,lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : Space d, B ∂μ := lintegral_mono hpot
    _ = B*μ univ := lintegral_const B
    _ < ∞ := ENNReal.mul_lt_top hB (measure_lt_top μ univ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMoments
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From radial projection moments to integer cap availability

The radial pushforwards form a Markov kernel. Mathlib's kernel
Radon--Nikodym derivative supplies a jointly measurable version of all
their angular densities, so separate choices of densities are unnecessary.
This connects the published radial-moment input to the truncation step.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

theorem radialKernel_apply {d : ℕ} (ν : ProbabilityMeasure (Space d)) (x : Space d) :
    radialKernel ν x = (ν : Measure (Space d)).map (radialDirection x) := by
  have hr : Measurable (radialDirection x) := by
    unfold radialDirection
    fun_prop
  ext S hS
  rw [radialKernel, Kernel.map_apply' _ measurable_radialDirection_joint _ hS,
    Kernel.id_prod_apply' _ _ (hS.preimage measurable_radialDirection_joint),
    Kernel.const_apply, Measure.map_apply hr hS]
  rfl

theorem radialKernelDensity_withDensity {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d)
    (h : (ν : Measure (Space d)).map (radialDirection x) ≪ σ) :
    (ν : Measure (Space d)).map (radialDirection x) =
      σ.withDensity (fun a => radialKernelDensity ν σ (x, a)) := by
  have hker : radialKernel ν x ≪ Kernel.const (Space d) σ x := by
    simpa only [radialKernel_apply, Kernel.const_apply] using h
  have heq := Kernel.withDensity_rnDeriv_eq hker
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _),
    Kernel.const_apply, radialKernel_apply] at heq
  exact heq.symm

theorem radialKernelDensity_moment {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d) (p : ℝ) :
    (∫⁻ a, radialKernelDensity ν σ (x, a) ^ p ∂σ) =
      ∫⁻ a, ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ := by
  apply lintegral_congr_ae
  have heq := Kernel.rnDeriv_eq_rnDeriv_measure (κ := radialKernel ν)
    (η := Kernel.const (Space d) σ) (a := x)
  simp only [Kernel.const_apply, radialKernel_apply] at heq
  filter_upwards [heq] with a ha
  exact congrArg (fun t : ℝ≥0∞ => t ^ p) ha

/-- A.e. absolute continuity and integrated radial `p`th moments imply the
integer cap conclusion. These are precisely the density data used from
the radial projection input; the geometric cap bound on `σ` is explicit. -/
theorem capAvailable_of_radial_moments {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d)) [IsFiniteMeasure σ]
    (hν : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) ≪ σ)
    (hμ : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) ≪ σ)
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a,
      ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ
        ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a,
        ((μ : Measure (Space d)).map (radialDirection y)).rnDeriv σ a ^ p ∂σ
          ∂(ν : Measure (Space d))) ≠ ∞)
    (Γ : ℕ → Set (Space d × Space d)) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ q := by
  apply capAvailable_of_bilateral_radial_densities_restrict μ ν σ
    (radialKernelDensity ν σ) (radialKernelDensity μ σ)
    (measurable_radialKernelDensity ν σ) (measurable_radialKernelDensity μ σ)
    _ _ hp hA hσ _ Γ hΓ
  · filter_upwards [hν] with x hx
    exact radialKernelDensity_withDensity ν σ x hx
  · filter_upwards [hμ] with y hy
    exact radialKernelDensity_withDensity μ σ y hy
  · simpa only [radialKernelDensity_moment] using hmoment

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMomentParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed exponents used in Orponen's published radial moment estimate -/

namespace Falconer

theorem radial_moment_parameters {h δ : ℝ} (hh : 1 ≤ h) (hδ : 0 < δ) (hδ1 : δ < 1) :
    h < h+δ/2 ∧ h+δ/2 < h+1 ∧ 0 < h-δ/4 ∧ h-δ/4 < h ∧
    2*h-(h+δ/2) < h-δ/4 ∧ 1 < 1+δ/(8*h) ∧
    1+δ/(8*h) < 2-(h-δ/4)/h ∧
    1+δ/(8*h) < (h-δ/4)/(2*h-(h+δ/2)) := by
  have hh0 : 0 < h := by linarith only [hh]
  have hden : 0 < 2*h-(h+δ/2) := by linarith only [hh,hδ1]
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,?_,?_,?_⟩
  · have := div_pos hδ (mul_pos (by norm_num : (0:ℝ) < 8) hh0)
    linarith
  · have he : 2-(h-δ/4)/h = 1+δ/(4*h) := by
      field_simp
      ring
    rw [he]
    have hd := div_lt_div_of_pos_left hδ
      (by positivity : 0 < 4*h) (by linarith : 4*h < 8*h)
    linarith only [hd]
  · apply (lt_div_iff₀ hden).mpr
    have he : (1+δ/(8*h))*(2*h-(h+δ/2)) = h-3*δ/8-δ^2/(16*h) := by
      field_simp
      ring
    rw [he]
    have hn : 0 ≤ δ^2/(16*h) := by positivity
    linarith only [hδ,hn]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_PublishedIntegerCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cap availability from the precise published radial moment -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem integer_caps_of_published_radial (hpublished : PublishedRadialMoment)
    (h : ℕ) (hh : 1 ≤ h) (μ ν : ProbabilityMeasure (Space (h+1)))
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hμK : IsCompact (μ : Measure (Space (h+1))).support)
    (hνK : IsCompact (ν : Measure (Space (h+1))).support)
    (hsep : Disjoint (μ : Measure (Space (h+1))).support (ν : Measure (Space (h+1))).support)
    (hμfrost : FrostmanBallBound (μ : Measure (Space (h+1))) ((h:ℝ)+δ) C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space (h+1))) ((h:ℝ)+δ) C)
    (Γ : ℕ → Set (Space (h+1) × Space (h+1))) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ (h:ℝ) := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨hs,_,ht0,ht,_,hp,_,_⟩ := radial_moment_parameters hh' hδ hδ1
  have hsrc : (h:ℝ)+δ/2 < (h:ℝ)+δ := by linarith only [hδ]
  have hpin : (h:ℝ)-δ/4 < (h:ℝ)+δ := by linarith only [hδ]
  have hμs := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space (h+1)))
    (show 0 < (h:ℝ)+δ/2 by linarith only [hh',hs]) hsrc hμfrost
  have hνs := rieszEnergyOn_lt_top_of_frostman (ν : Measure (Space (h+1)))
    (show 0 < (h:ℝ)+δ/2 by linarith only [hh',hs]) hsrc hνfrost
  have hμt := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space (h+1))) ht0 hpin hμfrost
  have hνt := rieszEnergyOn_lt_top_of_frostman (ν : Measure (Space (h+1))) ht0 hpin hνfrost
  have hμν := hpublished h hh μ ν δ hδ hδ1 hμK hνK hsep hμs hνt
  have hνμ := hpublished h hh ν μ δ hδ hδ1 hνK hμK hsep.symm hνs hμt
  apply capAvailable_of_radial_moments μ ν (surfaceMeasure (h+1)) hνμ.1 hμν.1 hp
    (show 0 < (((h+1:ℕ):ℝ)*(2:ℝ)^(h+1)) by positivity) _
    (ENNReal.add_lt_top.mpr ⟨hνμ.2,hμν.2⟩).ne Γ hΓ
  intro w hw r hr _
  simpa only [Real.rpow_natCast] using surfaceMeasure_ball_bound h w hw hr.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GramSchmidtSlab
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small Gram--Schmidt residual lies in a fixed thin slab -/

namespace Falconer
open Set Submodule InnerProductSpace NormedSpace
open scoped BigOperators
variable {d : ℕ}

theorem normalized_direction_slab (u c x : Space d) {R r : ℝ}
    (hx : ‖c-x‖ ≤ R) (hr : 0 ≤ r)
    (h : |inner ℝ u (normalize (c-x))| ≤ r) :
    |inner ℝ u x-inner ℝ u c| ≤ R*r := by
  have he : inner ℝ u (c-x) = ‖c-x‖*inner ℝ u (normalize (c-x)) := by
    nth_rw 1 [← norm_smul_normalize (c-x)]
    rw [inner_smul_right]
  calc
    _ = |inner ℝ u (c-x)| := by rw [inner_sub_right,abs_sub_comm]
    _ = ‖c-x‖*|inner ℝ u (normalize (c-x))| := by rw [he,abs_mul,abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖c-x‖*r := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ ≤ R*r := mul_le_mul_of_nonneg_right hx hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original radial laws and source balls under positive affine rescaling -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_preimage_ball {a : ℝ} (ha : 0 < a) (c x : Space d) (r : ℝ) :
    radialZoom a ha.ne' c ⁻¹' Metric.ball x r = Metric.ball (c+a⁻¹ • x) (r/a) := by
  ext z
  have he : a • (z-c)-x = a • (z-(c+a⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    abel
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,radialZoom_apply]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha,lt_div_iff₀ ha]
  rw [mul_comm a]

theorem radialZoom_ball_apply (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c x : Space d) (r : ℝ) :
    Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) =
      μ (Metric.ball (c+a⁻¹ • x) (r/a)) := by
  rw [Measure.map_apply (radialZoom a ha.ne' c).measurable Metric.isOpen_ball.measurableSet,
    radialZoom_preimage_ball ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded supports and Frostman bounds survive the fixed cell normalization -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_norm {a : ℝ} (ha : 0 < a) (c x : Space d) :
    ‖radialZoom a ha.ne' c x‖ = a*‖x-c‖ := by
  rw [radialZoom_apply,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlateZoom
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact affine normalization of the heavy-plate inputs -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_full_frostman (μ : Measure (Space d))
    {a s C : ℝ} (ha : 0 < a) (c : Space d) (hfrost : FrostmanBallBound μ s C) :
    FrostmanBallBound (Measure.map (radialZoom a ha.ne' c) μ) s (C*a^(-s)) := by
  intro x r hr
  rw [radialZoom_ball_apply μ ha]
  have he : C*(r/a)^s = (C*a^(-s))*r^s := by
    rw [Real.div_rpow hr.le ha.le,Real.rpow_neg ha.le]
    ring
  rw [← he]
  exact hfrost _ _ (div_pos hr ha)

theorem radialZoom_zero_slab (μ : Measure (Space d))
    {a : ℝ} (ha : 0 < a) (w : Space d) (t r : ℝ) :
    Measure.map (radialZoom a ha.ne' (0:Space d)) μ
      {y | |inner ℝ w y-a*t| ≤ a*r} = μ {x | |inner ℝ w x-t| ≤ r} := by
  rw [Measure.map_apply (radialZoom a ha.ne' (0:Space d)).measurable
    (measurableSet_le (by fun_prop) measurable_const)]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,radialZoom_apply,sub_zero,inner_smul_right]
  rw [show a*inner ℝ w x-a*t = a*(inner ℝ w x-t) by ring,abs_mul,abs_of_pos ha]
  exact mul_le_mul_iff_right₀ ha

theorem pullback_affine_slab {a R t : ℝ} (ha : 0 < a) (w x : Space d)
    (h : |inner ℝ w (a • x)-t| ≤ R) : |inner ℝ w x-t/a| ≤ R/a := by
  have he : inner ℝ w x-t/a = (inner ℝ w (a • x)-t)/a := by
    rw [inner_smul_right]
    field_simp
  rw [he,abs_div,abs_of_pos ha]
  exact div_le_div_of_nonneg_right h ha.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionDilation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive dilations of the chosen auxiliary projections -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem compact_projected_support (μ : Measure (Space d))
    (hK : IsCompact μ.support) (P : Space d →L[ℝ] Space m) :
    (μ.map P).support ⊆ P '' μ.support ∧ IsCompact (μ.map P).support := by
  have himage := hK.image P.continuous
  have hsub : (μ.map P).support ⊆ P '' μ.support := by
    apply Measure.support_subset_of_isClosed himage.isClosed
    change μ.map P (P '' μ.support)ᶜ = 0
    rw [Measure.map_apply P.continuous.measurable himage.isClosed.measurableSet.compl]
    apply measure_mono_null _ μ.measure_compl_support
    intro x hx hxS
    exact hx ⟨x,hxS,rfl⟩
  exact ⟨hsub,himage.of_isClosed_subset Measure.isClosed_support hsub⟩

theorem projected_supports_disjoint (μ ν : Measure (Space d))
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    (P : Space d →L[ℝ] Space m)
    (hneq : ∀ x ∈ μ.support, ∀ y ∈ ν.support, P x ≠ P y) :
    Disjoint (μ.map P).support (ν.map P).support := by
  apply Set.disjoint_left.mpr
  intro z hzμ hzν
  obtain ⟨x,hx,rfl⟩ := (compact_projected_support μ hμ P).1 hzμ
  obtain ⟨y,hy,hxy⟩ := (compact_projected_support ν hν P).1 hzν
  exact hneq x hx y hy hxy.symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Put compact projected supports in a fixed unit cube -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem mem_centeredUnitCube_of_norm {x : Space d} (hx : ‖x‖ ≤ 1/4) :
    x ∈ (centeredUnitCube d).carrier := by
  intro i
  have hi : |x i| ≤ 1/4 := (PiLp.norm_apply_le x i).trans hx
  change -(1/2:ℝ) ≤ x i ∧ x i < -(1/2:ℝ)+1
  constructor <;> linarith [abs_le.mp hi]

theorem centeredUnitCube_norm_bound {x : Space d}
    (hx : x ∈ (centeredUnitCube d).carrier) : ‖x‖ ≤ Real.sqrt d := by
  have hzero : (0 : Space d) ∈ (centeredUnitCube d).carrier :=
    mem_centeredUnitCube_of_norm (by simp)
  have hd := (centeredUnitCube d).dist_le (by norm_num [centeredUnitCube]) hx hzero
  simpa [centeredUnitCube] using hd

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoProjectionPiecePair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first auxiliary pair and its inherited root geometry -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m k : ℕ} {μ : ProbabilityMeasure (Space d)} {s ε : ℝ}
  {f : TwoProjectionFrame μ m k s}

namespace TwoProjectionPieces
variable (p : TwoProjectionPieces f ε)

theorem first_support_left :
    ((p.left : Measure (Space d)).map f.first).support ⊆ (centeredUnitCube m).carrier := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := (compact_projected_support _ p.left_support_compact f.first).1 hx
  exact f.first_root y (p.left_subset (p.left_support hy))

theorem first_support_right :
    ((p.right : Measure (Space d)).map f.first).support ⊆ (centeredUnitCube m).carrier := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := (compact_projected_support _ p.right_support_compact f.first).1 hx
  exact f.first_root y (p.right_subset (p.right_support hy))

theorem first_noncharging (w : Space m) (hw : ‖w‖ = 1) (t : ℝ) :
    (((p.left : Measure (Space d)).map f.first)+
      ((p.right : Measure (Space d)).map f.first)) {y | inner ℝ w y = t} = 0 := by
  rw [Measure.add_apply]
  have hL := (p.left_ac.map f.first.continuous.measurable) (f.noncharging w hw t)
  have hR := (p.right_ac.map f.first.continuous.measurable) (f.noncharging w hw t)
  rw [hL,hR,add_zero]

theorem first_pair_separation :
    ∀ x ∈ ((p.left : Measure (Space d)).map f.first).support,
    ∀ y ∈ ((p.right : Measure (Space d)).map f.first).support,
      p.lower*(p.radius/2) ≤ dist x y := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := (compact_projected_support _ p.left_support_compact f.first).1 hx
  obtain ⟨b,hb,rfl⟩ := (compact_projected_support _ p.right_support_compact f.first).1 hy
  exact projected_distance_lower f.first a b p.lower_pos.le (by linarith [p.radius_pos])
    (p.geometry a (p.left_support ha) b (p.right_support hb)).1
    (p.first_lower (p.left_support ha) (p.right_support hb)).1

theorem second_direction_lower :
    ∀ x ∈ ((p.left : Measure (Space d)).map f.first).support,
    ∀ y ∈ ((p.right : Measure (Space d)).map f.first).support,
      p.lower/4 ≤ ‖f.second (radialDirection x y)‖ ∧
      p.lower/4 ≤ ‖f.second (radialDirection y x)‖ := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := (compact_projected_support _ p.left_support_compact f.first).1 hx
  obtain ⟨b,hb,rfl⟩ := (compact_projected_support _ p.right_support_compact f.first).1 hy
  obtain ⟨hlo,hhi,h1,h2,_⟩ := p.geometry a (p.left_support ha) b (p.right_support hb)
  have hdist := (contractive_distance_le f.first f.first_contractive a b).trans hhi
  have hlower := projected_distance_lower (f.second.comp f.first) a b p.lower_pos.le
    (by linarith [p.radius_pos]) hlo h1
  have hradius : 0 < p.lower*(p.radius/2) := mul_pos p.lower_pos (by linarith [p.radius_pos])
  have heq : (p.lower*(p.radius/2))/(2*p.radius) = p.lower/4 := by
    field_simp [p.radius_pos.ne']
    ring
  constructor
  · rw [← heq]
    exact projected_direction_lower_of_dist f.second (f.first a) (f.first b) hradius hlower hdist
  · rw [← heq]
    apply projected_direction_lower_of_dist f.second (f.first b) (f.first a) hradius
    · simpa only [ContinuousLinearMap.comp_apply,dist_comm] using hlower
    · simpa only [dist_comm] using hdist

end TwoProjectionPieces
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_TwoProjectionIntegerCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cap availability in the first auxiliary space -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m h : ℕ} {μ : ProbabilityMeasure (Space d)} {s δ ε : ℝ}
  {f : TwoProjectionFrame μ m (h+1) s}

namespace TwoProjectionPieces

theorem first_integer_caps (p : TwoProjectionPieces f ε)
    (hpublished : PublishedRadialMoment) (hh : 1 ≤ h)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hδs : s = (h:ℝ)+δ)
    (Γ : ℕ → Set (Space m × Space m)) (hΓ : ∀ N, MeasurableSet (Γ N))
    (hΓsub : ∀ N, Γ N ⊆
      ((p.left : Measure (Space d)).map f.first).support ×ˢ
        ((p.right : Measure (Space d)).map f.first).support) :
    CapAvailable (p.left.map (f.first.continuous.aemeasurable)) (p.right.map (f.first.continuous.aemeasurable)) Γ (h:ℝ) := by
  subst s
  let ν₁ := p.left.map (f.first.continuous.aemeasurable)
  let ν₂ := p.right.map (f.first.continuous.aemeasurable)
  have hK₁ : IsCompact (ν₁ : Measure (Space m)).support :=
    (compact_projected_support _ p.left_support_compact f.first).2
  have hK₂ : IsCompact (ν₂ : Measure (Space m)).support :=
    (compact_projected_support _ p.right_support_compact f.first).2
  have hfrost := p.projected_frostman (f.second.comp f.first) f.second_frostman
  have hmap₁ : (ν₁ : Measure (Space m)).map f.second =
      (p.left : Measure (Space d)).map (f.second.comp f.first) :=
    Measure.map_map f.second.continuous.measurable f.first.continuous.measurable
  have hmap₂ : (ν₂ : Measure (Space m)).map f.second =
      (p.right : Measure (Space d)).map (f.second.comp f.first) :=
    Measure.map_map f.second.continuous.measurable f.first.continuous.measurable
  have hsep : Disjoint ((ν₁ : Measure (Space m)).map f.second).support
      ((ν₂ : Measure (Space m)).map f.second).support := by
    rw [hmap₁,hmap₂]
    apply projected_supports_disjoint _ _ p.left_support_compact p.right_support_compact
    intro x hx y hy he
    have hlow := (p.geometry x (p.left_support hx) y (p.right_support hy)).2.2.1
    have hz : (f.second.comp f.first) (radialDirection x y) = 0 := by
      simp only [radialDirection,map_smul,map_sub,he,sub_self,smul_zero]
    rw [hz,norm_zero] at hlow
    exact (not_le_of_gt p.lower_pos) hlow
  have hcap := integer_caps_of_published_radial hpublished h hh
    (ν₁.map (f.second.continuous.aemeasurable)) (ν₂.map (f.second.continuous.aemeasurable)) hδ hδ1
    (compact_projected_support _ hK₁ f.second).2
    (compact_projected_support _ hK₂ f.second).2 hsep
    (by
      change FrostmanBallBound ((ν₁ : Measure (Space m)).map f.second) _ _
      rw [hmap₁]
      exact hfrost.1)
    (by
      change FrostmanBallBound ((ν₂ : Measure (Space m)).map f.second) _ _
      rw [hmap₂]
      exact hfrost.2)
    (fun _ => univ) (fun _ => MeasurableSet.univ)
  apply CapAvailable.pullback f.second ν₁ ν₂
    (by linarith [p.lower_pos] : 0 < p.lower/4) f.second_contractive (Nat.cast_nonneg h)
    hΓ (fun _ _ _ => mem_univ _) _ hcap
  intro N z hz
  exact p.second_direction_lower z.1 (hΓsub N hz).1 z.2 (hΓsub N hz).2

end TwoProjectionPieces
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_PairCorePruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Core restrictions and density pruning preserve the original pair-cost ledger -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_core_compl_null (ν : Measure X) (μ : Measure Y) [SFinite μ] (P : Set X) (S : Set Y)
    (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) : (ν.prod μ) (P ×ˢ S)ᶜ = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ ∪ univ ×ˢ Sᶜ) := by
      apply measure_mono
      intro p hp
      by_cases hx : p.1 ∈ P
      · exact Or.inr ⟨mem_univ _,fun hy => hp ⟨hx,hy⟩⟩
      · exact Or.inl ⟨hx,mem_univ _⟩
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ)+(ν.prod μ) (univ ×ˢ Sᶜ) := measure_union_le _ _
    _ = 0 := by simp only [Measure.prod_prod,hP,hS,zero_mul,mul_zero,add_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SupportPairFilter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restrict pair filters to the original supports without losing mass -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem supportPair_measurable (μ ν : ProbabilityMeasure (Space d)) :
    MeasurableSet (supportPair μ ν) :=
  Measure.isClosed_support.measurableSet.prod Measure.isClosed_support.measurableSet

theorem supportPair_compl_null (μ ν : ProbabilityMeasure (Space d)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (supportPair μ ν)ᶜ = 0 :=
  product_core_compl_null _ _ _ _ Measure.measure_compl_support Measure.measure_compl_support

theorem supportPair_inter_mass (μ ν : ProbabilityMeasure (Space d))
    (G : Set (Space d × Space d)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (G ∩ supportPair μ ν) =
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) G :=
  measure_inter_conull (supportPair_compl_null μ ν)

theorem supportPair_iInter_mass (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋂ N, Γ N ∩ supportPair μ ν) =
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋂ N, Γ N) := by
  have heq : (⋂ N, Γ N ∩ supportPair μ ν) = (⋂ N, Γ N) ∩ supportPair μ ν := by
    ext z
    simp only [mem_iInter,mem_inter_iff]
    exact ⟨fun h => ⟨fun N => (h N).1,(h 0).2⟩,fun h N => ⟨h.1 N,h.2⟩⟩
  rw [heq,supportPair_inter_mass]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyPlateCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual dyadic cell-pair exclusion generated by heavy affine plates -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurableSet_heavyPlateCellPairs (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j : ℕ) (r m : ℝ) : MeasurableSet (heavyPlateCellPairs ρ Q j r m) := by
  classical
  apply MeasurableSet.iUnion
  intro pq
  apply MeasurableSet.iUnion
  intro _
  split_ifs
  · exact (Q.descendant pq.1).measurable.prod (Q.descendant pq.2).measurable
  · exact MeasurableSet.empty

theorem mem_heavyPlateCellPairs_iff (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j : ℕ) (r m : ℝ) (x y : Space d) :
    (x,y) ∈ heavyPlateCellPairs ρ Q j r m ↔
      ∃ p ∈ cubePaths d j, ∃ q ∈ cubePaths d j,
        HeavyPlateHits ρ (Q.descendant p) (Q.descendant q) r m ∧
        x ∈ (Q.descendant p).carrier ∧ y ∈ (Q.descendant q).carrier := by
  classical
  constructor
  · intro h
    obtain ⟨⟨p,q⟩,hpq,h⟩ := mem_iUnion₂.mp h
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    split_ifs at h with hhit
    · exact ⟨p,hp,q,hq,hhit,h⟩
    · exact h.elim
  · rintro ⟨p,hp,q,hq,hhit,hx,hy⟩
    exact mem_iUnion₂.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,
      by rw [ite_eq_left hhit]; exact ⟨hx,hy⟩⟩

theorem heavyPlateCellPairs_subset_root (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j : ℕ) (r m : ℝ) : heavyPlateCellPairs ρ Q j r m ⊆ Q.carrier ×ˢ Q.carrier := by
  rintro ⟨x,y⟩ h
  obtain ⟨p,_,q,_,_,hx,hy⟩ := (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mp h
  exact ⟨Q.descendant_subset p hx,Q.descendant_subset q hy⟩

theorem heavyPlateCellPairs_of_points (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j : ℕ) (r m : ℝ) {x y w : Space d} {a : ℝ}
    (hx : x ∈ Q.carrier) (hy : y ∈ Q.carrier) (hw : ‖w‖ = 1)
    (hm : ENNReal.ofReal m ≤ ρ {z | |inner ℝ w z-a| ≤ r})
    (hxw : |inner ℝ w x-a| ≤ r) (hyw : |inner ℝ w y-a| ≤ r) :
    (x,y) ∈ heavyPlateCellPairs ρ Q j r m := by
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth j hx
  obtain ⟨q,hq,hyq⟩ := Q.mem_descendant_at_depth j hy
  exact (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mpr
    ⟨p,hp,q,hq,⟨w,hw,a,hm,⟨x,hxp,hxw⟩,y,hyq,hyw⟩,hxp,hyq⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateFilter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decreasing coarse dyadic filters and their unnormalized fiber bounds -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurableSet_coarsePlateFilter (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ J : ℕ) (r m : ℕ → ℝ) : MeasurableSet (coarsePlateFilter ρ Q j₀ J r m) := by
  apply (Q.measurable.prod Q.measurable).diff
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ =>
    measurableSet_heavyPlateCellPairs ρ Q j (r j) (m j)))

theorem coarsePlateFilter_antitone (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ : ℕ) (r m : ℕ → ℝ) : Antitone (fun J => coarsePlateFilter ρ Q j₀ J r m) := by
  intro J K hJK p hp
  refine ⟨hp.1,?_⟩
  intro h
  apply hp.2
  obtain ⟨j,hj,hp'⟩ := mem_iUnion₂.mp h
  exact mem_iUnion₂.mpr ⟨j,Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2.trans hJK⟩,hp'⟩

theorem coarsePlateFilter_avoids (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ J : ℕ) (r m : ℕ → ℝ) {j : ℕ} (hj : j ∈ Finset.Icc j₀ J)
    {p : Space d × Space d} (hp : p ∈ coarsePlateFilter ρ Q j₀ J r m) :
    p ∉ heavyPlateCellPairs ρ Q j (r j) (m j) := by
  intro h
  exact hp.2 (mem_iUnion₂.mpr ⟨j,hj,h⟩)

theorem coarsePlateFilter_fiber_slab_bound (μ ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ)
    (hμ : μ ≤ ρ) {j : ℕ} (hj : j ∈ Finset.Icc j₀ J)
    (x w : Space d) (a : ℝ) (hw : ‖w‖ = 1)
    (hxw : |inner ℝ w x-a| ≤ r j) :
    μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m ∧
      |inner ℝ w y-a| ≤ r j} ≤ ENNReal.ofReal (m j) := by
  by_cases hh : ρ {y | |inner ℝ w y-a| ≤ r j} ≤ ENNReal.ofReal (m j)
  · exact (measure_mono (fun _ hy => hy.2)).trans ((hμ _).trans hh)
  · have hheavy := (not_le.mp hh).le
    have hempty : {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m ∧
        |inner ℝ w y-a| ≤ r j} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact coarsePlateFilter_avoids ρ Q j₀ J r m hj hy.1
        (heavyPlateCellPairs_of_points ρ Q j (r j) (m j) hy.1.1.1 hy.1.1.2
          hw hheavy hxw hy.2)
    rw [hempty,measure_empty]
    exact bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product-cell structure of every finite coarse plate filter -/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.descendant_subset_take {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (j : ℕ) :
    (Q.descendant p).carrier ⊆ (Q.descendant (p.take j)).carrier := by
  have he : Q.descendant p = (Q.descendant (p.take j)).descendant (p.drop j) := by
    rw [← Q.descendant_append,List.take_append_drop]
  rw [he]
  exact (Q.descendant (p.take j)).descendant_subset (p.drop j)

theorem DyadicCube.same_fine_cell_coarse {d J j : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = J) (hq : q.length = j) (hj : j ≤ J)
    {x x' : Space d} (hx : x ∈ (Q.descendant p).carrier)
    (hx' : x' ∈ (Q.descendant p).carrier) (hxq : x ∈ (Q.descendant q).carrier) :
    x' ∈ (Q.descendant q).carrier := by
  have htake : (p.take j).length = j := by simp only [List.length_take,hp,min_eq_left hj]
  have heq : p.take j = q := by
    by_contra hn
    exact Set.disjoint_left.mp (Q.descendants_disjoint (htake.trans hq.symm) hn)
      (Q.descendant_subset_take p j hx) hxq
  rw [← heq]
  exact Q.descendant_subset_take p j hx'

theorem heavyPlateCellPairs_fine_invariant {d J j : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (r m : ℝ) (p q : List (Fin d → Bool))
    (hp : p.length = J) (hq : q.length = J) (hj : j ≤ J)
    {x y x' y' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hy : y ∈ (Q.descendant q).carrier)
    (hx' : x' ∈ (Q.descendant p).carrier) (hy' : y' ∈ (Q.descendant q).carrier)
    (hxy : (x,y) ∈ heavyPlateCellPairs ρ Q j r m) :
    (x',y') ∈ heavyPlateCellPairs ρ Q j r m := by
  obtain ⟨a,ha,b,hb,hhit,hxa,hyb⟩ := (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mp hxy
  exact (mem_heavyPlateCellPairs_iff ρ Q j r m x' y').mpr
    ⟨a,ha,b,hb,hhit,Q.same_fine_cell_coarse p a hp ((mem_cubePaths d j a).mp ha) hj hx hx' hxa,
      Q.same_fine_cell_coarse q b hq ((mem_cubePaths d j b).mp hb) hj hy hy' hyb⟩

theorem coarsePlateFilter_fine_invariant {d J : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ : ℕ) (r m : ℕ → ℝ) (p q : List (Fin d → Bool))
    (hp : p.length = J) (hq : q.length = J) {x y x' y' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hy : y ∈ (Q.descendant q).carrier)
    (hx' : x' ∈ (Q.descendant p).carrier) (hy' : y' ∈ (Q.descendant q).carrier)
    (hxy : (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m) :
    (x',y') ∈ coarsePlateFilter ρ Q j₀ J r m := by
  refine ⟨⟨Q.descendant_subset p hx',Q.descendant_subset q hy'⟩,?_⟩
  intro hex
  obtain ⟨j,hj,hxy'⟩ := mem_iUnion₂.mp hex
  apply hxy.2
  exact mem_iUnion₂.mpr ⟨j,hj,heavyPlateCellPairs_fine_invariant ρ Q (r j) (m j)
    p q hp hq (Finset.mem_Icc.mp hj).2 hx' hy' hx hy hxy'⟩

theorem coarsePlateFilter_product_cells {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ) :
    ∃ T : Finset (List (Fin d → Bool) × List (Fin d → Bool)),
      T ⊆ (cubePaths d J).product (cubePaths d J) ∧
      coarsePlateFilter ρ Q j₀ J r m =
        ⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier := by
  classical
  let T := ((cubePaths d J).product (cubePaths d J)).filter
    (fun pq => (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier ⊆
      coarsePlateFilter ρ Q j₀ J r m)
  refine ⟨T,Finset.filter_subset _ _,?_⟩
  apply Subset.antisymm
  · rintro ⟨x,y⟩ hxy
    obtain ⟨p,hp,hx⟩ := Q.mem_descendant_at_depth J hxy.1.1
    obtain ⟨q,hq,hy⟩ := Q.mem_descendant_at_depth J hxy.1.2
    apply mem_iUnion₂.mpr
    refine ⟨(p,q),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,?_⟩,hx,hy⟩
    rintro ⟨x',y'⟩ ⟨hx',hy'⟩
    exact coarsePlateFilter_fine_invariant ρ Q j₀ r m p q
      ((mem_cubePaths d J p).mp hp) ((mem_cubePaths d J q).mp hq) hx hy hx' hy' hxy
  · intro xy hxy
    obtain ⟨pq,hpq,hxy⟩ := mem_iUnion₂.mp hxy
    exact (Finset.mem_filter.mp hpq).2 hxy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointPowerAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict power gaps used in endpoint row and triple selection -/

namespace Falconer
open Real Filter
open scoped Topology

theorem eventually_const_mul_rpow_lt {p q : ℝ} (hpq : q < p) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ C*δ^p < δ^q := by
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show q-p < 0 by linarith)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  calc
    _ < δ^(q-p)*δ^p := mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = _ := by rw [← Real.rpow_add hδ.1]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointDyadicScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic cutoff and power conversions for endpoint assembly -/

namespace Falconer
open Filter
open scoped Topology

theorem dyadic_inverse_tendsto :
    Tendsto (fun N : ℕ => 1/(2:ℝ)^N) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div,inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1))
  · filter_upwards [] with N
    change 0 < 1/(2:ℝ)^N
    positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanBallNet
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite nets in a Euclidean ball with the dimension-sharp cardinal bound -/

namespace Falconer
open Set Metric

theorem finite_euclidean_ball_net (d : ℕ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ S : Finset (Space d), (∀ x ∈ S, ‖x‖ ≤ R) ∧
      (∀ x : Space d, ‖x‖ ≤ R → ∃ y ∈ S, dist x y ≤ δ) ∧
      (S.card : ℝ) ≤ (2*R/δ+1)^d := by
  classical
  let P : Finset (Space d) → Prop := fun S => (∀ x ∈ S, ‖x‖ ≤ R) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < dist x y)
  have hcard (S : Finset (Space d)) (hS : P S) : (S.card:ℝ) ≤ (2*R/δ+1)^d :=
    separated_ball_card S 0 hδ hR (fun x hx y hy hxy => (hS.2 x hx y hy hxy).le)
      (fun x hx => by simpa only [dist_zero_right] using hS.1 x hx)
  let K : Set ℕ := {n | ∃ S : Finset (Space d), P S ∧ S.card = n}
  have hbounded : BddAbove K := by
    obtain ⟨N,hN⟩ := exists_nat_ge ((2*R/δ+1)^d)
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨S,hS,rfl⟩ := hn
    exact_mod_cast (hcard S hS).trans hN
  have hnonempty : K.Nonempty := ⟨0,∅,by simp [P],rfl⟩
  obtain ⟨n,hn,hmax⟩ := hbounded.exists_isGreatest_of_nonempty hnonempty
  obtain ⟨S,hS,hSn⟩ := hn
  refine ⟨S,hS.1,?_,hcard S hS⟩
  intro x hx
  by_contra hnocover
  have hfar : ∀ y ∈ S, δ < dist x y := by
    simpa only [not_exists,not_and,not_le] using hnocover
  have hxS : x ∉ S := by
    intro hh
    have hh' := hfar x hh
    simp only [dist_self] at hh'
    exact (not_lt_of_ge hδ.le) hh'
  have hnew : P (insert x S) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hS.1 y hy
    · intro y hy z hz hyz
      by_cases hyx : y = x
      · subst y
        exact hfar z (Finset.mem_of_mem_insert_of_ne hz (Ne.symm hyz))
      · have hyS : y ∈ S := Finset.mem_of_mem_insert_of_ne hy hyx
        by_cases hzx : z = x
        · subst z
          simpa only [dist_comm] using hfar y hyS
        · exact hS.2 y hyS z (Finset.mem_of_mem_insert_of_ne hz hzx) hyz
  have hh := hmax (show (insert x S).card ∈ K from ⟨insert x S,hnew,rfl⟩)
  rw [Finset.card_insert_of_notMem hxS,← hSn] at hh
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffinePlaneCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covering a bounded neighborhood of an affine plane -/

namespace Falconer
open Set Metric
variable {k d : ℕ}

theorem affine_plane_neighborhood_cover (F : Space k →ₗᵢ[ℝ] Space d) (a : Space d)
    {M A r : ℝ} (hM : 0 ≤ M) (hA : ‖a‖ ≤ A) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ S : Finset (Space d), (S.card:ℝ) ≤ (2*(M+A+1)/r+1)^k ∧
      ∀ x : Space d, ‖x‖ ≤ M → (∃ y : Space k, ‖x-(a+F y)‖ ≤ r) →
        ∃ c ∈ S, x ∈ ball c (3*r) := by
  classical
  have hA0 : 0 ≤ A := (norm_nonneg a).trans hA
  obtain ⟨T,_,hcover,hcard⟩ := finite_euclidean_ball_net k
    (by positivity : 0 ≤ M+A+1) hr
  let S := T.image (fun y => a+F y)
  refine ⟨S,?_,?_⟩
  · exact (Nat.cast_le.mpr (Finset.card_image_le)).trans hcard
  · intro x hx hnear
    obtain ⟨y,hy⟩ := hnear
    have hyR : ‖y‖ ≤ M+A+1 := by
      have hF := norm_sub_le (a+F y) a
      have hxF := norm_le_norm_add_norm_sub' (a+F y) x
      rw [add_sub_cancel_left,F.norm_map] at hF
      rw [norm_sub_rev] at hy
      linarith only [hF,hxF,hy,hx,hA,hr1]
    obtain ⟨z,hz,hyz⟩ := hcover y hyR
    refine ⟨a+F z,Finset.mem_image.mpr ⟨z,hz,rfl⟩,?_⟩
    have hd : dist (a+F y) (a+F z) ≤ r := by
      simpa only [dist_add_left,F.dist_map] using hyz
    apply mem_ball.mpr
    have ht := dist_triangle x (a+F y) (a+F z)
    have hxF : dist x (a+F y) ≤ r := by simpa only [dist_eq_norm] using hy
    linarith only [ht,hxF,hd,hr]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffinePlaneFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Frostman power bound near a lower-dimensional affine plane -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
variable {k d : ℕ}

theorem affine_plane_frostman_bound (μ : Measure (Space d))
    (F : Space k →ₗᵢ[ℝ] Space d) (a : Space d) {M A s C r : ℝ}
    (hM : 0 ≤ M) (hA : ‖a‖ ≤ A) (hC : 0 ≤ C)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    μ {x | ∃ y : Space k, ‖x-(a+F y)‖ ≤ r} ≤
      ENNReal.ofReal ((C*(3:ℝ)^s*(2*(M+A+1)+1)^k)*r^(s-(k:ℝ))) := by
  classical
  have hA0 : 0 ≤ A := (norm_nonneg a).trans hA
  obtain ⟨S,hcard,hcover⟩ := affine_plane_neighborhood_cover F a hM hA hr hr1
  have hmono : ∀ᵐ x ∂μ, x ∈ {x | ∃ y : Space k, ‖x-(a+F y)‖ ≤ r} →
      x ∈ ⋃ c ∈ S, ball c (3*r) := by
    filter_upwards [hbounded] with x hx
    intro hnear
    obtain ⟨c,hc,hxc⟩ := hcover x hx hnear
    exact mem_iUnion₂.mpr ⟨c,hc,hxc⟩
  have hcard' : (S.card:ℝ) ≤ ((2*(M+A+1)+1)/r)^k := by
    apply hcard.trans
    apply pow_le_pow_left₀ (by positivity)
    have he : 2*(M+A+1)/r+1 = (2*(M+A+1)+r)/r := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith only [hr1]) hr.le
  have hmass : μ {x | ∃ y : Space k, ‖x-(a+F y)‖ ≤ r} ≤
      ENNReal.ofReal ((S.card:ℝ)*(C*(3*r)^s)) := by
    apply (measure_mono_ae hmono).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc
      _ ≤ ∑ c ∈ S, ENNReal.ofReal (C*(3*r)^s) :=
        Finset.sum_le_sum (fun c _ => hfrost c (3*r) (by positivity))
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg S.card),ENNReal.ofReal_natCast]
  apply hmass.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (((2*(M+A+1)+1)/r)^k)*(C*(3*r)^s) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr.le,div_pow,Real.rpow_sub hr,
        Real.rpow_natCast]
      field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffineSubspaceFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for neighborhoods of lower-dimensional affine subspaces -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

theorem affine_subspace_frostman_bound (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (a : Space d) {M s C r : ℝ}
    (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (hC : 0 ≤ C)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hdim : Module.finrank ℝ V ≤ k) (hr : 0 < r) (hr1 : r ≤ 1) :
    μ (affineSubspaceNeighborhood V a r) ≤
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^k)*r^(s-(k:ℝ))) := by
  let F : Space (Module.finrank ℝ V) →ₗᵢ[ℝ] Space d :=
    V.subtypeₗᵢ.comp (sliceCoordinates V rfl).symm.toLinearIsometry
  have hnear : affineSubspaceNeighborhood V a r ⊆
      {x | ∃ y : Space (Module.finrank ℝ V), ‖x-(a+F y)‖ ≤ r} := by
    intro x hx
    refine ⟨sliceCoordinates V rfl (V.orthogonalProjectionOnto (x-a)),?_⟩
    have he : F (sliceCoordinates V rfl (V.orthogonalProjectionOnto (x-a))) =
        V.starProjection (x-a) := by simp [F]
    rw [he]
    have hv := V.starProjection_orthogonal_val (x-a)
    change ‖Vᗮ.starProjection (x-a)‖ ≤ r at hx
    convert hx using 2
    all_goals try with_reducible_and_instances rfl
    rw [hv]
    abel
  apply (measure_mono hnear).trans
    ((affine_plane_frostman_bound μ F a hM ha hC hbounded hfrost hr hr1).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hp : (2*(M+M+1)+1)^(Module.finrank ℝ V) ≤ (4*M+3)^k := by
    rw [show 2*(M+M+1)+1 = 4*M+3 by ring]
    exact pow_le_pow_right₀ (by linarith only [hM]) hdim
  have hrp : r^(s-(Module.finrank ℝ V:ℝ)) ≤ r^(s-(k:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hr1
    exact sub_le_sub_left (Nat.cast_le.mpr hdim) s
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hrp
    (by positivity) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PublishedHeavyPlates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published heavy-hyperplane cover used by the coarse-filter construction

P. Shmerkin, *A non-linear version of Bourgain's projection theorem*,
J. Eur. Math. Soc. 25 (2023), 4155--4204, Appendix B, Lemma B.3,
printed pages 4201--4202, DOI 10.4171/JEMS/1283.
Publisher PDF: https://ems.press/content/serial-article-files/32954 .

This is only the hyperplane case k=d-1, at the single scale used in the
application, with heavy threshold delta^(a/8192). The lower-dimensional
concentration hypothesis is retained explicitly. The conclusion covers
each heavy plate in the unit ball by one of finitely many thicker plates.
The constant is allowed to depend on the dimension, a and C. No assertion
about dyadic filters, retained product mass or distance sets is assumed.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem heavyPlateExponent_pos {a : ℝ} (ha : 0 < a) : 0 < heavyPlateExponent a := by
  unfold heavyPlateExponent
  positivity

theorem heavyPlate_cover_exponent {a : ℝ} (ha : 1/2 < a) :
    (1/4:ℝ) < a-2*heavyPlateExponent a := by
  unfold heavyPlateExponent
  linarith only [ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlateScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic powers and the earlier scale used by the coarse plate filter -/

namespace Falconer
open Filter
open scoped Topology

theorem plateScale_eq (j : ℕ) : plateScale j = 1/(2:ℝ)^j := by
  rw [plateScale,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]

theorem plateScale_pos (j : ℕ) : 0 < plateScale j :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem plateScale_le_one (j : ℕ) : plateScale j ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))

theorem plateScale_antitone : Antitone plateScale := by
  intro i j hij
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (Nat.cast_le.mpr hij)

theorem plateScale_rpow (j : ℕ) (t : ℝ) :
    (plateScale j)^t = ((2:ℝ)^(-t))^j := by
  rw [plateScale,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem plateScale_tendsto : Tendsto plateScale atTop (𝓝[>] (0:ℝ)) := by
  have he : plateScale = (fun j => 1/(2:ℝ)^j) := funext plateScale_eq
  rw [he]
  exact dyadic_inverse_tendsto

theorem plateScale_power_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => (plateScale j)^t) atTop (𝓝 (0:ℝ)) := by
  simp_rw [plateScale_rpow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht))

theorem plateScale_div_lower (j : ℕ) :
    (plateScale j)^(1/32:ℝ) ≤ plateScale (j/32) := by
  rw [plateScale,plateScale,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hnat : (j/32)*32 ≤ j := Nat.div_mul_le_self j 32
  have hreal : ((j/32:ℕ):ℝ)*32 ≤ (j:ℝ) := by exact_mod_cast hnat
  linarith only [hreal]

theorem plateScale_div_upper (j : ℕ) :
    plateScale (j/32) ≤ 2*(plateScale j)^(1/32:ℝ) := by
  have hnat : j < (j/32+1)*32 := by omega
  have hreal : (j:ℝ) < (((j/32:ℕ):ℝ)+1)*32 := by exact_mod_cast hnat
  have hexp : -((j/32:ℕ):ℝ) ≤ 1+(-(j:ℝ))*(1/32:ℝ) := by linarith only [hreal]
  calc
    _ ≤ (2:ℝ)^(1+(-(j:ℝ))*(1/32:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = _ := by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rfl

theorem plateScale_div_power (j : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (plateScale (j/32))^b ≤ (2:ℝ)^b*(plateScale j)^(b/32) := by
  apply (Real.rpow_le_rpow (plateScale_pos _).le (plateScale_div_upper j) hb).trans_eq
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (plateScale_pos _).le _),
    ← Real.rpow_mul (plateScale_pos _).le]
  congr 1
  ring_nf

theorem plate_exponent_gaps {a : ℝ} (ha : 0 < a) :
    0 < heavyPlateExponent a ∧ a/16 < a/8-2*heavyPlateExponent a ∧
      a/16 < a/8-256*heavyPlateExponent a := by
  unfold heavyPlateExponent
  constructor
  · positivity
  · constructor <;> linarith only [ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CoarseFloorPowers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The last coarse scale interpolates to a fixed positive directional exponent -/

namespace Falconer

theorem plateScale_floor_mul (N : ℕ) (ω : ℝ) :
    plateScale ⌊ω*(N:ℝ)⌋₊ ≤ 2*(plateScale N)^ω := by
  have hf := Nat.lt_floor_add_one (ω*(N:ℝ))
  have he : -(⌊ω*(N:ℝ)⌋₊:ℝ) ≤ 1+(-(N:ℝ))*ω := by linarith only [hf]
  calc
    _ ≤ (2:ℝ)^(1+(-(N:ℝ))*ω) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = _ := by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rfl

theorem coarse_floor_radius_power (N : ℕ) {ω b r : ℝ}
    (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hb : 0 ≤ b)
    (hr : plateScale N ≤ r) (hr1 : r ≤ 1) (D : ℝ) :
    (max (D*r) (plateScale ⌊ω*(N:ℝ)⌋₊))^b ≤
      (2*max D 1)^b*r^(ω*b) := by
  have hr0 : 0 < r := (plateScale_pos N).trans_le hr
  have hrpow : r ≤ r^ω := by
    calc
      r = r^(1:ℝ) := (Real.rpow_one r).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hω1
  have hmax : 1 ≤ max D 1 := le_max_right _ _
  have hD : 0 ≤ max D 1 := zero_le_one.trans hmax
  have hscale : plateScale ⌊ω*(N:ℝ)⌋₊ ≤ (2*max D 1)*r^ω := by
    calc
      _ ≤ 2*(plateScale N)^ω := plateScale_floor_mul N ω
      _ ≤ 2*r^ω := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (plateScale_pos N).le hr hω) (by norm_num)
      _ ≤ _ := by nlinarith only [hmax,Real.rpow_nonneg hr0.le ω]
  have hDr : D*r ≤ (2*max D 1)*r^ω := by
    have h₁ := mul_le_mul (le_max_left D 1) hrpow hr0.le hD
    have h₂ : 0 ≤ max D 1*r^ω := mul_nonneg hD (Real.rpow_nonneg hr0.le _)
    nlinarith only [h₁,h₂]
  apply (Real.rpow_le_rpow
    ((plateScale_pos _).le.trans (le_max_right _ _)) (max_le hDr hscale) hb).trans_eq
  rw [Real.mul_rpow (mul_nonneg (by norm_num) hD) (Real.rpow_nonneg hr0.le _),
    ← Real.rpow_mul hr0.le]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialDyadicBracket
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a retained dyadic scale for an arbitrary cap radius -/

namespace Falconer

theorem radial_dyadic_bracket (N : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hr1 : r ≤ 1) :
    ∃ j ≤ N, r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hr0 hr1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have he : (1/2:ℝ)^j = ((2:ℝ)^j)⁻¹ := by rw [one_div,inv_pow]
  rw [he] at hhi
  have hj : j ≤ N := by
    by_contra h
    have hp : (2:ℝ)^N < (2:ℝ)^j := pow_lt_pow_right₀ (by norm_num) (by omega)
    have hi : ((2:ℝ)^j)⁻¹ < ((2:ℝ)^N)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by positivity)).mpr hp
    exact (not_lt_of_ge hr) (hhi.trans_lt hi)
  refine ⟨j,hj,hhi,?_⟩
  rw [pow_succ,he] at hlo
  linarith

theorem radial_dyadic_bracket_above (N B : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hrB : r ≤ ((2:ℝ)^B)⁻¹) :
    ∃ j, B ≤ j ∧ j ≤ N ∧ r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr1 : r ≤ 1 := hrB.trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  obtain ⟨j,hj,hhi,hlo⟩ := radial_dyadic_bracket N hr hr1
  have hBj : B ≤ j := by
    by_contra h
    have hp : (2:ℝ)^(j+1) ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
    have hinv : ((2:ℝ)^B)⁻¹ ≤ ((2:ℝ)^(j+1))⁻¹ := inv_anti₀ (by positivity) hp
    have he : ((2:ℝ)^(j+1))⁻¹ = ((2:ℝ)^j)⁻¹/2 := by rw [pow_succ,mul_inv_rev]; ring
    rw [he] at hinv
    linarith
  exact ⟨j,hBj,hj,hhi,hlo⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TruncatedDyadicBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform interpolation above and below a finite dyadic scale window -/

namespace Falconer
open scoped ENNReal

theorem truncated_dyadic_bound (j₀ J : ℕ) (f : ℝ → ℝ≥0∞) (hf : Monotone f)
    (hmass : ∀ r, f r ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hdyadic : ∀ j, j₀ ≤ j → j ≤ J → f (plateScale j) ≤ ENNReal.ofReal (2*(plateScale j)^b))
    (r : ℝ) :
    f r ≤ ENNReal.ofReal ((max ((plateScale j₀)^(-b)) (2*(2:ℝ)^b))*
      (max r (plateScale J))^b) := by
  let C := max ((plateScale j₀)^(-b)) (2*(2:ℝ)^b)
  let t := max r (plateScale J)
  have hδJ : plateScale J ≤ t := le_max_right _ _
  have ht : 0 < t := (plateScale_pos J).trans_le (le_max_right _ _)
  by_cases hc : plateScale j₀ ≤ t
  · apply (hmass r).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    change 1 ≤ C*t^b
    have he : (plateScale j₀)^(-b)*(plateScale j₀)^b = 1 := by
      rw [← Real.rpow_add (plateScale_pos _),neg_add_cancel,Real.rpow_zero]
    calc
      1 = (plateScale j₀)^(-b)*(plateScale j₀)^b := he.symm
      _ ≤ C*t^b := mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow (plateScale_pos _).le hc hb)
        (Real.rpow_nonneg (plateScale_pos _).le _)
        (by dsimp [C]; exact (Real.rpow_nonneg (plateScale_pos _).le _).trans (le_max_left _ _))
  · have ht0 : t ≤ plateScale j₀ := (not_le.mp hc).le
    obtain ⟨j,hj₀,hjJ,htj,hjt⟩ := radial_dyadic_bracket_above J j₀
      (show ((2:ℝ)^J)⁻¹ ≤ t by simpa only [plateScale_eq,one_div] using hδJ)
      (show t ≤ ((2:ℝ)^j₀)⁻¹ by simpa only [plateScale_eq,one_div] using ht0)
    have htj' : t ≤ plateScale j := by simpa only [plateScale_eq,one_div] using htj
    have hjt' : plateScale j ≤ 2*t := by simpa only [plateScale_eq,one_div] using hjt.le
    apply ((hf ((le_max_left _ _).trans htj')).trans (hdyadic j hj₀ hjJ)).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      2*(plateScale j)^b ≤ 2*(2*t)^b :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (plateScale_pos _).le hjt' hb) (by norm_num)
      _ = (2*(2:ℝ)^b)*t^b := by rw [Real.mul_rpow (by norm_num) ht.le]; ring
      _ ≤ C*t^b := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateAffineBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-width affine slab bounds for the original coarse-filter fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem coarseSlabConstant_pos (j₀ : ℕ) (b : ℝ) : 0 < coarseSlabConstant j₀ b :=
  (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)).trans_le (le_max_right _ _)

theorem coarse_filter_affine_bound {d : ℕ} (μ ρ : Measure (Space d))
    [IsProbabilityMeasure μ] (Q : DyadicCube d) (j₀ J : ℕ)
    {b : ℝ} (hb : 0 ≤ b) (hμ : μ ≤ ρ)
    (x w : Space d) (hw : ‖w‖ = 1) (r : ℝ) :
    μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ J plateScale (fun j => 2*(plateScale j)^b) ∧
      |inner ℝ w y-inner ℝ w x| ≤ r} ≤
      ENNReal.ofReal (coarseSlabConstant j₀ b*(max r (plateScale J))^b) := by
  let f := fun r : ℝ => μ {y |
    (x,y) ∈ coarsePlateFilter ρ Q j₀ J plateScale (fun j => 2*(plateScale j)^b) ∧
      |inner ℝ w y-inner ℝ w x| ≤ r}
  apply truncated_dyadic_bound j₀ J f
    (fun r t hrt => measure_mono (fun _ hy => ⟨hy.1,hy.2.trans hrt⟩))
    (fun _ => prob_le_one) hb _ r
  intro j hj₀ hjJ
  exact coarsePlateFilter_fiber_slab_bound μ ρ Q j₀ J plateScale
    (fun j => 2*(plateScale j)^b) hμ (Finset.mem_Icc.mpr ⟨hj₀,hjJ⟩)
    x w (inner ℝ w x) hw (by simpa only [sub_self,abs_zero] using (plateScale_pos j).le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The all-radius directional slab estimate for each coarse filter -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem coarseDirectionalConstant_pos {d : ℕ} (Q : DyadicCube d) (j₀ : ℕ) (b : ℝ) :
    0 < coarseDirectionalConstant Q j₀ b := by
  apply mul_pos (coarseSlabConstant_pos j₀ b)
  apply Real.rpow_pos_of_pos
  have h := le_max_right (Real.sqrt d*Q.side) (1:ℝ)
  linarith

theorem coarse_filter_directional_bound {d : ℕ} (μ ρ : Measure (Space d))
    [IsProbabilityMeasure μ] (Q : DyadicCube d) (hQ : 0 ≤ Q.side) (j₀ N : ℕ)
    {b ω : ℝ} (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hμ : μ ≤ ρ)
    (x w : Space d) (hw : ‖w‖ = 1) {r : ℝ} (hr : plateScale N ≤ r) (hr1 : r ≤ 1) :
    μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale
      (fun j => 2*(plateScale j)^b) ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
      ENNReal.ofReal (coarseDirectionalConstant Q j₀ b*r^(ω*b)) := by
  let D := Real.sqrt d*Q.side
  have hr0 : 0 < r := (plateScale_pos N).trans_le hr
  have hm : μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale
      (fun j => 2*(plateScale j)^b) ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
      μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale
      (fun j => 2*(plateScale j)^b) ∧ |inner ℝ w y-inner ℝ w x| ≤ D*r} := by
    apply measure_mono
    intro y hy
    refine ⟨hy.1,?_⟩
    have hnorm : ‖y-x‖ ≤ D := by
      simpa only [dist_eq_norm] using Q.dist_le hQ hy.1.1.2 hy.1.1.1
    have hs := normalized_direction_slab w y x hnorm hr0.le hy.2
    simpa only [abs_sub_comm] using hs
  apply hm.trans ((coarse_filter_affine_bound μ ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ hb hμ x w hw (D*r)).trans
    (ENNReal.ofReal_le_ofReal ?_))
  calc
    _ ≤ coarseSlabConstant j₀ b*((2*max D 1)^b*r^(ω*b)) :=
      mul_le_mul_of_nonneg_left (coarse_floor_radius_power N hω hω1 hb hr hr1 D)
        (coarseSlabConstant_pos j₀ b).le
    _ = _ := by dsimp [coarseDirectionalConstant,D]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateLimit
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact limiting set of the decreasing coarse plate filters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem iInter_coarsePlateFilter {d : ℕ} (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ : ℕ) (r m : ℕ → ℝ) :
    (⋂ J : ℕ, coarsePlateFilter ρ Q j₀ J r m) =
      (Q.carrier ×ˢ Q.carrier) \ ⋃ n : ℕ, heavyPlateCellPairs ρ Q (j₀+n) (r (j₀+n)) (m (j₀+n)) := by
  ext xy
  constructor
  · intro h
    have hall := mem_iInter.mp h
    refine ⟨(hall 0).1,?_⟩
    intro hex
    obtain ⟨n,hn⟩ := mem_iUnion.mp hex
    exact (hall (j₀+n)).2 (mem_iUnion₂.mpr
      ⟨j₀+n,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,hn⟩)
  · rintro ⟨hroot,hgood⟩
    apply mem_iInter.mpr
    intro J
    refine ⟨hroot,?_⟩
    intro hex
    obtain ⟨j,hj,hxy⟩ := mem_iUnion₂.mp hex
    have hj₀ := (Finset.mem_Icc.mp hj).1
    apply hgood
    exact mem_iUnion.mpr ⟨j-j₀,by simpa only [Nat.add_sub_of_le hj₀] using hxy⟩

theorem coarsePlateFilter_limit_pos {d : ℕ} (ξ : Measure (Space d × Space d))
    (ρ : Measure (Space d)) (Q : DyadicCube d) (j₀ : ℕ) (r m : ℕ → ℝ)
    (hroot : ξ (Q.carrier ×ˢ Q.carrier) = 1)
    (hloss : ξ (⋃ n : ℕ, heavyPlateCellPairs ρ Q (j₀+n) (r (j₀+n)) (m (j₀+n))) < 1) :
    0 < ξ (⋂ J : ℕ, coarsePlateFilter ρ Q j₀ J r m) := by
  rw [iInter_coarsePlateFilter]
  apply pos_iff_ne_zero.mpr
  intro hz
  have hbound := (measure_le_inter_add_sdiff ξ (Q.carrier ×ˢ Q.carrier)
    (⋃ n : ℕ, heavyPlateCellPairs ρ Q (j₀+n) (r (j₀+n)) (m (j₀+n)))).trans
    (add_le_add (measure_mono inter_subset_right) le_rfl)
  rw [hz,add_zero,hroot] at hbound
  exact (not_le_of_gt hloss) hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyPlateCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing a finite plate cover to the actual dyadic cell exclusions -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem affine_slab_point_transport {w x y : Space d} {a r D : ℝ}
    (hw : ‖w‖ = 1) (hy : |inner ℝ w y-a| ≤ r) (hxy : dist x y ≤ D) :
    |inner ℝ w x-a| ≤ r+D := by
  have he : inner ℝ w x-a = inner ℝ w (x-y)+(inner ℝ w y-a) := by
    rw [inner_sub_right]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hi : |inner ℝ w (x-y)| ≤ D := by
    have hn := abs_real_inner_le_norm w (x-y)
    rw [hw,one_mul,← dist_eq_norm] at hn
    exact hn.trans hxy
  linarith only [hi,hy]

theorem heavyPlateCellPairs_finite_cover (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j : ℕ) (S : Finset (Space d × ℝ)) {r m R D : ℝ}
    (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hdiam : ∀ p ∈ cubePaths d j, ∀ x ∈ (Q.descendant p).carrier,
      ∀ y ∈ (Q.descendant p).carrier, dist x y ≤ D)
    (hcover : ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ,
      ENNReal.ofReal m ≤ ρ {x | |inner ℝ w x-a| ≤ r} →
      ∃ p ∈ S, ∀ x ∈ Q.carrier, |inner ℝ w x-a| ≤ r → |inner ℝ p.1 x-p.2| ≤ R) :
    heavyPlateCellPairs ρ Q j r m ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R+D} ×ˢ
        {y | |inner ℝ p.1 y-p.2| ≤ R+D} := by
  rintro ⟨x,y⟩ h
  obtain ⟨P,hP,T,hT,⟨w,hw,a,hm,⟨x',hx',hxw⟩,⟨y',hy',hyw⟩⟩,hx,hy⟩ :=
    (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mp h
  obtain ⟨p,hp,hpc⟩ := hcover w hw a hm
  refine mem_iUnion₂.mpr ⟨p,hp,?_,?_⟩
  · exact affine_slab_point_transport (hunit p hp)
      (hpc x' (Q.descendant_subset P hx') hxw) (hdiam P hP x hx x' hx')
  · exact affine_slab_point_transport (hunit p hp)
      (hpc y' (Q.descendant_subset T hy') hyw) (hdiam T hT y hy y' hy')

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MeanProbability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean probability of the two original endpoint laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem meanProbability_apply (μ ν : ProbabilityMeasure X) (A : Set X) :
    (meanProbability μ ν : Measure X) A = (2:ℝ≥0∞)⁻¹ *
      ((μ : Measure X) A+(ν : Measure X) A) := rfl

theorem meanProbability_ae (μ ν : ProbabilityMeasure X) (P : X → Prop)
    (hμ : ∀ᵐ x ∂(μ : Measure X), P x) (hν : ∀ᵐ x ∂(ν : Measure X), P x) :
    ∀ᵐ x ∂(meanProbability μ ν : Measure X), P x :=
  Measure.ae_smul_measure (ae_add_measure_iff.mpr ⟨hμ,hν⟩) _

theorem meanProbability_frostman {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    {s C : ℝ} (hμ : FrostmanBallBound (μ : Measure (Space d)) s C) (hν : FrostmanBallBound (ν : Measure (Space d)) s C) :
    FrostmanBallBound (meanProbability μ ν : Measure (Space d)) s C := by
  intro x r hr
  rw [meanProbability_apply]
  apply (mul_le_mul_right (add_le_add (hμ x r hr) (hν x r hr)) _).trans_eq
  rw [← two_mul,← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_mul]

theorem meanProbability_heavy (μ ν : ProbabilityMeasure X) (A : Set X) (m : ℝ)
    (h : ENNReal.ofReal (2*m) ≤ (μ : Measure X) A+(ν : Measure X) A) :
    ENNReal.ofReal m ≤ (meanProbability μ ν : Measure X) A := by
  rw [meanProbability_apply]
  have hh := mul_le_mul_right h ((2:ℝ≥0∞)⁻¹)
  rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat,← mul_assoc] at hh
  norm_num only [ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞),one_mul] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_UniformLowerPlanes
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lower-plane concentration, with arbitrary affine offset -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

theorem affine_subspace_change_anchor (V : Submodule ℝ (Space d))
    {a p x : Space d} {r : ℝ}
    (hp : p ∈ affineSubspaceNeighborhood V a r)
    (hx : x ∈ affineSubspaceNeighborhood V a r) :
    x ∈ affineSubspaceNeighborhood V p (2*r) := by
  have he : Vᗮ.starProjection (x-p) =
      Vᗮ.starProjection (x-a)-Vᗮ.starProjection (p-a) := by
    rw [← map_sub]
    congr 1
    abel
  change ‖Vᗮ.starProjection (x-p)‖ ≤ _
  change ‖Vᗮ.starProjection (x-a)‖ ≤ r at hx
  change ‖Vᗮ.starProjection (p-a)‖ ≤ r at hp
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith only [hx,hp])

theorem uniform_lower_plane_frostman (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {M s C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hs : 0 ≤ s-(k:ℝ))
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hfrost : FrostmanBallBound μ s C) :
    ∃ D : ℝ, 0 < D ∧ ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ k →
      ∀ a : Space d, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ (affineSubspaceNeighborhood V a r) ≤ ENNReal.ofReal (D*r^(s-(k:ℝ))) := by
  let A := max 1 (C*(3:ℝ)^s*(4*M+3)^k)
  have hA : 1 ≤ A := le_max_left _ _
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨A*2^(s-(k:ℝ)),by positivity,?_⟩
  intro V hV a r hr _hr1
  by_cases hsmall : 2*r ≤ 1
  · let T := {p : Space d | ‖p‖ ≤ M ∧ p ∈ affineSubspaceNeighborhood V a r}
    by_cases hT : T.Nonempty
    · obtain ⟨p,hp⟩ := hT
      have hmono : affineSubspaceNeighborhood V a r ⊆ affineSubspaceNeighborhood V p (2*r) :=
        fun _ hx => affine_subspace_change_anchor V hp.2 hx
      apply (measure_mono hmono).trans
      apply (affine_subspace_frostman_bound μ V p hM hp.1 hC hbounded hfrost hV
        (by positivity) hsmall).trans
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le]
      have hcA : C*(3:ℝ)^s*(4*M+3)^k ≤ A := le_max_right _ _
      have hm : (C*(3:ℝ)^s*(4*M+3)^k)*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) ≤
          A*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) :=
        mul_le_mul_of_nonneg_right hcA (by positivity)
      simpa only [mul_assoc] using hm
    · have hzero : μ (affineSubspaceNeighborhood V a r) ≤ μ (∅ : Set (Space d)) := by
        apply measure_mono_ae
        filter_upwards [hbounded] with x hx hnear
        exact (hT ⟨x,hx,hnear⟩).elim
      exact hzero.trans (by rw [measure_empty]; exact bot_le)
  · apply prob_le_one.trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hrp : 1 ≤ (2*r)^(s-(k:ℝ)) := Real.one_le_rpow (by linarith only [hsmall]) hs
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le] at hrp
    have hm : 1*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) ≤
        A*((2:ℝ)^(s-(k:ℝ))*r^(s-(k:ℝ))) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    simp only [one_mul] at hm
    simpa only [mul_assoc] using hrp.trans hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_UnitHeavyPlateCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise published cover applied to an original Frostman probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem unit_heavy_plate_cover (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ < 1)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ≤
            (μ : Measure (Space d)) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ < 1 → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(1/4:ℝ) := by
  have hα : 0 ≤ s-((d-2:ℕ):ℝ) := by linarith only [hs]
  have hbound : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ 1 := hbounded.mono (fun _ h => h.le)
  obtain ⟨D,hD,hplane⟩ := uniform_lower_plane_frostman (k := d-2)
    (μ : Measure (Space d)) (by norm_num) hC hα hbound hfrost
  obtain ⟨K,hK,hcover⟩ := hpublished d hd (s-((d-2:ℕ):ℝ)) D hs hs' hD
  refine ⟨K,hK,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover μ δ hδ hδ1 hbounded
    (fun V hV p => hplane V hV.le p δ hδ hδ1)
  refine ⟨S,hunit,hcard,?_⟩
  intro w hw t hheavy
  obtain ⟨p,hp,hpcover⟩ := hcoverS w hw t hheavy
  refine ⟨p,hp,?_⟩
  intro x hx hxw
  apply (hpcover x hx hxw).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    (heavyPlate_cover_exponent hs).le) (zero_le_one.trans hK)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_BoundedHeavyPlateCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the unit-ball normalization from the published heavy-plate cover -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem bounded_heavy_plate_cover (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ : ProbabilityMeasure (Space d)) {M s C : ℝ}
    (hM : 0 ≤ M) (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1)
    (hC : 0 ≤ C) (hbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ≤
            (μ : Measure (Space d)) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ ≤ M → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(1/4:ℝ) := by
  classical
  let c : ℝ := 1/(2*(M+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; apply (div_le_iff₀ (by positivity)).mpr; linarith only [hM]
  have hcM : c*M < 1 := by
    dsimp [c]
    rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith only [hM]
  let e := radialZoom c hc.ne' (0:Space d)
  let μ' : ProbabilityMeasure (Space d) := μ.map (f := e) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hbound' : ∀ᵐ y ∂(μ' : Measure (Space d)), ‖y‖ < 1 := by
    change ∀ᵐ y ∂Measure.map e (μ : Measure (Space d)), ‖y‖ < 1
    rw [ae_map_iff e.measurable.aemeasurable (measurableSet_lt measurable_norm measurable_const)]
    filter_upwards [hbounded] with x hx
    have he : ‖e x‖ = c*‖x‖ := by simpa only [sub_zero] using radialZoom_norm hc (0:Space d) x
    rw [he]
    exact (mul_le_mul_of_nonneg_left hx hc.le).trans_lt hcM
  have hfrost' : FrostmanBallBound (μ' : Measure (Space d)) s (C*c^(-s)) :=
    radialZoom_full_frostman (μ : Measure (Space d)) hc (0:Space d) hfrost
  obtain ⟨K,hK,hcover⟩ := unit_heavy_plate_cover hpublished hd μ' hs hs'
    (mul_nonneg hC (Real.rpow_nonneg hc.le _)) hbound' hfrost'
  let b := heavyPlateExponent (s-((d-2:ℕ):ℝ))
  have hb : 0 < b := heavyPlateExponent_pos (by linarith only [hs])
  let L := max 1 (max (K*c^(-b)) (K*c^(1/4:ℝ)/c))
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLK : K*c^(-b) ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLW : K*c^(1/4:ℝ)/c ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨L,hL1,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover (c*δ) (mul_pos hc hδ)
    ((mul_le_mul_of_nonneg_right hc1 hδ.le).trans (by simpa only [one_mul] using hδ1))
  let S' := S.image (fun p => (p.1,p.2/c))
  refine ⟨S',?_,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hunit q hq
  · have hcard' : (S'.card:ℝ) ≤ (S.card:ℝ) := Nat.cast_le.mpr Finset.card_image_le
    apply hcard'.trans (hcard.trans ?_)
    rw [Real.mul_rpow hc.le hδ.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hLK (Real.rpow_nonneg hδ.le (-b))
  · intro w hw t hheavy
    have hheavy' : ENNReal.ofReal ((c*δ)^b) ≤
        (μ' : Measure (Space d)) {y | |inner ℝ w y-c*t| ≤ c*δ} := by
      change ENNReal.ofReal ((c*δ)^b) ≤ Measure.map (radialZoom c hc.ne' (0:Space d))
        (μ : Measure (Space d)) {y | |inner ℝ w y-c*t| ≤ c*δ}
      rw [radialZoom_zero_slab (μ : Measure (Space d)) hc w t δ]
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) hheavy
      exact Real.rpow_le_rpow (mul_nonneg hc.le hδ.le)
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hδ.le) hb.le
    obtain ⟨p,hp,hpcover⟩ := hcoverS w hw (c*t) hheavy'
    refine ⟨(p.1,p.2/c),Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    intro x hx hxw
    have hcx : ‖c • x‖ < 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left hx hc.le).trans_lt hcM
    have hxw' : |inner ℝ w (c • x)-c*t| ≤ c*δ := by
      rw [inner_smul_right,show c*inner ℝ w x-c*t = c*(inner ℝ w x-t) by ring,
        abs_mul,abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hxw hc.le
    apply (pullback_affine_slab hc p.1 x (hpcover (c • x) hcx hxw')).trans
    rw [Real.mul_rpow hc.le hδ.le]
    have hh := mul_le_mul_of_nonneg_right hLW (Real.rpow_nonneg hδ.le (1/4:ℝ))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_OriginalHeavyPlateCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The heavy-plate cover for the sum of the two original probability laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem original_heavy_plate_cover (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d)) {M s C : ℝ}
    (hM : 0 ≤ M) (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (2*δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ≤
            ((μ : Measure (Space d))+(ν : Measure (Space d))) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ ≤ M → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(1/4:ℝ) := by
  obtain ⟨K,hK,hcover⟩ := bounded_heavy_plate_cover hpublished hd (meanProbability μ ν)
    hM hs hs' hC (meanProbability_ae μ ν _ hμbounded hνbounded)
    (meanProbability_frostman μ ν hμfrost hνfrost)
  refine ⟨K,hK,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover δ hδ hδ1
  refine ⟨S,hunit,hcard,?_⟩
  intro w hw t hheavy
  apply hcoverS w hw t
  apply meanProbability_heavy μ ν _ (δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ))))
  simpa only [Measure.add_apply] using hheavy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_DyadicHeavyCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite thicker-plate covers of the actual original dyadic exclusions -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem dyadic_heavy_plate_covers (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d))
    (Q : DyadicCube d) (hQ : 0 < Q.side) {M s C : ℝ}
    (hM : 0 ≤ M) (hroot : ∀ x ∈ Q.carrier, ‖x‖ ≤ M)
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ j : ℕ, let δ := (2:ℝ)^(-(j:ℝ))
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ A*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        heavyPlateCellPairs ((μ : Measure (Space d))+(ν : Measure (Space d))) Q j δ
          (2*δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ⊆
          ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ A*δ^(1/4:ℝ)} ×ˢ
            {y | |inner ℝ p.1 y-p.2| ≤ A*δ^(1/4:ℝ)} := by
  obtain ⟨K,hK,hcover⟩ := original_heavy_plate_cover hpublished hd μ ν hM hs hs' hC
    hμbounded hνbounded hμfrost hνfrost
  let D := Real.sqrt d*Q.side
  have hD : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) hQ.le
  refine ⟨K+D,by linarith only [hK,hD],?_⟩
  intro j
  let δ := (2:ℝ)^(-(j:ℝ))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by norm_num) _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hδeq : δ = 1/(2:ℝ)^j := by
    dsimp [δ]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover δ hδ hδ1
  refine ⟨S,hunit,hcard.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith only [hD]) (Real.rpow_nonneg hδ.le _)
  · have hdiam : ∀ p ∈ cubePaths d j, ∀ x ∈ (Q.descendant p).carrier,
        ∀ y ∈ (Q.descendant p).carrier, dist x y ≤ D*δ := by
      intro p hp x hx y hy
      have hh := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hx hy
      rw [Q.descendant_side,(mem_cubePaths d j p).mp hp] at hh
      apply hh.trans_eq
      rw [hδeq]
      dsimp [D]
      ring
    have hc := heavyPlateCellPairs_finite_cover
      ((μ : Measure (Space d))+(ν : Measure (Space d))) Q j S hunit hdiam
      (fun w hw t ht => by
        obtain ⟨p,hp,hpc⟩ := hcoverS w hw t ht
        exact ⟨p,hp,fun x hx hxt => hpc x (hroot x hx) hxt⟩)
    have hδgrow : δ ≤ δ^(1/4:ℝ) := by
      calc
        δ = δ^(1:ℝ) := (Real.rpow_one δ).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
    have hwidth : K*δ^(1/4:ℝ)+D*δ ≤ (K+D)*δ^(1/4:ℝ) := by
      nlinarith only [mul_le_mul_of_nonneg_left hδgrow hD]
    intro xy hxy
    obtain ⟨p,hp,hx,hy⟩ := mem_iUnion₂.mp (hc hxy)
    exact mem_iUnion₂.mpr ⟨p,hp,hx.trans hwidth,hy.trans hwidth⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_InitialPlateCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common thicker-plate cover for the initial block of exclusion scales -/

namespace Falconer
open Set

private theorem plateScale_mul (j k : ℕ) :
    plateScale (k*j) = (plateScale j)^(k:ℝ) := by
  rw [plateScale,plateScale,Nat.cast_mul,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem initial_plate_block_cover {d : ℕ}
    (E : ℕ → Set (Space d × Space d)) (S : ℕ → Finset (Space d × ℝ))
    {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hunit : ∀ j, ∀ p ∈ S j, ‖p.1‖ = 1)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ A*(plateScale j)^(-b))
    (hcover : ∀ j, E j ⊆ ⋃ p ∈ S j,
      {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)})
    (j₀ : ℕ) :
    ∃ T : Finset (Space d × ℝ), (∀ p ∈ T, ‖p.1‖ = 1) ∧
      (T.card:ℝ) ≤ ((63*j₀:ℕ):ℝ)*A*(plateScale j₀)^(-64*b) ∧
      (⋃ i ∈ Finset.range (63*j₀), E (j₀+i)) ⊆
        ⋃ p ∈ T, {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j₀)^(1/4:ℝ)} ×ˢ
          {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j₀)^(1/4:ℝ)} := by
  classical
  let T := (Finset.range (63*j₀)).biUnion (fun i => S (j₀+i))
  refine ⟨T,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,hpi⟩ := Finset.mem_biUnion.mp hp
    exact hunit (j₀+i) p hpi
  · have hpower : (plateScale (64*j₀))^(-b) = (plateScale j₀)^(-64*b) := by
      rw [plateScale_mul,← Real.rpow_mul (plateScale_pos _).le]
      congr 1
      norm_num
    calc
      (T.card:ℝ) ≤ ∑ i ∈ Finset.range (63*j₀), ((S (j₀+i)).card:ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.range (63*j₀))
          (t := fun i => S (j₀+i)))
      _ ≤ ∑ _i ∈ Finset.range (63*j₀), A*(plateScale (64*j₀))^(-b) := by
        apply Finset.sum_le_sum
        intro i hi
        apply (hcard (j₀+i)).trans
        apply mul_le_mul_of_nonneg_left _ hA
        apply Real.rpow_le_rpow_of_nonpos (plateScale_pos _)
          (plateScale_antitone (by have := Finset.mem_range.mp hi; omega)) (neg_nonpos.mpr hb)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,hpower]
        ring
  · intro xy hxy
    obtain ⟨i,hi,hxy⟩ := mem_iUnion₂.mp hxy
    obtain ⟨p,hp,hx,hy⟩ := mem_iUnion₂.mp (hcover (j₀+i) hxy)
    have hw : A*(plateScale (j₀+i))^(1/4:ℝ) ≤ A*(plateScale j₀)^(1/4:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (plateScale_pos _).le
        (plateScale_antitone (by omega)) (by norm_num)) hA
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_biUnion.mpr ⟨i,hi,hp⟩,hx.trans hw,hy.trans hw⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ExceptionalFiberMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a uniform fiber bound outside a measurable exceptional set -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_mass_of_exceptional_fibers (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Set (X × Y)) (hG : MeasurableSet G) (E : Set X) (hE : MeasurableSet E)
    {B : ℝ≥0∞} (hfiber : ∀ᵐ x ∂μ, x ∉ E → ν {y | (x,y) ∈ G} ≤ B) :
    (μ.prod ν) G ≤ μ E+B := by
  rw [Measure.prod_apply hG]
  calc
    _ ≤ ∫⁻ x, E.indicator (fun _ => (1:ℝ≥0∞)) x+B ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hfiber] with x hx
      by_cases hxe : x ∈ E
      · rw [indicator_of_mem hxe]
        exact (prob_le_one).trans (le_add_right le_rfl)
      · rw [indicator_of_notMem hxe,zero_add]
        exact hx hxe
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hE),
        lintegral_indicator_const hE,lintegral_const,measure_univ,one_mul,mul_one]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_VanishingSlabs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shrinking affine slabs have vanishing mass when their hyperplanes are null -/

namespace Falconer
open Set MeasureTheory Filter NormedSpace
open scoped ENNReal Topology

theorem exists_small_sublevel_of_null_fiber {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hzero : μ {x | f x = 0} = 0) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ μ {x | |f x| ≤ r} < η := by
  let E : ℝ → Set X := fun r => {x | |f x| ≤ r}
  have hlim := tendsto_measure_biInter_gt (μ := μ) (s := E) (a := (0:ℝ))
    (fun r _ => (measurableSet_le
      (by simpa only [Real.norm_eq_abs] using hf.norm) measurable_const).nullMeasurableSet)
    (fun _ _ _ hij => fun _ hx => hx.trans hij)
    ⟨1,by norm_num,measure_ne_top μ _⟩
  have heq : (⋂ r > (0:ℝ), E r) = {x | f x = 0} := by
    ext x
    simp only [mem_iInter,mem_ofPred_eq,E]
    constructor
    · intro hx
      have hh : |f x| = 0 := by
        by_contra hn
        have hp : 0 < |f x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
        have h := hx (|f x|/2) (by positivity)
        linarith only [h,hp]
      exact abs_eq_zero.mp hh
    · intro hx r hr
      simpa only [hx,abs_zero] using hr.le
  rw [heq,hzero] at hlim
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0, μ (E r) < η := hlim.eventually (gt_mem_nhds hη)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,hr,hsmall⟩ := (hpos.and hevent).exists
  exact ⟨r,hr,hsmall⟩

theorem exists_small_affine_slab {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (w : Space d) (a : ℝ) (hzero : μ {x | inner ℝ w x = a} = 0)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ μ {x | |inner ℝ w x-a| ≤ r} < η := by
  apply exists_small_sublevel_of_null_fiber μ (fun x => inner ℝ w x-a)
    ((continuous_const.inner continuous_id).sub continuous_const).measurable _ hη
  simpa only [sub_eq_zero] using hzero

theorem affine_slab_parameter_bound {d : ℕ} {w w' x : Space d} {a a' M : ℝ}
    (hx : ‖x‖ ≤ M) :
    |(inner ℝ w x-a)-(inner ℝ w' x-a')| ≤ M*‖w-w'‖+|a-a'| := by
  calc
    _ = |inner ℝ (w-w') x-(a-a')| := by congr 1; rw [inner_sub_left]; ring
    _ ≤ |inner ℝ (w-w') x|+|a-a'| := abs_sub _ _
    _ ≤ ‖w-w'‖*‖x‖+|a-a'| := add_le_add (abs_real_inner_le_norm _ _) le_rfl
    _ ≤ M*‖w-w'‖+|a-a'| := by nlinarith only [hx,norm_nonneg (w-w')]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffineSlabCluster
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine slabs with a common point and nearby normal directions -/

namespace Falconer
open Set NormedSpace
variable {d : ℕ}

theorem affine_slab_cluster {u v x y : Space d} {a b M r τ : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hτ : normalDistance u v ≤ τ)
    (hux : |inner ℝ u x-a| ≤ r) (hvx : |inner ℝ v x-b| ≤ r)
    (hvy : |inner ℝ v y-b| ≤ r) :
    |inner ℝ u y-a| ≤ 2*M*τ+3*r := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  have hxy : ‖y-x‖ ≤ 2*M := (norm_sub_le y x).trans (by linarith only [hx,hy])
  have hvxy : |inner ℝ v (y-x)| ≤ 2*r := by
    rw [inner_sub_right]
    have he : inner ℝ v y-inner ℝ v x = (inner ℝ v y-b)-(inner ℝ v x-b) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith only [hvx,hvy])
  have huxy : |inner ℝ u (y-x)| ≤ 2*M*τ+2*r := by
    have helper (w : Space d) (hw : ‖u-w‖ ≤ τ)
        (hwi : |inner ℝ w (y-x)| ≤ 2*r) :
        |inner ℝ u (y-x)| ≤ 2*M*τ+2*r := by
      have he : inner ℝ u (y-x) = inner ℝ (u-w) (y-x)+inner ℝ w (y-x) := by
        rw [inner_sub_left]; ring
      rw [he]
      apply (abs_add_le _ _).trans
      have hb : |inner ℝ (u-w) (y-x)| ≤ τ*(2*M) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul hw hxy (norm_nonneg _) ((norm_nonneg _).trans hw))
      linarith only [hb,hwi]
    rcases (min_le_iff.mp hτ) with h | h
    · exact helper v h hvxy
    · apply helper (-v) (by simpa only [sub_neg_eq_add] using h)
      simpa only [inner_neg_left,abs_neg] using hvxy
  have he : inner ℝ u y-a = inner ℝ u (y-x)+(inner ℝ u x-a) := by
    rw [inner_sub_right]; ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith only [huxy,hux])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation of unoriented normals controls their transverse component -/

namespace Falconer
variable {d : ℕ}

theorem normalDistance_le_perpendicular {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    normalDistance u v ≤ 2*‖perpendicularPart u v‖ := by
  by_cases h : 0 ≤ inner ℝ u v
  · exact (min_le_left _ _).trans (unit_close_of_perpendicular hu hv h)
  · have hneg : 0 ≤ inner ℝ u (-v) := by
      rw [inner_neg_right]
      linarith only [h]
    have hn : ‖-v‖ = 1 := by simpa only [norm_neg] using hv
    have hh := unit_close_of_perpendicular hu hn hneg
    have he : perpendicularPart u (-v) = -(perpendicularPart u v) := by
      simp only [perpendicularPart,inner_neg_right,neg_smul]
      abel
    rw [he,norm_neg,sub_neg_eq_add] at hh
    exact (min_le_right _ _).trans hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoNormalProjection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The codimension-two plane orthogonal to two orthonormal directions -/

namespace Falconer
open Set Submodule
open scoped BigOperators
variable {d : ℕ}

theorem orthonormal_pair_complement (v : Fin 2 → Space d) (hv : Orthonormal ℝ v) :
    ∃ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 ∧
      ∀ z : Space d, ‖Vᗮ.starProjection z‖ ≤ |inner ℝ (v 0) z|+|inner ℝ (v 1) z| := by
  classical
  let W := Submodule.span ℝ (Set.range v)
  refine ⟨Wᗮ,?_,?_⟩
  · have hdim : Module.finrank ℝ W = 2 := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hv.linearIndependent
    have hd := W.finrank_add_finrank_orthogonal
    rw [hdim] at hd
    simp only [finrank_euclideanSpace_fin] at hd
    omega
  · intro z
    let p := ∑ i : Fin 2, inner ℝ (v i) z • v i
    have hp : p ∈ W := Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    have hpinner (i : Fin 2) : inner ℝ p (v i) = inner ℝ z (v i) := by
      calc
        _ = inner ℝ (v i) p := real_inner_comm _ _
        _ = inner ℝ (v i) z := hv.inner_right_fintype (fun j => inner ℝ (v j) z) i
        _ = _ := real_inner_comm _ _
    have he : W.starProjection z = p := by
      apply W.eq_starProjection_of_mem_of_inner_eq_zero hp
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i,rfl⟩ := hw
        rw [inner_sub_left,hpinner,sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp only [inner_add_right,hx,hy,add_zero]
      | smul a x _ hx => simp only [inner_smul_right,hx,mul_zero]
    simp only [Submodule.orthogonal_orthogonal]
    rw [he]
    calc
      _ ≤ ∑ i : Fin 2, ‖inner ℝ (v i) z • v i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_smul,hv.norm_eq_one,Fin.sum_univ_two]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TwoSlabGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The intersection of two separated affine slabs lies near a codimension-two plane -/

namespace Falconer
open Set NormedSpace
variable {d : ℕ}

theorem two_slab_intersection_near_plane (u v : Space d)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {τ r : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr : 0 ≤ r)
    (hsep : τ ≤ normalDistance u v) :
    ∃ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 ∧
      ∀ (p x : Space d) (a b : ℝ),
        |inner ℝ u p-a| ≤ r → |inner ℝ v p-b| ≤ r →
        |inner ℝ u x-a| ≤ r → |inner ℝ v x-b| ≤ r →
        x ∈ affineSubspaceNeighborhood V p (10*r/τ) := by
  let w := perpendicularPart u v
  have ht : τ ≤ 2*‖w‖ := hsep.trans (normalDistance_le_perpendicular hu hv)
  have hw : 0 < ‖w‖ := by linarith only [ht,hτ]
  let e := normalize w
  have he : ‖e‖ = 1 := by
    dsimp [e,NormedSpace.normalize]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw),inv_mul_cancel₀ hw.ne']
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq,hu]; norm_num
  have hwu : inner ℝ u w = 0 := by
    simp only [w,perpendicularPart,inner_sub_right,inner_smul_right,huu,mul_one,sub_self]
  have heu : inner ℝ u e = 0 := by
    simp only [e,NormedSpace.normalize,inner_smul_right,hwu,mul_zero]
  have horth : Orthonormal ℝ (![u,e] : Fin 2 → Space d) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using huu
    · simpa using heu
    · have h : inner ℝ e u = 0 := (real_inner_comm u e).trans heu
      simpa using h
    · simp [he]
  obtain ⟨V,hV,hproj⟩ := orthonormal_pair_complement _ horth
  refine ⟨V,hV,?_⟩
  intro p x a b hup hvp hux hvx
  have hdiff (n : Space d) (c : ℝ) (hp : |inner ℝ n p-c| ≤ r)
      (hx : |inner ℝ n x-c| ≤ r) : |inner ℝ n (x-p)| ≤ 2*r := by
    rw [inner_sub_right]
    have heq : inner ℝ n x-inner ℝ n p = (inner ℝ n x-c)-(inner ℝ n p-c) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith only [hp,hx])
  have hudz := hdiff u a hup hux
  have hvdz := hdiff v b hvp hvx
  have hc : |inner ℝ u v| ≤ 1 := by
    simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v
  have hwdz : |inner ℝ w (x-p)| ≤ 4*r := by
    rw [show inner ℝ w (x-p) = inner ℝ v (x-p)-inner ℝ u v*inner ℝ u (x-p) by
      simp only [w,perpendicularPart,inner_sub_left,real_inner_smul_left]]
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul hc hudz (abs_nonneg _) zero_le_one
    linarith only [hm,hvdz]
  have hedz : |inner ℝ e (x-p)| ≤ 8*r/τ := by
    change |inner ℝ (‖w‖⁻¹ • w) (x-p)| ≤ _
    rw [real_inner_smul_left,abs_mul,abs_of_pos (inv_pos.mpr hw)]
    calc
      _ ≤ ‖w‖⁻¹*(4*r) := mul_le_mul_of_nonneg_left hwdz (inv_nonneg.mpr hw.le)
      _ ≤ 8*r/τ := by
        rw [inv_mul_eq_div]
        apply (div_le_div_iff₀ hw hτ).mpr
        have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hr)
        nlinarith only [hm]
  change ‖Vᗮ.starProjection (x-p)‖ ≤ _
  have hh := hproj (x-p)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  apply hh.trans
  apply (add_le_add hudz hedz).trans
  apply (le_div_iff₀ hτ).mpr
  have hm := mul_le_mul_of_nonneg_left hτ1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr)
  rw [add_mul,div_mul_cancel₀ _ hτ.ne']
  nlinarith only [hm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TwoSlabMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frostman mass of the intersection of two transversely oriented slabs -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem two_slab_frostman_bound (μ : Measure (Space d))
    (u v : Space d) (a b : ℝ) {M s C τ r : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr : 0 < r)
    (hsep : τ ≤ normalDistance u v) (hsmall : 10*r/τ ≤ 1) :
    μ {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ≤
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*r/τ)^(s-((d-2:ℕ):ℝ))) := by
  let X := {x : Space d | ‖x‖ ≤ M ∧
    |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r}
  have hmono : μ {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ≤ μ X := by
    apply measure_mono_ae
    filter_upwards [hbounded] with x hx
    exact fun h => ⟨hx,h⟩
  by_cases hX : X.Nonempty
  · obtain ⟨p,hp⟩ := hX
    obtain ⟨V,hV,hnear⟩ := two_slab_intersection_near_plane u v hu hv hτ hτ1 hr.le hsep
    have hXnear : X ⊆ affineSubspaceNeighborhood V p (10*r/τ) := by
      intro x hx
      exact hnear p x a b hp.2.1 hp.2.2 hx.2.1 hx.2.2
    exact hmono.trans ((measure_mono hXnear).trans
      (affine_subspace_frostman_bound μ V p hM hp.1 hC hbounded hfrost hV.le
        (by positivity) hsmall))
  · rw [Set.not_nonempty_iff_eq_empty.mp hX,measure_empty] at hmono
    exact hmono.trans bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_FinitePlateException
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite family of plates: exceptional intersections and clustering -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem measurableSet_slabPairException (S : Finset (Space d × ℝ)) (r τ : ℝ) :
    MeasurableSet (slabPairException S r τ) := by
  classical
  apply Finset.measurableSet_biUnion S
  intro p _
  apply Finset.measurableSet_biUnion S
  intro q _
  split_ifs
  · exact (measurableSet_le
      (by fun_prop : Measurable (fun x : Space d => |inner ℝ p.1 x-p.2|))
      measurable_const).inter (measurableSet_le
      (by fun_prop : Measurable (fun x : Space d => |inner ℝ q.1 x-q.2|)) measurable_const)
  · exact MeasurableSet.empty

theorem slabPairException_mass (μ : Measure (Space d))
    (S : Finset (Space d × ℝ)) {M s C r τ : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C) (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr : 0 < r) (hsmall : 10*r/τ ≤ 1) :
    μ (slabPairException S r τ) ≤ (S.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*r/τ)^(s-((d-2:ℕ):ℝ))) := by
  classical
  let B := ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
    (10*r/τ)^(s-((d-2:ℕ):ℝ)))
  change μ (⋃ p ∈ S, ⋃ q ∈ S, if τ ≤ normalDistance p.1 q.1 then
    {x | |inner ℝ p.1 x-p.2| ≤ r ∧ |inner ℝ q.1 x-q.2| ≤ r} else ∅) ≤ _
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ S, ∑ _q ∈ S, B := by
      apply Finset.sum_le_sum
      intro p hp
      apply (measure_biUnion_finset_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hsep
      · exact two_slab_frostman_bound μ p.1 q.1 p.2 q.2 hM hC hbounded hfrost
          (hunit p hp) (hunit q hq) hτ hτ1 hr hsep hsmall
      · simp only [measure_empty]; exact bot_le
    _ = _ := by simp [nsmul_eq_mul,pow_two,mul_assoc,B]

theorem cluster_outside_slabPairException (S : Finset (Space d × ℝ))
    {x : Space d} {M r τ : ℝ} (hx : ‖x‖ ≤ M)
    (hgood : x ∉ slabPairException S r τ)
    {p : Space d × ℝ} (hp : p ∈ S) (hxp : |inner ℝ p.1 x-p.2| ≤ r) :
    ∀ q ∈ S, |inner ℝ q.1 x-q.2| ≤ r → ∀ y : Space d,
      ‖y‖ ≤ M → |inner ℝ q.1 y-q.2| ≤ r →
      |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*r := by
  classical
  intro q hq hxq y hy hyq
  have hclose : normalDistance p.1 q.1 < τ := by
    by_contra! hn
    apply hgood
    exact mem_iUnion₂.mpr ⟨p,hp,mem_iUnion₂.mpr ⟨q,hq,by
      rw [ite_eq_left hn]; exact ⟨hxp,hxq⟩⟩⟩
  exact affine_slab_cluster hx hy hclose.le hxp hxq hyq

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_LatePlateFiber
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Newly deleted pairs outside the exceptional first endpoints have small fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem late_plate_fiber_bound (ν ρ : Measure (Space d)) (Q : DyadicCube d)
    (j j' : ℕ) (S : Finset (Space d × ℝ)) (G : Set (Space d × Space d))
    {r m r' m' R τ M : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hτ : 0 ≤ τ)
    (hwidth : 2*M*τ+3*R ≤ r') (hν : ν ≤ ρ)
    (hbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hG : G ⊆ heavyPlateCellPairs ρ Q j r m \ heavyPlateCellPairs ρ Q j' r' m')
    (hcover : heavyPlateCellPairs ρ Q j r m ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ {y | |inner ℝ p.1 y-p.2| ≤ R})
    (x : Space d) (hx : ‖x‖ ≤ M) (hgood : x ∉ slabPairException S R τ) :
    ν {y | (x,y) ∈ G} ≤ ENNReal.ofReal m' := by
  classical
  let F := {y | (x,y) ∈ G}
  by_cases hF : F.Nonempty
  · obtain ⟨y₀,hy₀⟩ := hF
    obtain ⟨p,hp,hxp,hyp⟩ := mem_iUnion₂.mp (hcover (hG hy₀).1)
    have hRr : R ≤ r' := by
      have hMT := mul_nonneg hM hτ
      nlinarith only [hwidth,hMT,hR]
    have hxfar : |inner ℝ p.1 x-p.2| ≤ r' := hxp.trans hRr
    have hfiber : ∀ᵐ y ∂ν, y ∈ F → |inner ℝ p.1 y-p.2| ≤ r' := by
      filter_upwards [hbounded] with y hy hGy
      obtain ⟨q,hq,hxq,hyq⟩ := mem_iUnion₂.mp (hcover (hG hGy).1)
      exact (cluster_outside_slabPairException S hx hgood hp hxp q hq hxq y hy hyq).trans hwidth
    by_cases hmass : ρ {y | |inner ℝ p.1 y-p.2| ≤ r'} ≤ ENNReal.ofReal m'
    · exact (measure_mono_ae hfiber).trans ((hν _).trans hmass)
    · have hempty : ν F ≤ ν (∅ : Set (Space d)) := by
        apply measure_mono_ae
        filter_upwards [hfiber] with y hy hGy
        have hroot := heavyPlateCellPairs_subset_root ρ Q j r m (hG hGy).1
        exact (hG hGy).2 (heavyPlateCellPairs_of_points ρ Q j' r' m'
          hroot.1 hroot.2 (hunit p hp) (not_le.mp hmass).le hxfar (hy hGy))
      exact hempty.trans (by simp only [measure_empty]; exact bot_le)
  · have he : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    change ν F ≤ _
    rw [he,measure_empty]
    exact bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlatePairLoss
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial and later product-mass losses for finite plate covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem initial_plate_fiber_bound (ν ρ : Measure (Space d))
    (S : Finset (Space d × ℝ)) (G : Set (Space d × Space d))
    {R τ M : ℝ} {η : ℝ≥0∞} (hν : ν ≤ ρ)
    (hbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M)
    (hsmall : ∀ p ∈ S, ρ {y | |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*R} ≤ η)
    (hcover : G ⊆ ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ R})
    (x : Space d) (hx : ‖x‖ ≤ M) (hgood : x ∉ slabPairException S R τ) :
    ν {y | (x,y) ∈ G} ≤ η := by
  classical
  let F := {y | (x,y) ∈ G}
  by_cases hF : F.Nonempty
  · obtain ⟨y₀,hy₀⟩ := hF
    obtain ⟨p,hp,hxp,_⟩ := mem_iUnion₂.mp (hcover hy₀)
    have hfiber : ∀ᵐ y ∂ν, y ∈ F → |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*R := by
      filter_upwards [hbounded] with y hy hGy
      obtain ⟨q,hq,hxq,hyq⟩ := mem_iUnion₂.mp (hcover hGy)
      exact cluster_outside_slabPairException S hx hgood hp hxp q hq hxq y hy hyq
    exact (measure_mono_ae hfiber).trans ((hν _).trans (hsmall p hp))
  · change ν F ≤ _
    rw [not_nonempty_iff_eq_empty.mp hF,measure_empty]
    exact bot_le

theorem late_plate_pair_mass (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (j j' : ℕ) (S : Finset (Space d × ℝ))
    (G : Set (Space d × Space d)) (hGm : MeasurableSet G)
    {r m r' m' R τ M s C : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hwidth : 2*M*τ+3*R ≤ r') (hsmall : 10*R/τ ≤ 1)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hG : G ⊆ heavyPlateCellPairs ρ Q j r m \ heavyPlateCellPairs ρ Q j' r' m')
    (hcover : heavyPlateCellPairs ρ Q j r m ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ {y | |inner ℝ p.1 y-p.2| ≤ R}) :
    (μ.prod ν) G ≤ (S.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*R/τ)^(s-((d-2:ℕ):ℝ))) + ENNReal.ofReal m' := by
  apply (product_mass_of_exceptional_fibers μ ν G hGm (slabPairException S R τ) (B := ENNReal.ofReal m')
    (measurableSet_slabPairException S R τ) ?_).trans
    (add_le_add (slabPairException_mass μ S hM hC hμbounded hfrost
      hunit hτ hτ1 hR hsmall) le_rfl)
  filter_upwards [hμbounded] with x hx hgood
  exact late_plate_fiber_bound ν ρ Q j j' S G hM hR.le hτ.le hwidth hν hνbounded
    hunit hG hcover x hx hgood

theorem initial_plate_pair_mass (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Finset (Space d × ℝ)) (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    {R τ M s C : ℝ} {η : ℝ≥0∞}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hsmall : 10*R/τ ≤ 1) (hν : ν ≤ ρ)
    (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C) (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hslab : ∀ p ∈ S, ρ {y | |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*R} ≤ η)
    (hcover : G ⊆ ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ R}) :
    (μ.prod ν) G ≤ (S.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*R/τ)^(s-((d-2:ℕ):ℝ))) + η := by
  apply (product_mass_of_exceptional_fibers μ ν G hG (slabPairException S R τ) (B := η)
    (measurableSet_slabPairException S R τ) ?_).trans
    (add_le_add (slabPairException_mass μ S hM hC hμbounded hfrost
      hunit hτ hτ1 hR hsmall) le_rfl)
  filter_upwards [hμbounded] with x hx hgood
  exact initial_plate_fiber_bound ν ρ S G hν hνbounded hslab hcover x hx hgood

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlatePowerBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit power budget for transverse plate intersections -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem plate_intersection_ratio {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    10*(A*δ^(1/4:ℝ))/δ^(1/8:ℝ) = (10*A)*δ^(1/8:ℝ) := by
  have he : (1/4:ℝ) = 1/8+1/8 := by norm_num
  rw [he,Real.rpow_add hδ]
  field_simp

theorem plate_power_identity {δ : ℝ} (hδ : 0 < δ) (A B a q : ℝ) (hA : 0 ≤ A) :
    (A*δ^(-q))^2*(B*(10*(A*δ^(1/4:ℝ))/δ^(1/8:ℝ))^a) =
      (A^2*B*(10*A)^a)*δ^(a/8-2*q) := by
  have hsquare : (δ^(-q))^2 = δ^(-2*q) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    norm_num
    ring
  have hp : (δ^(1/8:ℝ))^a = δ^(a/8) := by
    rw [← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [mul_pow,hsquare,plate_intersection_ratio hδ,
    Real.mul_rpow (mul_nonneg (by norm_num) hA) (Real.rpow_nonneg hδ.le _),hp]
  calc
    _ = (A^2*B*(10*A)^a)*(δ^(-2*q)*δ^(a/8)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hδ]
      congr 2
      ring

theorem plate_card_power_bound {n : ℕ} {δ A B a q : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (hcard : (n:ℝ) ≤ A*δ^(-q)) :
    (n:ℝ≥0∞)^2*ENNReal.ofReal (B*(10*(A*δ^(1/4:ℝ))/δ^(1/8:ℝ))^a) ≤
      ENNReal.ofReal ((A^2*B*(10*A)^a)*δ^(a/8-2*q)) := by
  have hN : 0 ≤ A*δ^(-q) := mul_nonneg hA (Real.rpow_nonneg hδ.le _)
  have hc : (n:ℝ≥0∞) ≤ ENNReal.ofReal (A*δ^(-q)) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard
  apply (mul_le_mul_left (pow_le_pow_left' hc 2) _).trans_eq
  rw [← ENNReal.ofReal_pow hN,← ENNReal.ofReal_mul (sq_nonneg _),
    plate_power_identity hδ A B a q hA]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic number of dyadic tests fits inside the chosen power loss -/

namespace Falconer
open Real Filter
open scoped Topology

theorem dyadic_log_depth (N : ℕ) :
    1-Real.log (1/(2:ℝ)^N)/Real.log 2 = (N:ℝ)+1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [one_div,Real.log_inv,Real.log_pow]
  field_simp
  ring

theorem eventually_dyadic_loss_absorption {ε κ : ℝ} (hεκ : ε < κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ C*(1-Real.log δ/Real.log 2)*δ^(-ε) ≤ δ^(-κ) := by
  have hr : 0 < κ-ε := sub_pos.mpr hεκ
  have hp : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝[>] 0) (𝓝 0) := by
    have hp₀ : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [Real.zero_rpow hr.ne'] using (Real.continuous_rpow_const hr.le).tendsto (0:ℝ)
    exact hp₀.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have ht : Tendsto (fun δ : ℝ => C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div,sub_zero,mul_zero] using (hp.sub (hl.div_const (Real.log 2))).const_mul C
  have hsmall := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hsmall,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hs hδone
  have hδ := hδone.1
  refine ⟨hδ,?_⟩
  calc
    _ = (C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))*δ^(-κ) := by
      calc
        _ = C*(1-Real.log δ/Real.log 2)*δ^((κ-ε)+(-κ)) := by congr 2; ring
        _ = C*(1-Real.log δ/Real.log 2)*(δ^(κ-ε)*δ^(-κ)) := by rw [Real.rpow_add hδ]
        _ = _ := by ring
    _ ≤ 1*δ^(-κ) := mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlateScaleChoices
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform scale choices for the initial block and the later plate losses -/

namespace Falconer
open Filter
open scoped Topology

theorem eventually_plate_geometry (M A : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      10*A*(plateScale j)^(1/8:ℝ) ≤ 1 ∧
      2*M*(plateScale j)^(1/8:ℝ)+3*A*(plateScale j)^(1/4:ℝ) ≤
        plateScale (j/32) := by
  have hs := eventually_const_mul_rpow_lt (by norm_num : (0:ℝ) < 1/8) (10*A)
  have h₁ := eventually_const_mul_rpow_lt (by norm_num : (1/32:ℝ) < 1/8) (4*M)
  have h₂ := eventually_const_mul_rpow_lt (by norm_num : (1/32:ℝ) < 1/4) (6*A)
  filter_upwards [plateScale_tendsto.eventually hs,plateScale_tendsto.eventually h₁,
    plateScale_tendsto.eventually h₂] with j hj h₁j h₂j
  refine ⟨by simpa only [Real.rpow_zero] using hj.2.le,?_⟩
  apply (show 2*M*(plateScale j)^(1/8:ℝ)+3*A*(plateScale j)^(1/4:ℝ) ≤
    (plateScale j)^(1/32:ℝ) from by linarith only [h₁j.2,h₂j.2]).trans
  exact plateScale_div_lower j

theorem eventually_initial_plate_card {b A : ℝ} (hb : 0 < b) (hA : 1 ≤ A) :
    ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      (n:ℝ) ≤ ((63*j:ℕ):ℝ)*A*(plateScale j)^(-64*b) →
      (n:ℝ) ≤ A*(plateScale j)^(-128*b) := by
  have he := eventually_dyadic_loss_absorption
    (show 64*b < 128*b by linarith only [hb]) (63*A)
  filter_upwards [plateScale_tendsto.eventually he] with j hj
  intro n hn
  have hlog : 1-Real.log (plateScale j)/Real.log 2 = (j:ℝ)+1 := by
    rw [plateScale_eq]
    exact dyadic_log_depth j
  rw [hlog] at hj
  have hcoeff : ((63*j:ℕ):ℝ)*A ≤ 63*A*((j:ℝ)+1) := by
    push_cast
    nlinarith only [hA]
  have hbnd : 63*A*((j:ℝ)+1)*(plateScale j)^(-64*b) ≤
      (plateScale j)^(-128*b) := by simpa only [neg_mul] using hj.2
  apply (hn.trans ((mul_le_mul_of_nonneg_right hcoeff
    (Real.rpow_nonneg (plateScale_pos _).le _)).trans hbnd)).trans
  exact le_mul_of_one_le_left (Real.rpow_nonneg (plateScale_pos _).le _) hA

theorem plate_cluster_width_tendsto (M A : ℝ) :
    Tendsto (fun j => 2*M*(plateScale j)^(1/8:ℝ)+3*A*(plateScale j)^(1/4:ℝ))
      atTop (𝓝 (0:ℝ)) := by
  simpa only [mul_zero,zero_add] using
    ((plateScale_power_tendsto (by norm_num : (0:ℝ) < 1/8)).const_mul (2*M)).add
      ((plateScale_power_tendsto (by norm_num : (0:ℝ) < 1/4)).const_mul (3*A))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_UniformVanishingSlabs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform small mass for bounded families of null affine hyperplanes -/

namespace Falconer
open Set Metric MeasureTheory Filter NormedSpace
open scoped ENNReal Topology

private theorem finite_positive_minorant {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ I, 0 < f i) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ I, r ≤ f i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a I ha ih =>
    obtain ⟨r,hr,hrI⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min r (f a),lt_min hr (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hrI i hi)

theorem uniform_bounded_affine_slabs {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {M B : ℝ} (hM : 0 ≤ M)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ, μ {x | inner ℝ w x = a} = 0)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : Space d, ‖w‖ = 1 → ∀ a ∈ Icc (-B) B,
      μ {x | |inner ℝ w x-a| ≤ r} < η := by
  classical
  let K : Set (Space d × ℝ) := sphere 0 1 ×ˢ Icc (-B) B
  have hK : IsCompact K := (isCompact_sphere (0 : Space d) 1).prod isCompact_Icc
  have hsmall : ∀ p : K, ∃ r : ℝ, 0 < r ∧ μ {x | |inner ℝ p.val.1 x-p.val.2| ≤ r} < η := by
    intro p
    apply exists_small_affine_slab μ p.val.1 p.val.2 (hzero p.val.1 ?_ p.val.2) hη
    simpa only [mem_sphere,dist_zero_right] using p.property.1
  choose r hr hsmall using hsmall
  let U : K → Set (Space d × ℝ) := fun p => ball p.val (r p/(2*(M+1)))
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) (by
    intro p hp
    have hrp : 0 < r ⟨p,hp⟩/(2*(M+1)) := div_pos (hr ⟨p,hp⟩) (by positivity)
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self hrp⟩)
  obtain ⟨ρ,hρ,hρI⟩ := finite_positive_minorant I (fun p => r p/2)
    (fun p _ => half_pos (hr p))
  refine ⟨ρ,hρ,?_⟩
  intro w hw a ha
  have hpK : (w,a) ∈ K := ⟨by simpa only [mem_sphere,dist_zero_right] using hw,ha⟩
  obtain ⟨p,hp,hclose⟩ := mem_iUnion₂.mp (hI hpK)
  have hdist : dist (w,a) p.val < r p/(2*(M+1)) := hclose
  have hnear : (M+1)*dist (w,a) p.val ≤ r p/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hdist
    nlinarith only [hh]
  have hmono : ∀ᵐ x ∂μ, x ∈ {x | |inner ℝ w x-a| ≤ ρ} →
      x ∈ {x | |inner ℝ p.val.1 x-p.val.2| ≤ r p} := by
    filter_upwards [hbounded] with x hx
    intro hxr
    have hdiff := affine_slab_parameter_bound (w := p.val.1) (w' := w)
      (a := p.val.2) (a' := a) hx
    have hw' : ‖p.val.1-w‖ ≤ dist (w,a) p.val := by
      calc
        ‖p.val.1-w‖ = dist w p.val.1 := by rw [dist_eq_norm,norm_sub_rev]
        _ ≤ max (dist w p.val.1) (dist a p.val.2) := le_max_left _ _
        _ = dist (w,a) p.val := rfl
    have ha' : |p.val.2-a| ≤ dist (w,a) p.val := by
      simpa only [Prod.dist_eq,Real.dist_eq,abs_sub_comm] using
        (le_max_right (dist w p.val.1) (dist a p.val.2))
    have hdiff' : |(inner ℝ p.val.1 x-p.val.2)-(inner ℝ w x-a)| ≤ r p/2 :=
      hdiff.trans ((add_le_add (mul_le_mul_of_nonneg_left hw' hM) ha').trans
        (by nlinarith only [hnear]))
    have habs : |inner ℝ p.val.1 x-p.val.2| ≤ |inner ℝ w x-a|+
        |(inner ℝ p.val.1 x-p.val.2)-(inner ℝ w x-a)| := by
      calc
        _ = |(inner ℝ w x-a)+((inner ℝ p.val.1 x-p.val.2)-(inner ℝ w x-a))| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    have hrp := hρI p hp
    change |inner ℝ p.val.1 x-p.val.2| ≤ r p
    change |inner ℝ w x-a| ≤ ρ at hxr
    linarith only [habs,hdiff',hxr,hrp]
  exact (measure_mono_ae hmono).trans_lt (hsmall p)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_UniformAffineSlabs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform vanishing over all affine hyperplanes for a bounded measure -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem uniform_affine_slabs {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {M : ℝ} (hM : 0 ≤ M)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ, μ {x | inner ℝ w x = a} = 0)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ,
      μ {x | |inner ℝ w x-a| ≤ r} < η := by
  obtain ⟨ρ,hρ,hsmall⟩ := uniform_bounded_affine_slabs (B := M+1) μ hM hbounded hzero hη
  refine ⟨min ρ 1,lt_min hρ zero_lt_one,min_le_right _ _,?_⟩
  intro w hw a
  by_cases ha : |a| ≤ M+1
  · apply (measure_mono (show {x | |inner ℝ w x-a| ≤ min ρ 1} ⊆
        {x | |inner ℝ w x-a| ≤ ρ} from by
          intro x hx
          exact le_trans (show |inner ℝ w x-a| ≤ min ρ 1 from hx) (min_le_left _ _))).trans_lt
    exact hsmall w hw a (abs_le.mp ha)
  · have hm : μ {x | |inner ℝ w x-a| ≤ min ρ 1} ≤ μ (∅ : Set (Space d)) := by
      apply measure_mono_ae
      filter_upwards [hbounded] with x hx
      intro hxa
      change |inner ℝ w x-a| ≤ min ρ 1 at hxa
      have hi : |inner ℝ w x| ≤ M := by
        have hh := abs_real_inner_le_norm w x
        rw [hw,one_mul] at hh
        exact hh.trans hx
      have habs : |a| ≤ |inner ℝ w x|+|inner ℝ w x-a| := by
        calc
          _ = |inner ℝ w x-(inner ℝ w x-a)| := by congr 1; ring
          _ ≤ _ := abs_sub _ _
      have hr : min ρ 1 ≤ 1 := min_le_right _ _
      exact (ha (by linarith only [hi,habs,hxa,hr])).elim
    exact hm.trans_lt (by simpa only [measure_empty] using hη)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_InitialPlateLoss
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The total initial-block exclusion has arbitrarily small product mass -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem eventually_initial_plate_loss {d : ℕ} (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (E : ℕ → Set (Space d × Space d)) (hE : ∀ j, MeasurableSet (E j))
    (S : ℕ → Finset (Space d × ℝ)) {A b M s C : ℝ}
    (hA : 1 ≤ A) (hb : 0 < b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hgap : 0 < (s-((d-2:ℕ):ℝ))/8-256*b)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hρbounded : ∀ᵐ x ∂ρ, ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ, ρ {x | inner ℝ w x = t} = 0)
    (hunit : ∀ j, ∀ p ∈ S j, ‖p.1‖ = 1)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ A*(plateScale j)^(-b))
    (hcover : ∀ j, E j ⊆ ⋃ p ∈ S j,
      {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)}) :
    ∀ᶠ j₀ : ℕ in atTop,
      (μ.prod ν) (⋃ i ∈ Finset.range (63*j₀), E (j₀+i)) ≤ ENNReal.ofReal (1/4:ℝ) := by
  let B := A^2*(C*(3:ℝ)^s*(4*M+3)^(d-2))*(10*A)^(s-((d-2:ℕ):ℝ))
  obtain ⟨r,hr,_,hslab⟩ := uniform_affine_slabs ρ hM hρbounded hzero
    (show 0 < ENNReal.ofReal (1/8:ℝ) by positivity)
  have hwidth := (plate_cluster_width_tendsto M A).eventually (eventually_lt_nhds hr)
  have ht : Tendsto (fun j => B*(plateScale j)^((s-((d-2:ℕ):ℝ))/8-256*b))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (plateScale_power_tendsto hgap).const_mul B
  have herror := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1/8 by norm_num))
  filter_upwards [eventually_initial_plate_card hb hA,eventually_plate_geometry M A,
    hwidth,herror] with j₀ hjcard hjgeom hjwidth hjerror
  obtain ⟨T,hTunit,hTcard,hTcover⟩ := initial_plate_block_cover E S
    (show 0 ≤ A by linarith only [hA]) hb.le hunit hcard hcover j₀
  have hTc : (T.card:ℝ) ≤ A*(plateScale j₀)^(-(128*b)) := by
    simpa only [neg_mul] using hjcard T.card hTcard
  have hsmall : 10*(A*(plateScale j₀)^(1/4:ℝ))/(plateScale j₀)^(1/8:ℝ) ≤ 1 := by
    simpa only [plate_intersection_ratio (plateScale_pos j₀) A] using hjgeom.1
  have hw : 2*M*(plateScale j₀)^(1/8:ℝ)+3*(A*(plateScale j₀)^(1/4:ℝ)) ≤ r := by
    nlinarith only [hjwidth.le]
  have hinit := initial_plate_pair_mass μ ν ρ T
    (⋃ i ∈ Finset.range (63*j₀), E (j₀+i))
    (Finset.measurableSet_biUnion _ (fun i _ => hE (j₀+i)))
    hM hC (mul_pos (show 0 < A by linarith only [hA])
      (Real.rpow_pos_of_pos (plateScale_pos _) _))
    (Real.rpow_pos_of_pos (plateScale_pos _) _)
    (Real.rpow_le_one (plateScale_pos _).le (plateScale_le_one _) (by norm_num))
    hsmall hν hμbounded hνbounded hfrost hTunit
    (fun p hp => (measure_mono (fun _ hx => hx.trans hw)).trans (hslab p.1 (hTunit p hp) p.2).le)
    hTcover
  have hpower := plate_card_power_bound (plateScale_pos j₀)
    (show 0 ≤ A by linarith only [hA]) hTc
    (B := C*(3:ℝ)^s*(4*M+3)^(d-2)) (a := s-((d-2:ℕ):ℝ))
  have hpower' : (T.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*(A*(plateScale j₀)^(1/4:ℝ))/(plateScale j₀)^(1/8:ℝ))^(s-((d-2:ℕ):ℝ))) ≤
      ENNReal.ofReal (B*(plateScale j₀)^((s-((d-2:ℕ):ℝ))/8-256*b)) := by
    simpa only [show (2:ℝ)*(128*b) = 256*b by ring] using hpower
  have he : ENNReal.ofReal (B*(plateScale j₀)^((s-((d-2:ℕ):ℝ))/8-256*b)) ≤
      ENNReal.ofReal (1/8:ℝ) := ENNReal.ofReal_le_ofReal hjerror.le
  apply hinit.trans ((add_le_add (hpower'.trans he) le_rfl).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FirstExclusionMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Charging each pair only at its first exclusion scale -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_firstExclusion (E : ℕ → Set X)
    (hE : ∀ n, MeasurableSet (E n)) (n : ℕ) : MeasurableSet (firstExclusion E n) :=
  (hE n).diff (Finset.measurableSet_biUnion _ (fun j _ => hE j))

omit [MeasurableSpace X] in
theorem union_exclusion_subset_initial_first (E : ℕ → Set X) (K : ℕ) :
    (⋃ n, E n) ⊆ (⋃ j ∈ Finset.range K, E j) ∪ ⋃ n, firstExclusion E (K+n) := by
  classical
  intro x hx
  have hex : ∃ n, x ∈ E n := mem_iUnion.mp hx
  let N := Nat.find hex
  have hN : x ∈ E N := Nat.find_spec hex
  by_cases hNK : N < K
  · exact Or.inl (mem_iUnion₂.mpr ⟨N,Finset.mem_range.mpr hNK,hN⟩)
  · have hKN : K ≤ N := Nat.le_of_not_gt hNK
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨N-K,?_⟩
    rw [Nat.add_sub_of_le hKN]
    refine ⟨hN,?_⟩
    intro hprev
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hprev
    exact Nat.find_min hex (Finset.mem_range.mp hj) hxj

theorem union_exclusion_mass (μ : Measure X) (E : ℕ → Set X) (K : ℕ)
    {A : ℝ≥0∞} (cost : ℕ → ℝ≥0∞)
    (hinit : μ (⋃ j ∈ Finset.range K, E j) ≤ A)
    (hlate : ∀ n, μ (firstExclusion E (K+n)) ≤ cost n) :
    μ (⋃ n, E n) ≤ A+∑' n, cost n := by
  apply (measure_mono (union_exclusion_subset_initial_first E K)).trans
  apply (measure_union_le _ _).trans
  exact add_le_add hinit ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hlate))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FirstExclusionShift
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Earlier-scale exclusions disappear from every later first-loss set -/

namespace Falconer
open Set MeasureTheory

variable {X : Type*}

theorem firstExclusion_shift_subset (E : ℕ → Set X) (j₀ n m : ℕ)
    (hm₀ : j₀ ≤ m) (hmn : m < j₀+n) :
    firstExclusion (fun i => E (j₀+i)) n ⊆ E (j₀+n) \ E m := by
  intro x hx
  refine ⟨hx.1,?_⟩
  intro hxm
  apply hx.2
  refine mem_iUnion₂.mpr ⟨m-j₀,Finset.mem_range.mpr (by omega),?_⟩
  simpa only [Nat.add_sub_of_le hm₀] using hxm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_LatePlatePowerLoss
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable power bounds for a genuinely new dyadic pair exclusion -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem late_plate_power_loss {d : ℕ} (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (j : ℕ) (S : Finset (Space d × ℝ))
    (G : Set (Space d × Space d)) (hGm : MeasurableSet G)
    {A b M s C : ℝ} (hA : 0 < A) (hb : 0 ≤ b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hwidth : 2*M*(plateScale j)^(1/8:ℝ)+3*(A*(plateScale j)^(1/4:ℝ)) ≤
      plateScale (j/32))
    (hsmall : 10*A*(plateScale j)^(1/8:ℝ) ≤ 1)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hcard : (S.card:ℝ) ≤ A*(plateScale j)^(-b))
    (hG : G ⊆ heavyPlateCellPairs ρ Q j (plateScale j) (2*(plateScale j)^b) \
      heavyPlateCellPairs ρ Q (j/32) (plateScale (j/32)) (2*(plateScale (j/32))^b))
    (hcover : heavyPlateCellPairs ρ Q j (plateScale j) (2*(plateScale j)^b) ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
        {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)}) :
    (μ.prod ν) G ≤
      ENNReal.ofReal ((A^2*(C*(3:ℝ)^s*(4*M+3)^(d-2))*(10*A)^(s-((d-2:ℕ):ℝ)))*
        (plateScale j)^((s-((d-2:ℕ):ℝ))/8-2*b)) +
      ENNReal.ofReal ((2*(2:ℝ)^b)*(plateScale j)^(b/32)) := by
  have hsmall' : 10*(A*(plateScale j)^(1/4:ℝ))/(plateScale j)^(1/8:ℝ) ≤ 1 := by
    simpa only [plate_intersection_ratio (plateScale_pos j) A] using hsmall
  apply (late_plate_pair_mass μ ν ρ Q j (j/32) S G hGm hM hC
    (mul_pos hA (Real.rpow_pos_of_pos (plateScale_pos j) _))
    (Real.rpow_pos_of_pos (plateScale_pos j) _)
    (Real.rpow_le_one (plateScale_pos j).le (plateScale_le_one j) (by norm_num))
    hwidth hsmall' hν hμbounded hνbounded hfrost hunit hG hcover).trans
  apply add_le_add (plate_card_power_bound (plateScale_pos j) hA.le hcard)
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (plateScale_div_power j hb) (by norm_num : (0:ℝ) ≤ 2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlateLossSeries
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable tails of the actual dyadic plate loss bounds -/

namespace Falconer
open Filter
open scoped ENNReal Topology

theorem plateScale_add_power (J n : ℕ) (t : ℝ) :
    (plateScale (J+n))^t = (plateScale J)^t*((2:ℝ)^(-t))^n := by
  simp only [plateScale_rpow,pow_add]

theorem summable_plate_loss (J : ℕ) (B : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n => B*(plateScale (J+n))^t) := by
  have hs := (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-t))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht))).mul_left
      (B*(plateScale J)^t)
  simpa only [plateScale_add_power,mul_assoc] using hs

theorem plate_loss_tsum (J : ℕ) {B t : ℝ} (hB : 0 ≤ B) (ht : 0 < t) :
    (∑' n : ℕ, ENNReal.ofReal (B*(plateScale (J+n))^t)) =
      ENNReal.ofReal (B*(plateScale J)^t/(1-(2:ℝ)^(-t))) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
    mul_nonneg hB (Real.rpow_nonneg (plateScale_pos _).le _)) (summable_plate_loss J B ht)]
  congr 1
  simp_rw [plateScale_add_power,← mul_assoc]
  rw [tsum_mul_left,tsum_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-t))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)),div_eq_mul_inv]

theorem plate_loss_real_tail_tendsto (B : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun J => B*(plateScale J)^t/(1-(2:ℝ)^(-t))) atTop (𝓝 (0:ℝ)) := by
  simpa only [mul_zero,zero_div] using
    ((plateScale_power_tendsto ht).const_mul B).div_const (1-(2:ℝ)^(-t))

theorem eventually_plate_loss_tail {B t η : ℝ} (hB : 0 ≤ B) (ht : 0 < t) (hη : 0 < η) :
    ∀ᶠ J : ℕ in atTop,
      (∑' n : ℕ, ENNReal.ofReal (B*(plateScale (J+n))^t)) < ENNReal.ofReal η := by
  have he := (plate_loss_real_tail_tendsto B ht).eventually (eventually_lt_nhds hη)
  filter_upwards [he] with J hJ
  rw [plate_loss_tsum J hB ht]
  exact ENNReal.ofReal_lt_ofReal_iff hη |>.mpr hJ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_LatePlateTail
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The tail of all first-time plate exclusions has small product mass -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem measurableSet_dyadicPlateExclusions {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (b : ℝ) (j : ℕ) : MeasurableSet (dyadicPlateExclusions ρ Q b j) :=
  measurableSet_heavyPlateCellPairs ρ Q j _ _

theorem eventually_late_plate_tail {d : ℕ} (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (S : ℕ → Finset (Space d × ℝ)) {A b M s C : ℝ}
    (hA : 1 ≤ A) (hb : 0 < b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hgap : 0 < (s-((d-2:ℕ):ℝ))/8-2*b)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hunit : ∀ j, ∀ p ∈ S j, ‖p.1‖ = 1)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ A*(plateScale j)^(-b))
    (hcover : ∀ j, dyadicPlateExclusions ρ Q b j ⊆ ⋃ p ∈ S j,
      {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)}) :
    ∀ᶠ j₀ : ℕ in atTop,
      (∑' n : ℕ, (μ.prod ν)
        (firstExclusion (fun i => dyadicPlateExclusions ρ Q b (j₀+i)) (63*j₀+n))) ≤
        ENNReal.ofReal (1/4:ℝ) := by
  let B := A^2*(C*(3:ℝ)^s*(4*M+3)^(d-2))*(10*A)^(s-((d-2:ℕ):ℝ))
  let L := 2*(2:ℝ)^b
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨Ng,hNg⟩ := eventually_atTop.mp (eventually_plate_geometry M A)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp
    (eventually_plate_loss_tail hB hgap (by norm_num : (0:ℝ) < 1/8))
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp
    (eventually_plate_loss_tail hL (by linarith : 0 < b/32) (by norm_num : (0:ℝ) < 1/8))
  filter_upwards [eventually_ge_atTop (max 1 (max Ng (max N₁ N₂)))] with j₀ hj₀
  have hj₀pos : 0 < j₀ := by omega
  have hcost : ∀ n : ℕ, (μ.prod ν)
      (firstExclusion (fun i => dyadicPlateExclusions ρ Q b (j₀+i)) (63*j₀+n)) ≤
      ENNReal.ofReal (B*(plateScale (64*j₀+n))^((s-((d-2:ℕ):ℝ))/8-2*b)) +
      ENNReal.ofReal (L*(plateScale (64*j₀+n))^(b/32)) := by
    intro n
    let j := 64*j₀+n
    have hj : j₀+(63*j₀+n) = j := by dsimp [j]; omega
    have hgj := hNg j (by dsimp [j]; omega)
    have hs := firstExclusion_shift_subset (dyadicPlateExclusions ρ Q b)
      j₀ (63*j₀+n) (j/32) (by dsimp [j]; omega) (by dsimp [j]; omega)
    rw [hj] at hs
    have hh := late_plate_power_loss μ ν ρ Q j (S j)
      (firstExclusion (fun i => dyadicPlateExclusions ρ Q b (j₀+i)) (63*j₀+n))
      (measurableSet_firstExclusion _ (fun i => measurableSet_dyadicPlateExclusions ρ Q b _) _)
      (show 0 < A by linarith only [hA]) hb.le hM hC
      (by simpa only [mul_assoc] using hgj.2) hgj.1 hν hμbounded hνbounded hfrost
      (hunit j) (hcard j) hs (hcover j)
    exact hh
  apply (ENNReal.tsum_le_tsum hcost).trans
  rw [ENNReal.tsum_add]
  apply (add_le_add (hN₁ (64*j₀) (by omega)).le (hN₂ (64*j₀) (by omega)).le).trans_eq
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlatePositive
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive limiting mass of the actual coarse dyadic plate filter -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem coarse_plate_positive_limit (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d))
    (Q : DyadicCube d) (hQ : 0 < Q.side) {M s C : ℝ}
    (hM : 0 ≤ M) (hroot : ∀ x ∈ Q.carrier, ‖x‖ ≤ M)
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C)
    (hμroot : (μ : Measure (Space d)) Q.carrier = 1)
    (hνroot : (ν : Measure (Space d)) Q.carrier = 1)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
      ((μ : Measure (Space d))+(ν : Measure (Space d))) {x | inner ℝ w x = t} = 0) :
    ∃ j₀ : ℕ, 0 < ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
      (⋂ J : ℕ, coarsePlateFilter ((μ : Measure (Space d))+(ν : Measure (Space d)))
        Q j₀ J plateScale (fun j => 2*(plateScale j)^(heavyPlateExponent (s-((d-2:ℕ):ℝ))))) := by
  classical
  let ρ := (μ : Measure (Space d))+(ν : Measure (Space d))
  let b := heavyPlateExponent (s-((d-2:ℕ):ℝ))
  let E := dyadicPlateExclusions ρ Q b
  obtain ⟨A,hA,hS⟩ := dyadic_heavy_plate_covers hpublished hd μ ν Q hQ hM hroot
    hs hs' hC hμbounded hνbounded hμfrost hνfrost
  choose S hunit hcard hcover using hS
  have hνle : (ν : Measure (Space d)) ≤ ρ := by
    intro t
    change (ν : Measure (Space d)) t ≤ (μ : Measure (Space d)) t+(ν : Measure (Space d)) t
    exact le_add_left le_rfl
  have hρbounded : ∀ᵐ x ∂ρ, ‖x‖ ≤ M := ae_add_measure_iff.mpr ⟨hμbounded,hνbounded⟩
  have ha : 0 < s-((d-2:ℕ):ℝ) := by linarith only [hs]
  obtain ⟨hb,hgap,hgap'⟩ := plate_exponent_gaps ha
  have ha16 : 0 < (s-((d-2:ℕ):ℝ))/16 := by positivity
  have hinit := eventually_initial_plate_loss (μ : Measure (Space d)) (ν : Measure (Space d)) ρ
    E (fun j => measurableSet_dyadicPlateExclusions ρ Q b j) S hA hb hM hC
    (ha16.trans hgap') hνle hμbounded hνbounded hρbounded hμfrost hzero hunit hcard hcover
  have hlate := eventually_late_plate_tail (μ : Measure (Space d)) (ν : Measure (Space d)) ρ
    Q S hA hb hM hC (ha16.trans hgap) hνle hμbounded hνbounded hμfrost hunit hcard hcover
  obtain ⟨j₀,hi,hl⟩ := (hinit.and hlate).exists
  have hu := union_exclusion_mass ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
    (fun i => E (j₀+i)) (63*j₀)
    (fun n => ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
      (firstExclusion (fun i => E (j₀+i)) (63*j₀+n))) hi (fun _ => le_rfl)
  have hu' : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋃ i : ℕ, E (j₀+i)) ≤
      ENNReal.ofReal (1/2:ℝ) := by
    apply hu.trans ((add_le_add le_rfl hl).trans_eq ?_)
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  refine ⟨j₀,coarsePlateFilter_limit_pos _ ρ Q j₀ plateScale (fun j => 2*(plateScale j)^b) ?_ ?_⟩
  · rw [Measure.prod_prod,hμroot,hνroot,one_mul]
  · exact hu'.trans_lt (by norm_num)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateSymmetry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original coarse exclusions are symmetric in their two endpoints -/

namespace Falconer
open Set MeasureTheory

theorem heavyPlateCellPairs_swap {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j : ℕ) (r m : ℝ) {x y : Space d}
    (h : (x,y) ∈ heavyPlateCellPairs ρ Q j r m) :
    (y,x) ∈ heavyPlateCellPairs ρ Q j r m := by
  obtain ⟨p,hp,q,hq,⟨w,hw,t,hm,hp',hq'⟩,hx,hy⟩ :=
    (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mp h
  exact (mem_heavyPlateCellPairs_iff ρ Q j r m y x).mpr
    ⟨q,hq,p,hp,⟨w,hw,t,hm,hq',hp'⟩,hy,hx⟩

theorem coarsePlateFilter_swap {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ) {x y : Space d}
    (h : (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m) :
    (y,x) ∈ coarsePlateFilter ρ Q j₀ J r m := by
  refine ⟨⟨h.1.2,h.1.1⟩,?_⟩
  intro hex
  obtain ⟨j,hj,hxy⟩ := mem_iUnion₂.mp hex
  exact h.2 (mem_iUnion₂.mpr ⟨j,hj,heavyPlateCellPairs_swap ρ Q j (r j) (m j) hxy⟩)

theorem coarsePlateFilter_swap_iff {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ) (x y : Space d) :
    (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m ↔
      (y,x) ∈ coarsePlateFilter ρ Q j₀ J r m :=
  ⟨coarsePlateFilter_swap ρ Q j₀ J r m,coarsePlateFilter_swap ρ Q j₀ J r m⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlatePreparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse heavy-plate preparation with positive mass and both directional bounds -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem coarse_plate_preparation (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d))
    (Q : DyadicCube d) (hQ : 0 < Q.side) {M s C : ℝ}
    (hM : 0 ≤ M) (hroot : ∀ x ∈ Q.carrier, ‖x‖ ≤ M)
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C)
    (hμroot : (μ : Measure (Space d)) Q.carrier = 1)
    (hνroot : (ν : Measure (Space d)) Q.carrier = 1)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
      ((μ : Measure (Space d))+(ν : Measure (Space d))) {x | inner ℝ w x = t} = 0)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ (Γ : ℕ → Set (Space d × Space d)) (K ζ : ℝ), 0 < K ∧ 0 < ζ ∧
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N : ℕ, ∃ T : Finset (List (Fin d → Bool) × List (Fin d → Bool)),
        T ⊆ (cubePaths d ⌊ω*(N:ℝ)⌋₊).product (cubePaths d ⌊ω*(N:ℝ)⌋₊) ∧
        Γ N = ⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier) ∧
      ∀ N : ℕ, ∀ x w : Space d, ‖w‖ = 1 → ∀ r : ℝ,
        1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (ν : Measure (Space d)) {y | (x,y) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
          ENNReal.ofReal (K*r^ζ) ∧
        (μ : Measure (Space d)) {y | (y,x) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
          ENNReal.ofReal (K*r^ζ) := by
  obtain ⟨j₀,hpositive⟩ := coarse_plate_positive_limit hpublished hd μ ν Q hQ hM hroot
    hs hs' hC hμbounded hνbounded hμfrost hνfrost hμroot hνroot hzero
  let ρ := (μ : Measure (Space d))+(ν : Measure (Space d))
  let b := heavyPlateExponent (s-((d-2:ℕ):ℝ))
  let Γ := fun N : ℕ => coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale (fun j => 2*(plateScale j)^b)
  have hb : 0 < b := heavyPlateExponent_pos (by linarith only [hs])
  have hμle : (μ : Measure (Space d)) ≤ ρ := by
    intro t
    change (μ : Measure (Space d)) t ≤ (μ : Measure (Space d)) t+(ν : Measure (Space d)) t
    exact le_add_right le_rfl
  have hνle : (ν : Measure (Space d)) ≤ ρ := by
    intro t
    change (ν : Measure (Space d)) t ≤ (μ : Measure (Space d)) t+(ν : Measure (Space d)) t
    exact le_add_left le_rfl
  refine ⟨Γ,coarseDirectionalConstant Q j₀ b,ω*b,coarseDirectionalConstant_pos Q j₀ b,
    mul_pos hω hb,?_,?_,?_,?_,?_⟩
  · intro N
    exact measurableSet_coarsePlateFilter ρ Q j₀ _ _ _
  · intro N N' hNN'
    exact coarsePlateFilter_antitone ρ Q j₀ _ _ (Nat.floor_mono
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hNN') hω.le))
  · apply hpositive.trans_le
    apply measure_mono
    intro xy hxy
    exact mem_iInter.mpr (fun N => mem_iInter.mp hxy ⌊ω*(N:ℝ)⌋₊)
  · intro N
    exact coarsePlateFilter_product_cells ρ Q j₀ _ _ _
  · intro N x w hw r hr hr1
    have hr' : plateScale N ≤ r := by simpa only [plateScale_eq] using hr
    constructor
    · exact coarse_filter_directional_bound (ν : Measure (Space d)) ρ Q hQ.le j₀ N
        hb.le hω.le hω1 hνle x w hw hr' hr1
    · have he : {y | (y,x) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} =
          {y | (x,y) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} := by
        ext y
        exact and_congr (coarsePlateFilter_swap_iff ρ Q j₀ _ _ _ y x) Iff.rfl
      rw [he]
      exact coarse_filter_directional_bound (μ : Measure (Space d)) ρ Q hQ.le j₀ N
        hb.le hω.le hω1 hμle x w hw hr' hr1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialScaleWindow
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative estimates on the retained interval of dyadic scales -/

namespace Falconer
open scoped BigOperators ENNReal

lemma radial_scale_window_half {K N : ℕ} (hK : 0 < K) (hN : 2*K ≤ N) :
    N ≤ 2*K*(N/K) := by
  have hq : 2 ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by omega)
  have hr := Nat.mod_lt N hK
  have he := Nat.div_add_mod N K
  nlinarith

lemma radial_scale_window_loss {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^N)^(a/(2*(K:ℝ))) ≤ ((2:ℝ)^j)^a := by
  have he : (N:ℝ) ≤ 2*(K:ℝ)*(j:ℝ) := by
    exact_mod_cast (radial_scale_window_half hK hN).trans (Nat.mul_le_mul_left (2*K) hj)
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ) < 2*K)).mp
  have hh := mul_le_mul_of_nonneg_right he ha
  calc
    (2*K)*((N:ℝ)*(a/(2*(K:ℝ)))) = (N:ℝ)*a := by field_simp
    _ ≤ (2*(K:ℝ)*(j:ℝ))*a := hh
    _ = (2*K)*((j:ℝ)*a) := by ring

lemma radial_scale_window_decay {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^j)^(-a) ≤ ((2:ℝ)^N)^(-(a/(2*(K:ℝ)))) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact inv_anti₀ (by positivity) (radial_scale_window_loss hK hN hj ha)

theorem radial_scale_window_cost (K : ℕ) (hK : 0 < K) {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∑ j ∈ Finset.Icc (N/K) N, ENNReal.ofReal (((2:ℝ)^j)^(-a))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  let c : ℝ := a/(4*(K:ℝ))
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Np,hp⟩ := PlanarFalconer.fixed_polynomial_subpower 1 hc
  refine ⟨c,hc,2*K+Np,?_⟩
  intro N hN
  have hhalf : 2*K ≤ N := by omega
  have hpoly : (N:ℝ)+1 ≤ ((2:ℝ)^N)^c := by
    apply le_trans _ (hp N (by omega))
    simp only [pow_one]
    linarith [show (0:ℝ) ≤ N by positivity]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (N/K) N,
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal (radial_scale_window_decay hK hhalf
        (Finset.mem_Icc.mp hj).1 ha.le)
    _ = ((Finset.Icc (N/K) N).card:ℝ≥0∞)*
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by simp
    _ ≤ ((N:ℝ≥0∞)+1)*ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      gcongr
      exact_mod_cast (show (Finset.Icc (N/K) N).card ≤ N+1 by simp)
    _ = ENNReal.ofReal (((N:ℝ)+1)*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    _ ≤ ENNReal.ofReal (((2:ℝ)^N)^c*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpoly (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      congr 2
      dsimp [c]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RelativeScaleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform constant absorption when passing from the full to the middle scale -/

namespace Falconer

theorem dyadic_relative_scale_bound (N k : ℕ) {α β : ℝ}
    (h : (N:ℝ)*α ≤ (k:ℝ)*β) : ((2:ℝ)^N)^α ≤ ((2:ℝ)^k)^β := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_DyadicWindowInterpolation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From a window of improved dyadic caps to every radius -/

namespace Falconer
open scoped ENNReal

theorem dyadic_window_interpolation (f : ℝ → ℝ≥0∞) (hf : Monotone f)
    (hmass : ∀ r : ℝ, f r ≤ 1) {N m : ℕ} (_hmN : m ≤ N)
    {e q v : ℝ} (hq : 0 ≤ q) (hqv : q ≤ v)
    (hcoarse : (m:ℝ)*q ≤ (N:ℝ)*e)
    (hconstant : (2:ℝ)^v ≤ ((2:ℝ)^N)^e)
    (hdyadic : ∀ j : ℕ, m ≤ j → j ≤ N → f (1/(2:ℝ)^j) ≤
      ENNReal.ofReal ((1/(2:ℝ)^j)^v))
    {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
    f r ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hc : 1/(2:ℝ)^m ≤ r
  · apply (hmass r).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hp := dyadic_relative_scale_bound m N hcoarse
    have hi : ((2:ℝ)^m)^q*(1/(2:ℝ)^m)^q = 1 := by
      rw [one_div,Real.inv_rpow (by positivity)]
      exact mul_inv_cancel₀ (by positivity)
    calc
      1 = ((2:ℝ)^m)^q*(1/(2:ℝ)^m)^q := hi.symm
      _ ≤ ((2:ℝ)^N)^e*r^q := mul_le_mul hp
        (Real.rpow_le_rpow (by positivity) hc hq) (by positivity) (by positivity)
  · obtain ⟨j,hj,hrj,hjr⟩ := Regularization.dyadic_radius_bracket hr hr1
    have hmj : m ≤ j := by
      by_contra hn
      have hjm : j+1 ≤ m := by omega
      have hd : 1/(2:ℝ)^m ≤ 1/(2:ℝ)^(j+1) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hjm)
      have he : 1/(2:ℝ)^j = 2*(1/(2:ℝ)^(j+1)) := by rw [pow_succ]; field_simp
      have hh : 1/(2:ℝ)^(j+1) ≤ r := by rw [he] at hjr; linarith only [hjr]
      exact hc (hd.trans hh)
    apply ((hf hrj).trans (hdyadic j hmj hj)).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ (2*r)^v := Real.rpow_le_rpow (by positivity) hjr (hq.trans hqv)
      _ = (2:ℝ)^v*r^v := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ ((2:ℝ)^N)^e*r^q := mul_le_mul hconstant
        (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hqv) (by positivity) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialWindowAvailability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning the improved scale window into the manuscript's radial cap bound -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem exists_radial_window_denominator {e q : ℝ} (he : 0 < e) (hq : 0 ≤ q) :
    ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, ((N/K:ℕ):ℝ)*q ≤ (N:ℝ)*e := by
  obtain ⟨K,hK⟩ := exists_nat_gt (q/e)
  have hKe : q < (K:ℝ)*e := (div_lt_iff₀ he).mp hK
  have hKpos : 0 < K := by
    have hh : (0:ℝ) < K := lt_of_le_of_lt (div_nonneg hq he.le) hK
    exact_mod_cast hh
  refine ⟨K,hKpos,fun N => ?_⟩
  have hKr : (0:ℝ) < K := by exact_mod_cast hKpos
  calc
    _ ≤ ((N:ℝ)/(K:ℝ))*q := mul_le_mul_of_nonneg_right Nat.cast_div_le hq
    _ ≤ ((N:ℝ)/(K:ℝ))*((K:ℝ)*e) := mul_le_mul_of_nonneg_left hKe.le (by positivity)
    _ = _ := by field_simp

theorem radialCapBound_of_window {d N m : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (G : Set (Space d × Space d))
    (hmN : m ≤ N) {e q v : ℝ} (hq : 0 ≤ q) (hqv : q ≤ v)
    (hcoarse : (m:ℝ)*q ≤ (N:ℝ)*e)
    (hconstant : (2:ℝ)^v ≤ ((2:ℝ)^N)^e)
    (hdyadic : ∀ j : ℕ, m ≤ j → j ≤ N →
      (∀ x u : Space d, (μ : Measure (Space d))
        {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^j)^v)) ∧
      (∀ z u : Space d, (ν : Measure (Space d))
        {x | (z,x) ∈ G ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^j)^v))) : RadialCapBound μ ν G N e q := by
  have hμ (x w : Space d) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      (μ : Measure (Space d)) {z | (z,x) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
    apply dyadic_window_interpolation
      (fun r => (μ : Measure (Space d)) {z | (z,x) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r})
      (fun _ _ hrs => measure_mono (fun _ hz => ⟨hz.1,hz.2.trans hrs⟩))
      (fun r => (measure_mono (subset_univ _)).trans_eq (measure_univ)) hmN hq hqv hcoarse hconstant
      (fun j hj hjN => (hdyadic j hj hjN).1 x w) hr hr1
  have hν (z w : Space d) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      (ν : Measure (Space d)) {x | (z,x) ∈ G ∧ ‖normalize (x-z)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
    apply dyadic_window_interpolation
      (fun r => (ν : Measure (Space d)) {x | (z,x) ∈ G ∧ ‖normalize (x-z)-w‖ ≤ r})
      (fun _ _ hrs => measure_mono (fun _ hz => ⟨hz.1,hz.2.trans hrs⟩))
      (fun r => (measure_mono (subset_univ _)).trans_eq (measure_univ)) hmN hq hqv hcoarse hconstant
      (fun j hj hjN => (hdyadic j hj hjN).2 z w) hr hr1
  constructor
  · intro x _ w _ r hr hr1
    change (ν : Measure (Space d)) {y | (x,y) ∈ G ∧ ‖normalize (y-x)-w‖ < r} ≤ _
    apply le_trans _ (hν x w (by simpa only [one_div] using hr) hr1)
    exact measure_mono (fun _ hz => ⟨hz.1,hz.2.le⟩)
  · intro y _ w _ r hr hr1
    change (μ : Measure (Space d)) {x | (x,y) ∈ G ∧ ‖normalize (x-y)-w‖ < r} ≤ _
    apply le_trans _ (hμ y w (by simpa only [one_div] using hr) hr1)
    exact measure_mono (fun _ hz => ⟨hz.1,hz.2.le⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ReverseCapsAllRadii
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reverse-cap bounds under source restriction at every original radius -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_caps_all_radii (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N v : ℕ} (hvN : v ≤ N) {K K' q : ℝ} (hK : K ≤ K')
    (hcap : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ᵐ z ∂ρ, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K'*r^q) := by
  filter_upwards [hρ.ae_le hcap] with z hz
  intro r hr hr1 u hu
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have hm : ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hm.trans ((hz r (hδ.trans hr) hr1 u hu).trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr) _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RelativePairCore
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discarding null source and pin sets relative to the incoming relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem relative_pruning_cost_trans {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (G H K : Set X) {a b : ℝ≥0∞} (hGH : μ (G \ H) ≤ a) (hHK : μ (H \ K) ≤ b) :
    μ (G \ K) ≤ a+b := by
  have hsub : G \ K ⊆ (G \ H) ∪ (H \ K) := by
    intro x hx
    by_cases hh : x ∈ H
    · exact Or.inr ⟨hh,hx.2⟩
    · exact Or.inl ⟨hx.1,hh⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hGH hHK))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TwoSidedRadialIntersection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the two original orientations without normalizing pair fibers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem intersect_radial_orientations (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G H K : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hH : MeasurableSet H) (hK : MeasurableSet K)
    (hHG : H ⊆ G) (_hKG : K ⊆ Prod.swap ⁻¹' G)
    {a b C r : ℝ≥0∞} {δ : ℝ}
    (hHcost : (μ.prod ν) (G \ H) ≤ a)
    (hKcost : (ν.prod μ) ((Prod.swap ⁻¹' G) \ K) ≤ b)
    (hHcap : ∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ δ} ≤ C)
    (hKcap : ∀ z u : Space d, ν {x | (x,z) ∈ K ∧ ‖normalize (x-z)-u‖ ≤ δ} ≤ r) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ a+b ∧
      (∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ δ} ≤ C) ∧
      (∀ z u : Space d, ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ δ} ≤ r) := by
  let G' := H ∩ (Prod.swap ⁻¹' K)
  refine ⟨G',hH.inter (hK.preimage measurable_swap),fun z hz => hHG hz.1,?_,?_,?_⟩
  · have hsub : G \ G' ⊆ (G \ H) ∪ (Prod.swap ⁻¹' ((Prod.swap ⁻¹' G) \ K)) := by
      intro z hz
      by_cases hh : z ∈ H
      · right
        exact ⟨hz.1,fun hk => hz.2 ⟨hh,hk⟩⟩
      · exact Or.inl ⟨hz.1,hh⟩
    apply (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    apply add_le_add hHcost
    rw [← Measure.map_apply measurable_swap ((hG.preimage measurable_swap).diff hK),Measure.prod_swap]
    exact hKcost
  · intro x u
    apply le_trans _ (hHcap x u)
    exact measure_mono (fun _ hz => ⟨hz.1.1,hz.2⟩)
  · intro z u
    apply le_trans _ (hKcap z u)
    exact measure_mono (fun _ hz => ⟨hz.1.2,hz.2⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointTwoSidedScale
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both orientations of the endpoint one-scale preparation estimate -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_two_sided_one_scale (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {α t q ζ C D s : ℝ}
    (hq : q = (h:ℝ)+1) (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+3)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+3:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 → ν Q.carrierᶜ = 0 →
        (∀ y : Space (h+3), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space (h+3), ∀ r > 0, ν (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+3)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+3) × Space (h+3)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+3), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
        (∀ᵐ z ∂μ, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
          1/(2:ℝ)^N ≤ r → r ≤ 1 →
            ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+3), ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
        (∀ᵐ x ∂ν, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
          1/(2:ℝ)^N ≤ r → r ≤ 1 →
            μ {z | (z,x) ∈ G ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        (∀ x u : Space (h+3), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c))) ∧
        (∀ z u : Space (h+3), ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c))) := by
  obtain ⟨ε,c,hε,hc,N₀,hscale⟩ := endpoint_one_scale_gain hLW hq ht ht' hζ htα hC
    Q hQ hD hDdim hs
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hslab hcap' hslab'
  obtain ⟨H,hH,hHG,hHcost,hHcap⟩ := hscale N hN μ ν hμroot hμfrost A P hA hP hμA hνP
    hsep (fun y hy x hx => hpin y hy x (Or.inr hx)) G hG hcap hslab
  obtain ⟨K,hK,hKG,hKcost,hKcap⟩ := hscale N hN ν μ hνroot hνfrost P A hP hA hνP hμA
    (fun x hx z hz => by simpa only [norm_sub_rev] using hsep z hz x hx)
    (fun y hy x hx => hpin y hy x (Or.inl hx)) (Prod.swap ⁻¹' G) (hG.preimage measurable_swap)
    (by simpa only [mem_preimage,Prod.swap_prod_mk] using hcap')
    (by simpa only [mem_preimage,Prod.swap_prod_mk] using hslab')
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := intersect_radial_orientations μ ν G H K hG hH hK hHG hKG
    hHcost hKcost hHcap hKcap
  refine ⟨G',hG',hsub,?_,hcaps⟩
  simpa only [two_mul] using hdel

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_FiniteRadialRefinement
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intersecting finitely many two-sided radial refinements -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem finite_radial_refinement (μ ν : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (I : Finset ℕ) (cost bound : ℕ → ℝ≥0∞) (radius : ℕ → ℝ)
    (hlocal : ∀ j ∈ I, ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost j ∧
      (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
      (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j)) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ ∑ j ∈ I, cost j ∧
      ∀ j ∈ I,
        (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
        (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j) := by
  classical
  have hex : ∀ j : ℕ, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (j ∈ I → H ⊆ G ∧ (μ.prod ν) (G \ H) ≤ cost j ∧
        (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
        (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j)) := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨H,hH,hsub,hd,hc⟩ := hlocal j hj
      exact ⟨H,hH,fun _ => ⟨hsub,hd,hc⟩⟩
    · exact ⟨G,hG,fun h => (hj h).elim⟩
  choose H hH hrest using hex
  let B := ⋃ j ∈ I, G \ H j
  let K := G \ B
  have hK : MeasurableSet K := hG.diff (Finset.measurableSet_biUnion I (fun j _ => hG.diff (hH j)))
  have hsub (j : ℕ) (hj : j ∈ I) : K ⊆ H j := by
    intro z hz
    by_contra hn
    exact hz.2 (mem_iUnion₂.mpr ⟨j,hj,hz.1,hn⟩)
  refine ⟨K,hK,sdiff_subset,?_,?_⟩
  · have hdiff : G \ K ⊆ B := by
      intro z hz
      by_contra hn
      exact hz.2 ⟨hz.1,hn⟩
    exact (measure_mono hdiff).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum (fun j hj => (hrest j hj).2.1)))
  · intro j hj
    refine ⟨?_,?_⟩
    · intro x u
      apply le_trans _ ((hrest j hj).2.2.1 x u)
      exact measure_mono (fun _ hz => ⟨hsub j hj hz.1,hz.2⟩)
    · intro z u
      apply le_trans _ ((hrest j hj).2.2.2 z u)
      exact measure_mono (fun _ hz => ⟨hsub j hj hz.1,hz.2⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ReverseSlabsAllRadii
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original all-radius slab bounds under restriction of a pair relation -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_slabs_all_radii (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N v : ℕ} (hvN : v ≤ N) {K K' ζ : ℝ} (hK : K ≤ K')
    (hslab : ∀ᵐ z ∂μ, ∀ u : Space d, ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤ ENNReal.ofReal (K*r^ζ)) :
    ∀ᵐ z ∂ρ, ∀ u : Space d, ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^v ≤ r → r ≤ 1 →
        ν {x | (z,x) ∈ G' ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤ ENNReal.ofReal (K'*r^ζ) := by
  filter_upwards [hρ.ae_le hslab] with z hz
  intro u hu r hr hr1
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have hm : ν {x | (z,x) ∈ G' ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
      ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hm.trans ((hz u hu r (hδ.trans hr) hr1).trans ?_)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK
    (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr) _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_EndpointScaleWindow
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same original pair set can be improved throughout a dyadic scale window -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators

theorem endpoint_scale_window_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {α t q ζ C D s : ℝ}
    (hq : q = (h:ℝ)+1) (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+3)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+3:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧ ∀ K : ℕ, 0 < K →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 → ν Q.carrierᶜ = 0 →
        (∀ y : Space (h+3), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space (h+3), ∀ r > 0, ν (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+3)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+3) × Space (h+3)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+3), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q)) →
        (∀ᵐ z ∂μ, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
          1/(2:ℝ)^N ≤ r → r ≤ 1 →
            ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^ζ)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+3), ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q)) →
        (∀ᵐ x ∂ν, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
          1/(2:ℝ)^N ≤ r → r ≤ 1 →
            μ {z | (z,x) ∈ G ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^ζ)) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ j : ℕ, N/K ≤ j → j ≤ N →
          (∀ x u : Space (h+3), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) ∧
          (∀ z u : Space (h+3), ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) := by
  obtain ⟨ε,gain,hε,hgain,Ns,hscale⟩ := endpoint_two_sided_one_scale hLW hq ht ht' hζ
    htα hC Q hQ hD hDdim hs
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro K hK
  obtain ⟨c,hc,Nc,hcost⟩ := radial_scale_window_cost K hK hgain
  refine ⟨c,hc,max (K*Ns) (max (2*K) Nc),?_⟩
  intro N hN μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hslab hcap' hslab'
  simp only [max_le_iff] at hN
  obtain ⟨hNs,hNK,hNc⟩ := hN
  have hstart : Ns ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by simpa only [Nat.mul_comm] using hNs)
  have hcapSwap : ∀ᵐ z ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+3), ‖u‖ = 1 →
        μ {x | (z,x) ∈ Prod.swap ⁻¹' G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    simpa only [mem_preimage,Prod.swap_prod_mk] using hcap'
  have hslabSwap : ∀ᵐ z ∂ν, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^N ≤ r → r ≤ 1 →
        μ {x | (z,x) ∈ Prod.swap ⁻¹' G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^ζ) := by
    simpa only [mem_preimage,Prod.swap_prod_mk] using hslab'
  obtain ⟨H,hH,hsub,hdel,hbounds⟩ := finite_radial_refinement μ ν G hG (Finset.Icc (N/K) N)
    (fun j => 2*ENNReal.ofReal (((2:ℝ)^j)^(-gain)))
    (fun j => ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) (fun j => 1/(2:ℝ)^j) (by
      intro j hj
      obtain ⟨hjlo,hjhi⟩ := Finset.mem_Icc.mp hj
      have hloss := radial_scale_window_loss hK hNK hjlo hε.le
      have hc₁ := reverse_caps_all_radii μ μ ν Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := G)) hjhi hloss hcap
      have hc₂ := reverse_caps_all_radii ν ν μ Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := Prod.swap ⁻¹' G)) hjhi hloss hcapSwap
      have hs₁ := reverse_slabs_all_radii μ μ ν Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := G)) hjhi hloss hslab
      have hs₂ := reverse_slabs_all_radii ν ν μ Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := Prod.swap ⁻¹' G)) hjhi hloss hslabSwap
      obtain ⟨H,hH,hsub,hdel,hbounds⟩ := hscale j (hstart.trans hjlo) μ ν
        hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hc₁ hs₁
        (by simpa only [mem_preimage,Prod.swap_prod_mk] using hc₂)
        (by simpa only [mem_preimage,Prod.swap_prod_mk] using hs₂)
      refine ⟨H,hH,hsub,hdel,?_⟩
      have he : ((2:ℝ)^j)^(-q-gain) = (1/(2:ℝ)^j)^(q+gain) := by
        rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
        congr 1
        ring
      simpa only [he] using hbounds)
  refine ⟨H,hH,hsub,?_,fun j hjlo hjhi => hbounds j (Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩)⟩
  apply hdel.trans
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (hcost N hNc)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointAvailabilityGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict improvement of the actual available radial exponent -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem CapAvailable.endpoint_improve (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {α t q ζ C D s Cplate : ℝ}
    (hq : q = (h:ℝ)+1) (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+3)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+3:ℕ) ≤ D) (hs : 0 < s)
    (μ ν : ProbabilityMeasure (Space (h+3)))
    (hμroot : (μ : Measure (Space (h+3))) Q.carrierᶜ = 0)
    (hνroot : (ν : Measure (Space (h+3))) Q.carrierᶜ = 0)
    (hμfrost : ∀ y : Space (h+3), ∀ r > 0, (μ : Measure (Space (h+3))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (hνfrost : ∀ y : Space (h+3), ∀ r > 0, (ν : Measure (Space (h+3))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (A P : Set (Space (h+3))) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hμA : (μ : Measure (Space (h+3))) Aᶜ = 0) (hνP : (ν : Measure (Space (h+3))) Pᶜ = 0)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (hpin : ∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D)
    (Γ : ℕ → Set (Space (h+3) × Space (h+3))) (hΓ : ∀ N, MeasurableSet (Γ N))
    (hslab : ∀ N : ℕ, ∀ᵐ z ∂(μ : Measure (Space (h+3))),
      ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (ν : Measure (Space (h+3))) {x | (z,x) ∈ Γ N ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
          ENNReal.ofReal (Cplate*r^ζ))
    (hslab' : ∀ N : ℕ, ∀ᵐ x ∂(ν : Measure (Space (h+3))),
      ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (μ : Measure (Space (h+3))) {z | (z,x) ∈ Γ N ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
          ENNReal.ofReal (Cplate*r^ζ))
    (havailable : CapAvailable μ ν Γ q) :
    ∃ q' : ℝ, q < q' ∧ CapAvailable μ ν Γ q' := by
  obtain ⟨ε,gain,hε,hgain,hwindow⟩ := Regularization.endpoint_scale_window_gain
    hLW hq ht ht' hζ htα hC Q hQ hD hDdim hs
  refine ⟨q+gain,by linarith only [hgain],?_⟩
  intro e he
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  obtain ⟨K,hK,hcoarse⟩ := exists_radial_window_denominator he (by positivity : 0 ≤ q+gain)
  obtain ⟨c,hc,Nw,hNw⟩ := hwindow K hK
  have hin : 0 < ε/(2*(K:ℝ)) := by positivity
  obtain ⟨Np,hNp⟩ := Regularization.fixed_constant_absorbed hin Cplate
  obtain ⟨c₀,C₀,hc₀,hC₀,Na,hNa⟩ := havailable (ε/(2*(K:ℝ))) hin
  obtain ⟨Nb,hNb⟩ := Regularization.fixed_constant_absorbed he ((2:ℝ)^(q+gain))
  refine ⟨min c₀ c,C₀+2,lt_min hc₀ hc,by positivity,max Np (max Na (max Nw Nb)),?_⟩
  intro N hN
  simp only [max_le_iff] at hN
  obtain ⟨hNp',hNa',hNw',hNb'⟩ := hN
  obtain ⟨B,hB,hBΓ,hBcost,hcaps⟩ := hNa N hNa'
  let G := Γ N \ B
  have hG : MeasurableSet G := (hΓ N).diff hB
  have hcap₁ : ∀ᵐ z ∂(μ : Measure (Space (h+3))), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+3), ‖u‖ = 1 →
        (ν : Measure (Space (h+3))) {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    filter_upwards [Measure.support_mem_ae (μ := (μ : Measure (Space (h+3))))] with z hz
    intro r hr hr1 u hu
    exact hcaps.1 z hz u hu r (by simpa only [one_div] using hr) hr1
  have hcap₂ : ∀ᵐ x ∂(ν : Measure (Space (h+3))), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+3), ‖u‖ = 1 →
        (μ : Measure (Space (h+3))) {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    filter_upwards [Measure.support_mem_ae (μ := (ν : Measure (Space (h+3))))] with x hx
    intro r hr hr1 u hu
    exact hcaps.2 x hx u hu r (by simpa only [one_div] using hr) hr1
  have hs₁ := reverse_slabs_all_radii (μ : Measure (Space (h+3))) μ ν
    Measure.AbsolutelyContinuous.rfl (sdiff_subset : G ⊆ Γ N) (le_refl N) (hNp N hNp') (hslab N)
  have hs₂ : ∀ᵐ x ∂(ν : Measure (Space (h+3))), ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (μ : Measure (Space (h+3))) {z | (z,x) ∈ G ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^ζ) := by
    filter_upwards [hslab' N] with x hx
    intro u hu r hr hr1
    have hm : (μ : Measure (Space (h+3))) {z | (z,x) ∈ G ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
        (μ : Measure (Space (h+3))) {z | (z,x) ∈ Γ N ∧ |inner ℝ u (normalize (z-x))| ≤ r} :=
      measure_mono (fun _ hz => ⟨hz.1.1,hz.2⟩)
    apply hm.trans ((hx u hu r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right (hNp N hNp') (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ 1/(2:ℝ)^N).trans hr) _)
  obtain ⟨H,hH,hHG,hHcost,hHcaps⟩ := hNw N hNw' μ ν hμroot hνroot hμfrost hνfrost
    A P hA hP hμA hνP hsep hpin G hG hcap₁ hs₁ hcap₂ hs₂
  have hHΓ : H ⊆ Γ N := hHG.trans sdiff_subset
  refine ⟨Γ N \ H,(hΓ N).diff hH,sdiff_subset,?_,?_⟩
  · have hfirst : ((μ : Measure (Space (h+3))).prod ν) (Γ N \ G) ≤
        ENNReal.ofReal (C₀*((2:ℝ)^N)^(-c₀)) := by
      apply (measure_mono (show Γ N \ G ⊆ B from ?_)).trans hBcost
      intro z hz
      by_contra hn
      exact hz.2 ⟨hz.1,hn⟩
    have htotal := relative_pruning_cost_trans ((μ : Measure (Space (h+3))).prod ν)
      (Γ N) G H hfirst hHcost
    apply htotal.trans
    have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hp₀ : ((2:ℝ)^N)^(-c₀) ≤ ((2:ℝ)^N)^(-min c₀ c) :=
      Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_left _ _))
    have hp : ((2:ℝ)^N)^(-c) ≤ ((2:ℝ)^N)^(-min c₀ c) :=
      Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_right _ _))
    calc
      _ ≤ ENNReal.ofReal (C₀*((2:ℝ)^N)^(-min c₀ c))+
          2*ENNReal.ofReal (((2:ℝ)^N)^(-min c₀ c)) :=
        add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp₀ hC₀.le))
          (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hp))
      _ = _ := by
        rw [add_mul,ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
  · have hbound := radialCapBound_of_window μ ν H (Nat.div_le_self N K)
      (by positivity : 0 ≤ q+gain) le_rfl (hcoarse N) (hNb N hNb') hHcaps
    have heq : Γ N \ (Γ N \ H) = H := by
      ext z
      constructor
      · intro hz
        by_contra hn
        exact hz.2 ⟨hz.1,hn⟩
      · intro hz
        exact ⟨hHΓ hz,fun hn => hn.2 hz⟩
    simpa only [heq] using hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NonendpointTwoSidedScale
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both orientations of the nonendpoint one-scale preparation estimate -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_two_sided_one_scale (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 → ν Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space (h+2), ∀ r > 0, ν (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        (∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c))) ∧
        (∀ z u : Space (h+2), ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c))) := by
  obtain ⟨ε,c,hε,hc,N₀,hscale⟩ := nonendpoint_one_scale_gain hpublished hq hq' hqt ht htα hC
    Q hQ hD hDdim hs
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hcap'
  obtain ⟨H,hH,hHG,hHcost,hHcap⟩ := hscale N hN μ ν hμroot hμfrost A P hA hP hμA hνP
    hsep (fun y hy x hx => hpin y hy x (Or.inr hx)) G hG hcap
  obtain ⟨K,hK,hKG,hKcost,hKcap⟩ := hscale N hN ν μ hνroot hνfrost P A hP hA hνP hμA
    (fun x hx z hz => by simpa only [norm_sub_rev] using hsep z hz x hx)
    (fun y hy x hx => hpin y hy x (Or.inl hx)) (Prod.swap ⁻¹' G) (hG.preimage measurable_swap)
    (by simpa only [mem_preimage,Prod.swap_prod_mk] using hcap')
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := intersect_radial_orientations μ ν G H K hG hH hK hHG hKG
    hHcost hKcost hHcap hKcap
  refine ⟨G',hG',hsub,?_,hcaps⟩
  simpa only [two_mul] using hdel

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_NonendpointScaleWindow
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same original pair set can be improved throughout a dyadic scale window -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators

theorem nonendpoint_scale_window_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧ ∀ K : ℕ, 0 < K →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 → ν Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space (h+2), ∀ r > 0, ν (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ j : ℕ, N/K ≤ j → j ≤ N →
          (∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) ∧
          (∀ z u : Space (h+2), ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) := by
  obtain ⟨ε,gain,hε,hgain,Ns,hscale⟩ := nonendpoint_two_sided_one_scale hpublished hq hq' hqt
    ht htα hC Q hQ hD hDdim hs
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro K hK
  obtain ⟨c,hc,Nc,hcost⟩ := radial_scale_window_cost K hK hgain
  refine ⟨c,hc,max (K*Ns) (max (2*K) Nc),?_⟩
  intro N hN μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hcap'
  simp only [max_le_iff] at hN
  obtain ⟨hNs,hNK,hNc⟩ := hN
  have hstart : Ns ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by simpa only [Nat.mul_comm] using hNs)
  have hcapSwap : ∀ᵐ z ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        μ {x | (z,x) ∈ Prod.swap ⁻¹' G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    simpa only [mem_preimage,Prod.swap_prod_mk] using hcap'
  obtain ⟨H,hH,hsub,hdel,hbounds⟩ := finite_radial_refinement μ ν G hG (Finset.Icc (N/K) N)
    (fun j => 2*ENNReal.ofReal (((2:ℝ)^j)^(-gain)))
    (fun j => ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) (fun j => 1/(2:ℝ)^j) (by
      intro j hj
      obtain ⟨hjlo,hjhi⟩ := Finset.mem_Icc.mp hj
      have hloss := radial_scale_window_loss hK hNK hjlo hε.le
      have hc₁ := reverse_caps_all_radii μ μ ν Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := G)) hjhi hloss hcap
      have hc₂ := reverse_caps_all_radii ν ν μ Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := Prod.swap ⁻¹' G)) hjhi hloss hcapSwap
      obtain ⟨H,hH,hsub,hdel,hbounds⟩ := hscale j (hstart.trans hjlo) μ ν
        hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hc₁
        (by simpa only [mem_preimage,Prod.swap_prod_mk] using hc₂)
      refine ⟨H,hH,hsub,hdel,?_⟩
      have he : ((2:ℝ)^j)^(-q-gain) = (1/(2:ℝ)^j)^(q+gain) := by
        rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
        congr 1
        ring
      simpa only [he] using hbounds)
  refine ⟨H,hH,hsub,?_,fun j hjlo hjhi => hbounds j (Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩)⟩
  apply hdel.trans
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (hcost N hNc)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NonendpointAvailabilityGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict improvement of the actual available radial exponent -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem CapAvailable.nonendpoint_improve (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s)
    (μ ν : ProbabilityMeasure (Space (h+2)))
    (hμroot : (μ : Measure (Space (h+2))) Q.carrierᶜ = 0)
    (hνroot : (ν : Measure (Space (h+2))) Q.carrierᶜ = 0)
    (hμfrost : ∀ y : Space (h+2), ∀ r > 0, (μ : Measure (Space (h+2))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (hνfrost : ∀ y : Space (h+2), ∀ r > 0, (ν : Measure (Space (h+2))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (A P : Set (Space (h+2))) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hμA : (μ : Measure (Space (h+2))) Aᶜ = 0) (hνP : (ν : Measure (Space (h+2))) Pᶜ = 0)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (hpin : ∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D)
    (Γ : ℕ → Set (Space (h+2) × Space (h+2))) (hΓ : ∀ N, MeasurableSet (Γ N))
    (havailable : CapAvailable μ ν Γ q) :
    ∃ q' : ℝ, q < q' ∧ CapAvailable μ ν Γ q' := by
  obtain ⟨ε,gain,hε,hgain,hwindow⟩ := Regularization.nonendpoint_scale_window_gain
    hpublished hq hq' hqt ht htα hC Q hQ hD hDdim hs
  refine ⟨q+gain,by linarith only [hgain],?_⟩
  intro e he
  have hq0 : 0 ≤ q := by have hh := Nat.cast_nonneg (α := ℝ) h; linarith only [hh,hq]
  obtain ⟨K,hK,hcoarse⟩ := exists_radial_window_denominator he (by positivity : 0 ≤ q+gain)
  obtain ⟨c,hc,Nw,hNw⟩ := hwindow K hK
  have hin : 0 < ε/(2*(K:ℝ)) := by positivity
  obtain ⟨c₀,C₀,hc₀,hC₀,Na,hNa⟩ := havailable (ε/(2*(K:ℝ))) hin
  obtain ⟨Nb,hNb⟩ := Regularization.fixed_constant_absorbed he ((2:ℝ)^(q+gain))
  refine ⟨min c₀ c,C₀+2,lt_min hc₀ hc,by positivity,max Na (max Nw Nb),?_⟩
  intro N hN
  simp only [max_le_iff] at hN
  obtain ⟨hNa',hNw',hNb'⟩ := hN
  obtain ⟨B,hB,hBΓ,hBcost,hcaps⟩ := hNa N hNa'
  let G := Γ N \ B
  have hG : MeasurableSet G := (hΓ N).diff hB
  have hcap₁ : ∀ᵐ z ∂(μ : Measure (Space (h+2))), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        (ν : Measure (Space (h+2))) {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    filter_upwards [Measure.support_mem_ae (μ := (μ : Measure (Space (h+2))))] with z hz
    intro r hr hr1 u hu
    exact hcaps.1 z hz u hu r (by simpa only [one_div] using hr) hr1
  have hcap₂ : ∀ᵐ x ∂(ν : Measure (Space (h+2))), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        (μ : Measure (Space (h+2))) {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    filter_upwards [Measure.support_mem_ae (μ := (ν : Measure (Space (h+2))))] with x hx
    intro r hr hr1 u hu
    exact hcaps.2 x hx u hu r (by simpa only [one_div] using hr) hr1
  obtain ⟨H,hH,hHG,hHcost,hHcaps⟩ := hNw N hNw' μ ν hμroot hνroot hμfrost hνfrost
    A P hA hP hμA hνP hsep hpin G hG hcap₁ hcap₂
  have hHΓ : H ⊆ Γ N := hHG.trans sdiff_subset
  refine ⟨Γ N \ H,(hΓ N).diff hH,sdiff_subset,?_,?_⟩
  · have hfirst : ((μ : Measure (Space (h+2))).prod ν) (Γ N \ G) ≤
        ENNReal.ofReal (C₀*((2:ℝ)^N)^(-c₀)) := by
      apply (measure_mono (show Γ N \ G ⊆ B from ?_)).trans hBcost
      intro z hz
      by_contra hn
      exact hz.2 ⟨hz.1,hn⟩
    have htotal := relative_pruning_cost_trans ((μ : Measure (Space (h+2))).prod ν)
      (Γ N) G H hfirst hHcost
    apply htotal.trans
    have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hp₀ : ((2:ℝ)^N)^(-c₀) ≤ ((2:ℝ)^N)^(-min c₀ c) :=
      Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_left _ _))
    have hp : ((2:ℝ)^N)^(-c) ≤ ((2:ℝ)^N)^(-min c₀ c) :=
      Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_right _ _))
    calc
      _ ≤ ENNReal.ofReal (C₀*((2:ℝ)^N)^(-min c₀ c))+
          2*ENNReal.ofReal (((2:ℝ)^N)^(-min c₀ c)) :=
        add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp₀ hC₀.le))
          (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hp))
      _ = _ := by
        rw [add_mul,ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
  · have hbound := radialCapBound_of_window μ ν H (Nat.div_le_self N K)
      (by positivity : 0 ≤ q+gain) le_rfl (hcoarse N) (hNb N hNb') hHcaps
    have heq : Γ N \ (Γ N \ H) = H := by
      ext z
      constructor
      · intro hz
        by_contra hn
        exact hz.2 ⟨hz.1,hn⟩
      · intro hz
        exact ⟨hHΓ hz,fun hn => hn.2 hz⟩
    simpa only [heq] using hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ThinTubeUpgrade
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The thin-tube upgrade in the original pair measures

Proposition `prep:thin-upgrade`: the integer exponent improves to the adjacent
half-integer. The endpoint and nonendpoint gains below are proved geometric
inputs, not extra hypotheses about availability.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem thin_tube_upgrade (hpublished : PublishedPlanarFurstenberg)
    (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {α ζ C D s Cplate : ℝ}
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2) (hζ : 0 < ζ) (hC : 0 ≤ C)
    (Q : DyadicCube (h+3)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+3:ℕ) ≤ D) (hs : 0 < s)
    (μ ν : ProbabilityMeasure (Space (h+3)))
    (hμroot : (μ : Measure (Space (h+3))) Q.carrierᶜ = 0)
    (hνroot : (ν : Measure (Space (h+3))) Q.carrierᶜ = 0)
    (hμfrost : ∀ y : Space (h+3), ∀ r > 0, (μ : Measure (Space (h+3))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (hνfrost : ∀ y : Space (h+3), ∀ r > 0, (ν : Measure (Space (h+3))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (A P : Set (Space (h+3))) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hμA : (μ : Measure (Space (h+3))) Aᶜ = 0) (hνP : (ν : Measure (Space (h+3))) Pᶜ = 0)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (hpin : ∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D)
    (Γ : ℕ → Set (Space (h+3) × Space (h+3))) (hΓ : ∀ N, MeasurableSet (Γ N))
    (hslab : ∀ N : ℕ, ∀ᵐ z ∂(μ : Measure (Space (h+3))),
      ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (ν : Measure (Space (h+3))) {x | (z,x) ∈ Γ N ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
          ENNReal.ofReal (Cplate*r^ζ))
    (hslab' : ∀ N : ℕ, ∀ᵐ x ∂(ν : Measure (Space (h+3))),
      ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (μ : Measure (Space (h+3))) {z | (z,x) ∈ Γ N ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
          ENNReal.ofReal (Cplate*r^ζ))
    (hstart : CapAvailable μ ν Γ ((h:ℝ)+1)) :
    CapAvailable μ ν Γ ((h:ℝ)+3/2) := by
  let t := (α+((h:ℝ)+3/2))/2
  have htt : (h:ℝ)+3/2 < t := by dsimp [t]; linarith only [hα]
  have htα : t < α := by dsimp [t]; linarith only [hα]
  have ht' : t < (h:ℝ)+2 := htα.trans hα'
  have hbase : ((h+2:ℕ):ℝ)-1 = (h:ℝ)+1 := by push_cast; ring
  have htop : ((h+2:ℕ):ℝ)-1/2 = (h:ℝ)+3/2 := by push_cast; ring
  have hresult := capAvailable_half_integer (h+2) μ ν Γ (by simpa only [hbase] using hstart) (by
    intro q hlow hu havail
    have hlo : (h:ℝ)+1 ≤ q := by simpa only [hbase] using hlow
    have hupper : q < (h:ℝ)+3/2 := by simpa only [htop] using hu
    have hex : ∃ r : ℝ, q < r ∧ CapAvailable μ ν Γ r := by
      by_cases heq : q = (h:ℝ)+1
      · exact CapAvailable.endpoint_improve hLW heq htt ht' hζ htα hC Q hQ hD hDdim hs μ ν
          hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin Γ hΓ hslab hslab' havail
      · have hq : ((h+1:ℕ):ℝ) < q := by push_cast; exact lt_of_le_of_ne hlo (Ne.symm heq)
        have hq' : q-((h+1:ℕ):ℝ) ≤ 1/2 := by push_cast; linarith only [hupper]
        have hqt : q < t := hupper.trans htt
        have ht : t-((h+1:ℕ):ℝ) < 1 := by push_cast; linarith only [ht']
        exact CapAvailable.nonendpoint_improve hpublished hq hq' hqt ht htα hC Q hQ hD hDdim hs μ ν
          hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin Γ hΓ havail
    obtain ⟨r,hqr,hr⟩ := hex
    refine ⟨min r (((h+2:ℕ):ℝ)-1/2),lt_min hqr hu,min_le_right _ _,?_⟩
    exact hr.mono (min_le_left _ _))
  simpa only [htop] using hresult

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OddAuxiliaryCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half-integer cap availability in the first auxiliary space

All geometric hypotheses of the coarse-filter and thin-tube theorems are
verified for the selected, normalized original restrictions.
-/
namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h : ℕ} {μ : ProbabilityMeasure (Space d)} {α ε : ℝ}
  {f : TwoProjectionFrame μ (h+3) (h+2) α}

namespace TwoProjectionPieces

theorem odd_auxiliary_caps_grid (p : TwoProjectionPieces f ε)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ Γ : ℕ → Set (Space (h+3) × Space (h+3)),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < (((p.left.map (f.first.continuous.aemeasurable) : ProbabilityMeasure (Space (h+3))) : Measure (Space (h+3))).prod
        (p.right.map (f.first.continuous.aemeasurable) : Measure (Space (h+3)))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ supportPair (p.left.map (f.first.continuous.aemeasurable)) (p.right.map (f.first.continuous.aemeasurable))) ∧
      CapAvailable (p.left.map (f.first.continuous.aemeasurable)) (p.right.map (f.first.continuous.aemeasurable)) Γ ((h:ℝ)+3/2) ∧
      (∀ N : ℕ, ∃ T : Finset (List (Fin (h+3) → Bool) × List (Fin (h+3) → Bool)),
        T ⊆ (cubePaths (h+3) ⌊ω*(N:ℝ)⌋₊).product (cubePaths (h+3) ⌊ω*(N:ℝ)⌋₊) ∧
        Γ N = (⋃ pq ∈ T,
          ((centeredUnitCube (h+3)).descendant pq.1).carrier ×ˢ
          ((centeredUnitCube (h+3)).descendant pq.2).carrier) ∩
            supportPair (p.left.map (f.first.continuous.aemeasurable)) (p.right.map (f.first.continuous.aemeasurable))) := by
  let ν₁ := p.left.map (f.first.continuous.aemeasurable)
  let ν₂ := p.right.map (f.first.continuous.aemeasurable)
  let Q := centeredUnitCube (h+3)
  have hroot₁ : (ν₁ : Measure (Space (h+3))) Q.carrier = 1 := by
    apply (mem_ae_iff_prob_eq_one Q.measurable).mp
    filter_upwards [Measure.support_mem_ae (μ := (ν₁ : Measure (Space (h+3))))] with x hx
    exact p.first_support_left hx
  have hroot₂ : (ν₂ : Measure (Space (h+3))) Q.carrier = 1 := by
    apply (mem_ae_iff_prob_eq_one Q.measurable).mp
    filter_upwards [Measure.support_mem_ae (μ := (ν₂ : Measure (Space (h+3))))] with x hx
    exact p.first_support_right hx
  have hbounded₁ : ∀ᵐ x ∂(ν₁ : Measure (Space (h+3))), ‖x‖ ≤ Real.sqrt (h+3:ℕ) := by
    filter_upwards [Measure.support_mem_ae (μ := (ν₁ : Measure (Space (h+3))))] with x hx
    exact centeredUnitCube_norm_bound (p.first_support_left hx)
  have hbounded₂ : ∀ᵐ x ∂(ν₂ : Measure (Space (h+3))), ‖x‖ ≤ Real.sqrt (h+3:ℕ) := by
    filter_upwards [Measure.support_mem_ae (μ := (ν₂ : Measure (Space (h+3))))] with x hx
    exact centeredUnitCube_norm_bound (p.first_support_right hx)
  have hfrost := p.projected_frostman f.first f.first_frostman
  have hnat : h+3-2 = h+1 := by omega
  have hs : 1/2 < α-((h+3-2:ℕ):ℝ) := by rw [hnat]; push_cast; linarith
  have hs' : α-((h+3-2:ℕ):ℝ) < 1 := by rw [hnat]; push_cast; linarith
  obtain ⟨Γ₀,K,ζ,hK,hζ,hΓ₀,hanti,hpos,hpartition,hslabs⟩ :=
    coarse_plate_preparation hH (by omega : 3 ≤ h+3) ν₁ ν₂ Q
      (by norm_num [Q,centeredUnitCube]) (Real.sqrt_nonneg _)
      (fun _ hx => centeredUnitCube_norm_bound hx) hs hs' p.constant_pos.le
      hbounded₁ hbounded₂ hfrost.1 hfrost.2 hroot₁ hroot₂ p.first_noncharging hω hω1
  let Γ := fun N => Γ₀ N ∩ supportPair ν₁ ν₂
  have hΓ : ∀ N, MeasurableSet (Γ N) := fun N => (hΓ₀ N).inter (supportPair_measurable ν₁ ν₂)
  have hΓsub : ∀ N, Γ N ⊆ supportPair ν₁ ν₂ := fun _ => inter_subset_right
  have hstart : CapAvailable ν₁ ν₂ Γ ((h:ℝ)+1) := by
    have heq : α = ((h+1:ℕ):ℝ)+(α-((h+1:ℕ):ℝ)) := by ring
    have hδ : 0 < α-((h+1:ℕ):ℝ) := by push_cast; linarith
    have hδ1 : α-((h+1:ℕ):ℝ) < 1 := by push_cast; linarith
    have hcaps := p.first_integer_caps hR (by omega : 1 ≤ h+1) hδ hδ1 heq Γ hΓ hΓsub
    simpa only [Nat.cast_add,Nat.cast_one] using hcaps
  have hsep : 0 < p.lower*(p.radius/2) := mul_pos p.lower_pos (by linarith [p.radius_pos])
  have hpin : ∀ y ∈ Q.carrier, ∀ x ∈
      (ν₁ : Measure (Space (h+3))).support ∪ (ν₂ : Measure (Space (h+3))).support,
      ‖y-x‖ ≤ max 1 (Real.sqrt (h+3:ℕ)) := by
    intro y hy x hx
    have hxQ : x ∈ Q.carrier := hx.elim
      (fun hx' => p.first_support_left hx') (fun hx' => p.first_support_right hx')
    have hd := Q.dist_le (by norm_num [Q,centeredUnitCube]) hy hxQ
    have hd' : ‖y-x‖ ≤ Real.sqrt (h+3:ℕ) := by
      simpa only [dist_eq_norm,Q,centeredUnitCube,mul_one] using hd
    exact hd'.trans (le_max_right _ _)
  have hup := thin_tube_upgrade (Cplate := K) hF hLW hα hα' hζ p.constant_pos.le Q rfl
    (le_max_left _ _) (le_max_right _ _) hsep ν₁ ν₂
    ((prob_compl_eq_zero_iff Q.measurable).mpr hroot₁)
    ((prob_compl_eq_zero_iff Q.measurable).mpr hroot₂) hfrost.1 hfrost.2
    (ν₁ : Measure (Space (h+3))).support (ν₂ : Measure (Space (h+3))).support
    Measure.isClosed_support.measurableSet Measure.isClosed_support.measurableSet
    Measure.measure_compl_support Measure.measure_compl_support
    (fun z hz x hx => by simpa only [dist_eq_norm] using p.first_pair_separation z hz x hx)
    hpin Γ hΓ ?_ ?_ hstart
  · refine ⟨Γ,hΓ,?_,?_,hΓsub,hup,?_⟩
    · intro N N' hNN z hz
      exact ⟨hanti hNN hz.1,hz.2⟩
    · change 0 < ((ν₁ : Measure (Space (h+3))).prod (ν₂ : Measure (Space (h+3))))
        (⋂ N, Γ₀ N ∩ supportPair ν₁ ν₂)
      rw [supportPair_iInter_mass]
      exact hpos
    · intro N
      obtain ⟨T,hT,hTeq⟩ := hpartition N
      exact ⟨T,hT,congrArg (fun S => S ∩ supportPair ν₁ ν₂) hTeq⟩
  · intro N
    exact Filter.Eventually.of_forall (fun z w hw r hr hr1 =>
      (measure_mono (by intro x hx; exact ⟨hx.1.1,hx.2⟩)).trans ((hslabs N z w hw r hr hr1).1))
  · intro N
    exact Filter.Eventually.of_forall (fun x w hw r hr hr1 =>
      (measure_mono (by intro z hz; exact ⟨hz.1.1,hz.2⟩)).trans ((hslabs N x w hw r hr hr1).2))

end TwoProjectionPieces
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OriginalPairFilter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lift the auxiliary filters to the original pair law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

theorem liftedPairFilter_measurable (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)}
    (hΓ : ∀ N, MeasurableSet (Γ N)) (N : ℕ) :
    MeasurableSet (liftedPairFilter μ ν P Γ N) :=
  (supportPair_measurable μ ν).inter ((hΓ N).preimage
    (P.continuous.measurable.prodMap P.continuous.measurable))

theorem liftedPairFilter_antitone (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)}
    (hΓ : Antitone Γ) : Antitone (liftedPairFilter μ ν P Γ) := by
  intro N M hNM z hz
  exact ⟨hz.1,hΓ hNM hz.2⟩

theorem liftedPairFilter_limit_mass (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)}
    (hΓ : ∀ N, MeasurableSet (Γ N)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
      (⋂ N, liftedPairFilter μ ν P Γ N) =
    (((μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure (Space k)) : Measure (Space k)).prod
      (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure (Space k))) (⋂ N, Γ N) := by
  have heq : (⋂ N, liftedPairFilter μ ν P Γ N) =
      (Prod.map P P ⁻¹' (⋂ N, Γ N)) ∩ supportPair μ ν := by
    ext z
    simp only [liftedPairFilter,mem_iInter,mem_inter_iff,mem_preimage]
    exact ⟨fun h => ⟨fun N => (h N).2,(h 0).1⟩,fun h N => ⟨h.2,h.1 N⟩⟩
  rw [heq,supportPair_inter_mass]
  change _ = (((μ : Measure (Space d)).map P).prod ((ν : Measure (Space d)).map P)) _
  rw [Measure.map_prod_map _ _ P.continuous.measurable P.continuous.measurable,
    Measure.map_apply (P.continuous.measurable.prodMap P.continuous.measurable)
      (MeasurableSet.iInter hΓ)]

theorem CapAvailable.lift_original_pair (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)} {c q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (hq : 0 ≤ q)
    (hΓ : ∀ N, MeasurableSet (Γ N))
    (hlower : ∀ x ∈ (μ : Measure (Space d)).support,
      ∀ y ∈ (ν : Measure (Space d)).support,
      c ≤ ‖P (radialDirection x y)‖ ∧ c ≤ ‖P (radialDirection y x)‖)
    (hcap : CapAvailable (μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Γ q) :
    CapAvailable μ ν (liftedPairFilter μ ν P Γ) q := by
  apply hcap.pullback P μ ν hc hP hq (liftedPairFilter_measurable μ ν P hΓ)
    (fun _ => inter_subset_right)
  intro N z hz
  exact hlower z.1 hz.1.1 z.2 hz.1.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_BorelProductPartition
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite disjoint Borel products in the original ambient space -/
namespace Falconer
open Set MeasureTheory

theorem HasBorelProductPartition.mono_bound {d : ℕ} {S : Set (Space d × Space d)}
    {K L : ℝ} (h : HasBorelProductPartition S K) (hKL : K ≤ L) :
    HasBorelProductPartition S L := by
  obtain ⟨n,hn,A,B,hAB,hdis,hS⟩ := h
  exact ⟨n,hn.trans hKL,A,B,hAB,hdis,hS⟩

theorem borel_product_partition_of_finset {d : ℕ} {ι : Type*}
    (T : Finset ι) (A B : ι → Set (Space d))
    (hm : ∀ i ∈ T, MeasurableSet (A i) ∧ MeasurableSet (B i))
    (hd : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) :
    HasBorelProductPartition (⋃ i ∈ T, A i ×ˢ B i) (T.card:ℝ) := by
  classical
  let e := T.equivFin
  refine ⟨T.card,le_rfl,(fun i => A (e.symm i).val),(fun i => B (e.symm i).val),?_,?_,?_⟩
  · intro i
    exact hm _ (e.symm i).property
  · intro i j hij
    apply hd _ (e.symm i).property _ (e.symm j).property
    intro h
    apply hij
    exact e.symm.injective (Subtype.ext h)
  · ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi,hz⟩
      refine ⟨e ⟨i,hi⟩,?_⟩
      simpa only [Equiv.symm_apply_apply] using hz
    · rintro ⟨i,hz⟩
      exact ⟨(e.symm i).val,(e.symm i).property,hz⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ProductCellPartition
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite product-cell count in the starting-pair preparation -/
namespace Falconer
open Set MeasureTheory

theorem DyadicCube.product_cells_disjoint {d J : ℕ} (Q : DyadicCube d)
    {p q : List (Fin d → Bool) × List (Fin d → Bool)}
    (hp : p ∈ (cubePaths d J).product (cubePaths d J))
    (hq : q ∈ (cubePaths d J).product (cubePaths d J)) (hne : p ≠ q) :
    Disjoint ((Q.descendant p.1).carrier ×ˢ (Q.descendant p.2).carrier)
      ((Q.descendant q.1).carrier ×ˢ (Q.descendant q.2).carrier) := by
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
  apply Set.disjoint_left.mpr
  intro z hz hz'
  by_cases he : p.1 = q.1
  · have he2 : p.2 ≠ q.2 := fun hh => hne (Prod.ext he hh)
    exact Set.disjoint_left.mp (Q.descendants_disjoint
      (((mem_cubePaths d J p.2).mp hp2).trans ((mem_cubePaths d J q.2).mp hq2).symm) he2) hz.2 hz'.2
  · exact Set.disjoint_left.mp (Q.descendants_disjoint
      (((mem_cubePaths d J p.1).mp hp1).trans ((mem_cubePaths d J q.1).mp hq1).symm) he) hz.1 hz'.1

theorem dyadic_product_card_bound {d N : ℕ} {ω : ℝ} (hω : 0 ≤ ω)
    (T : Finset (List (Fin d → Bool) × List (Fin d → Bool)))
    (hT : T ⊆ (cubePaths d ⌊ω*(N:ℝ)⌋₊).product (cubePaths d ⌊ω*(N:ℝ)⌋₊)) :
    (T.card : ℝ) ≤ (2:ℝ)^(2*(d:ℝ)*ω*(N:ℝ)) := by
  let J := ⌊ω*(N:ℝ)⌋₊
  have hc := Finset.card_le_card hT
  rw [Finset.product_eq_sprod,Finset.card_product,card_cubePaths,← pow_add] at hc
  have he : d*J+d*J = 2*d*J := by ring
  change T.card ≤ 2^(d*J+d*J) at hc
  rw [he] at hc
  have hreal : (T.card:ℝ) ≤ (2:ℝ)^(2*d*J) := by exact_mod_cast hc
  have hf : (J:ℝ) ≤ ω*(N:ℝ) := Nat.floor_le (mul_nonneg hω (Nat.cast_nonneg N))
  have hpower : ((2*d*J:ℕ):ℝ) ≤ 2*(d:ℝ)*ω*(N:ℝ) := by
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hf (show 0 ≤ 2*(d:ℝ) by positivity)]
  exact hreal.trans ((Real.rpow_natCast (2:ℝ) (2*d*J)).symm.le.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hpower))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_LiftedProductPartition
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product partitions retain disjointness after the original-law pullback -/
namespace Falconer
open Set MeasureTheory
variable {d k N : ℕ} {ω : ℝ}

theorem continuous_image_support {μ : Measure (Space d)}
    (P : Space d →L[ℝ] Space k) {x : Space d} (hx : x ∈ μ.support) :
    P x ∈ (μ.map P).support := by
  have hclosed : IsClosed (P ⁻¹' (μ.map P).support) :=
    Measure.isClosed_support.preimage P.continuous
  apply Measure.support_subset_of_isClosed hclosed _ hx
  change μ (P ⁻¹' ((μ.map P).support)ᶜ) = 0
  rw [← Measure.map_apply P.continuous.measurable Measure.isClosed_support.measurableSet.compl]
  exact Measure.measure_compl_support

theorem lifted_dyadic_product_partition (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) (Q : DyadicCube k)
    (Γ : ℕ → Set (Space k × Space k)) (hω : 0 ≤ ω)
    (T : Finset (List (Fin k → Bool) × List (Fin k → Bool)))
    (hT : T ⊆ (cubePaths k ⌊ω*(N:ℝ)⌋₊).product (cubePaths k ⌊ω*(N:ℝ)⌋₊))
    (hΓ : Γ N = (⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ
      (Q.descendant pq.2).carrier) ∩ supportPair (μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) :
    (T.card : ℝ) ≤ (2:ℝ)^(2*(k:ℝ)*ω*(N:ℝ)) ∧
    (∀ pq ∈ T,
      MeasurableSet ((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.1).carrier) ∧
      MeasurableSet ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.2).carrier)) ∧
    (∀ pq ∈ T, ∀ ab ∈ T, pq ≠ ab →
      Disjoint
        (((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.1).carrier) ×ˢ
         ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.2).carrier))
        (((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant ab.1).carrier) ×ˢ
         ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant ab.2).carrier))) ∧
    liftedPairFilter μ ν P Γ N = ⋃ pq ∈ T,
      ((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.1).carrier) ×ˢ
      ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.2).carrier) := by
  refine ⟨dyadic_product_card_bound hω T hT,?_,?_,?_⟩
  · intro pq _
    exact ⟨Measure.isClosed_support.measurableSet.inter
      ((Q.descendant pq.1).measurable.preimage P.continuous.measurable),
      Measure.isClosed_support.measurableSet.inter
      ((Q.descendant pq.2).measurable.preimage P.continuous.measurable)⟩
  · intro pq hpq ab hab hne
    apply Set.disjoint_left.mpr
    rintro ⟨x,y⟩ ⟨hx,hy⟩ ⟨hx',hy'⟩
    have hp : (P x,P y) ∈ (Q.descendant pq.1).carrier ×ˢ
        (Q.descendant pq.2).carrier := ⟨hx.2,hy.2⟩
    have ha : (P x,P y) ∈ (Q.descendant ab.1).carrier ×ˢ
        (Q.descendant ab.2).carrier := ⟨hx'.2,hy'.2⟩
    exact Set.disjoint_left.mp (Q.product_cells_disjoint (hT hpq) (hT hab) hne)
      hp ha
  · ext z
    simp only [liftedPairFilter,hΓ,supportPair,mem_inter_iff,mem_preimage,
      mem_iUnion,mem_prod]
    constructor
    · rintro ⟨⟨hx,hy⟩,⟨pq,hpq,hpx,hpy⟩,_⟩
      exact ⟨pq,hpq,⟨hx,hpx⟩,hy,hpy⟩
    · rintro ⟨pq,hpq,⟨hx,hpx⟩,hy,hpy⟩
      exact ⟨⟨hx,hy⟩,⟨pq,hpq,hpx,hpy⟩,continuous_image_support P hx,continuous_image_support P hy⟩


theorem lifted_pair_has_borel_product_partition (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) (Q : DyadicCube k)
    (Γ : ℕ → Set (Space k × Space k)) (hω : 0 ≤ ω)
    (T : Finset (List (Fin k → Bool) × List (Fin k → Bool)))
    (hT : T ⊆ (cubePaths k ⌊ω*(N:ℝ)⌋₊).product (cubePaths k ⌊ω*(N:ℝ)⌋₊))
    (hΓ : Γ N = (⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ
      (Q.descendant pq.2).carrier) ∩ supportPair (μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) :
    HasBorelProductPartition (liftedPairFilter μ ν P Γ N)
      ((2:ℝ)^(2*(k:ℝ)*ω*(N:ℝ))) := by
  obtain ⟨hcard,hm,hd,heq⟩ := lifted_dyadic_product_partition μ ν P Q Γ hω T hT hΓ
  rw [heq]
  exact (borel_product_partition_of_finset T _ _ hm hd).mono_bound hcard

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OddOriginalCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Return the odd-dimensional half-integer estimate to the original pair law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {μ : ProbabilityMeasure (Space d)} {α ε : ℝ}
  {f : TwoProjectionFrame μ (h+3) (h+2) α}

namespace TwoProjectionPieces

theorem odd_original_caps_partition_oai (p : TwoProjectionPieces f ε)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ Γ : ℕ → Set (Space d × Space d),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ supportPair p.left p.right) ∧
      CapAvailable p.left p.right Γ ((h:ℝ)+3/2) ∧
      (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*((h+3:ℕ):ℝ)*ω*(N:ℝ)))) := by
  obtain ⟨Γ',hΓ',hanti,hpos,_,hcap,hpartition⟩ := p.odd_auxiliary_caps_grid hR hH hF hLW hα hα' hω hω1
  let Γ := liftedPairFilter p.left p.right f.first Γ'
  refine ⟨Γ,liftedPairFilter_measurable _ _ _ hΓ',
    liftedPairFilter_antitone _ _ _ hanti,?_,fun _ => inter_subset_left,?_,?_⟩
  · rw [liftedPairFilter_limit_mass _ _ _ hΓ']
    exact hpos
  · apply CapAvailable.lift_original_pair _ _ _ p.lower_pos f.first_contractive
      (by positivity) hΓ' _ hcap
    intro x hx y hy
    exact p.first_lower (p.left_support hx) (p.right_support hy)

  · intro N
    obtain ⟨T,hT,hTeq⟩ := hpartition N
    exact lifted_pair_has_borel_product_partition p.left p.right f.first
      (centeredUnitCube (h+3)) Γ' hω.le T hT hTeq

end TwoProjectionPieces
end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition_oai := @OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition_oai
