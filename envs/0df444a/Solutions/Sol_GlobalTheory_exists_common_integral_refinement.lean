-- Prove2me | solution 1 for GlobalTheory.exists_common_integral_refinement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:06.81109+00:00
-- url     : https://prove2.me/submissions/41c64a50-caee-404e-bff4-23b0cffe120f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetDivIndexEqOfSpanEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory
theorem _root_.solution {V ι : Type} [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] (w w' : ι → V) (hw' : LinearIndependent E w')
    (h : Submodule.span E (Set.range w) = Submodule.span E (Set.range w')) :
    ∃ A A' : Matrix ι ι (𝓞 E), A.det ≠ 0 ∧ A'.det ≠ 0 ∧
      (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) = (fun a => ∑ b, ((A' b a : 𝓞 E) : E) • w' b) := by
  have h1 : ∀ a, ∃ c : ι → E, ∑ b, c b • w b = w' a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun E).1
      (h ▸ Submodule.subset_span (Set.mem_range_self a))
  choose B hB using h1
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun p : ι × ι => B p.1 p.2)
  have hc' : ∀ a b, ∃ y : 𝓞 E, (y : E) = ((c : 𝓞 E) : E) * B a b := by
    intro a b
    obtain ⟨y, hy⟩ := hc (a, b)
    refine ⟨y, ?_⟩
    have : (y : E) = algebraMap (𝓞 E) E y := rfl
    rw [this, hy, Algebra.smul_def]
  choose A hA using hc'
  have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hcE : ((c : 𝓞 E) : E) ≠ 0 := by
    simp
  have key : ∀ a, ∑ b, ((A a b : 𝓞 E) : E) • w b = ((c : 𝓞 E) : E) • w' a := by
    intro a
    rw [← hB a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [hA, mul_smul]
  refine ⟨Matrix.of fun b a => A a b, Matrix.diagonal fun _ => (c : 𝓞 E), ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have h2 : ∑ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a = 0 := by
      have : ∀ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a
          = ∑ b, (((A a b * v a : 𝓞 E)) : E) • w b := by
        intro a
        rw [mul_smul, ← key, Finset.smul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← mul_smul, mul_comm]
        simp
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_comm]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [← Finset.sum_smul]
      have hb : ∑ a, A a b * v a = 0 := by
        have := congrFun hv b
        simpa [Matrix.mulVec, dotProduct] using this
      have hb' : ∑ a, (((A a b * v a : 𝓞 E)) : E) = 0 := by
        have := congrArg (algebraMap (𝓞 E) E) hb
        rw [map_sum, map_zero] at this
        exact this
      rw [hb', zero_smul]
    funext a
    have h3 := Fintype.linearIndependent_iff.1 hw' _ h2 a
    have h4 : ((v a : 𝓞 E) : E) = 0 := (mul_eq_zero.1 h3).resolve_right hcE
    simpa using h4
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hc0
  · funext a
    simp only [Matrix.of_apply]
    rw [key, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · simp
end GlobalTheory
