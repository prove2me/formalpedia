-- Prove2me | solution 1 for GlobalTheory.MajorantContinuity.eventually_comparable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:49.511932+00:00
-- url     : https://prove2.me/submissions/efe5bc53-fe04-44e3-9846-6712ba3e364a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Theorems.Thm_GlobalTheory_MajorantContinuity_maj_real_smul
import Theorems.Thm_GlobalTheory_MajorantContinuity_continuousAt_maj
import Theorems.Thm_GlobalTheory_MajorantContinuity_exists_sphere
import Theorems.Thm_GlobalTheory_MajorantContinuity_maj_at_zero
import Theorems.Thm_GlobalTheory_MajorantContinuity_ne_zero_of_sphere
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_isOpen_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
open GlobalTheory GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantContinuity
theorem _root_.solution {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v := by
  have hdom : ∀ᶠ y in 𝓝 x, y ∈ X.dom := (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).mem_nhds hx
  have key : ∀ τ : X.Ψ, ∀ᶠ y in 𝓝 x, ∀ w ∈ Metric.sphere (0 : Fin r → ℂ) 1,
      X.maj x τ w < (1 + ε) * X.maj y τ w ∧ X.maj y τ w < (1 + ε) * X.maj x τ w := by
    intro τ
    refine (isCompact_sphere (0 : Fin r → ℂ) 1).eventually_forall_of_forall_eventually ?_
    intro w hw
    have hpos : 0 < X.maj x τ w := X.maj_pos hx τ (ne_zero_of_sphere hw)
    have h1 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, w) :=
      continuousAt_maj X τ hx w
    have h2 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj x τ p.2) (x, w) :=
      ContinuousAt.comp_of_eq (g := fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
        (f := fun p : Frame X.Ψ r × (Fin r → ℂ) => (x, p.2)) h1
        (continuous_const.prodMk continuous_snd).continuousAt rfl
    refine (h2.eventually_lt (continuousAt_const.mul h1) ?_).and
      (h1.eventually_lt (continuousAt_const.mul h2) ?_)
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
  filter_upwards [hdom, Filter.eventually_all.2 key] with y hy hk
  refine ⟨hy, fun τ v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hx' : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hy' : X.maj y τ v = ‖v‖ ^ 2 * X.maj y τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X y τ _ w
  obtain ⟨k1, k2⟩ := hk τ w hw
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hx', hy']
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left k1.le ht]
  · nlinarith [mul_le_mul_of_nonneg_left k2.le ht]
end GlobalTheory.MajorantContinuity
