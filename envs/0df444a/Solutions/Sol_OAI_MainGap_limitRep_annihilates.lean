-- Prove2me | solution 1 for OAI.MainGap.limitRep_annihilates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:06:54.620565+00:00
-- url     : https://prove2.me/submissions/5b678ae5-6201-49b9-a4a4-24beaf96bedd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Representation.lean:L152-L172
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.limitRep_annihilates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Representation ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

section Ultra
variable {ι : Type*} (ω : Ultrafilter ι)

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
variable (f : ι → A →ₚ[ℂ] ℂ) (hf : ∀ i a, ‖f i a‖ ≤ ‖a‖)

lemma tendsto_ultraPositive (a : A) :
    Tendsto (fun i => f i a) (ω : Filter ι) (𝓝 (ultraPositive ω f hf a)) :=
  tendsto_ultraValue ω f hf a

lemma ultraPositive_eq_zero_of_tendsto {a : A}
    (ha : Tendsto (fun i => f i a) (ω : Filter ι) (𝓝 0)) :
    ultraPositive ω f hf a = 0 :=
  tendsto_nhds_unique (tendsto_ultraPositive ω f hf a) ha
end Ultra

section GNS
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

lemma gns_zero_of_sandwich (a : A)
    (ha : ∀ b : A, f (star (a * b) * (a * b)) = 0) :
    f.gnsNonUnitalStarAlgHom a = 0 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (f.gnsNonUnitalStarAlgHom a).continuous continuous_const
  | ih b =>
    rw [zero_apply, ← norm_eq_zero]
    rw [f.gnsNonUnitalStarAlgHom_apply_coe, UniformSpace.Completion.norm_coe]
    change ‖f.toPreGNS (a * f.ofPreGNS b)‖ = 0
    rw [f.preGNS_norm_def]
    simp only [f.ofPreGNS_toPreGNS, ha, Complex.zero_re, Real.sqrt_zero]

end GNS

section Vector
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

lemma vectorPositive_star_mul (a : A) :
    vectorPositive π ξ (star a * a) = (‖π a ξ‖ ^ 2 : ℝ) := by
  change ⟪ξ, π (star a * a) ξ⟫_ℂ = _
  rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl
end Vector

section LimitRep
variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (ω : Ultrafilter ι) (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
  (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)

lemma limitRep_annihilates (a : A)
    (ha : Tendsto (fun i => ‖π i a‖) (ω : Filter ι) (𝓝 0)) :
    limitRep ω π ξ hξ a = 0 := by
  change (limitFunctional ω π ξ hξ).gnsNonUnitalStarAlgHom a = 0
  apply gns_zero_of_sandwich
  intro b
  apply ultraPositive_eq_zero_of_tendsto
  have hh : Tendsto (fun i => ‖π i (a * b) (ξ i)‖) (ω : Filter ι) (𝓝 0) := by
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_)
      (show Tendsto (fun i => ‖π i a‖ * ‖b‖) (ω : Filter ι) (𝓝 0) by
        simpa using ha.mul_const ‖b‖)
    have hmul : ‖π i (a * b)‖ ≤ ‖π i a‖ * ‖b‖ := by
      rw [map_mul]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (NonUnitalStarAlgHom.norm_apply_le (π i) b) (norm_nonneg _))
    calc
      ‖π i (a * b) (ξ i)‖ ≤ ‖π i (a * b)‖ * ‖ξ i‖ := (π i (a * b)).le_opNorm _
      _ ≤ (‖π i a‖ * ‖b‖) * 1 := mul_le_mul hmul (hξ i) (norm_nonneg _) (by positivity)
      _ = ‖π i a‖ * ‖b‖ := mul_one _
  simpa only [vectorPositive_star_mul, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero]
    using (hh.pow 2).ofReal

end LimitRep
end MainGap

noncomputable section
open scoped Topology ComplexOrder InnerProductSpace
namespace MainGap

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : A)

end MainGap

end
end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.limitRep_annihilates := @_root_.OAI.MainGap.limitRep_annihilates
