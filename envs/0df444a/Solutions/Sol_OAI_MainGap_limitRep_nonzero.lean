-- Prove2me | solution 1 for OAI.MainGap.limitRep_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:08:19.034816+00:00
-- url     : https://prove2.me/submissions/b7dc7398-bb3d-4fac-9e03-a33469fd3b44

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Representation.lean:L174-L187
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.limitRep_nonzero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Theorems.Thm_OAI_MainGap_gnsStar_nonzero_of_value

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

end Ultra

section GNS
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

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

lemma limitFunctional_tendsto (a : A) :
    Tendsto (fun i => vectorPositive (π i) (ξ i) a) (ω : Filter ι)
      (𝓝 (limitFunctional ω π ξ hξ a)) := tendsto_ultraPositive _ _ _ _

lemma limitRep_nonzero (a : A) {δ : ℝ} (hδ : 0 < δ)
    (ha : ∀ᶠ i in (ω : Filter ι), δ ≤ ‖π i a (ξ i)‖) :
    limitRep ω π ξ hξ a ≠ 0 := by
  apply gnsStar_nonzero_of_value
  have hlim := (Complex.continuous_re.tendsto _).comp
    (limitFunctional_tendsto ω π ξ hξ (star a * a))
  have hle : δ ^ 2 ≤ (limitFunctional ω π ξ hξ (star a * a)).re := by
    apply ge_of_tendsto hlim
    filter_upwards [ha] with i hi
    simp only [Function.comp_apply, vectorPositive_star_mul, Complex.ofReal_re]
    exact pow_le_pow_left₀ hδ.le hi 2
  intro hf
  rw [hf, Complex.zero_re] at hle
  nlinarith [sq_pos_of_pos hδ]
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


theorem solution : type_of% @_root_.OAI.MainGap.limitRep_nonzero := @_root_.OAI.MainGap.limitRep_nonzero
