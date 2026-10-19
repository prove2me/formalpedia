-- Prove2me | solution 1 for OAI.MainGap.individual_to_strong
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:36:23.668722+00:00
-- url     : https://prove2.me/submissions/b95d172d-5151-4bae-a7f6-d56d36d6e862

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Diagonalization.lean:L66-L94
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.individual_to_strong. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Diagonalization
import Theorems.Thm_OAI_MainGap_HerCompression_right_products
import Theorems.Thm_OAI_MainGap_iterated_separation
import Theorems.Thm_OAI_MainGap_signal_coefficient

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

lemma rampFn_nonneg {l u t : ℝ} (hlu : l ≤ u) : 0 ≤ rampFn l u t :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) (sub_nonneg.mpr hlu))

lemma rampFn_le_one (l u t : ℝ) : rampFn l u t ≤ 1 := min_le_left _ _

lemma ramp_nonneg (a : A) {l u : ℝ} (hlu : l ≤ u) : 0 ≤ ramp a l u :=
  cfcₙ_nonneg (fun _ _ => rampFn_nonneg hlu)

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_ramp_le_one (a : A) {l u : ℝ} (hlu : l ≤ u) : ‖ramp a l u‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  rw [Real.norm_eq_abs, abs_of_nonneg (rampFn_nonneg hlu)]
  exact rampFn_le_one _ _ _

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Diagonalization ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.boundedDiagonalizationPartialOrder
attribute [local instance] OAI.MainGap.boundedDiagonalizationStarOrderedRing
theorem bounded_diagonalization (hP : PropertyP A) {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (han : ‖a‖ ≤ 1) (hbn : ‖b‖ ≤ 1) (c : A) {δ ρ ζ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1/2) (hρ : 0 < ρ) (hρδ : ρ ≤ 2*δ) (hζ : 0 < ζ) :
    ∃ s t : A, ‖star s*a*s-a‖ < 2*δ+ρ ∧ ‖star t*b*t-b‖ < 2*δ+ρ ∧
      ‖star s*c*t‖ < ζ ∧ ‖s‖ ≤ Real.sqrt δ⁻¹ ∧ ‖t‖ ≤ Real.sqrt δ⁻¹ := by
  let M := max 1 ‖c‖
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hcn : ‖M⁻¹ • c‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
    calc M⁻¹ * ‖c‖ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hM.le)
         _ = 1 := inv_mul_cancel₀ hM.ne'
  obtain ⟨p,q,κ,hp0,hpn,hpH,hq0,hqn,hqH,hκ0,hκζ,hcomp,hps,hqs⟩ :=
    iterated_separation hP (ramp_nonneg a (by linarith : δ ≤ 2*δ))
      (norm_ramp_le_one a (by linarith : δ ≤ 2*δ))
      (ramp_nonneg b (by linarith : δ ≤ 2*δ))
      (norm_ramp_le_one b (by linarith : δ ≤ 2*δ)) hcn
      (by positivity : 0 < δ*ζ/M)
  obtain ⟨w,hw,hsn⟩ := signal_coefficient hP ha han hδ hδhalf hρ hρδ hpH hps
  obtain ⟨z,hz,htn⟩ := signal_coefficient hP hb hbn hδ hδhalf hρ hρδ hqH hqs
  refine ⟨p*w,q*z,hw,hz,?_,hsn,htn⟩
  have hc : HerCompression p q c (M*κ) := by
    intro x hx y hy
    have hh := hcomp x hx y hy
    rw [mul_smul_comm, smul_mul_assoc, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hM)] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hM.le
    calc ‖x*c*y‖ = M * (M⁻¹ * ‖x*c*y‖) := by rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]
         _ ≤ M*(κ*‖x‖*‖y‖) := hh'
         _ = (M*κ)*‖x‖*‖y‖ := by ring
  have hprod : ‖p*w‖*‖q*z‖ ≤ δ⁻¹ := by
    calc ‖p*w‖*‖q*z‖ ≤ Real.sqrt δ⁻¹ * Real.sqrt δ⁻¹ :=
            mul_le_mul hsn htn (norm_nonneg _) (Real.sqrt_nonneg _)
         _ = δ⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr hδ.le)
  calc
    ‖star (p*w)*c*(q*z)‖ ≤ (M*κ)*‖p*w‖*‖q*z‖ :=
      HerCompression.right_products (mul_nonneg hM.le hκ0) hp0 hq0 hc w z
    _ = (M*κ)*(‖p*w‖*‖q*z‖) := by ring
    _ ≤ (M*κ)*δ⁻¹ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hM.le hκ0)
    _ < ζ := by
      rw [← div_eq_mul_inv]
      apply (div_lt_iff₀ hδ).mpr
      have hh := (lt_div_iff₀ hM).mp hκζ
      nlinarith

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.diagonalizationPartialOrder
attribute [local instance] OAI.MainGap.diagonalizationStarOrderedRing
theorem individual_to_strong (hP : PropertyP A) : UnrestrictedDiagonalization A := by
  intro a b ha hb c ε hε
  let M := max 1 (max ‖a‖ ‖b‖)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have haM : ‖a‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hbM : ‖b‖ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  let δ := min (1/4 : ℝ) (ε/(8*M))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hM))
  have hδhalf : δ < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  have hsmall : M*(2*δ+δ) < ε := by
    have hh : δ ≤ ε/(8*M) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 8*M)).mp hh
    nlinarith
  have hn {x : A} (hx : ‖x‖ ≤ M) : ‖M⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
    calc M⁻¹*‖x‖ ≤ M⁻¹*M := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hM.le)
         _ = 1 := inv_mul_cancel₀ hM.ne'
  obtain ⟨s,t,hs,ht,hc,hsn,htn⟩ := bounded_diagonalization hP
    (smul_nonneg (inv_nonneg.mpr hM.le) ha) (smul_nonneg (inv_nonneg.mpr hM.le) hb)
    (hn haM) (hn hbM) c hδ hδhalf hδ (by linarith : δ ≤ 2*δ) hε
  have hscale (x r : A) : M • (star r*(M⁻¹ • x)*r-(M⁻¹ • x)) = star r*x*r-x := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul,
      mul_inv_cancel₀ hM.ne', one_smul]
  refine ⟨s,t,?_,?_,hc⟩
  · rw [← hscale a s, norm_smul, Real.norm_eq_abs, abs_of_pos hM]
    exact (mul_lt_mul_of_pos_left hs hM).trans hsmall
  · rw [← hscale b t, norm_smul, Real.norm_eq_abs, abs_of_pos hM]
    exact (mul_lt_mul_of_pos_left ht hM).trans hsmall

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.diagonalizationPartialOrder
attribute [local instance] OAI.MainGap.diagonalizationStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.individual_to_strong := @_root_.OAI.MainGap.individual_to_strong
