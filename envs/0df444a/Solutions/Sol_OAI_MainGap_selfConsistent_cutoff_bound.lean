-- Prove2me | solution 1 for OAI.MainGap.selfConsistent_cutoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:31:58.239111+00:00
-- url     : https://prove2.me/submissions/7d9cd678-4249-4a07-9a36-f49da4ebb09a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean:L305-L340
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.selfConsistent_cutoff_bound. The node keeps its source
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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_sandwich {h k : A} (hk : k ∈ Her h) (a : A) : k * a * star k ∈ Her h := by
  let k' : Her h := ⟨k, hk⟩
  change (k' : A) * a * star (k' : A) ∈ Her h
  refine (sandwichMap_dense h).induction_on k'
    ((isClosed_Her h).preimage (by fun_prop)) ?_
  intro b
  change (h * b * star h) * a * star (h * b * star h) ∈ Her h
  convert sandwich_mem_Her h (b * star h * a * h * star b) using 1
  simp only [star_mul, star_star, mul_assoc]

lemma Her_mono_of_mem {h k : A} (hk : k ∈ Her h) : Her k ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  exact Her_sandwich hk a

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma mul_star_mem_Her (h : A) : h * star h ∈ Her h := by
  apply (isClosed_Her h).mem_of_tendsto
    (((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const (star h))
  exact Filter.Eventually.of_forall (sandwich_mem_Her h)

lemma self_mem_Her {h : A} (hh : 0 ≤ h) : h ∈ Her h := by
  have hm : h * h ∈ Her h := by
    simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using mul_star_mem_Her h
  simpa only [CFC.sqrt_mul_self h hh] using
    sqrt_mem_Her hm (by simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using
      star_mul_self_nonneg h)

lemma cut_mem_Her {d : A} (hd : 0 ≤ d) (ε : ℝ) : cut d ε ∈ Her d := by
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her hd)

end Order

end MainGap

end

end OAI

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

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_fixed_left {h t : A} (ht : t * h = h) {k : A} (hk : k ∈ Her h) : t * k = k := by
  have hc : IsClosed {k : A | t * k = k} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change t * (h * a * star h) = h * a * star h
  simp only [← mul_assoc, ht]

lemma positive_kernel_factor [PartialOrder A] [StarOrderedRing A] {x Q z : A} (hx : 0 ≤ x) (hQ : IsSelfAdjoint Q)
    (hz : Q * (x * Q * z) = 0) : x * Q * z = 0 := by
  let s := CFC.sqrt x
  have hs : IsSelfAdjoint s := .of_nonneg (CFC.sqrt_nonneg x)
  have hss : s * s = x := CFC.sqrt_mul_sqrt_self x hx
  have hzero : star (s * Q * z) * (s * Q * z) = 0 := by
    rw [star_mul, star_mul, hs.star_eq, hQ.star_eq]
    calc
      star z * (Q * s) * (s * Q * z) = star z * (Q * ((s * s) * Q * z)) := by noncomm_ring
      _ = 0 := by rw [hss, hz, mul_zero]
  have hz' := (CStarRing.star_mul_self_eq_zero_iff _).mp hzero
  rw [← hss, mul_assoc s s, mul_assoc s, hz', mul_zero]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma cut_eq_cfc (d : B) {ε : ℝ} (hε : 0 ≤ ε) :
    cut d ε = cfc (fun t : ℝ => max (t - ε) 0) d := by
  unfold cut
  apply cfcₙ_eq_cfc
  · exact ((continuous_id.sub continuous_const).max continuous_const).continuousOn
  · simp [max_eq_right (neg_nonpos.mpr hε)]

lemma continuous_reciprocalCutoff {η : ℝ} (hη : 0 < η) :
    Continuous (fun t : ℝ => (max t η)⁻¹) := by
  apply Continuous.inv₀ (continuous_id.max continuous_const)
  intro t
  exact ne_of_gt (hη.trans_le (le_max_right t η))

omit [PartialOrder B] [StarOrderedRing B] in
lemma cutoffHer_factor {x Q : B} (hx : IsSelfAdjoint x) (hQ : IsSelfAdjoint Q)
    {η : ℝ} (hη : 0 < η) {k : B} (hk : k ∈ Her (cut (x * Q * Q * x) η)) :
    ∃ z : B, k = x * Q * z := by
  let U := x * Q * Q * x
  let f : ℝ → ℝ := fun t => (max t η)⁻¹
  have hU : IsSelfAdjoint U := by
    change star (x * Q * Q * x) = x * Q * Q * x
    simp only [star_mul, hx.star_eq, hQ.star_eq]
    noncomm_ring
  have hf : Continuous f := continuous_reciprocalCutoff hη
  have hg : Continuous (fun t : ℝ => max (t - η) 0) :=
    (continuous_id.sub continuous_const).max continuous_const
  have hfix : (U * cfc f U) * cut U η = cut U η := by
    rw [cut_eq_cfc U hη.le]
    conv_lhs => lhs; lhs; rw [← cfc_id ℝ U hU]
    rw [← cfc_mul _ _ U continuousOn_id hf.continuousOn]
    simp only [id_eq]
    have hif : ContinuousOn (fun t : ℝ => t * f t) (spectrum ℝ U) := (continuous_id.mul hf).continuousOn
    rw [← cfc_mul _ _ U hif hg.continuousOn]
    apply cfc_congr
    intro t _
    dsimp only
    by_cases ht : η ≤ t
    · simp only [f, max_eq_left ht, mul_inv_cancel₀ (ne_of_gt (hη.trans_le ht)), one_mul]
    · rw [max_eq_right (by linarith : t - η ≤ 0), mul_zero]
  have hfixk := Her_fixed_left hfix hk
  refine ⟨Q * x * cfc f U * k, ?_⟩
  calc
    k = (U * cfc f U) * k := hfixk.symm
    _ = x * Q * (Q * x * cfc f U * k) := by dsimp [U]; noncomm_ring

lemma selfConsistent_cutoff_bound {x d : B} (hx : 0 ≤ x) (hd : 0 ≤ d)
    {η h : ℝ} (hη : 0 < η) (hh : 0 ≤ h)
    (hmem : d ∈ Her (cut (x * cfc (fun t : ℝ => max (h - t) 0) d *
      cfc (fun t : ℝ => max (h - t) 0) d * x) η)) :
    d ≤ h • (1 : B) := by
  let Q := cfc (fun t : ℝ => max (h - t) 0) d
  have hQ : IsSelfAdjoint Q := IsSelfAdjoint.cfc
  have hq : Continuous (fun t : ℝ => max (h - t) 0) :=
    (continuous_const.sub continuous_id).max continuous_const
  have hk : Continuous (fun t : ℝ => max (t - h) 0) :=
    (continuous_id.sub continuous_const).max continuous_const
  have hkill : Q * cut d h = 0 := by
    rw [cut_eq_cfc d hh]
    change cfc (fun t : ℝ => max (h-t) 0) d * cfc (fun t : ℝ => max (t-h) 0) d = 0
    rw [← cfc_mul _ _ d hq.continuousOn hk.continuousOn, ← cfc_zero d (R := ℝ)]
    apply cfc_congr
    intro t _
    by_cases ht : h ≤ t
    · simp [max_eq_right (by linarith : h - t ≤ 0)]
    · simp [max_eq_right (by linarith : t - h ≤ 0)]
  have hcutmem : cut d h ∈ Her (cut (x * Q * Q * x) η) :=
    Her_mono_of_mem hmem (cut_mem_Her hd h)
  obtain ⟨z, hz⟩ := cutoffHer_factor (.of_nonneg hx) hQ hη hcutmem
  have hcutzero : cut d h = 0 := by
    rw [hz]
    exact positive_kernel_factor hx hQ (by rwa [← hz])
  rw [cut_eq_cfc d hh, ← cfc_zero d (R := ℝ)] at hcutzero
  have hzspec := eqOn_of_cfc_eq_cfc (ha := IsSelfAdjoint.of_nonneg hd) hcutzero
  rw [← Algebra.algebraMap_eq_smul_one, ← cfc_const h d]
  conv_lhs => rw [← cfc_id ℝ d (.of_nonneg hd)]
  apply (cfc_le_iff _ _ d continuousOn_id continuousOn_const (.of_nonneg hd)).mpr
  intro t ht
  have hm : max (t - h) 0 = 0 := hzspec ht
  have := le_max_left (t - h) 0
  dsimp only [id_eq]
  linarith

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.selfConsistent_cutoff_bound := @_root_.OAI.MainGap.selfConsistent_cutoff_bound
