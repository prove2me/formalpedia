-- Prove2me | solution 1 for OAI.MainGap.exists_rep_killing_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:21:20.903865+00:00
-- url     : https://prove2.me/submissions/73084387-ad27-4c17-8042-70f0c5a69432

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealDetection.lean:L40-L113
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.exists_rep_killing_ideal. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_exists_norming_positive
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

end Vector

section LimitRep
variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (ω : Ultrafilter ι) (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
  (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealDetection ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma compressedPositive_norm (f : A →ₚ[ℂ] ℂ) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    {u : A} (hu : ‖u‖ ≤ 1) (a : A) : ‖compressedPositive f u a‖ ≤ ‖a‖ := by
  calc
    ‖compressedPositive f u a‖ ≤ ‖star u * a * u‖ := hf _
    _ ≤ ‖u‖ * ‖a‖ * ‖u‖ := by
      grw [norm_mul_le, norm_mul_le, norm_star]
    _ ≤ 1 * ‖a‖ * 1 := by gcongr
    _ = ‖a‖ := by ring

lemma compressedPositive_square (f : A →ₚ[ℂ] ℂ) (u a : A) :
    compressedPositive f u (star a * a) = f (star (a * u) * (a * u)) := by
  change f (star u * (star a * a) * u) = _
  simp only [star_mul, mul_assoc]

lemma norm_one_sub_positive_contraction {e : A} (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) :
    ‖1 - e‖ ≤ 1 := by
  have he1 : e ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg e he).mp hen
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1 - e) (sub_nonneg.mpr he1)).mpr
    (sub_le_self _ he)

lemma exists_rep_killing_ideal (J : NonUnitalStarSubalgebra ℂ A)
    (hJ : IsClosed (J : Set A))
    (hleft : ∀ a : A, ∀ z ∈ J, a * z ∈ J)
    (hright : ∀ a : A, ∀ z ∈ J, z * a ∈ J)
    {a : A} (ha : a ∉ J) :
    ∃ R : HilbertRep.{u,u} A, (∀ z ∈ J, R.hom z = 0) ∧ R.hom a ≠ 0 := by
  classical
  have : Nontrivial A := ⟨⟨a, 0, fun h => ha (h.symm ▸ J.zero_mem)⟩⟩
  have : CompleteSpace J := hJ.completeSpace_coe
  let : PartialOrder J := CStarAlgebra.spectralOrder J
  let : StarOrderedRing J := CStarAlgebra.spectralOrderedRing J
  have hau := CStarAlgebra.increasingApproximateUnit J
  let I := {e : J // @LE.le J (CStarAlgebra.spectralOrder J).toLE 0 e ∧ ‖e‖ ≤ 1}
  let F : Filter I := Filter.comap Subtype.val (CStarAlgebra.approximateUnit J)
  have : F.NeBot := Filter.NeBot.comap_of_range_mem inferInstance (by
    filter_upwards [hau.eventually_nonneg.and hau.eventually_norm] with e he
    exact ⟨⟨e, he⟩, rfl⟩)
  let ω := Ultrafilter.of F
  have hω : (ω : Filter I) ≤ F := Ultrafilter.of_le F
  have hunit (z : J) : Tendsto (fun e : I => (z : A) * (1 - (e.val : A)))
      (ω : Filter I) (𝓝 0) := by
    have hh := (continuous_subtype_val.tendsto z).comp
      (hau.tendsto_mul_left z |>.comp (Filter.tendsto_comap.mono_left hω))
    have hz := (tendsto_const_nhds (x := (z : A))).sub hh
    convert hz using 1 <;> simp only [mul_sub, mul_one, sub_self]
    rfl
  have hadef : a ∉ closure (J : Set A) := by rwa [hJ.closure_eq]
  rw [Metric.mem_closure_iff] at hadef
  push Not at hadef
  obtain ⟨r, hr, hdist⟩ := hadef
  have hlower (e : I) : r ≤ ‖a * (1 - (e.val : A))‖ := by
    have hh := hdist (a * (e.val : A)) (hleft a _ e.val.property)
    simpa only [dist_eq_norm, mul_sub, mul_one] using hh
  have hen (e : I) : ‖1 - (e.val : A)‖ ≤ 1 := by
    apply norm_one_sub_positive_contraction
    · obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp e.property.1
      have hm := congrArg (fun z : J => (z : A)) hb
      change (e.val : A) = star (b : A) * (b : A) at hm
      rw [hm]
      exact star_mul_self_nonneg _
    · exact e.property.2
  have hex (e : I) := exists_norming_positive (A := A)
    (star_mul_self_nonneg (a * (1 - (e.val : A))))
  choose f hf hfa using hex
  let g (e : I) := compressedPositive (f e) (1 - (e.val : A))
  have hg (e : I) (z : A) : ‖g e z‖ ≤ ‖z‖ := compressedPositive_norm (f e) (hf e) (hen e) z
  let L := ultraPositive ω g hg
  have hL (z : A) (hz : z ∈ J) : L.gnsStarAlgHom z = 0 := by
    change L.gnsNonUnitalStarAlgHom z = 0
    apply gns_zero_of_sandwich
    intro b
    apply ultraPositive_eq_zero_of_tendsto
    have hlim := (hunit ⟨z * b, hright b z hz⟩).norm
    apply squeeze_zero_norm (fun e => ?_) (by simpa only [norm_zero, mul_zero] using hlim.mul hlim)
    calc
      ‖g e (star (z * b) * (z * b))‖ =
          ‖f e (star ((z * b) * (1 - (e.val : A))) * ((z * b) * (1 - (e.val : A))))‖ := by
        change ‖compressedPositive (f e) (1 - (e.val : A)) (star (z * b) * (z * b))‖ = _
        rw [compressedPositive_square]
      _ ≤ ‖star ((z * b) * (1 - (e.val : A))) * ((z * b) * (1 - (e.val : A)))‖ := hf e _
      _ = _ := CStarRing.norm_star_mul_self
  have hnon : L (star a * a) ≠ 0 := by
    have hv (e : I) : g e (star a * a) = (‖a * (1 - (e.val : A))‖ ^ 2 : ℝ) := by
      change compressedPositive (f e) (1 - (e.val : A)) (star a * a) = _
      rw [compressedPositive_square, hfa e, CStarRing.norm_star_mul_self, pow_two]
    have hb : (r ^ 2 : ℂ) ≤ L (star a * a) :=
      ge_of_tendsto' (tendsto_ultraPositive ω g hg _) (fun e => by
        rw [hv e]
        exact_mod_cast pow_le_pow_left₀ hr.le (hlower e) 2)
    intro heq
    rw [heq] at hb
    have : r ^ 2 ≤ 0 := by exact_mod_cast hb
    nlinarith
  exact ⟨⟨L.GNS, L.gnsStarAlgHom⟩, hL, gnsStar_nonzero_of_value L a hnon⟩
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.idealDetectionOrder
attribute [local instance] OAI.MainGap.idealDetectionStarOrder
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution.{u} : type_of% @_root_.OAI.MainGap.exists_rep_killing_ideal.{u} := @_root_.OAI.MainGap.exists_rep_killing_ideal.{u}
