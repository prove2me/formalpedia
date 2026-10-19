-- Prove2me | solution 1 for OAI.PettyProjection.petty_projection_volume
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:13:45.912636+00:00
-- url     : https://prove2.me/submissions/937cd640-a331-41e4-a7e7-91674e5a48d2

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000
import Theorems.Thm_OAI_PettyProjection_measure_bilinear
import Theorems.Thm_OAI_PettyProjection_minkowski_first_inequality_euclidean

section
-- module Solutions.OAIQW_PettyProjection.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
namespace OAI.PettyProjection
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
end OAI.PettyProjection
end

section
-- module Solutions.OAIQW_PettyProjection.Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection

lemma support_minkowski {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hLn : L.Nonempty)
    (u : Space n) : support (K+L) u = support K u+support L u := by
  apply le_antisymm
  · apply (support_le_iff (hK.add hL) (hKn.add hLn)).mpr
    rintro _ ⟨x,hx,y,hy,rfl⟩
    rw [inner_add_right]
    exact add_le_add (inner_le_support hK hx u) (inner_le_support hL hy u)
  · obtain ⟨x,hx,hxe⟩ := support_attained hK hKn u
    obtain ⟨y,hy,hye⟩ := support_attained hL hLn u
    rw [hxe,hye,← inner_add_right]
    exact inner_le_support (hK.add hL) (add_mem_add hx hy) u

lemma support_linear_image {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (T : Space n →L[ℝ] Space n) (u : Space n) :
    support (T '' K) u = support K (T.adjoint u) := by
  apply le_antisymm
  · apply (support_le_iff (hK.image T.continuous) (hKn.image T)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support hK hx _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn (T.adjoint u)
    rw [he,ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support (hK.image T.continuous) (mem_image_of_mem T hx) u

lemma support_eq_iff {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hKn : K.Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hLn : L.Nonempty) :
    support K = support L ↔ K = L := by
  constructor
  · intro h
    ext x
    rw [mem_iff_inner_le_support hK hcK hKn,mem_iff_inner_le_support hL hcL hLn,h]
  · rintro rfl; rfl

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.NormCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma wulff_closed {n : ℕ} (s : Sphere n → ℝ) : IsClosed (wulff s) := by
  unfold wulff
  rw [ofPred_forall]
  exact isClosed_iInter (fun _ => isClosed_le (by fun_prop) continuous_const)

lemma wulff_convex {n : ℕ} (s : Sphere n → ℝ) : Convex ℝ (wulff s) := by
  intro x hx y hy a b ha hb hab u
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
  calc
    _ ≤ a*s u+b*s u := add_le_add (mul_le_mul_of_nonneg_left (hx u) ha)
      (mul_le_mul_of_nonneg_left (hy u) hb)
    _ = s u := by rw [← add_mul,hab,one_mul]

lemma closedBall_subset_wulff {n : ℕ} {s : Sphere n → ℝ} {r : ℝ}
    (hr : ∀ u, r ≤ s u) : closedBall (0 : Space n) r ⊆ wulff s := by
  intro x hx u
  calc
    _ ≤ ‖(u : Space n)‖*‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [norm_coe,one_mul]
    _ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
    _ ≤ s u := hr u

lemma wulff_subset_closedBall {n : ℕ} {s : Sphere n → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ u, s u ≤ R) : wulff s ⊆ closedBall (0 : Space n) R := by
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_cases h : x = 0
  · simpa [h] using hR
  · let u : Sphere n := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩
    have hu : ⟪(u : Space n),x⟫ = ‖x‖ := by
      dsimp only [u]
      rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
      field_simp
    exact hu ▸ (hx u).trans (hs u)

lemma positive_constraint_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ u, m ≤ s u ∧ s u ≤ M := by
  have hne : (univ : Set (Sphere n)).Nonempty := by
    obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
    exact ⟨⟨u,hu⟩,mem_univ _⟩
  obtain ⟨u,_,hu⟩ := isCompact_univ.exists_isMinOn hne s.continuous.continuousOn
  obtain ⟨v,_,hv⟩ := isCompact_univ.exists_isMaxOn hne s.continuous.continuousOn
  exact ⟨s u,s v,hs u,hs v,fun w => ⟨hu (mem_univ w),hv (mem_univ w)⟩⟩

lemma wulff_nhds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulff s ∈ 𝓝 (0 : Space n) := by
  obtain ⟨m,M,hm,_,hb⟩ := positive_constraint_bounds s hs
  exact Metric.mem_nhds_iff.mpr ⟨m,hm,ball_subset_closedBall.trans
    (closedBall_subset_wulff (fun u => (hb u).1))⟩

lemma wulff_compact {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulff s) := by
  obtain ⟨m,M,_,hM,hb⟩ := positive_constraint_bounds s hs
  exact (isCompact_closedBall (0 : Space n) M).of_isClosed_subset (wulff_closed _)
    (wulff_subset_closedBall hM.le (fun u => (hb u).2))

lemma wulff_body {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsConvexBody (wulff s) :=
  ⟨wulff_compact s hs,wulff_convex s,⟨0,mem_interior_iff_mem_nhds.mpr (wulff_nhds s hs)⟩⟩

lemma gauge_ae_differentiable_sphere {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    ∀ᵐ (u : Sphere n) ∂Spherical.sigma n, DifferentiableAt ℝ (gauge K) (u : Space n) := by
  obtain ⟨C,hC⟩ := hc.lipschitz_gauge h0
  apply Spherical.sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hh : DifferentiableAt ℝ (fun x : Space n => r⁻¹ * gauge K (r • x)) (u : Space n) :=
    (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_mul r⁻¹
  have he : (fun x : Space n => r⁻¹ * gauge K (r • x)) = gauge K := by
    funext x
    rw [gauge_smul_of_nonneg (α := ℝ) hr.le,smul_eq_mul,← mul_assoc,
      inv_mul_cancel₀ hr.ne',one_mul]
  rwa [he] at hh

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.WulffVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uU

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma support_gradient_of_active {n : ℕ} {C : Set (Space n)}
    (hC : IsCompact C) {x y : Space n} (hy : y ∈ C)
    (hxy : support C x = ⟪x,y⟫)
    (hd : DifferentiableAt ℝ (support C) x) : ∇ (support C) x = y := by
  let l : Space n →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Space n) y
  have he (z : Space n) : l z = ⟪z,y⟫ := by
    change ⟪y,z⟫ = ⟪z,y⟫
    exact real_inner_comm z y
  have hl : IsLocalMin (fun z => support C z-l z) x := by
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [he,he,hxy,sub_self]
    exact sub_nonneg.mpr (inner_le_support hC hy z)
  have hz := hl.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub l.hasFDerivAt)
  have hd' : fderiv ℝ (support C) x = l := sub_eq_zero.mp hz
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,hd',he]
  exact real_inner_comm _ _

lemma wulff_gradient_of_active {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} {u : Sphere n}
    (hu : wulffMax s x = ⟪x,(u : Space n)⟫ / s u)
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    ∇ (gauge (wulff s)) x = (s u)⁻¹ • (u : Space n) := by
  have he : gauge (wulff s) = support (wulffCoefficients s) :=
    funext (gauge_wulff_eq_max s hs)
  rw [he] at hd ⊢
  apply support_gradient_of_active (wulffCoefficients_compact s hs) (mem_range_self u) _ hd
  simpa only [real_inner_smul_right,div_eq_inv_mul,wulffMax] using hu

lemma wulff_active_unique {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x)
    {u v : Sphere n} (hu : wulffMax s x = ⟪x,(u : Space n)⟫/s u)
    (hv : wulffMax s x = ⟪x,(v : Space n)⟫/s v) : u = v := by
  have he := (wulff_gradient_of_active s hs hu hd).symm.trans (wulff_gradient_of_active s hs hv hd)
  have hn := congrArg norm he
  simp only [norm_smul,norm_coe,mul_one,Real.norm_eq_abs,abs_inv,abs_of_pos (hs u),
    abs_of_pos (hs v)] at hn
  have hsuv : s u = s v := inv_injective hn
  apply Subtype.ext
  rw [hsuv] at he
  exact (smul_right_injective _ (inv_ne_zero (hs v).ne')) he

end PettyProjection
end

noncomputable section
open Set Filter Topology
namespace PettyProjection

/-- Convergence of maximizers at a unique maximum, with a compact parameter
space and joint continuity only at the limiting parameter. -/
lemma selected_max_tendsto {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f : ℝ → U → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u ≤ f t (a t))
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀) :
    Tendsto a (𝓝 0) (𝓝 u₀) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro u hu'
  obtain ⟨l,hl,hat⟩ := mapClusterPt_iff_ultrafilter.mp hu'
  apply hu
  intro v
  have ht : Tendsto (fun t : ℝ => t) (l : Filter ℝ) (𝓝 0) := hl
  have hv : Tendsto (fun t => f t v) (l : Filter ℝ) (𝓝 (f 0 v)) :=
    (hc v).tendsto.comp (ht.prodMk_nhds tendsto_const_nhds)
  have hav : Tendsto (fun t => f t (a t)) (l : Filter ℝ) (𝓝 (f 0 u)) :=
    (hc u).tendsto.comp (ht.prodMk_nhds hat)
  exact le_of_tendsto_of_tendsto hv hav (hl (hm.mono (fun t h => h v)))

lemma quotient_bounds {a b z t : ℝ} (ht : t ≠ 0) (hl : t*a ≤ z) (hh : z ≤ t*b) :
    min a b ≤ z/t ∧ z/t ≤ max a b := by
  have he : z/t*t = z := div_mul_cancel₀ z ht
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hb : b ≤ z/t := by nlinarith
    have ha : z/t ≤ a := by nlinarith
    exact ⟨(min_le_right a b).trans hb,ha.trans (le_max_left a b)⟩
  · have ha : a ≤ z/t := by nlinarith
    have hb : z/t ≤ b := by nlinarith
    exact ⟨(min_le_left a b).trans ha,hb.trans (le_max_right a b)⟩

/-- Envelope differentiation from an exact continuous difference quotient.
The statement does not require a smooth boundary or a smooth maximizer. -/
lemma hasDerivAt_selected_max {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f d : ℝ → U → ℝ} {q : ℝ → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hd : ContinuousAt (fun p : ℝ × U => d p.1 p.2) (0,u₀))
    (hq : ∀ᶠ t in 𝓝 (0 : ℝ), q t = f t (a t) ∧ ∀ u, f t u ≤ q t)
    (hq₀ : q 0 = f 0 u₀) (hm₀ : ∀ u, f 0 u ≤ q 0)
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀)
    (he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u) :
    HasDerivAt q (d 0 u₀) 0 := by
  have ha : Tendsto a (𝓝 0) (𝓝 u₀) := selected_max_tendsto hc
    (hq.mono (fun t h u => h.1 ▸ h.2 u)) hu
  have hd₀ : Tendsto (fun t => d t u₀) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds tendsto_const_nhds)
  have hda : Tendsto (fun t => d t (a t)) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds ha)
  have hlo : Tendsto (fun t => min (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [min_self] using hd₀.min hda
  have hhi : Tendsto (fun t => max (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [max_self] using hd₀.max hda
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,smul_eq_mul,← div_eq_inv_mul]
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), min (d t u₀) (d t (a t)) ≤ (q t-q 0)/t ∧
      (q t-q 0)/t ≤ max (d t u₀) (d t (a t)) := by
    filter_upwards [hq.filter_mono nhdsWithin_le_nhds,he.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht he ht0
    have htn : t ≠ 0 := ht0
    have hl : t*d t u₀ ≤ q t-q 0 := by
      rw [← he u₀,hq₀]
      exact sub_le_sub_right (ht.2 u₀) _
    have hh : q t-q 0 ≤ t*d t (a t) := by
      rw [← he (a t),ht.1]
      exact sub_le_sub_left (hm₀ (a t)) _
    exact quotient_bounds htn hl hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hlo.mono_left nhdsWithin_le_nhds) (hhi.mono_left nhdsWithin_le_nhds)
    (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma positive_constraints_eventually {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M) := by
  obtain ⟨a,b,ha,hb,hab⟩ := positive_constraint_bounds s hs
  refine ⟨a/2,b+a/2,by positivity,by positivity,?_⟩
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| *(‖φ‖+1) < a/2 := by
    have h : Tendsto (fun t : ℝ => |t| *(‖φ‖+1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const (‖φ‖+1)
    exact h.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [ht] with t ht u
  have hφ : |φ u| ≤ ‖φ‖ := φ.norm_coe_le_norm u
  have hbound : |t*φ u| ≤ |t| *(‖φ‖+1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hφ.trans (by linarith)) (abs_nonneg _)
  have hlo := neg_abs_le (t*φ u)
  have hhi := le_abs_self (t*φ u)
  have hh := hab u
  change a/2 ≤ s u+t*φ u ∧ s u+t*φ u ≤ b+a/2
  constructor <;> linarith

lemma positive_constraints_nhds {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, 0 < (s+t • φ) u := by
  obtain ⟨m,M,hm,_,he⟩ := positive_constraints_eventually s φ hs
  exact he.mono (fun _ h u => hm.trans_le (h u).1)

lemma wulff_derivative_active {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) {x : Space n}
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) {u₀ : Sphere n}
    (hu₀ : wulffMax s x = ⟪x,(u₀ : Space n)⟫/s u₀) :
    HasDerivAt (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) x)
      (-(gauge (wulff s) x)*φ u₀/s u₀) 0 := by
  classical
  let f : ℝ → Sphere n → ℝ := fun t u => ⟪x,(u : Space n)⟫/(s u+t*φ u)
  let d : ℝ → Sphere n → ℝ := fun t u => -(⟪x,(u : Space n)⟫*φ u)/(s u*(s u+t*φ u))
  let a : ℝ → Sphere n := fun t => if hp : ∀ u, 0 < (s+t • φ) u then
    (wulffMax_attained (s+t • φ) hp x).choose else u₀
  have hpos := positive_constraints_nhds s φ hs
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), gauge (wulff ⇑(s+t • φ)) x = f t (a t) ∧
      ∀ u, f t u ≤ gauge (wulff ⇑(s+t • φ)) x := by
    filter_upwards [hpos] with t ht
    rw [gauge_wulff_eq_max (s+t • φ) ht]
    constructor
    · dsimp only [a]
      rw [dite_eq_left ht]
      exact (wulffMax_attained (s+t • φ) ht x).choose_spec
    · intro u; exact le_wulffMax (s+t • φ) ht x u
  have hq0 : gauge (wulff (s+(0:ℝ) • φ)) x = f 0 u₀ := by
    simpa only [zero_smul,add_zero,f,zero_mul] using (gauge_wulff_eq_max s hs x).trans hu₀
  have hm0 : ∀ u, f 0 u ≤ gauge (wulff (s+(0:ℝ) • φ)) x := by
    intro u
    simpa only [zero_smul,add_zero,f,zero_mul,gauge_wulff_eq_max s hs x] using le_wulffMax s hs x u
  have hc (u : Sphere n) : ContinuousAt (fun p : ℝ × Sphere n => f p.1 p.2) (0,u) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using (hs u).ne'
  have hdc : ContinuousAt (fun p : ℝ × Sphere n => d p.1 p.2) (0,u₀) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using mul_ne_zero (hs u₀).ne' (hs u₀).ne'
  have hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀ := by
    intro u h
    apply wulff_active_unique s hs hd _ hu₀
    apply le_antisymm
    · simpa only [f,zero_mul,add_zero,← hu₀] using h u₀
    · exact le_wulffMax s hs x u
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u := by
    filter_upwards [hpos] with t ht u
    have hst : s u+t*φ u ≠ 0 := (ht u).ne'
    dsimp only [f,d]
    simp only [zero_mul,add_zero]
    field_simp [hst,(hs u).ne']
    ring
  have h := hasDerivAt_selected_max hc hdc hq hq0 hm0 hu he
  have he0 : d 0 u₀ = -(gauge (wulff s) x)*φ u₀/s u₀ := by
    rw [gauge_wulff_eq_max s hs x,hu₀]
    dsimp [d]
    ring
  rwa [he0] at h

/-- Wulff variation against an actual continuous positively homogeneous test.
No symmetry or boundary smoothness is assumed. -/
theorem wulff_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ), 0 < a → ∀ x, φ (a • x) = a*φ x)
    {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    HasDerivAt (fun t : ℝ => gauge (wulff (s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) x)
      (-(gauge (wulff s) x)*φ (∇ (gauge (wulff s)) x)) 0 := by
  obtain ⟨u,hu⟩ := wulffMax_attained s hs x
  have he := wulff_gradient_of_active s hs hu hd
  have h := wulff_derivative_active s ⟨fun u : Sphere n => φ u,hφ.comp continuous_subtype_val⟩ hs hd hu
  rw [he,hh _ (inv_pos.mpr (hs u))]
  convert h using 1
  dsimp
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma surface_real_univ (n : ℕ) [NeZero n] : (surface n).real univ = n*kappa n := by
  rw [surface,Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  exact congrArg ENNReal.toReal (Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : Space n) (1:ℝ)).symm

/-- Polar integration of an arbitrary convex neighborhood of zero; the body
need not be symmetric or have a smooth boundary. -/
lemma gauge_volume_lintegral {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume K = ∫⁻ u : Sphere n, ENNReal.ofReal ((gauge K (u : Space n))⁻¹ ^ n / n)
      ∂surface n := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  let A : Set ({0}ᶜ : Set (Space n)) := Subtype.val ⁻¹' interior K
  let S : Set (Sphere n × Ioi (0:ℝ)) :=
    {z | z.2.1 < (gauge K (z.1 : Space n))⁻¹}
  have hA : MeasurableSet A := isOpen_interior.measurableSet.preimage measurable_subtype_coe
  have hS : MeasurableSet S := by
    apply isOpen_lt (by fun_prop) ?_ |>.measurableSet
    exact ((continuous_gauge hc h0).comp (continuous_subtype_val.comp continuous_fst)).inv₀
      (fun z => (hp z.1).ne')
  have he : (homeomorphUnitSphereProd (Space n)).symm ⁻¹' A = S := by
    ext z
    change (↑((homeomorphUnitSphereProd (Space n)).symm z) : Space n) ∈ interior K ↔ _
    rw [homeomorphUnitSphereProd_symm_apply_coe,← gauge_lt_one_iff_mem_interior hc h0,
      gauge_smul_of_nonneg (α := ℝ) z.2.property.le]
    change (z.2 : ℝ)*gauge K (z.1 : Space n) < 1 ↔ (z.2 : ℝ) < (gauge K (z.1 : Space n))⁻¹
    rw [inv_eq_one_div,lt_div_iff₀ (hp z.1)]
  have hm := ((volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd).symm
    (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hm' := hm.measure_preimage hA.nullMeasurableSet
  change (surface n).prod ν ((homeomorphUnitSphereProd (Space n)).symm ⁻¹' A) = _ at hm'
  rw [he, ((MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Space n)).compl)).comap_apply] at hm'
  have hi : Subtype.val '' A = interior K \ {0} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨hy,y.property⟩
    · intro hx; exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  rw [hi,measure_sdiff_null (measure_singleton _),
    measure_interior_of_null_frontier (hc.addHaar_frontier volume)] at hm'
  rw [← hm',Measure.prod_apply hS]
  apply lintegral_congr
  intro u
  have hu : Prod.mk u ⁻¹' S = Iio (⟨(gauge K (u : Space n))⁻¹,inv_pos.mpr (hp u)⟩ : Ioi (0:ℝ)) := rfl
  rw [hu,Measure.volumeIoiPow_apply_Iio]
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have hnR := congrArg (fun j : ℕ => (j : ℝ)) hn
  simp only [Nat.cast_add,Nat.cast_one] at hnR
  simp only [finrank_euclideanSpace_fin,hn,hnR]

lemma gauge_volume {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume.real K = kappa n * mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) := by
  have hcont : Continuous (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) :=
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀ (fun u => (hp u).ne')).pow n
  have hnn : ∀ u : Sphere n, 0 ≤ (gauge K (u : Space n))⁻¹ ^ n := fun u => pow_nonneg (inv_nonneg.mpr (hp u).le) n
  have hv := congrArg ENNReal.toReal (gauge_volume_lintegral hc h0 hp)
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.div_const n |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (Eventually.of_forall (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    ENNReal.toReal_ofReal (integral_nonneg (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    integral_div] at hv
  change volume.real K = _ at hv
  rw [hv,mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _ = kappa n * (((surface n).real univ)⁻¹ * _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

lemma wulff_volume {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    volume.real (wulff s) = kappa n * mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹ ^ n) := by
  apply gauge_volume (wulff_convex s) (wulff_nhds s hs)
  intro u
  rw [gauge_wulff_eq_max s hs]
  exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma wulff_sphere_gauge_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    {m M : ℝ} (hm : 0 < m) (hs : ∀ u, m ≤ s u ∧ s u ≤ M)
    (u : Sphere n) : M⁻¹ ≤ gauge (wulff s) (u : Space n) ∧
      gauge (wulff s) (u : Space n) ≤ m⁻¹ := by
  have hp : ∀ v, 0 < s v := fun v => hm.trans_le (hs v).1
  rw [gauge_wulff_eq_max s hp]
  constructor
  · have h := le_wulffMax s hp (u : Space n) u
    rw [real_inner_self_eq_norm_sq,norm_coe,one_pow,one_div] at h
    exact (inv_anti₀ (hp u) (hs u).2).trans h
  · obtain ⟨v,hv⟩ := wulffMax_attained s hp (u : Space n)
    rw [hv]
    have hi : ⟪(u : Space n),(v : Space n)⟫ ≤ 1 := by
      simpa only [norm_coe,one_mul] using real_inner_le_norm (u : Space n) (v : Space n)
    calc
      _ ≤ 1 / s v := div_le_div_of_nonneg_right hi (hp v).le
      _ ≤ m⁻¹ := by simpa only [one_div] using inv_anti₀ hm (hs v).1

lemma quotient_perturb_bound {a b c t r m B : ℝ} (hm : 0 < m)
    (ht : m ≤ b+t*c) (hr : m ≤ b+r*c) (ha : |a| ≤ 1) (hc : |c| ≤ B) :
    |a/(b+t*c)-a/(b+r*c)| ≤ (B/m^2)*|t-r| := by
  have ht0 := hm.trans_le ht
  have hr0 := hm.trans_le hr
  have hB : 0 ≤ B := (abs_nonneg c).trans hc
  have he : a/(b+t*c)-a/(b+r*c) = a*c*(r-t)/((b+t*c)*(b+r*c)) := by
    rw [div_sub_div _ _ ht0.ne' hr0.ne']
    congr 1
    ring
  rw [he,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos ht0,abs_of_pos hr0,abs_sub_comm r t]
  calc
    _ ≤ (1*B)*|t-r|/(m*m) := by gcongr
    _ = _ := by ring

lemma wulff_gauge_param_sub_le {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m t r : ℝ} (hm : 0 < m) (ht : ∀ u, m ≤ (s+t • φ) u)
    (hr : ∀ u, m ≤ (s+r • φ) u) (u : Sphere n) :
    gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n) ≤
      (‖φ‖/m^2)*|t-r| := by
  have htp : ∀ v, 0 < (s+t • φ) v := fun v => hm.trans_le (ht v)
  have hrp : ∀ v, 0 < (s+r • φ) v := fun v => hm.trans_le (hr v)
  rw [gauge_wulff_eq_max (s+t • φ) htp,gauge_wulff_eq_max (s+r • φ) hrp]
  obtain ⟨v,hv⟩ := wulffMax_attained (s+t • φ) htp (u : Space n)
  rw [hv]
  have hi : |⟪(u : Space n),(v : Space n)⟫| ≤ 1 := by
    simpa only [norm_coe,one_mul] using abs_real_inner_le_norm (u : Space n) (v : Space n)
  calc
    _ ≤ ⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v :=
      sub_le_sub_left (le_wulffMax (s+r • φ) hrp _ v) _
    _ ≤ |⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v| := le_abs_self _
    _ ≤ _ := quotient_perturb_bound hm (ht v) (hr v) hi (φ.norm_coe_le_norm v)

lemma wulff_gauge_param_lipschitz {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m : ℝ} (hm : 0 < m) {T : Set ℝ} (hT : ∀ t ∈ T, ∀ u, m ≤ (s+t • φ) u)
    (u : Sphere n) : LipschitzOnWith ⟨‖φ‖/m^2,by positivity⟩
      (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) (u : Space n)) T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht r hr
  change |gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n)| ≤ (‖φ‖/m^2)*|t-r|
  apply abs_le.mpr
  constructor
  · have h := wulff_gauge_param_sub_le s φ hm (hT r hr) (hT t ht) u
    rw [abs_sub_comm r t] at h
    linarith
  · exact wulff_gauge_param_sub_le s φ hm (hT t ht) (hT r hr) u

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma wulff_invpow_param_lipschitz {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u,0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ C : ℝ≥0, ∀ u : Sphere n,
      LipschitzOnWith C (fun t : ℝ => (gauge (wulff ⇑(s+t • φ)) (u : Space n))⁻¹ ^ n) T := by
  obtain ⟨m,M,hm,hM,he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (fun a : ℝ => a⁻¹^n) (Icc M⁻¹ m⁻¹) := by
    intro a ha
    exact ((contDiffAt_id.inv ((inv_pos.mpr hM).trans_le ha.1).ne').pow n).contDiffWithinAt
  obtain ⟨D,hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := ⟨‖φ‖/m^2,by positivity⟩
  refine ⟨T,hT,D*C,?_⟩
  intro u
  apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
  intro t ht
  exact wulff_sphere_gauge_bounds (s+t • φ) hm ht u

lemma wulff_invpow_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u : Space n))⁻¹^n)
      (n*(gauge (wulff s) (u : Space n))⁻¹^n*φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp : 0 < gauge (wulff s) (u : Space n) := by
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have h := ((wulff_derivative s hs φ hφ hh hd).inv
    (by simpa only [zero_smul,add_zero] using hp.ne')).pow n
  simp only [zero_smul,add_zero] at h
  apply h.congr_deriv
  simp only [Pi.inv_apply,zero_smul,add_zero]
  let q := gauge (wulff s) (u : Space n)
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have he : (q⁻¹)^(n-1)*q⁻¹ = (q⁻¹)^n := by rw [← pow_succ,hn]
  change (n:ℝ)*q⁻¹^(n-1)*(-(-q*_)/q^2) = (n:ℝ)*q⁻¹^n*_
  rw [← he]
  field_simp [show q ≠ 0 from hp.ne']

/-- Actual two-sided first variation in positive Wulff constraints. This is
valid for arbitrary continuous degree-one tests, not only support functions. -/
theorem wulff_volume_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x) :
    HasDerivAt (fun t : ℝ => volume.real (wulff ⇑(s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))))
      (n*kappa n*mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹^n*
        φ (∇ (gauge (wulff s)) (u : Space n)))) 0 := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => (gauge (wulff ⇑(s+t • φs)) (u : Space n))⁻¹^n
  let F' : Sphere n → ℝ := fun u => (n:ℝ)*(gauge (wulff s) (u : Space n))⁻¹^n*
    φ (∇ (gauge (wulff s)) (u : Space n))
  have hg : Continuous (gauge (wulff s)) := continuous_gauge (wulff_convex s) (wulff_nhds s hs)
  have hgp : ∀ u : Sphere n,0 < gauge (wulff s) (u : Space n) := by
    intro u
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have hc : Continuous (F 0) := by
    change Continuous (fun u : Sphere n => (gauge (wulff ⇑(s+0 • φs)) (u : Space n))⁻¹^n)
    simp only [zero_smul,add_zero]
    exact ((hg.comp continuous_subtype_val).inv₀ (fun u => (hgp u).ne')).pow n
  obtain ⟨T,hT,C,hC⟩ := wulff_invpow_param_lipschitz s φs hs
  have hFm : ∀ᶠ t in 𝓝 (0:ℝ), AEStronglyMeasurable (F t) (sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact (((continuous_gauge (wulff_convex _) (wulff_nhds (s+t • φs) ht)).comp
      continuous_subtype_val).measurable.inv.pow_const n).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul ((hg.measurable.comp measurable_subtype_coe).inv.pow_const n)).mul
      (hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe))
  have hder : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    exact wulff_invpow_derivative s hs φ hφ hh hu
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hC u))
    (integrable_const (C:ℝ)) hder).2
  have he : (fun t => volume.real (wulff ⇑(s+t • φs))) =ᶠ[𝓝 (0:ℝ)]
      (fun t => kappa n * ∫ u,F t u ∂sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact wulff_volume (s+t • φs) ht
  have h := (hI.const_mul (kappa n)).congr_of_eventuallyEq he
  apply h.congr_deriv
  dsimp only [F']
  simp_rw [mul_assoc (n:ℝ)]
  rw [integral_const_mul]
  dsimp only [mean]
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

/-- First-variation identity for actual Minkowski addition; the added
set is allowed to have any dimension. -/
theorem minkowski_volume_derivative {n : ℕ} [NeZero n] {K M : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hM : IsCompact M) (hcM : Convex ℝ M) (hMn : M.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M))
      (n*kappa n*mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n*
        support M (∇ (gauge K) (u : Space n)))) (Ici 0) 0 := by
  have hKn : K.Nonempty := ⟨0,mem_of_mem_nhds h0⟩
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u,(support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u,0 < s u := support_pos_of_nhds hK h0
  let φ : C(Sphere n,ℝ) := ⟨fun u => support M u,(support_continuous hM).comp continuous_subtype_val⟩
  have he : ∀ t : ℝ, 0 ≤ t → wulff ⇑(s+t • φ) = K+t • M := by
    intro t ht
    have hf : ⇑(s+t • φ) = fun u : Sphere n => support (K+t • M) u := by
      funext u
      simp only [ContinuousMap.coe_add,ContinuousMap.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      change support K u+t*support M u = support (K+t • M) u
      rw [support_minkowski hK hKn (hM.smul t)
        (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩),
        support_smul_set hM hMn ht]
    rw [hf]
    exact wulff_support (hK.add (hM.smul t)) (hcK.add (hcM.smul t)) (hKn.add (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩))
  have h := (wulff_volume_derivative s hs (support M) (support_continuous hM)
    (fun a ha x => support_smul hM hMn ha.le x)).hasDerivWithinAt (s := Ici (0:ℝ))
  have hw : wulff s = K := wulff_support hK hcK hKn
  rw [hw] at h
  exact h.congr (fun t ht => congrArg volume.real (he t ht).symm)
    (congrArg volume.real (he 0 le_rfl).symm)

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.ShadowSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection

lemma compact_convex_real_interval {C : Set ℝ} (hC : IsCompact C) (hc : Convex ℝ C)
    (hn : C.Nonempty) : C = Icc (sInf C) (sSup C) := by
  apply Subset.antisymm
  · exact fun x hx => ⟨csInf_le hC.bddBelow hx,le_csSup hC.bddAbove hx⟩
  · exact (convex_iff_ordConnected.mp hc).out (hC.sInf_mem hn) (hC.sSup_mem hn)

lemma compact_convex_real_add_interval_volume {C : Set ℝ} (hC : IsCompact C)
    (hc : Convex ℝ C) (hn : C.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    volume (C+Icc (-t) t) = volume C+ENNReal.ofReal (2*t) := by
  rw [compact_convex_real_interval hC hc hn]
  have hab : sInf C ≤ sSup C := (hC.isGLB_sInf hn).1 (hC.sSup_mem hn)
  rw [Icc_add_Icc hab (by linarith),Real.volume_Icc,Real.volume_Icc,
    ← ENNReal.ofReal_add (sub_nonneg.mpr hab) (by positivity)]
  congr 1
  ring

section Product
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma compact_fiber {K : Set (E × ℝ)} (hK : IsCompact K) (x : E) :
    IsCompact (Prod.mk x ⁻¹' K) :=
  (IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight x) (isClosedMap_prodMk_left x)).isCompact_preimage hK

omit [MeasureSpace E] [BorelSpace E] in
lemma convex_fiber {K : Set (E × ℝ)} (hc : Convex ℝ K) (x : E) :
    Convex ℝ (Prod.mk x ⁻¹' K) := by
  intro a ha b hb s t hs ht hst
  have h := hc ha hb hs ht hst
  change (x,s • a+t • b) ∈ K
  simpa only [Prod.smul_mk,Prod.mk_add_mk,← add_smul,hst,one_smul] using h

omit [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma fiber_vertical_add (K : Set (E × ℝ)) (I : Set ℝ) (x : E) :
    Prod.mk x ⁻¹' (K+(Prod.mk (0:E) '' I)) = (Prod.mk x ⁻¹' K)+I := by
  ext r
  constructor
  · rintro ⟨z,hz,_,⟨a,ha,rfl⟩,he⟩
    have hx : z.1 = x := by simpa only [Prod.fst_add,add_zero] using congrArg Prod.fst he
    refine ⟨z.2,?_,a,ha,?_⟩
    · change (x,z.2) ∈ K
      simpa only [← hx,Prod.mk.eta] using hz
    · exact congrArg Prod.snd he
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact ⟨(x,a),ha,(0,b),⟨b,hb,rfl⟩,by simp only [Prod.mk_add_mk,add_zero]⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma fiber_nonempty_iff (K : Set (E × ℝ)) (x : E) :
    (Prod.mk x ⁻¹' K).Nonempty ↔ x ∈ Prod.fst '' K := by
  constructor
  · rintro ⟨r,hr⟩; exact ⟨(x,r),hr,rfl⟩
  · rintro ⟨⟨y,r⟩,hr,rfl⟩; exact ⟨r,hr⟩

/-- The actual Fubini segment-addition formula in orthogonal product coordinates. -/
theorem vertical_segment_volume {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) {t : ℝ} (ht : 0 ≤ t) :
    volume (K+Prod.mk (0:E) '' Icc (-t) t) =
      volume K+ENNReal.ofReal (2*t)*volume (Prod.fst '' K) := by
  have hC : IsCompact (K+Prod.mk (0:E) '' Icc (-t) t) :=
    hK.add (isCompact_Icc.image (by fun_prop))
  have hP : MeasurableSet (Prod.fst '' K) := (hK.image continuous_fst).measurableSet
  rw [Measure.volume_eq_prod,Measure.prod_apply hC.measurableSet,
    Measure.prod_apply hK.measurableSet]
  have he : ∀ x : E, volume (Prod.mk x ⁻¹' (K+Prod.mk (0:E) '' Icc (-t) t)) =
      volume (Prod.mk x ⁻¹' K)+(Prod.fst '' K).indicator (fun _ => ENNReal.ofReal (2*t)) x := by
    intro x
    rw [fiber_vertical_add]
    by_cases hn : (Prod.mk x ⁻¹' K).Nonempty
    · rw [indicator_of_mem ((fiber_nonempty_iff K x).mp hn)]
      exact compact_convex_real_add_interval_volume (compact_fiber hK x) (convex_fiber hc x) hn ht
    · rw [not_nonempty_iff_eq_empty.mp hn,empty_add,measure_empty,
        indicator_of_notMem (fun h => hn ((fiber_nonempty_iff K x).mpr h)),add_zero]
  simp_rw [he]
  rw [lintegral_add_left (measurable_measure_prodMk_left hK.measurableSet),
    lintegral_indicator hP,lintegral_const,Measure.restrict_apply_univ]

end Product
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma shadowCoords_apply {n : ℕ} (u : Sphere n) (z : perpendicular (u : Space n)) (t : ℝ) :
    shadowCoords u (WithLp.toLp 2 (z,t)) = z+t • (u : Space n) := rfl

lemma shadowCoords_projection {n : ℕ} (u : Sphere n)
    (z : perpendicular (u : Space n)) (t : ℝ) :
    (perpendicular (u : Space n)).orthogonalProjectionOnto
      (shadowCoords u (WithLp.toLp 2 (z,t))) = z := by
  rw [shadowCoords_apply,map_add,map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hz : (perpendicular (u : Space n)).orthogonalProjectionOnto (u : Space n) = 0 := by
    exact Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (u : Space n)
  rw [hz,smul_zero,add_zero]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma unitSegment_compact {n : ℕ} (y : Space n) : IsCompact (unitSegment y) :=
  isCompact_Icc.image (by fun_prop)

lemma unitSegment_nonempty {n : ℕ} (y : Space n) : (unitSegment y).Nonempty :=
  ⟨0,⟨0,by norm_num,zero_smul ℝ y⟩⟩

lemma unitSegment_convex {n : ℕ} (y : Space n) : Convex ℝ (unitSegment y) :=
  (convex_Icc (-1:ℝ) 1).linear_image (LinearMap.toSpanSingleton ℝ (Space n) y)

lemma unitSegment_support {n : ℕ} (y x : Space n) : support (unitSegment y) x = |⟪x,y⟫| := by
  apply le_antisymm
  · apply (support_le_iff (unitSegment_compact y) (unitSegment_nonempty y)).mpr
    rintro _ ⟨a,ha,rfl⟩
    rw [real_inner_smul_right]
    calc
      _ ≤ |a*⟪x,y⟫| := le_abs_self _
      _ = |a| * |⟪x,y⟫| := abs_mul _ _
      _ ≤ 1 * |⟪x,y⟫| := mul_le_mul_of_nonneg_right (abs_le.mpr ha) (abs_nonneg _)
      _ = _ := one_mul _
  · rw [abs_le]
    constructor
    · have h := inner_le_support (unitSegment_compact y)
        (mem_image_of_mem (fun a : ℝ => a • y) (left_mem_Icc.mpr (by norm_num : (-1:ℝ) ≤ 1))) x
      simp only [real_inner_smul_right,neg_one_mul] at h
      linarith
    · have h := inner_le_support (unitSegment_compact y)
        (mem_image_of_mem (fun a : ℝ => a • y) (right_mem_Icc.mpr (by norm_num : (-1:ℝ) ≤ 1))) x
      simpa only [real_inner_smul_right,one_mul] using h

lemma smul_unitSegment {n : ℕ} (y : Space n) {t : ℝ} (ht : 0 ≤ t) :
    t • unitSegment y = (fun a : ℝ => a • y) '' Icc (-t) t := by
  have he : Icc (-t) t = (fun a : ℝ => t*a) '' Icc (-1) 1 := by
    simpa only [mul_neg,mul_one] using (image_mul_left_Icc ht (by norm_num : (-1:ℝ) ≤ 1)).symm
  rw [he,image_image,unitSegment,← image_smul,image_image]
  congr 1
  funext a
  exact smul_smul t a y

lemma shadowContinuousEquiv_apply {n : ℕ} (u : Sphere n) (z : perpendicular (u : Space n) × ℝ) :
    shadowContinuousEquiv u z = z.1+z.2 • (u : Space n) := rfl

lemma shadow_preimage_projection {n : ℕ} (u : Sphere n) (K : Set (Space n)) :
    Prod.fst '' (shadowContinuousEquiv u ⁻¹' K) =
      (perpendicular (u : Space n)).orthogonalProjectionOnto '' K := by
  ext z
  constructor
  · rintro ⟨⟨w,t⟩,hw,rfl⟩
    exact ⟨shadowContinuousEquiv u (w,t),hw,shadowCoords_projection u w t⟩
  · rintro ⟨x,hx,rfl⟩
    let q := (shadowContinuousEquiv u).symm x
    have hq : shadowContinuousEquiv u q = x := (shadowContinuousEquiv u).apply_symm_apply x
    refine ⟨q,?_,?_⟩
    · change shadowContinuousEquiv u q ∈ K
      rwa [hq]
    · rw [← hq]
      exact (shadowCoords_projection u q.1 q.2).symm

lemma shadow_preimage_add_segment {n : ℕ} (u : Sphere n) (K : Set (Space n))
    {t : ℝ} (ht : 0 ≤ t) :
    shadowContinuousEquiv u ⁻¹' (K+t • unitSegment (u : Space n)) =
      (shadowContinuousEquiv u ⁻¹' K) + Prod.mk 0 '' Icc (-t) t := by
  rw [smul_unitSegment _ ht]
  ext z
  constructor
  · rintro ⟨x,hx,_,⟨a,ha,rfl⟩,he⟩
    refine ⟨(shadowContinuousEquiv u).symm x,by simpa using hx,(0,a),⟨a,ha,rfl⟩,?_⟩
    apply (shadowContinuousEquiv u).injective
    rw [map_add,ContinuousLinearEquiv.apply_symm_apply,shadowContinuousEquiv_apply,Submodule.coe_zero,zero_add]
    exact he
  · rintro ⟨x,hx,_,⟨a,ha,rfl⟩,rfl⟩
    change shadowContinuousEquiv u (x+(0,a)) ∈ K+(fun a : ℝ => a • (u : Space n)) '' Icc (-t) t
    rw [map_add,shadowContinuousEquiv_apply u (0,a),Submodule.coe_zero,zero_add]
    exact add_mem_add hx (mem_image_of_mem _ ha)

/-- Adding a centered segment increases volume by its length times the actual
orthogonal shadow volume. No boundary regularity is used. -/
theorem segment_volume {n : ℕ} (u : Sphere n) {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (K+t • unitSegment (u : Space n)) =
      volume.real K+2*t*shadowVolume K u := by
  let e := shadowContinuousEquiv u
  have hC : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hcv : Convex ℝ (e ⁻¹' K) := hc.linear_preimage e.toLinearMap
  have h := vertical_segment_volume hC hcv ht
  rw [← shadow_preimage_add_segment u K ht,shadow_preimage_projection] at h
  have hm := shadowMeasurableEquiv_measurePreserving u
  have hm' (B : Set (Space n)) (hB : MeasurableSet B) : volume (e ⁻¹' B) = volume B :=
    hm.measure_preimage hB.nullMeasurableSet
  rw [hm' _ (hK.add ((unitSegment_compact _).smul t)).measurableSet,hm' _ hK.measurableSet] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add hK.measure_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (hK.image (perpendicular (u : Space n)).orthogonalProjectionOnto.continuous).measure_ne_top),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr

/-- Gauge representation of actual orthogonal shadow volume. -/
theorem shadow_gauge_formula {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) :
    2*shadowVolume K u = n*kappa n*mean (fun v : Sphere n =>
      (gauge K (v : Space n))⁻¹^n*|⟪∇ (gauge K) (v : Space n),(u : Space n)⟫|) := by
  have hd := minkowski_volume_derivative hK hc h0 (unitSegment_compact (u : Space n))
    (unitSegment_convex (u : Space n)) (unitSegment_nonempty (u : Space n))
  simp_rw [unitSegment_support] at hd
  have hlin : HasDerivAt (fun t : ℝ => volume.real K+2*t*shadowVolume K u)
      (2*shadowVolume K u) 0 := by
    apply (((hasDerivAt_id (0:ℝ)).const_mul (2:ℝ)).mul_const (shadowVolume K u)).const_add (volume.real K) |>.congr_deriv
    ring
  have hd' := hlin.hasDerivWithinAt (s := Ici (0:ℝ)) |>.congr
    (fun t ht => segment_volume u hK hc ht) (segment_volume u hK hc le_rfl)
  exact (hd'.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ))).symm.trans
    (hd.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ)))

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma volumeReal_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (K : Set E) :
    volume.real (r • K)=r^(Module.finrank ℝ E)*volume.real K := by
  rw [Measure.real,Measure.addHaar_smul_of_nonneg volume hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]
  rfl

end
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Homothety
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma perpendicular_finrank {n : ℕ} (u : Sphere n) :
    Module.finrank ℝ (perpendicular (u : Space n))=n-1 := by
  have hu : (u : Space n) ≠ 0 := by intro h; simpa [h] using norm_coe u
  have hr := (Submodule.span ℝ {(u : Space n)}).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu] at hr
  have he : Module.finrank ℝ (Space n)=n := by simp [Space]
  rw [he] at hr
  change Module.finrank ℝ ((Submodule.span ℝ {(u : Space n)})ᗮ)=n-1
  omega

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

lemma volumeRoot_pow {n : ℕ} (hn : 0 < n) (K : Set (Space n)) :
    volumeRoot K^n=volume.real K :=
  Real.rpow_inv_natCast_pow measureReal_nonneg hn.ne'

lemma volumeRoot_smul {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (K : Set (Space n)) :
    volumeRoot (r • K)=r*volumeRoot K := by
  unfold volumeRoot
  rw [volumeReal_smul_nonneg hr]
  have hd : Module.finrank ℝ (Space n)=n := by simp [Space]
  rw [hd,Real.mul_rpow (pow_nonneg hr _) measureReal_nonneg,← Real.rpow_natCast,
    ← Real.rpow_mul hr, mul_inv_cancel₀ (by exact_mod_cast hn.ne'),Real.rpow_one]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

/-- The sharp first-variation inequality together with its global translated
homothety equality implication, derived from actual Brunn--Minkowski concavity. -/
theorem minkowski_derivative_bound_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M)) d (Ici 0) 0) :
    (n:ℝ)*volumeRoot K^(n-1)*volumeRoot M ≤ d ∧
      (d=(n:ℝ)*volumeRoot K^(n-1)*volumeRoot M →
        ∃ z : Space n, ∃ c : ℝ, 0 < c ∧ K=(fun x => z+c • x) '' M) :=
  minkowski_first_inequality_euclidean hn hK hcK hiK hM hcM hiM hd

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SupportMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma gaugeDensity_measurable {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) : Measurable (gaugeDensity K) :=
  ENNReal.measurable_ofReal.comp ((((continuous_gauge hc h0).measurable.comp
    measurable_subtype_coe).inv).pow_const n)

lemma gaugeDensity_toReal {n : ℕ} (K : Set (Space n)) (u : Sphere n) :
    (gaugeDensity K u).toReal=(gauge K (u : Space n))⁻¹^n := by
  exact ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr (gauge_nonneg _)) _)

lemma gaugeMeasure_integral {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) {f : Space n → ℝ}
    (hf : StronglyMeasurable f) :
    ∫ x,f x ∂gaugeProjectionMeasure K =
      mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n*f (∇ (gauge K) (u : Space n))) := by
  have hm : Measurable (fun u : Sphere n => ∇ (gauge K) (u : Space n)) :=
    (measurable_gradient _).comp measurable_subtype_coe
  rw [gaugeProjectionMeasure,integral_map_of_stronglyMeasurable hm hf,
    integral_withDensity_eq_integral_toReal_smul (gaugeDensity_measurable hc h0)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [gaugeDensity_toReal,smul_eq_mul,mean]

lemma gaugeMeasure_shadow {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) :
    2*shadowVolume K u=n*kappa n*∫ x,|⟪x,(u : Space n)⟫| ∂gaugeProjectionMeasure K := by
  rw [gaugeMeasure_integral hc h0 (by fun_prop)]
  exact shadow_gauge_formula hK hc h0 u

lemma gaugeMeasure_firstVariation {n : ℕ} [NeZero n] {K M : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hM : IsCompact M) (hcM : Convex ℝ M) (hMn : M.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M))
      (n*kappa n*∫ x,support M x ∂gaugeProjectionMeasure K) (Ici 0) 0 := by
  rw [gaugeMeasure_integral hcK h0 (support_continuous hM).stronglyMeasurable]
  exact minkowski_volume_derivative hK hcK h0 hM hcM hMn

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma normalizedVolume_formula {n : ℕ} (K : Set (Space n)) :
    normalizedVolume K=(volume.real K/kappa n)^((n:ℝ)⁻¹) := by
  rw [Real.div_rpow measureReal_nonneg (kappa_pos n).le]
  rfl

lemma gaugeMeasure_functional {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (hv : volume.real K=kappa n)
    (hM : IsCompact M) (hcM : Convex ℝ M) (hiM : (interior M).Nonempty) :
    normalizedVolume M ≤ supportFunctional (gaugeProjectionMeasure K) M ∧
      (supportFunctional (gaugeProjectionMeasure K) M=normalizedVolume M →
        ∃ z : Space n, ∃ c : ℝ, 0 < c ∧ K=(fun x => z+c • x) '' M) := by
  have hiK : (interior K).Nonempty := ⟨0,mem_interior_iff_mem_nhds.mpr h0⟩
  have hV := gaugeMeasure_firstVariation hK hcK h0 hM hcM (hiM.mono interior_subset)
  obtain ⟨hlow,heq⟩ := minkowski_derivative_bound_equality hn hK hcK hiK hM hcM hiM hV
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hp : 0 < (kappa n)^((n:ℝ)⁻¹) := Real.rpow_pos_of_pos (kappa_pos n) _
  have hroot : volumeRoot K=(kappa n)^((n:ℝ)⁻¹) := by unfold volumeRoot; rw [hv]
  have hmul : n*kappa n*normalizedVolume M=(n:ℝ)*volumeRoot K^(n-1)*volumeRoot M := by
    have hpow := volumeRoot_pow (show 0<n by omega) K
    have hsplit : volumeRoot K^(n-1)*volumeRoot K=kappa n := by
      rw [← pow_succ,Nat.sub_add_cancel (by omega),hpow,hv]
    rw [normalizedVolume,← hroot,← hsplit]
    field_simp [(volumeRoot_pos hK hiK).ne']
  refine ⟨?_,fun h => heq ?_⟩
  · rw [← hmul] at hlow
    exact (mul_le_mul_iff_right₀ (mul_pos hnR (kappa_pos n))).mp hlow
  · change n*kappa n*supportFunctional (gaugeProjectionMeasure K) M=_
    rw [h,hmul]

lemma gaugeMeasure_self {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    supportFunctional (gaugeProjectionMeasure K) K=volume.real K/kappa n := by
  have hKn : K.Nonempty := ⟨0,mem_of_mem_nhds h0⟩
  have hV := gaugeMeasure_firstVariation hK hc h0 hK hc hKn
  have hd : HasDerivAt (fun t : ℝ => (1+t)^n*volume.real K) (n*volume.real K) 0 := by
    simpa only [id_eq,Pi.pow_apply,add_zero,one_pow,mul_one] using
      (((hasDerivAt_id (0:ℝ)).const_add 1).pow n).mul_const (volume.real K)
  have he (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      volume.real (K+t • K)=(1+t)^n*volume.real K := by
    have he : K+t • K=(1+t) • K := by simpa only [one_smul] using (hc.add_smul (by norm_num : (0:ℝ)≤1) ht).symm
    rw [he,volumeReal_smul_nonneg (by have := ht; change 0 ≤ t at this; linarith : 0≤1+t)]
    simp only [finrank_euclideanSpace_fin]
  have hd' := hd.hasDerivWithinAt (s := Ici (0:ℝ)) |>.congr he (he 0 (by norm_num))
  have hdEq := (hV.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ))).symm.trans
    (hd'.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ)))
  change n*kappa n*supportFunctional (gaugeProjectionMeasure K) K=n*volume.real K at hdEq
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  apply (eq_div_iff (kappa_pos n).ne').mpr
  rw [mul_assoc] at hdEq
  simpa only [mul_comm] using (mul_left_cancel₀ hn hdEq)

lemma shadowVolume_pos {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (h0 : K ∈ 𝓝 (0 : Space n)) (u : Space n) : 0 < shadowVolume K u := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp h0
  have hball : ball (0 : perpendicular u) r ⊆ (perpendicular u).orthogonalProjectionOnto '' K := by
    intro z hz
    refine ⟨z,hrK ?_,?_⟩
    · simpa only [mem_ball,dist_zero_right,Submodule.norm_coe] using hz
    · exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z
  have hpos : 0 < (volume : Measure (perpendicular u))
      ((perpendicular u).orthogonalProjectionOnto '' K) :=
    (measure_ball_pos volume 0 hr).trans_le (measure_mono hball)
  exact ENNReal.toReal_pos hpos.ne'
    (hK.image (perpendicular u).orthogonalProjectionOnto.continuous).measure_ne_top

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.CosineSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma higherKernel_const_rotation {n : ℕ} (r : ℕ) (u : Sphere n)
    (U : Space n ≃ₗᵢ[ℝ] Space n) :
    higherKernel r (sphereMap U u) (fun _ => 1) = higherKernel r u (fun _ => 1) := by
  have h := mean_rotation U (fun x : Sphere n => max ⟪U (u : Space n),(x : Space n)⟫ 0 ^ r)
  change mean (fun x : Sphere n => max ⟪U (u : Space n),U (x : Space n)⟫ 0 ^ r) = _ at h
  simp only [U.inner_map_map] at h
  simp only [higherKernel, mul_one]
  change mean (fun x : Sphere n => max ⟪U (u : Space n),(x : Space n)⟫ 0 ^ r) = _
  exact h.symm

lemma higherKernel_const_independent {n : ℕ} (r : ℕ) (u v : Sphere n) :
    higherKernel r u (fun _ => 1) = higherKernel r v (fun _ => 1) := by
  let U := (ℝ ∙ ((u : Space n)-(v : Space n)))ᗮ.reflection
  have h : sphereMap U u = v := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((norm_coe u).trans (norm_coe v).symm)
  rw [← h, higherKernel_const_rotation]

lemma mean_pos_inner_even {n : ℕ} [NeZero n] (u : Sphere n) {f : Space n → ℝ}
    (heven : Function.Even f) (hf : Continuous f) :
    mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫| *f x) =
      2*higherKernel 1 u (fun x => f x) := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0*f x)
  have he : (fun x : Sphere n => max ⟪(u : Space n),((sphereMap (LinearIsometryEquiv.neg ℝ)) x : Space n)⟫ 0 *
      f (sphereMap (LinearIsometryEquiv.neg ℝ) x)) =
      (fun x : Sphere n => max (-⟪(u : Space n),(x : Space n)⟫) 0*f x) := by
    funext x
    change max ⟪(u : Space n),-(x : Space n)⟫ 0*f (-(x : Space n)) = _
    rw [inner_neg_right, heven]
  rw [he] at h
  have hk (t : ℝ) : |t| = max t 0+max (-t) 0 := by
    rcases le_total 0 t with ht | ht <;> simp [abs_of_nonneg, abs_of_nonpos, ht]
  simp only [higherKernel, pow_one]
  simp_rw [hk, add_mul]
  rw [mean, integral_add]
  · change mean (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0*f x) +
      mean (fun x : Sphere n => max (-⟪(u : Space n),(x : Space n)⟫) 0*f x) = _
    rw [h]
    ring
  · exact continuous_integrable (by fun_prop)
  · exact continuous_integrable (by fun_prop)

lemma mean_abs_inner {n : ℕ} [NeZero n] (u : Sphere n) :
    mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫|) = cosineConstant n := by
  have h := mean_pos_inner_even u (f := fun _ => 1) (fun _ => rfl) continuous_const
  simpa only [mul_one, higherKernel_const_independent 1 u (pole n), cosineConstant] using h

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.VariationalMinimizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe seminorm_continuous)

/-- Hahn--Banach attainment for the actual Wulff body of a seminorm. -/
lemma seminorm_supporting_vector {n : ℕ} (q : Seminorm ℝ (Space n)) (u : Sphere n) :
    ∃ z : Space n,(∀ x : Space n,|⟪x,z⟫|≤q x) ∧ ⟪(u:Space n),z⟫=q u := by
  let V := Submodule.span ℝ {(u:Space n)}
  let f : Module.Dual ℝ V := q u • ((innerSL ℝ (u:Space n)).toLinearMap.comp V.subtype)
  have hf (x : V) : |f x|≤q (x:Space n) := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp x.property
    change |q u*⟪(u:Space n),(x:Space n)⟫|≤q (x:Space n)
    rw [← ha,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,map_smul_eq_mul]
    simp only [one_pow,mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg (apply_nonneg q _)]
    rw [mul_comm]
  obtain ⟨φ,hφ,hb⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm_real
    V f (seminorm_continuous n q) (fun x => (le_abs_self _).trans (hf x))
  let z := (InnerProductSpace.toDual ℝ (Space n)).symm φ
  have hz (x : Space n) : ⟪x,z⟫=φ x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨z,fun x => by rw [hz];exact hb x,?_⟩
  rw [hz]
  have h := hφ ⟨(u:Space n),Submodule.mem_span_singleton_self (u:Space n)⟩
  simpa [f,real_inner_self_eq_norm_sq,norm_coe] using h

lemma support_wulff_seminorm_unit {n : ℕ} [NeZero n] (q : Seminorm ℝ (Space n))
    (hq : ∀ u : Sphere n,0<q u) (u : Sphere n) :
    support (wulff (fun v : Sphere n => q v)) u=q u := by
  let s : C(Sphere n,ℝ) := ⟨fun u => q u,(seminorm_continuous n q).comp continuous_subtype_val⟩
  have hc := wulff_compact s hq
  have hn : (wulff s).Nonempty := ⟨0,mem_of_mem_nhds (wulff_nhds s hq)⟩
  apply le_antisymm
  · exact (support_le_iff hc hn).mpr (fun x hx => hx u)
  · obtain ⟨z,hz,he⟩ := seminorm_supporting_vector q u
    have hmem : z∈wulff s := fun v => (le_abs_self _).trans (hz v)
    rw [← he]
    exact inner_le_support hc hmem u

lemma support_wulff_seminorm {n : ℕ} [NeZero n] (q : Seminorm ℝ (Space n))
    (hq : ∀ u : Sphere n,0<q u) (x : Space n) :
    support (wulff (fun v : Sphere n => q v)) x=q x := by
  let s : C(Sphere n,ℝ) := ⟨fun u => q u,(seminorm_continuous n q).comp continuous_subtype_val⟩
  have hc := wulff_compact s hq
  have hn : (wulff s).Nonempty := ⟨0,mem_of_mem_nhds (wulff_nhds s hq)⟩
  change IsCompact (wulff (fun v : Sphere n => q v)) at hc
  change (wulff (fun v : Sphere n => q v)).Nonempty at hn
  by_cases hx : x=0
  · subst x
    obtain ⟨z,_,he⟩ := support_attained hc hn 0
    simpa only [inner_zero_left,map_zero] using he
  · let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
    have hxu : x=‖x‖ • (u:Space n) := by simp [u,smul_smul,norm_ne_zero_iff.mpr hx]
    rw [hxu,support_smul hc hn (norm_nonneg _),support_wulff_seminorm_unit q hq]
    simpa only [Real.norm_of_nonneg (norm_nonneg x)] using (map_smul_eq_mul q ‖x‖ (u:Space n)).symm

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.VariationalRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe mean sigma)

lemma normalizedVolume_pow {n : ℕ} [NeZero n] (K : Set (Space n)) :
    normalizedVolume K^n=volume.real K/kappa n := by
  rw [normalizedVolume_formula]
  exact Real.rpow_inv_natCast_pow (div_nonneg measureReal_nonneg (kappa_pos n).le) (NeZero.ne n)

lemma normalizedVolume_smul {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (K : Set (Space n)) :
    normalizedVolume (a • K)=a*normalizedVolume K := by
  rw [normalizedVolume,volumeRoot_smul (NeZero.pos n) ha,normalizedVolume]
  ring

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.AffinePosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma volumeReal_linearEquiv (T : Space n ≃L[ℝ] Space n) (K : Set (Space n)) :
    volume.real (T '' K)=|LinearMap.det T.toLinearMap| * volume.real K := by
  unfold Measure.real
  rw [Measure.addHaar_image_continuousLinearEquiv,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]

lemma linearEquiv_body (T : Space n ≃L[ℝ] Space n) {K : Set (Space n)} (hK : IsConvexBody K) :
    IsConvexBody (T '' K) := by
  refine ⟨hK.1.image T.continuous,hK.2.1.linear_image T.toLinearMap,?_⟩
  change (interior (T.toHomeomorph '' K)).Nonempty
  rw [← T.toHomeomorph.image_interior]
  exact hK.2.2.image T

lemma linearEquiv_det_ne_zero (T : Space n ≃L[ℝ] Space n) : LinearMap.det T.toLinearMap≠0 :=
  T.toLinearEquiv.isUnit_det'.ne_zero

lemma measurePair_cosine {μ ν : Measure (Space n)}
    (hν : Integrable (fun x : Space n => ‖x‖) ν) :
    measurePair μ ν=∫ x,cosineSeminorm ν hν x ∂μ := by
  unfold measurePair
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y,|⟪x,y⟫| ∂ν)=∫ y,|⟪y,x⟫| ∂ν
  simp only [real_inner_comm x]

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.BilinearEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeMoment cosineConstant)
open RelativeGauge

lemma normalizedVolume_of_volume {n : ℕ} {K : Set (Space n)} (hK : volume.real K=kappa n) :
    normalizedVolume K=1 := by
  rw [normalizedVolume_formula,hK,div_self (kappa_pos n).ne',Real.one_rpow]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe seminorm_continuous)
variable {n : ℕ} [NeZero n] {K : Set (Space n)}

lemma gaugeMeasure_cosine_pos (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : K∈𝓝 (0:Space n)) :
    ∀ x : Space n,x≠0 → 0< cosineSeminorm (gaugeProjectionMeasure K) (gaugeMeasure_norm_integrable hK hc h0) x := by
  intro x hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
  have hu := gaugeMeasure_shadow hK hc h0 u
  have hh := shadowVolume_pos hK h0 (u:Space n)
  have hn : 0 < (n:ℝ)*kappa n := mul_pos (Nat.cast_pos.mpr (NeZero.pos n)) (kappa_pos n)
  have hp : 0< cosineSeminorm (gaugeProjectionMeasure K) (gaugeMeasure_norm_integrable hK hc h0) u := by
    change 0 < ∫ y,|⟪y,(u:Space n)⟫| ∂gaugeProjectionMeasure K
    nlinarith
  change 0< cosineSeminorm _ _ (‖x‖⁻¹ • x) at hp
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hp
  exact (mul_pos_iff.mp hp).elim (fun h => h.2) (fun h => False.elim (not_lt_of_ge (inv_nonneg.mpr (norm_nonneg x)) h.1))

lemma projectionSeminorm_unit (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (u : Sphere n) : projectionSeminorm hK hc h0 u=shadowVolume K u := by
  have hh := gaugeMeasure_shadow hK hc h0 u
  change (n*kappa n/2)*(∫ x,|⟪x,(u:Space n)⟫| ∂gaugeProjectionMeasure K)=_
  linarith

lemma projectionSeminorm_pos (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (u : Sphere n) : 0< projectionSeminorm hK hc h0 u := by
  rw [projectionSeminorm_unit]
  exact shadowVolume_pos hK h0 u

lemma projectionBody_eq_wulff (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionBody K=wulff (fun u : Sphere n => projectionSeminorm hK hc h0 u) := by
  ext x
  constructor
  · intro hx u
    change ⟪(u:Space n),x⟫ ≤ projectionSeminorm hK hc h0 u
    rw [projectionSeminorm_unit]
    exact hx u (norm_coe u)
  · intro hx u hu
    let v : Sphere n := ⟨u,by simpa only [mem_sphere,dist_zero_right] using hu⟩
    have h : ⟪u,x⟫ ≤ projectionSeminorm hK hc h0 v := hx v
    rw [projectionSeminorm_unit] at h
    exact h

lemma projectionBody_body (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    IsConvexBody (projectionBody K) := by
  rw [projectionBody_eq_wulff hK hc h0]
  exact wulff_body ⟨fun u : Sphere n => projectionSeminorm hK hc h0 (u:Space n),(seminorm_continuous n (projectionSeminorm hK hc h0)).comp continuous_subtype_val⟩
    (projectionSeminorm_pos hK hc h0)

lemma projectionBody_nhds (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionBody K∈𝓝 (0:Space n) := by
  rw [projectionBody_eq_wulff hK hc h0]
  exact wulff_nhds ⟨fun u : Sphere n => projectionSeminorm hK hc h0 (u:Space n),(seminorm_continuous n (projectionSeminorm hK hc h0)).comp continuous_subtype_val⟩
    (projectionSeminorm_pos hK hc h0)

lemma projectionBody_support (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (x : Space n) : support (projectionBody K) x=
      (n*kappa n/2)*∫ y,|⟪y,x⟫| ∂gaugeProjectionMeasure K := by
  rw [projectionBody_eq_wulff hK hc h0,support_wulff_seminorm _ (projectionSeminorm_pos hK hc h0)]
  rfl

lemma projectionBody_support_unit (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (u : Sphere n) : support (projectionBody K) u=shadowVolume K u := by
  rw [projectionBody_eq_wulff hK hc h0,support_wulff_seminorm _ (projectionSeminorm_pos hK hc h0),
    projectionSeminorm_unit]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe mean)
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma unitBall_body : IsConvexBody (unitBall n) := by
  exact ⟨isCompact_closedBall _ _,convex_closedBall _ _,⟨0,mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩⟩

omit [NeZero n] in
lemma unitBall_nhds : unitBall n∈𝓝 (0:Space n) := closedBall_mem_nhds _ (by norm_num)

omit [NeZero n] in
lemma shadowVolume_unitBall (u : Sphere n) : shadowVolume (unitBall n) u=kappa (n-1) := by
  have him : (perpendicular (u:Space n)).orthogonalProjectionOnto '' unitBall n=
      closedBall (0:perpendicular (u:Space n)) 1 := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      simp only [unitBall,mem_closedBall,dist_zero_right] at hx ⊢
      exact ((perpendicular (u:Space n)).norm_orthogonalProjectionOnto_apply_le x).trans hx
    · intro hz
      refine ⟨z,?_,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z⟩
      simpa [unitBall] using hz
  let e : perpendicular (u:Space n) ≃ₗᵢ[ℝ] Space (n-1) :=
    ((stdOrthonormalBasis ℝ (perpendicular (u:Space n))).reindex (finCongr (perpendicular_finrank u))).repr
  unfold shadowVolume
  rw [him]
  have he : e ⁻¹' unitBall (n-1)=closedBall (0:perpendicular (u:Space n)) 1 := by
    ext z
    simp [unitBall,dist_zero_right]
  have hh := e.measurePreserving.measure_preimage (isClosed_closedBall.measurableSet.nullMeasurableSet : NullMeasurableSet (unitBall (n-1)) volume)
  change volume (e ⁻¹' unitBall (n-1)) = volume (unitBall (n-1)) at hh
  rw [he] at hh
  exact congrArg ENNReal.toReal hh

omit [NeZero n] in
lemma gradient_norm_unit (u : Sphere n) : ∇ (fun x : Space n => ‖x‖) (u:Space n)=(u:Space n) := by
  have hd := (hasStrictFDerivAt_norm_sq (u:Space n)).hasFDerivAt.sqrt (by rw [norm_coe];norm_num)
  simp only [norm_coe,one_pow,Real.sqrt_one,mul_one] at hd
  have hs : (1/(2:ℝ)) • (2 • innerSL ℝ (u:Space n))=innerSL ℝ (u:Space n) := by
    ext v
    simp only [smul_apply,two_smul,smul_eq_mul,add_apply]
    ring
  rw [hs] at hd
  have hd' : HasFDerivAt (fun x : Space n => ‖x‖) (innerSL ℝ (u:Space n)) (u:Space n) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hd
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  rw [toDual_gradient,hd'.fderiv]
  rfl

lemma ball_cosine_constant : 2*kappa (n-1)=(n:ℝ)*kappa n*Spherical.cosineConstant n := by
  let u : Sphere n := Spherical.pole n
  have hh := shadow_gauge_formula (K :=unitBall n) unitBall_body.1 unitBall_body.2.1 unitBall_nhds u
  have hg : gauge (unitBall n)=(fun x : Space n => ‖x‖) := by
    funext x
    simp [unitBall,gauge_closedBall (E :=Space n) (by norm_num : (0:ℝ)≤1) x]
  have he : (fun v : Sphere n => (gauge (unitBall n) (v:Space n))⁻¹^n*
      |⟪∇ (gauge (unitBall n)) (v:Space n),(u:Space n)⟫|)=
      (fun v : Sphere n => |⟪(u:Space n),(v:Space n)⟫|) := by
    funext v
    rw [hg,gradient_norm_unit]
    change (‖(v:Space n)‖)⁻¹^n*|⟪(v:Space n),(u:Space n)⟫|=_
    rw [norm_coe]
    simp only [inv_one,one_pow,one_mul,real_inner_comm (v:Space n)]
  rw [shadowVolume_unitBall,he,Spherical.mean_abs_inner] at hh
  exact hh

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma smul_body {K : Set (Space n)} (hK : IsConvexBody K) {a : ℝ} (ha : a≠0) :
    IsConvexBody (a • K) := by
  refine ⟨hK.1.smul a,hK.2.1.smul a,?_⟩
  rw [interior_smul₀ ha]
  exact hK.2.2.image _

lemma translate_body {K : Set (Space n)} (hK : IsConvexBody K) (a : Space n) :
    IsConvexBody ((fun x => a+x) '' K) := by
  refine ⟨hK.1.image (by fun_prop),hK.2.1.translate a,?_⟩
  change (interior ((Homeomorph.addLeft a) '' K)).Nonempty
  rw [← (Homeomorph.addLeft a).image_interior]
  exact hK.2.2.image _

lemma isEllipsoid_linear_image {K : Set (Space n)} (hK : IsEllipsoid K)
    (T : Space n ≃ₗ[ℝ] Space n) : IsEllipsoid (T '' K) := by
  obtain ⟨a,S,rfl⟩ := hK
  refine ⟨T a,S.trans T,?_⟩
  simp only [image_image]
  congr 1
  funext x
  exact map_add T a (S x)

lemma isEllipsoid_translate {K : Set (Space n)} (hK : IsEllipsoid K) (b : Space n) :
    IsEllipsoid ((fun x => b+x) '' K) := by
  obtain ⟨a,T,rfl⟩ := hK
  refine ⟨b+a,T,?_⟩
  simp only [image_image]
  congr 1
  funext x
  exact (add_assoc b a (T x)).symm

lemma isEllipsoid_smul {K : Set (Space n)} (hK : IsEllipsoid K) {c : ℝ} (hc : c≠0) :
    IsEllipsoid (c • K) := by
  exact isEllipsoid_linear_image hK (LinearEquiv.smulOfNeZero ℝ (Space n) c hc)

lemma ellipsoid_homothety (T : Space n ≃L[ℝ] Space n) (a : Space n) {c : ℝ} (hc : c≠0) :
    IsEllipsoid ((fun x => a+c • x) '' (T '' unitBall n)) := by
  have he : IsEllipsoid (T '' unitBall n) := ⟨0,T.toLinearEquiv,by simp⟩
  have hh := isEllipsoid_translate (isEllipsoid_smul he hc) a
  change IsEllipsoid ((fun x => a+x) '' ((fun x => c • x) '' (T '' unitBall n))) at hh
  simpa only [image_image,Function.comp_def] using hh

lemma normalizeBody_body {K : Set (Space n)} (hK : IsConvexBody K) : IsConvexBody (normalizeBody K) :=
  smul_body hK (inv_ne_zero (normalizedVolume_pos hK.1 hK.2.2).ne')

lemma normalizeBody_nhds {K : Set (Space n)} (hK : IsCompact K) (h0 : K∈𝓝 (0:Space n)) :
    normalizeBody K∈𝓝 (0:Space n) := by
  apply (set_smul_mem_nhds_zero_iff (inv_ne_zero (normalizedVolume_pos hK ⟨0,mem_interior_iff_mem_nhds.mpr h0⟩).ne')).mpr h0

lemma normalizeBody_volume [NeZero n] {K : Set (Space n)} (hK : IsConvexBody K) : volume.real (normalizeBody K)=kappa n := by
  have hp := normalizedVolume_pos hK.1 hK.2.2
  rw [normalizeBody,volumeReal_smul_nonneg (inv_nonneg.mpr hp.le),finrank_euclideanSpace_fin,inv_pow,normalizedVolume_pow]
  field_simp [(volumeReal_pos_of_body hK.1 hK.2.2).ne',(kappa_pos n).ne']

lemma normalizeBody_ellipsoid {K : Set (Space n)} (hK : IsConvexBody K)
    (he : IsEllipsoid (normalizeBody K)) : IsEllipsoid K := by
  have hh := isEllipsoid_smul he (normalizedVolume_pos hK.1 hK.2.2).ne'
  simpa only [normalizeBody,smul_smul,mul_inv_cancel₀ (normalizedVolume_pos hK.1 hK.2.2).ne',one_smul] using hh

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma measurePair_comm {μ ν : Measure (Space n)} [SFinite μ] [SFinite ν]
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hν : Integrable (fun x : Space n => ‖x‖) ν) : measurePair μ ν=measurePair ν μ := by
  have hi : Integrable (fun z : Space n × Space n => |⟪z.1,z.2⟫|) (μ.prod ν) := by
    apply (hμ.mul_prod hν).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_abs] using abs_real_inner_le_norm z.1 z.2)
  rw [measurePair,integral_integral_swap hi]
  unfold measurePair
  simp_rw [real_inner_comm]

/-- Main geometric estimate and equality rigidity at the natural volume
normalization; both the input and the projection body remain nonsmooth. -/
theorem normalized_projection {n : ℕ} (hn : 4≤ n) [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (hv : volume.real K=kappa n) :
    kappa (n-1)≤ normalizedVolume (projectionBody K) ∧
      (normalizedVolume (projectionBody K)=kappa (n-1) → IsEllipsoid K) := by
  let P := projectionBody K
  let r := normalizedVolume P
  have hP : IsConvexBody P := projectionBody_body hK hc h0
  have hP0 : P∈𝓝 (0:Space n) := projectionBody_nhds hK hc h0
  have hr : 0< r := normalizedVolume_pos hP.1 hP.2.2
  let D := normalizeBody P
  have hD : IsConvexBody D := normalizeBody_body hP
  have hD0 : D∈𝓝 (0:Space n) := normalizeBody_nhds hP.1 hP0
  have hDv : volume.real D=kappa n := normalizeBody_volume hP
  let μ := gaugeProjectionMeasure K
  let ν := gaugeProjectionMeasure D
  let := gaugeMeasure_finite hK hc h0
  let := gaugeMeasure_finite hD.1 hD.2.1 hD0
  have hμ : Integrable (fun x : Space n => ‖x‖) μ := gaugeMeasure_norm_integrable hK hc h0
  have hν : Integrable (fun x : Space n => ‖x‖) ν := gaugeMeasure_norm_integrable hD.1 hD.2.1 hD0
  obtain ⟨hlow,heq⟩ := measure_bilinear hn hμ hν (gaugeMeasure_cosine_pos hK hc h0)
    (gaugeMeasure_cosine_pos hD.1 hD.2.1 hD0)
    (fun M hM => (gaugeMeasure_functional (by omega) hK hc h0 hv hM.1 hM.2.1 hM.2.2).1)
    (fun M hM => (gaugeMeasure_functional (by omega) hD.1 hD.2.1 hD0 hDv hM.1 hM.2.1 hM.2.2).1)
  have hself : supportFunctional ν D=1 := by
    rw [gaugeMeasure_self hD.1 hD.2.1 hD0,hDv,div_self (kappa_pos n).ne']
  have hs : supportFunctional ν D=r⁻¹*((n:ℝ)*kappa n/2)*measurePair μ ν := by
    change (∫ x,support (r⁻¹ • P) x ∂ν)=_
    simp_rw [support_smul_set hP.1 (hP.2.2.mono interior_subset) (inv_nonneg.mpr hr.le)]
    dsimp only [P]
    simp_rw [projectionBody_support hK hc h0]
    rw [integral_const_mul,integral_const_mul]
    change r⁻¹*((n:ℝ)*kappa n/2*(∫ x,cosineSeminorm μ hμ x ∂ν))=_
    rw [← measurePair_cosine hμ,measurePair_comm hν hμ]
    ring
  have hpair : (n:ℝ)*kappa n*measurePair μ ν=2*r := by
    rw [hself] at hs
    have h := congrArg (fun x : ℝ => (2*r)*x) hs
    field_simp at h
    nlinarith [h]
  have hb := ball_cosine_constant (n :=n)
  have hnk : 0<(n:ℝ)*kappa n := mul_pos (Nat.cast_pos.mpr (NeZero.pos n)) (kappa_pos n)
  refine ⟨?_,?_⟩
  · change kappa (n-1)≤ r
    have h := mul_le_mul_of_nonneg_left hlow hnk.le
    nlinarith
  · intro he
    have hp : measurePair μ ν=Spherical.cosineConstant n := by
      change r=kappa (n-1) at he
      apply (mul_left_cancel₀ hnk.ne')
      rw [hpair,he,← hb]
    obtain ⟨T,hT⟩ := heq hp
    have hE : IsConvexBody (T '' unitBall n) := linearEquiv_body T unitBall_body
    obtain ⟨z,c,hcpos,hset⟩ := (gaugeMeasure_functional (by omega) hK hc h0 hv hE.1 hE.2.1 hE.2.2).2 hT
    rw [hset]
    exact ellipsoid_homothety T z hcpos.ne'

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma volumeReal_translate (K : Set (Space n)) (a : Space n) :
    volume.real ((fun x => a+x) '' K)=volume.real K := by
  unfold Measure.real
  rw [image_add_left,measure_preimage_add]

lemma shadowVolume_translate (K : Set (Space n)) (a u : Space n) :
    shadowVolume ((fun x => a+x) '' K) u=shadowVolume K u := by
  have he : (perpendicular u).orthogonalProjectionOnto '' ((fun x => a+x) '' K)=
      (fun z => (perpendicular u).orthogonalProjectionOnto a+z) ''
        ((perpendicular u).orthogonalProjectionOnto '' K) := by
    simp only [image_image]
    congr 1
    funext x
    exact map_add _ a x
  unfold shadowVolume Measure.real
  rw [he,image_add_left,measure_preimage_add]

lemma projectionBody_translate (K : Set (Space n)) (a : Space n) :
    projectionBody ((fun x => a+x) '' K)=projectionBody K := by
  ext x
  simp only [projectionBody,mem_ofPred_eq,shadowVolume_translate]

lemma projectionRatio_translate (K : Set (Space n)) (a : Space n) :
    projectionRatio ((fun x => a+x) '' K)=projectionRatio K := by
  rw [projectionRatio,projectionBody_translate,volumeReal_translate,projectionRatio]

lemma shadowVolume_smul (K : Set (Space n)) {a : ℝ} (ha : 0≤ a) (u : Spherical.Sphere n) :
    shadowVolume (a • K) u=a^(n-1)*shadowVolume K u := by
  have he : (perpendicular (u:Space n)).orthogonalProjectionOnto '' (a • K)=
      a • ((perpendicular (u:Space n)).orthogonalProjectionOnto '' K) := by
    change _ '' ((fun x : Space n => a • x) '' K)=
      (fun z : perpendicular (u:Space n) => a • z) '' (_ '' K)
    simp only [image_image]
    congr 1
    funext x
    exact map_smul _ a x
  unfold shadowVolume
  rw [he,volumeReal_smul_nonneg ha,perpendicular_finrank]

lemma projectionBody_smul (K : Set (Space n)) {a : ℝ} (ha : 0< a) :
    projectionBody (a • K)=a^(n-1) • projectionBody K := by
  have hp : 0< a^(n-1) := pow_pos ha _
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hp.ne']
  change (∀ u : Space n,‖u‖=1 → ⟪u,x⟫≤ shadowVolume (a • K) u) ↔
    (∀ u : Space n,‖u‖=1 → ⟪u,(a^(n-1))⁻¹ • x⟫≤ shadowVolume K u)
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  have hv := shadowVolume_smul K ha.le (⟨u,by simpa only [mem_sphere,dist_zero_right] using hu⟩ : Spherical.Sphere n)
  change shadowVolume (a • K) u=a^(n-1)*shadowVolume K u at hv
  rw [hv,inner_smul_right]
  rw [show (a^(n-1))⁻¹*⟪u,x⟫=⟪u,x⟫/(a^(n-1)) by ring,div_le_iff₀ hp]
  rw [mul_comm (a^(n-1))]

lemma projectionRatio_smul (K : Set (Space n))
    {a : ℝ} (ha : 0< a) : projectionRatio (a • K)=projectionRatio K := by
  rw [projectionRatio,projectionBody_smul K ha,volumeReal_smul_nonneg (pow_nonneg ha.le _),
    volumeReal_smul_nonneg ha.le,finrank_euclideanSpace_fin,projectionRatio,mul_pow]
  have he : (a^(n-1))^n=(a^n)^(n-1) := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [he]
  field_simp [ha.ne']

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma projectionRatio_normalized {n : ℕ} (hn : 2≤n) [NeZero n] {K : Set (Space n)}
    (hv : volume.real K=kappa n) :
    projectionRatio K=normalizedVolume (projectionBody K)^n*kappa n^(2-(n:ℤ)) := by
  have hn1 : n-1=(n-2)+1 := by omega
  have hn2 : (2-(n:ℤ))=-((n-2:ℕ):ℤ) := by omega
  have hvP : volume.real (projectionBody K)=normalizedVolume (projectionBody K)^n*kappa n := by
    exact (div_eq_iff (kappa_pos n).ne').mp (normalizedVolume_pow (projectionBody K)).symm
  rw [projectionRatio,hv,hvP,hn1,pow_succ,hn2,zpow_neg,zpow_natCast]
  field_simp [(kappa_pos n).ne']

lemma normalized_projection_ratio {n : ℕ} (hn : 4≤n) [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (hv : volume.real K=kappa n) :
    pettyConstant n≤projectionRatio K ∧ (projectionRatio K=pettyConstant n → IsEllipsoid K) := by
  obtain ⟨hb,he⟩ := normalized_projection hn hK hc h0 hv
  have hkp := kappa_pos (n-1)
  have hpow := zpow_pos (kappa_pos n) (2-(n:ℤ))
  rw [projectionRatio_normalized (by omega) hv]
  unfold pettyConstant
  refine ⟨mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hkp.le hb n) hpow.le,?_⟩
  intro h
  apply he
  apply (pow_left_inj₀ (hkp.le.trans hb) hkp.le (NeZero.ne n)).mp
  exact mul_right_cancel₀ hpow.ne' h

lemma centered_projection_lower_bound {n : ℕ} (hn : 4≤n) [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    pettyConstant n≤projectionRatio K ∧ (projectionRatio K=pettyConstant n → IsEllipsoid K) := by
  have hbody : IsConvexBody K := ⟨hK,hc,⟨0,mem_interior_iff_mem_nhds.mpr h0⟩⟩
  have hM := normalizeBody_body hbody
  have hM0 := normalizeBody_nhds hK h0
  obtain ⟨hb,he⟩ := normalized_projection_ratio hn hM.1 hM.2.1 hM0 (normalizeBody_volume hbody)
  have hr : projectionRatio (normalizeBody K)=projectionRatio K :=
    projectionRatio_smul K (inv_pos.mpr (normalizedVolume_pos hK hbody.2.2))
  rw [hr] at hb he
  exact ⟨hb,fun hh => normalizeBody_ellipsoid hbody (he hh)⟩

/-- No origin, symmetry, localness, or boundary smoothness hypothesis is used. -/
theorem projection_lower_bound {n : ℕ} (hn : 4≤n) {K : Set (Space n)}
    (hK : IsConvexBody K) :
    pettyConstant n≤projectionRatio K ∧ (projectionRatio K=pettyConstant n → IsEllipsoid K) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨a,ha⟩ := hK.2.2
  let L := (fun x => -a+x) '' K
  have hL : IsConvexBody L := translate_body hK (-a)
  have hL0 : L∈𝓝 (0:Space n) := by
    have hh := (Homeomorph.addLeft (-a)).isOpenMap.image_mem_nhds (mem_interior_iff_mem_nhds.mp ha)
    simpa [L] using hh
  obtain ⟨hb,he⟩ := centered_projection_lower_bound hn hL.1 hL.2.1 hL0
  have hr : projectionRatio L=projectionRatio K := projectionRatio_translate K (-a)
  rw [hr] at hb he
  refine ⟨hb,fun hh => ?_⟩
  have h := isEllipsoid_translate (he hh) a
  simpa only [L,image_image,Function.comp_def,add_neg_cancel_left,image_id'] using h

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.AffineCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma unitSegment_smul (y : Space n) (a : ℝ) : unitSegment (a • y)=a • unitSegment y := by
  rw [unitSegment,unitSegment,← image_smul,image_image]
  congr 1
  funext t
  exact smul_comm t a y

lemma unitSegment_image (T : Space n →ₗ[ℝ] Space n) (y : Space n) :
    T '' unitSegment y=unitSegment (T y) := by
  rw [unitSegment,unitSegment,image_image]
  congr 1
  funext a
  exact map_smul T a y

lemma unitSegment_zero : unitSegment (0:Space n)={0} := by
  ext x
  simp only [unitSegment,mem_image,mem_Icc,smul_zero,mem_singleton_iff]
  constructor
  · rintro ⟨a,ha,hax⟩;exact hax.symm
  · rintro rfl;exact ⟨0,by norm_num, rfl⟩

lemma segment_volume_support [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) (y : Space n) :
    volume.real (K+unitSegment y)=volume.real K+2*support (projectionBody K) y := by
  have hP := projectionBody_body hK hc h0
  have hne := hP.2.2.mono interior_subset
  by_cases hy : y=0
  · rw [hy,unitSegment_zero,add_singleton]
    simp only [add_zero,image_id']
    have hs0 : support (projectionBody K) 0=0 := by
      simpa using support_smul hP.1 hne (r :=0) le_rfl (0:Space n)
    simp only [hs0,mul_zero,add_zero]
  · let u : Spherical.Sphere n := ⟨‖y‖⁻¹ • y,by simp [norm_smul,hy]⟩
    have he : y=‖y‖ • (u:Space n) := by simp [u,smul_smul,hy]
    conv_lhs => rw [he,unitSegment_smul]
    rw [segment_volume u hK hc (norm_nonneg y)]
    conv_rhs => rhs;rhs;rw [he,support_smul hP.1 hne (norm_nonneg y),projectionBody_support_unit hK hc h0 u]
    ring

lemma linearEquiv_nhds (T : Space n ≃L[ℝ] Space n) {K : Set (Space n)}
    (h0 : K∈𝓝 (0:Space n)) : T '' K∈𝓝 (0:Space n) := by
  have hh := T.toHomeomorph.isOpenMap.image_mem_nhds h0
  change T '' K∈𝓝 (T 0) at hh
  simpa only [map_zero] using hh

lemma projection_support_linearEquiv [NeZero n] (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (y : Space n) : support (projectionBody (T '' K)) y=
      |LinearMap.det T.toLinearMap| * support (projectionBody K) (T.symm y) := by
  have him : T '' (K+unitSegment (T.symm y))=T '' K+unitSegment y := by
    change T.toLinearMap '' (K+unitSegment (T.symm y))=T.toLinearMap '' K+unitSegment y
    rw [image_add T.toLinearMap,unitSegment_image T.toLinearMap]
    change T.toLinearMap '' K+unitSegment (T (T.symm y))=_
    rw [T.apply_symm_apply]
  have hh := volumeReal_linearEquiv T (K+unitSegment (T.symm y))
  rw [him,segment_volume_support (hK.image T.continuous) (hc.linear_image T.toLinearMap)
    (linearEquiv_nhds T h0),segment_volume_support hK hc h0,volumeReal_linearEquiv] at hh
  linarith

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma adjointEquiv_clm (T : Space n ≃L[ℝ] Space n) :
    (adjointEquiv T).toContinuousLinearMap=T.toContinuousLinearMap.adjoint := rfl

lemma det_adjoint (A : Space n →L[ℝ] Space n) :
    LinearMap.det A.adjoint.toLinearMap=LinearMap.det A.toLinearMap := by
  let b := stdOrthonormalBasis ℝ (Space n)
  rw [← LinearMap.det_toMatrix b.toBasis,← ContinuousLinearMap.adjoint_toLinearMap,
    LinearMap.toMatrix_adjoint,Matrix.det_conjTranspose,LinearMap.det_toMatrix]
  exact star_trivial _

lemma adjointEquiv_det (T : Space n ≃L[ℝ] Space n) :
    LinearMap.det (adjointEquiv T).toLinearMap=LinearMap.det T.toLinearMap := det_adjoint _

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ} [NeZero n]

/-- The actual unpolarized projection body transforms by the determinant and
inverse transpose, proved from orthogonal shadow volumes via segment addition. -/
theorem projectionBody_linearEquiv (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionBody (T '' K)=|LinearMap.det T.toLinearMap| • (adjointEquiv T.symm '' projectionBody K) := by
  let P := projectionBody K
  let S := adjointEquiv T.symm
  let d := |LinearMap.det T.toLinearMap|
  have hd : 0<d := abs_pos.mpr (linearEquiv_det_ne_zero T)
  have hP : IsConvexBody P := projectionBody_body hK hc h0
  have hS := linearEquiv_body S hP
  have hR := smul_body hS hd.ne'
  have hL := projectionBody_body (hK.image T.continuous) (hc.linear_image T.toLinearMap) (linearEquiv_nhds T h0)
  apply (support_eq_iff hL.1 hL.2.1 (hL.2.2.mono interior_subset) hR.1 hR.2.1 (hR.2.2.mono interior_subset)).mp
  funext y
  rw [projection_support_linearEquiv T hK hc h0]
  change d*support P (T.symm y)=support (d • (S '' P)) y
  rw [support_smul_set hS.1 (hS.2.2.mono interior_subset) hd.le]
  change d*support P (T.symm y)=d*support (S.toContinuousLinearMap '' P) y
  rw [support_linear_image hP.1 (hP.2.2.mono interior_subset),adjointEquiv_clm,
    ContinuousLinearMap.adjoint_adjoint]
  rfl

lemma projection_volume_linearEquiv (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    volume.real (projectionBody (T '' K))=|LinearMap.det T.toLinearMap|^(n-1)*volume.real (projectionBody K) := by
  rw [projectionBody_linearEquiv T hK hc h0,volumeReal_smul_nonneg (abs_nonneg _),
    finrank_euclideanSpace_fin,volumeReal_linearEquiv,adjointEquiv_det]
  rw [show T.symm.toLinearMap=(T.toLinearEquiv.symm : Space n →ₗ[ℝ] Space n) from rfl,
    LinearEquiv.det_coe_symm,abs_inv]
  have hd := abs_pos.mpr (linearEquiv_det_ne_zero T)
  have he : n=(n-1)+1 := by have := NeZero.pos n;omega
  have hp := congrArg (fun k : ℕ => |LinearMap.det T.toLinearMap|^k) he
  simp only [pow_succ] at hp
  rw [hp]
  field_simp

lemma projectionRatio_linearEquiv (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionRatio (T '' K)=projectionRatio K := by
  rw [projectionRatio,projection_volume_linearEquiv T hK hc h0,volumeReal_linearEquiv,
    projectionRatio,mul_pow]
  have hd := abs_pos.mpr (linearEquiv_det_ne_zero T)
  field_simp

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma projectionBody_unitBall : projectionBody (unitBall n)=kappa (n-1) • unitBall n := by
  have he : projectionBody (unitBall n)=wulff (fun _ : Spherical.Sphere n => kappa (n-1)) := by
    ext x
    constructor
    · intro hx u
      have hh := hx (u:Space n) (Spherical.norm_coe u)
      rwa [shadowVolume_unitBall u] at hh
    · intro hx u hu
      let v : Spherical.Sphere n := ⟨u,by simpa only [mem_sphere,dist_zero_right] using hu⟩
      have hh : ⟪u,x⟫≤kappa (n-1) := hx v
      have hv : shadowVolume (unitBall n) u=kappa (n-1) := shadowVolume_unitBall v
      rwa [hv]
  rw [he]
  have hb : wulff (fun _ : Spherical.Sphere n => kappa (n-1))=closedBall (0:Space n) (kappa (n-1)) :=
    Subset.antisymm (wulff_subset_closedBall (kappa_pos (n-1)).le (fun _ => le_rfl))
      (closedBall_subset_wulff (fun _ => le_rfl))
  rw [hb,unitBall,smul_closedBall' (kappa_pos (n-1)).ne']
  simp only [smul_zero,Real.norm_of_nonneg (kappa_pos (n-1)).le,mul_one]

lemma projectionRatio_unitBall {n : ℕ} (hn : 2≤n) : projectionRatio (unitBall n)=pettyConstant n := by
  let : NeZero n := ⟨by omega⟩
  rw [projectionRatio_normalized hn rfl,projectionBody_unitBall,
    normalizedVolume_smul (kappa_pos (n-1)).le,normalizedVolume_of_volume (K :=unitBall n) rfl,mul_one]
  rfl

/-- All affine ellipsoids, including arbitrary translates, attain equality. -/
theorem ellipsoid_projectionRatio {n : ℕ} (hn : 2≤n) {K : Set (Space n)}
    (hK : IsEllipsoid K) : projectionRatio K=pettyConstant n := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨a,T,rfl⟩ := hK
  have he : (fun x : Space n => a+T x) '' unitBall n=(fun y => a+y) '' (T '' unitBall n) := by
    rw [image_image]
  rw [he,projectionRatio_translate]
  change projectionRatio (T.toContinuousLinearEquiv '' unitBall n)=_
  rw [projectionRatio_linearEquiv T.toContinuousLinearEquiv unitBall_body.1 unitBall_body.2.1 unitBall_nhds,
    projectionRatio_unitBall hn]

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace PettyProjection

/-- The exact unrestricted inequality and its global equality characterization.
-/
theorem petty_projection_volume_oai (n : ℕ) (hn : 4 ≤ n)
    (K : Set (Space n)) (hK : IsConvexBody K) :
    pettyConstant n ≤ projectionRatio K ∧
      (projectionRatio K = pettyConstant n ↔ IsEllipsoid K) := by
  obtain ⟨hbound,hrigid⟩ := projection_lower_bound hn hK
  exact ⟨hbound,hrigid,ellipsoid_projectionRatio (by omega)⟩

end PettyProjection
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.petty_projection_volume_oai := @OAI.PettyProjection.petty_projection_volume_oai
