-- Prove2me | solution 1 for OAI.PettyProjection.RelativeGauge.exists_symmetric_position
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:10:30.083286+00:00
-- url     : https://prove2.me/submissions/0dda6cdc-15e5-4dfd-8898-86e8d93bf6da

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000
import Theorems.Thm_AGT_brouwer_fixed_point

section
-- module Solutions.OAIQW_PettyProjection.SphericalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise

namespace PettyProjection.Spherical

attribute [local instance] OAI.PettyProjection.Spherical.instCompleteSpaceContinuousLinearMapRealIdSpace
attribute [local instance] OAI.PettyProjection.Spherical.instNormedAlgebraRatContinuousLinearMapRealIdSpace
lemma mean_sum {n : ℕ} [NeZero n] {ι : Type uι} (s : Finset ι)
    {f : ι → Sphere n → ℝ} (hf : ∀ i ∈ s, Continuous (f i)) :
    mean (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, mean (f i) := by
  exact integral_finsetSum s fun i hi => continuous_integrable (hf i hi)

open MvPolynomial

end PettyProjection.Spherical
end

end OAI
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

lemma support_lipschitz {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {R : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) : LipschitzWith R (support K) := by
  apply LipschitzWith.of_le_add_mul
  intro u v
  obtain ⟨x,hx,he⟩ := support_attained hK hKn u
  rw [he]
  have hi := inner_le_support hK hx v
  have hbound : ⟪u-v,x⟫ ≤ R*dist u v := by
    calc
      _ ≤ ‖u-v‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖u-v‖*R := mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _)
      _ = _ := by rw [dist_eq_norm]; ring
  rw [inner_sub_left] at hbound
  linarith

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
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma surface_real_univ (n : ℕ) [NeZero n] : (surface n).real univ = n*kappa n := by
  rw [surface,Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  exact congrArg ENNReal.toReal (Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : Space n) (1:ℝ)).symm

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SeminormBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uι

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

lemma gauge_seminormUnit {n : ℕ} (g : Seminorm ℝ (Space n)) (x : Space n) :
    gauge (seminormUnit g) x=g x := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hp : 0<g x+ε := add_pos_of_nonneg_of_pos (apply_nonneg g x) hε
    apply gauge_le_of_mem hp.le
    refine ⟨(g x+ε)⁻¹ • x,?_,smul_inv_smul₀ hp.ne' x⟩
    change g ((g x+ε)⁻¹ • x)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_le_iff₀ hp]
    linarith
  · unfold gauge
    apply le_csInf (absorbent_nhds_zero (seminormUnit_nhds g)).gauge_set_nonempty
    rintro r ⟨hr,y,hy,rfl⟩
    rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le hy

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere)

lemma functional_add {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K L : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (hL : IsCompact L) (hLn : L.Nonempty) :
    supportFunctional μ (K+L)=supportFunctional μ K+supportFunctional μ L := by
  unfold supportFunctional
  simp_rw [support_minkowski hK hKn hL hLn]
  exact integral_add (support_integrable hμ hK hKn) (support_integrable hμ hL hLn)

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.RelativeGauges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma objective_mono_eq {n : ℕ} [NeZero n] (b : Bool) {g f : Seminorm ℝ (Space n)}
    (hg : g≠0) (hf : f≠0) (hle : ∀ x,g x≤f x) (heq : objective b g=objective b f) : g=f := by
  have hnn : 0≤ᵐ[sigma n] (fun u : Sphere n => objectiveIntegrand b (f u)-objectiveIntegrand b (g u)) := by
    filter_upwards [seminorm_pos_ae_sphere hg,seminorm_pos_ae_sphere hf] with u hu hv
    exact sub_nonneg.mpr ((objectiveIntegrand_strictMono b).monotoneOn hu hv (hle u))
  have hi := (objective_integrable b hf).sub (objective_integrable b hg)
  have hz : (∫ u : Sphere n,objectiveIntegrand b (f u)-objectiveIntegrand b (g u) ∂sigma n)=0 := by
    rw [integral_sub (objective_integrable b hf) (objective_integrable b hg)]
    exact sub_eq_zero.mpr heq.symm
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz
  have he : (fun u : Sphere n => f u)=ᵐ[sigma n] (fun u : Sphere n => g u) := by
    filter_upwards [hae,seminorm_pos_ae_sphere hg,seminorm_pos_ae_sphere hf] with u hu hgu hfu
    exact (objectiveIntegrand_strictMono b).injOn hfu hgu (sub_eq_zero.mp hu)
  have hpoint := Measure.eq_of_ae_eq he ((seminorm_continuous n f).comp continuous_subtype_val)
    ((seminorm_continuous n g).comp continuous_subtype_val)
  ext x
  rw [← radialExtension_seminorm g x,← radialExtension_seminorm f x,hpoint]

lemma objective_scale {n : ℕ} [NeZero n] (b : Bool) {g f : Seminorm ℝ (Space n)}
    (hg : g≠0) {a : ℝ} (ha : 0<a) (he : ∀ x,f x=a*g x) :
    objective b f=if b then Real.log a+objective b g else a*objective b g := by
  cases b
  · change (∫ u : Sphere n,f u ∂sigma n)=a*∫ u : Sphere n,g u ∂sigma n
    simp_rw [he]; exact integral_const_mul _ _
  · have hae : (fun u : Sphere n => Real.log (f u))=ᵐ[sigma n]
        (fun u : Sphere n => Real.log a+Real.log (g u)) := by
      filter_upwards [seminorm_pos_ae_sphere hg] with u hu
      rw [he,Real.log_mul ha.ne' hu.ne']
    change (∫ u : Sphere n,Real.log (f u) ∂sigma n)=Real.log a+∫ u : Sphere n,Real.log (g u) ∂sigma n
    rw [integral_congr_ae hae,integral_add (integrable_const _) (seminorm_log_integrable hg),integral_const]
    simp only [probReal_univ,one_smul]

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

lemma body_ofBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (hb : Balanced ℝ K)
    (hsub : K⊆V) (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) :
    (ofBody hK hc hb hinner).body=K := by
  ext x
  change (x∈V ∧ gauge (V.starProjection ⁻¹' K) x≤1) ↔ x∈K
  rw [gauge_le_one_iff_mem_closure (s := V.starProjection ⁻¹' K) (hc.linear_preimage V.starProjection.toLinearMap)
    (cylinder_nhds hinner),(hK.isClosed.preimage V.starProjection.continuous).closure_eq]
  constructor
  · rintro ⟨hx,hy⟩
    change V.starProjection x∈K at hy
    rwa [V.starProjection_eq_self_iff.mpr hx] at hy
  · intro hx
    refine ⟨hsub hx,?_⟩
    change V.starProjection x∈K
    rwa [V.starProjection_eq_self_iff.mpr (hsub hx)]

end RelativeGauge
end PettyProjection
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
namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

lemma midBody_sub (g f : RelativeGauge V) : midBody g f⊆V := by
  rintro x ⟨y,⟨a,ha,b,hb,rfl⟩,rfl⟩
  exact V.smul_mem _ (V.add_mem ha.1 hb.1)
lemma body_midpoint (g f : RelativeGauge V) : (midpoint g f).body=midBody g f :=
  body_ofBody _ _ _ (midBody_sub g f) _
lemma functional_midpoint (g f : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) :
    supportFunctional μ (midpoint g f).body=(supportFunctional μ g.body+supportFunctional μ f.body)/2 := by
  rw [body_midpoint,midBody,functional_smul (g.compact.add f.compact) (g.nonempty.add f.nonempty) (by norm_num : (0:ℝ)≤1/2),
    functional_add hμ g.compact g.nonempty f.compact f.nonempty]
  ring

lemma midpoint_harmonic (g f : RelativeGauge V) {x : Space n} (hx : V.starProjection x≠0) :
    midpoint g f x≤((g x)⁻¹+(f x)⁻¹)⁻¹*2 := by
  let y := V.starProjection x
  have hy : y∈V := V.starProjection_apply_mem x
  have hg : 0<g x := by simpa only [y,g.projection] using g.pos hy hx
  have hf : 0<f x := by simpa only [y,f.projection] using f.pos hy hx
  have hmem : ((g x)⁻¹/2+(f x)⁻¹/2) • y∈(midpoint g f).body := by
    rw [body_midpoint]
    refine ⟨(g x)⁻¹ • y+(f x)⁻¹ • y,⟨_,?_,_,?_,rfl⟩,?_⟩
    · simpa only [y,g.projection] using g.radial_mem hy hx
    · simpa only [y,f.projection] using f.radial_mem hy hx
    · simp only [smul_smul,← add_smul]; congr 1; ring
  have hpos : 0<(g x)⁻¹/2+(f x)⁻¹/2 := by positivity
  have hh : (midpoint g f).toSeminorm (((g x)⁻¹/2+(f x)⁻¹/2) • y)≤1 := hmem.2
  rw [map_smul_eq_mul,Real.norm_of_nonneg hpos.le,(midpoint g f).projection] at hh
  have hb := (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hh)
  have he : 1/((g x)⁻¹/2+(f x)⁻¹/2)=((g x)⁻¹+(f x)⁻¹)⁻¹*2 := by
    rw [show (g x)⁻¹/2+(f x)⁻¹/2=((g x)⁻¹+(f x)⁻¹)/2 by ring,one_div,inv_div]
    ring
  exact hb.trans_eq he

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set
namespace PettyProjection.Spherical

lemma harmonic_objective {a d c : ℝ} (ha : 0<a) (hd : 0<d) (hc : 0<c)
    (hle : c≤(a⁻¹+d⁻¹)⁻¹*2) (b : Bool) :
    objectiveIntegrand b c≤(objectiveIntegrand b a+objectiveIntegrand b d)/2 ∧
      (objectiveIntegrand b c=(objectiveIntegrand b a+objectiveIntegrand b d)/2 → a=d) := by
  have hsum : 0<a+d := add_pos ha hd
  have he : (a⁻¹+d⁻¹)⁻¹*2=2*a*d/(a+d) := by field_simp; ring
  have hmul : c*(a+d)≤2*a*d := (le_div_iff₀ hsum).mp (by rwa [← he])
  have havg : c≤(a+d)/2 := by nlinarith [sq_nonneg (a-d)]
  cases b
  · change c≤(a+d)/2 ∧ (c=(a+d)/2 → a=d)
    refine ⟨havg,fun hh => ?_⟩
    nlinarith [sq_nonneg (a-d)]
  · change Real.log c≤(Real.log a+Real.log d)/2 ∧
      (Real.log c=(Real.log a+Real.log d)/2 → a=d)
    have hmean : 0<(a⁻¹+d⁻¹)/2 := by positivity
    have he' : (a⁻¹+d⁻¹)⁻¹*2=((a⁻¹+d⁻¹)/2)⁻¹ := by field_simp
    have hlog : Real.log c≤ -Real.log ((a⁻¹+d⁻¹)/2) := by
      have hh := Real.strictMonoOn_log.monotoneOn hc (inv_pos.mpr hmean) (by rwa [← he'])
      simpa only [Real.log_inv] using hh
    have hj : (1/2:ℝ)*Real.log a⁻¹+(1/2:ℝ)*Real.log d⁻¹≤Real.log ((1/2:ℝ)*a⁻¹+(1/2:ℝ)*d⁻¹) :=
      (strictConcaveOn_log_Ioi).concaveOn.2 (inv_pos.mpr ha) (inv_pos.mpr hd) (by norm_num) (by norm_num) (by norm_num)
    simp only [Real.log_inv] at hj
    have hemean : (1/2:ℝ)*a⁻¹+(1/2:ℝ)*d⁻¹=(a⁻¹+d⁻¹)/2 := by ring
    rw [hemean] at hj
    refine ⟨by linarith,fun hh => ?_⟩
    by_contra hne
    have hi : a⁻¹≠d⁻¹ := by intro he; exact hne (inv_injective he)
    have hs : (1/2:ℝ)*Real.log a⁻¹+(1/2:ℝ)*Real.log d⁻¹<Real.log ((1/2:ℝ)*a⁻¹+(1/2:ℝ)*d⁻¹) :=
      strictConcaveOn_log_Ioi.2 (inv_pos.mpr ha) (inv_pos.mpr hd) hi (by norm_num) (by norm_num) (by norm_num)
    simp only [Real.log_inv,hemean] at hs
    linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere sigma objective objectiveIntegrand objective_integrable)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}

lemma midpoint_objective {g f : RelativeGauge V} (hV : V≠⊥) (b : Bool) :
    objective b (midpoint g f).toSeminorm≤(objective b g.toSeminorm+objective b f.toSeminorm)/2 ∧
      (objective b (midpoint g f).toSeminorm=(objective b g.toSeminorm+objective b f.toSeminorm)/2 → g=f) := by
  let h := midpoint g f
  have hpos := Spherical.seminorm_pos_ae_sphere (g.ne_zero hV)
  have hposf := Spherical.seminorm_pos_ae_sphere (f.ne_zero hV)
  have hposh := Spherical.seminorm_pos_ae_sphere (h.ne_zero hV)
  have hmul : ∀ᵐ u : Sphere n ∂sigma n,
      objectiveIntegrand b (h u)≤(objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2 ∧
        (objectiveIntegrand b (h u)=(objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2 → g u=f u) := by
    filter_upwards [hpos,hposf,hposh] with u hu hv hw
    have hx : V.starProjection (u:Space n)≠0 := by
      intro he
      have hz := g.projection u
      rw [he,map_zero] at hz
      linarith
    exact Spherical.harmonic_objective hu hv hw (g.midpoint_harmonic f hx) b
  have hi : Integrable (fun u : Sphere n => (objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2) (sigma n) :=
    ((objective_integrable b (g.ne_zero hV)).add (objective_integrable b (f.ne_zero hV))).div_const 2
  have hh := objective_integrable b (h.ne_zero hV)
  have havg : (∫ u : Sphere n,(objectiveIntegrand b (g u)+objectiveIntegrand b (f u))/2 ∂sigma n)=
      (objective b g.toSeminorm+objective b f.toSeminorm)/2 := by
    rw [integral_div,integral_add (objective_integrable b (g.ne_zero hV)) (objective_integrable b (f.ne_zero hV))]
    rfl
  have hle := integral_mono_ae hh hi (hmul.mono (fun _ h => h.1))
  refine ⟨by simpa only [havg,objective,Spherical.mean,h] using hle,fun he => ?_⟩
  have hae := (integral_eq_iff_of_ae_le hh hi (hmul.mono (fun _ h => h.1))).mp (by
    rw [havg]; exact he)
  have hae' : (fun u : Sphere n => g u)=ᵐ[sigma n] (fun u : Sphere n => f u) := by
    filter_upwards [hae,hmul] with u hu hv
    exact hv.2 hu
  have hp := Measure.eq_of_ae_eq hae' ((Spherical.seminorm_continuous n g.toSeminorm).comp continuous_subtype_val)
    ((Spherical.seminorm_continuous n f.toSeminorm).comp continuous_subtype_val)
  apply ext
  ext x
  rw [← Spherical.radialExtension_seminorm g.toSeminorm x,← Spherical.radialExtension_seminorm f.toSeminorm x,hp]

lemma minimizer_unique {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥) (b : Bool)
    {g f : RelativeGauge V} (hgn : supportFunctional μ g.body=1) (hfn : supportFunctional μ f.body=1)
    (hmin : ∀ q : RelativeGauge V,supportFunctional μ q.body=1 → objective b g.toSeminorm≤objective b q.toSeminorm)
    (heq : objective b g.toSeminorm=objective b f.toSeminorm) : g=f := by
  have hn : supportFunctional μ (midpoint g f).body=1 := by
    rw [functional_midpoint g f hμ,hgn,hfn]; norm_num
  have hm := hmin (midpoint g f) hn
  obtain ⟨hle,he⟩ := midpoint_objective (g := g) (f := f) hV b
  apply he
  rw [← heq] at hle ⊢
  linarith

end RelativeGauge
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
open scoped RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeField gaugeMoment)

lemma exponent_pos (n : ℕ) : 0 < Scalar.exponent n := by unfold Scalar.exponent;split_ifs <;> norm_num

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.FixedPointCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uι uα

noncomputable section
open Set Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.FixedPoint

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma nearest_unique {K : Set E} {x p q : E}
    (hp : ∀ z ∈ K, ⟪x-p,z-p⟫ ≤ 0) (hq : ∀ z ∈ K, ⟪x-q,z-q⟫ ≤ 0)
    (hpK : p∈K) (hqK : q∈K) : p=q := by
  have h1 := hp q hqK
  have h2 := hq p hpK
  have he : ⟪x-p,q-p⟫+⟪x-q,p-q⟫ = ‖p-q‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hn : ‖p-q‖^2 ≤ 0 := by linarith
  have hz : ‖p-q‖=0 := by nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma nearest_mem (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) (x : E) : nearest K hne hcomplete hc x∈K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hc x)).1

lemma nearest_inner (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) (x : E) :
    ∀ z∈K, ⟪x-nearest K hne hcomplete hc x,z-nearest K hne hcomplete hc x⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hc (nearest_mem K hne hcomplete hc x)).mp
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hc x)).2

lemma nearest_eq_of_mem (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) {x : E} (hx : x∈K) : nearest K hne hcomplete hc x=x := by
  apply nearest_unique (nearest_inner K hne hcomplete hc x) _
    (nearest_mem K hne hcomplete hc x) hx
  intro z hz
  simp only [sub_self,inner_zero_left,le_refl]

lemma nearest_lipschitz (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) : LipschitzWith 1 (nearest K hne hcomplete hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let p := nearest K hne hcomplete hc x
  let q := nearest K hne hcomplete hc y
  have h1 := nearest_inner K hne hcomplete hc x q (nearest_mem K hne hcomplete hc y)
  have h2 := nearest_inner K hne hcomplete hc y p (nearest_mem K hne hcomplete hc x)
  change ⟪x-p,q-p⟫≤0 at h1
  change ⟪y-q,p-q⟫≤0 at h2
  have he : ⟪x-p,q-p⟫+⟪y-q,p-q⟫ = ‖p-q‖^2-⟪x-y,p-q⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right]
    ring
  have hle : ‖p-q‖^2 ≤ ‖x-y‖*‖p-q‖ := by
    have hcs := real_inner_le_norm (x-y) (p-q)
    linarith
  change dist p q ≤ (1:ℝ)*dist x y
  simp only [one_mul,dist_eq_norm]
  by_cases hz : ‖p-q‖=0
  · rw [hz]; exact norm_nonneg _
  · nlinarith [lt_of_le_of_ne (norm_nonneg (p-q)) (Ne.symm hz)]

end PettyProjection.FixedPoint
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Brouwer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set Metric Topology
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Brouwer on any nonempty compact convex set: the published standalone
`AGT.brouwer_fixed_point` (any finite-dimensional real normed space). -/
theorem fixedPoint_compact_convex {K : Set E} (hne : K.Nonempty)
    (hk : IsCompact K) (hc : Convex ℝ K) {f : E → E}
    (hf : ContinuousOn f K) (hmap : MapsTo f K K) : ∃ x∈K, f x=x :=
  AGT.brouwer_fixed_point hc hk hne f hf hmap

end PettyProjection.FixedPoint
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.GaussianMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma gaussianRadial_eq (d : ℕ) : gaussianRadial d=(1/2:ℝ)*Real.Gamma (((d:ℝ)+1)/2) := by
  simpa only [gaussianRadial,Real.rpow_natCast,Real.rpow_two] using
    integral_rpow_mul_exp_neg_rpow (p := (2:ℝ)) (q := (d:ℝ)) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d])

lemma gaussianRadial_pos (d : ℕ) : 0<gaussianRadial d := by
  rw [gaussianRadial_eq]
  exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by positivity))

lemma gaussianRadial_add_two (d : ℕ) :
    gaussianRadial (d+2)=((d:ℝ)+1)/2*gaussianRadial d := by
  rw [gaussianRadial_eq,gaussianRadial_eq]
  have he : (((d+2:ℕ):ℝ)+1)/2=((d:ℝ)+1)/2+1 := by push_cast;ring
  rw [he,Real.Gamma_add_one (by positivity)]
  ring

lemma integral_radial_gaussian (m k : ℕ) :
    (∫ r : Ioi (0:ℝ),r.val^k*Real.exp (-(r.val^2)) ∂Measure.volumeIoiPow m)=gaussianRadial (m+k) := by
  simp only [Measure.volumeIoiPow,ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (r^m).toNNReal • (r^k*Real.exp (-(r^2))))]
    unfold gaussianRadial
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [NNReal.smul_def,Real.coe_toNNReal _ (pow_nonneg hx.le _),pow_add]
    ring
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma surface_integral_eq_mean {n : ℕ} [NeZero n] (f : Sphere n → ℝ) :
    (∫ u,f u ∂surface n)=(n:ℝ)*kappa n*mean f := by
  rw [mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _=(n:ℝ)*kappa n*(((surface n).real univ)⁻¹* _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

/-- Polar separation for any positively homogeneous integrand. No smoothness
or differentiability is used, and the Bochner integral has its ordinary meaning. -/
lemma homogeneous_gaussian_integral {n : ℕ} [NeZero n] (k : ℕ) (f : Space n → ℝ)
    (hh : ∀ r : ℝ,0<r → ∀ x,f (r • x)=r^k*f x) :
    (∫ x,f x*Real.exp (-(‖x‖^2)))=
      (n:ℝ)*kappa n*mean (fun u : Sphere n => f u)*gaussianRadial (n-1+k) := by
  let F : Space n → ℝ := fun x => f x*Real.exp (-(‖x‖^2))
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  have he : (∫ x,F x)=∫ x : ({0}ᶜ : Set (Space n)),F x ∂volume.comap Subtype.val := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl,restrict_compl_singleton]
  rw [show (∫ x,f x*Real.exp (-(‖x‖^2)))=∫ x,F x from rfl,he]
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  rw [← (hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv).integral_comp
    (homeomorphUnitSphereProd (Space n)).symm.measurableEmbedding (fun x => F x)]
  have hfun : (fun z : Sphere n × Ioi (0:ℝ) => F ↑((homeomorphUnitSphereProd (Space n)).symm z))=
      (fun z => f z.1*(z.2.val^k*Real.exp (-(z.2.val^2)))) := by
    funext z
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    dsimp only [F]
    rw [hh _ z.2.property,norm_smul,Real.norm_of_nonneg z.2.property.le,norm_coe,mul_one]
    ring
  change (∫ z : Sphere n × Ioi (0:ℝ),F ↑((homeomorphUnitSphereProd (Space n)).symm z) ∂(surface n).prod ν)=_
  rw [hfun]
  rw [integral_prod_mul (fun u : Sphere n => f u) (fun r : Ioi (0:ℝ) => r.val^k*Real.exp (-(r.val^2))),
    surface_integral_eq_mean]
  dsimp only [ν]
  rw [integral_radial_gaussian]
  simp only [finrank_euclideanSpace_fin]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
variable {n : ℕ}

lemma functional_map {μ : Measure (Space n)} (A : Space n →L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) :
    supportFunctional (μ.map A) K=∫ x,support K (A x) ∂μ := by
  exact integral_map A.continuous.measurable.aemeasurable (support_continuous hK).aestronglyMeasurable

lemma cosine_map_projection {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (A : Space n →L[ℝ] Space n) (x : Space n) :
    cosineSeminorm (μ.map A) (norm_integrable_map hμ A)
      ((LinearMap.range A.toLinearMap).starProjection x)=
        cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x := by
  change (∫ y,|⟪y,(LinearMap.range A.toLinearMap).starProjection x⟫| ∂μ.map A)=∫ y,|⟪y,x⟫| ∂μ.map A
  rw [integral_map A.continuous.measurable.aemeasurable (by fun_prop),
    integral_map A.continuous.measurable.aemeasurable (by fun_prop)]
  congr 1
  funext y
  rw [← Submodule.inner_starProjection_left_eq_right,
    (LinearMap.range A.toLinearMap).starProjection_eq_self_iff.mpr
      (show A y∈LinearMap.range A.toLinearMap from ⟨y,rfl⟩)]

lemma functional_map_continuous {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous (fun A : Space n →L[ℝ] Space n => supportFunctional (μ.map A) K) := by
  simp_rw [functional_map _ hK]
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  have hlip := support_lipschitz hK hne (R := ⟨R,hR.le⟩) hbound
  apply continuous_iff_continuousAt.mpr
  intro A
  apply continuousAt_of_dominated (bound := fun x => R*(‖A‖+1)*‖x‖) <;> try infer_instance
  · filter_upwards [] with B
    exact (support_continuous hK).aestronglyMeasurable.comp_measurable B.continuous.measurable
  · filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (show ‖A‖<‖A‖+1 by linarith))] with B hB
    filter_upwards [] with x
    have hz : support K 0=0 := by
      obtain ⟨z,hz,he⟩ := support_attained hK hne 0
      simpa only [inner_zero_left] using he
    have hh := hlip.norm_sub_le (B x) 0
    rw [hz,sub_zero,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (B.le_opNorm x) hR.le).trans
      (by
        calc
          R*(‖B‖*‖x‖) ≤ R*((‖A‖+1)*‖x‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hB.le (norm_nonneg _)) hR.le
          _ = R*(‖A‖+1)*‖x‖ := by ring))
  · exact hμ.const_mul (R*(‖A‖+1))
  · filter_upwards [] with x
    exact ((support_continuous hK).comp (by fun_prop : Continuous (fun B : Space n →L[ℝ] Space n => B x))).continuousAt

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (seminorm_continuous)
variable {n : ℕ}

lemma projectedUnit_sub (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    projectedUnit V g⊆V := by
  apply closure_minimal _ V.closed_of_finiteDimensional
  rintro _ ⟨x,_,rfl⟩
  exact V.starProjection_apply_mem x

namespace RelativeGauge
variable {V : Submodule ℝ (Space n)}

lemma project_body (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) :
    (project V g hc hl).body=projectedUnit V g :=
  body_ofBody _ _ _ (projectedUnit_sub V g) _

lemma project_le (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) (x : Space n) :
    project V g hc hl x≤g x := by
  change gauge (V.starProjection ⁻¹' projectedUnit V g) x≤g x
  rw [← gauge_seminormUnit g x]
  apply gauge_mono (absorbent_nhds_zero (seminormUnit_nhds g))
  intro y hy
  exact subset_closure ⟨y,hy,rfl⟩

lemma support_cylinder_bound (g : RelativeGauge V) (u : Space n) (hu : u∈V) (z : Space n) :
    ⟪u,z⟫ / max 1 (g z) ≤ support g.body u := by
  have ha : 0 < max 1 (g z) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let y := (max 1 (g z))⁻¹ • V.starProjection z
  have hy : y∈g.body := by
    refine ⟨V.smul_mem _ (V.starProjection_apply_mem z),?_⟩
    change g.toSeminorm ((max 1 (g z))⁻¹ • V.starProjection z)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le),inv_mul_le_iff₀ ha,mul_one]
    change g (V.starProjection z)≤ max 1 (g z)
    rw [g.projection]
    exact le_max_right _ _
  have hh := inner_le_support g.compact hy u
  dsimp only [y] at hh
  rw [inner_smul_right,← Submodule.inner_starProjection_left_eq_right,
    V.starProjection_eq_self_iff.mpr hu] at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.RankContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere)
variable {n : ℕ}

/-- Actual lower-semicontinuity at a singular change of range, formulated
with a bounded projected cylinder instead of extended real support functions. -/
lemma support_min_tendsto {V : Submodule ℝ (Space n)}
    {Vj : ℕ → Submodule ℝ (Space n)} (gj : ∀ i,RelativeGauge (Vj i))
    (g : Seminorm ℝ (Space n)) {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x)
    (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x)))
    {uj : ℕ → Space n} {u : Space n} (hu : u∈V) (huj : ∀ i,uj i∈Vj i)
    (ht : Tendsto uj atTop (𝓝 u)) :
    Tendsto (fun i => min (support (gj i).body (uj i))
      (support (RelativeGauge.project V g hc hl).body u)) atTop
      (𝓝 (support (RelativeGauge.project V g hc hl).body u)) := by
  let f := RelativeGauge.project V g hc hl
  apply tendsto_order.mpr
  constructor
  · intro r hr
    have hex : ∃ z∈seminormUnit g,r<⟪u,z⟫ := by
      by_contra! hn
      have hb : support f.body u≤r := by
        apply (support_le_iff f.compact f.nonempty).mpr
        intro y hy
        rw [RelativeGauge.project_body] at hy
        have hs : projectedUnit V g⊆{y | ⟪u,y⟫≤r} := by
          apply closure_minimal _ (isClosed_le (by fun_prop) continuous_const)
          rintro _ ⟨z,hz,rfl⟩
          change ⟪u,V.starProjection z⟫≤r
          rw [← Submodule.inner_starProjection_left_eq_right,V.starProjection_eq_self_iff.mpr hu]
          exact hn z hz
        exact hs hy
      exact (not_le_of_gt hr) hb
    obtain ⟨z,hz,hzr⟩ := hex
    have hm : max 1 (g z)=1 := max_eq_left hz
    have hd : Tendsto (fun i => ⟪uj i,z⟫ / max 1 (gj i z)) atTop (𝓝 ⟪u,z⟫) := by
      have hh := (ht.inner (tendsto_const_nhds (x := z))).div (tendsto_const_nhds.max (hg z)) (by rw [hm]; norm_num)
      change Tendsto (fun i => ⟪uj i,z⟫ / max 1 (gj i z)) atTop (𝓝 (⟪u,z⟫ / max 1 (g z))) at hh
      simpa only [hm,div_one] using hh
    filter_upwards [hd.eventually (lt_mem_nhds hzr)] with i hi
    exact lt_min (hi.trans_le ((gj i).support_cylinder_bound (uj i) (huj i) z)) hr
  · intro r hr
    exact Eventually.of_forall (fun i => (min_le_right _ _).trans_lt hr)

lemma projected_limit_normalization {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {A : Space n →L[ℝ] Space n} {Aj : ℕ → Space n →L[ℝ] Space n}
    (hA : ∀ x,Tendsto (fun i => Aj i x) atTop (𝓝 (A x)))
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hjn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    (g : Seminorm ℝ (Space n))
    (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x)))
    {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖(LinearMap.range A.toLinearMap).starProjection x‖≤g x) :
    supportFunctional (μ.map A) (RelativeGauge.project (LinearMap.range A.toLinearMap) g hc hl).body≤1 := by
  let V := LinearMap.range A.toLinearMap
  let f := RelativeGauge.project V g hc hl
  let H : Space n → ℝ := fun x => support f.body (A x)
  let Hj : ℕ → Space n → ℝ := fun i x => support (gj i).body (Aj i x)
  have hi : Integrable H μ := by
    exact (integrable_map_measure (support_continuous f.compact).aestronglyMeasurable
      A.continuous.measurable.aemeasurable).mp
        (support_integrable (norm_integrable_map hμ A) f.compact f.nonempty)
  have hij (i : ℕ) : Integrable (Hj i) μ := by
    exact (integrable_map_measure (support_continuous (gj i).compact).aestronglyMeasurable
      (Aj i).continuous.measurable.aemeasurable).mp
        (support_integrable (norm_integrable_map hμ (Aj i)) (gj i).compact (gj i).nonempty)
  have hpos (x : Space n) : 0≤H x := support_nonneg f.compact f.zero_mem _
  have hjpos (i : ℕ) (x : Space n) : 0≤Hj i x := support_nonneg (gj i).compact (gj i).zero_mem _
  have ht : Tendsto (fun i => ∫ x,min (Hj i x) (H x) ∂μ) atTop (𝓝 (∫ x,H x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence H
    · intro i
      exact ((hij i).inf hi).aestronglyMeasurable
    · exact hi
    · intro i
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hjpos i x) (hpos x))]
      exact min_le_right _ _
    · filter_upwards [] with x
      exact support_min_tendsto gj g hc hl hg (show A x∈V from ⟨x,rfl⟩)
        (fun i => show Aj i x∈LinearMap.range (Aj i).toLinearMap from ⟨x,rfl⟩) (hA x)
  have hb (i : ℕ) : (∫ x,min (Hj i x) (H x) ∂μ)≤1 := by
    have hh := integral_mono ((hij i).inf hi) (hij i) (fun _ => min_le_left _ _)
    have he : (∫ x,Hj i x ∂μ)=1 := by rw [← functional_map _ (gj i).compact,hjn]
    exact hh.trans he.le
  rw [functional_map _ f.compact]
  exact le_of_tendsto ht (Eventually.of_forall hb)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ}

lemma projectFull_le (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) (x : Space n) : projectFull V f x≤ f x :=
  project_le _ _ _ _ _

lemma projectFull_body (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    (projectFull V f).body=V.starProjection '' f.body := by
  rw [projectFull,project_body,projectedUnit,← f.top_body]
  exact (f.compact.image V.starProjection.continuous).isClosed.closure_eq

lemma support_projectFull (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) {u : Space n} (hu : u∈V) :
    support (projectFull V f).body u=support f.body u := by
  have he (x : Space n) : ⟪u,V.starProjection x⟫=⟪u,x⟫ := by
    rw [← Submodule.inner_starProjection_left_eq_right,V.starProjection_eq_self_iff.mpr hu]
  apply le_antisymm
  · apply (support_le_iff (projectFull V f).compact (projectFull V f).nonempty).mpr
    intro x hx
    rw [projectFull_body] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    rw [he]
    exact inner_le_support f.compact hy u
  · obtain ⟨x,hx,hxe⟩ := support_attained f.compact f.nonempty u
    rw [hxe,← he]
    apply inner_le_support (projectFull V f).compact
    rw [projectFull_body]
    exact mem_image_of_mem _ hx

lemma functional_projectFull {μ : Measure (Space n)} (A : Space n →L[ℝ] Space n)
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    supportFunctional (μ.map A) (projectFull (LinearMap.range A.toLinearMap) f).body=
      supportFunctional (μ.map A) f.body := by
  rw [functional_map _ (projectFull _ f).compact,functional_map _ f.compact]
  congr 1
  funext x
  exact support_projectFull _ f (show A x∈LinearMap.range A.toLinearMap from ⟨x,rfl⟩)

lemma minimizer_full_comparison [NeZero n] {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (A : Space n →L[ℝ] Space n) (hA : LinearMap.range A.toLinearMap≠⊥) (b : Bool)
    (g : RelativeGauge (LinearMap.range A.toLinearMap))
    (hmin : ∀ q : RelativeGauge (LinearMap.range A.toLinearMap),supportFunctional (μ.map A) q.body=1 →
      objective b g.toSeminorm≤ objective b q.toSeminorm)
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    ∃ ha : 0< supportFunctional (μ.map A) f.body,
      objective b g.toSeminorm≤ objective b (f.scale _ ha).toSeminorm := by
  let p := projectFull (LinearMap.range A.toLinearMap) f
  have hp := p.functional_pos hA (norm_integrable_map hμ A) (cosine_map_pos hμ hq A)
  have he : supportFunctional (μ.map A) p.body=supportFunctional (μ.map A) f.body := functional_projectFull A f
  have ha : 0< supportFunctional (μ.map A) f.body := he ▸ hp
  refine ⟨ha,?_⟩
  have hpn : supportFunctional (μ.map A) (p.scale _ ha).body=1 := by
    rw [p.functional_scale _ ha (μ.map A),he,inv_mul_cancel₀ ha.ne']
  apply (hmin _ hpn).trans
  apply Spherical.objective_mono b ((p.scale _ ha).ne_zero hA) ((f.scale _ ha).ne_zero top_ne_bot)
  intro x
  exact mul_le_mul_of_nonneg_left (projectFull_le _ f x) ha.le

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

lemma thicken_apply (g : RelativeGauge V) {ε : ℝ} (hε : 0<ε) (x : Space n) :
    thicken g ε hε x=g x+ε*‖x‖ := rfl

lemma thicken_ge (g : RelativeGauge V) {ε : ℝ} (hε : 0<ε) (x : Space n) :
    g x≤ thicken g ε hε x := le_add_of_nonneg_right (mul_nonneg hε.le (norm_nonneg x))

lemma support_thicken_le (g : RelativeGauge V) {ε : ℝ} (hε : 0<ε)
    {u : Space n} (hu : u∈V) : support (thicken g ε hε).body u≤ support g.body u := by
  apply (support_le_iff (thicken g ε hε).compact (thicken g ε hε).nonempty).mpr
  intro x hx
  have hpx : V.starProjection x∈g.body := by
    refine ⟨V.starProjection_apply_mem x,?_⟩
    change g (V.starProjection x)≤1
    rw [g.projection]
    exact (g.thicken_ge hε x).trans hx.2
  have hh := inner_le_support g.compact hpx u
  rwa [← Submodule.inner_starProjection_left_eq_right,V.starProjection_eq_self_iff.mpr hu] at hh

lemma functional_thicken_le {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (A : Space n →L[ℝ] Space n) (g : RelativeGauge (LinearMap.range A.toLinearMap))
    {ε : ℝ} (hε : 0<ε) :
    supportFunctional (μ.map A) (g.thicken ε hε).body≤ supportFunctional (μ.map A) g.body := by
  rw [functional_map _ (g.thicken ε hε).compact,functional_map _ g.compact]
  have hi (f : Set (Space n)) (hf : IsCompact f) (hfn : f.Nonempty) :=
    (integrable_map_measure (support_continuous hf).aestronglyMeasurable A.continuous.measurable.aemeasurable).mp
      (support_integrable (norm_integrable_map hμ A) hf hfn)
  exact integral_mono (hi _ (g.thicken ε hε).compact (g.thicken ε hε).nonempty) (hi _ g.compact g.nonempty)
    (fun x => support_thicken_le g hε (show A x∈LinearMap.range A.toLinearMap from ⟨x,rfl⟩))

lemma objective_thicken_tendsto [NeZero n] (g : RelativeGauge V) (hV : V≠⊥) (b : Bool) :
    Tendsto (fun i : ℕ => objective b (g.thicken (1/((i:ℝ)+1)) (by positivity)).toSeminorm)
      atTop (𝓝 (objective b g.toSeminorm)) := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx0]⟩
  have huV : (u:Space n)∈V := V.smul_mem _ hx
  have hun : (u:Space n)≠0 := by intro he; have hh := Spherical.norm_coe u; simp [he] at hh
  have hp := g.pos huV hun
  let F : C(Sphere n,ℝ) := ⟨fun u => g u,(Spherical.seminorm_continuous n g.toSeminorm).comp continuous_subtype_val⟩
  refine Spherical.objective_tendsto b hp (fun i => ⟨u,g.thicken_ge (by positivity) u⟩)
    (R := ‖F‖+1) ?_ (g.ne_zero hV) ?_
  · intro i v
    rw [thicken_apply,Spherical.norm_coe,mul_one]
    have hf : g v≤‖F‖ := (le_abs_self _).trans (F.norm_coe_le_norm v)
    have hi : (1:ℝ)/((i:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
    linarith
  · intro v
    have ht := (tendsto_const_nhds (x := g v)).add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖(v:Space n)‖)
    simpa only [thicken_apply,zero_mul,add_zero] using ht

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma cosine_map_tendsto (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (x : Space n) :
    Tendsto (fun i => cosineSeminorm (μ.map (Aj i)) (norm_integrable_map hμ (Aj i)) x)
      atTop (𝓝 (cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x)) := by
  simp_rw [cosine_map μ hμ]
  have hc : Continuous (fun B : Space n →L[ℝ] Space n => cosineSeminorm μ hμ (B.adjoint x)) :=
    (Spherical.seminorm_continuous n _).comp (by fun_prop)
  exact (hc.tendsto A).comp hA

omit [NeZero n] in
lemma normalized_limit_lower (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A))
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    {g : Seminorm ℝ (Space n)} (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x))) (x : Space n) :
    cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x≤ g x := by
  apply le_of_tendsto_of_tendsto (cosine_map_tendsto hμ hA x) (hg x)
  apply Eventually.of_forall
  intro i
  have hh := (gj i).normalized_lower (norm_integrable_map hμ (Aj i)) (hn i) x
  rwa [cosine_map_projection hμ] at hh

lemma full_comparison_limit (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 → objective b (gj i).toSeminorm≤ objective b q.toSeminorm)
    {g : Seminorm ℝ (Space n)}
    (hobj : Tendsto (fun i => objective b (gj i).toSeminorm) atTop (𝓝 (objective b g)))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    ∃ ha : 0< supportFunctional (μ.map A) f.body,
      objective b g≤ objective b (f.scale _ ha).toSeminorm := by
  obtain ⟨gA,hgn,hgm⟩ := exists_minimizer (norm_integrable_map hμ A) hAn (cosine_map_pos hμ hq A) b
  obtain ⟨ha,_⟩ := minimizer_full_comparison hμ hq A hAn b gA hgm f
  refine ⟨ha,?_⟩
  have hscale : ∀ {a : ℝ} (ha : 0< a),objective b (f.scale a ha).toSeminorm=
      if b then Real.log a+objective b f.toSeminorm else a*objective b f.toSeminorm := by
    intro a ha
    exact Spherical.objective_scale b (f.ne_zero top_ne_bot) ha (fun _ => rfl)
  rw [hscale]
  have ht := ((functional_map_continuous hμ f.compact f.nonempty).tendsto A).comp hA
  have htr : Tendsto (fun i => if b then Real.log (supportFunctional (μ.map (Aj i)) f.body)+objective b f.toSeminorm
      else supportFunctional (μ.map (Aj i)) f.body*objective b f.toSeminorm)
      atTop (𝓝 (if b then Real.log (supportFunctional (μ.map A) f.body)+objective b f.toSeminorm
        else supportFunctional (μ.map A) f.body*objective b f.toSeminorm)) := by
    cases b
    · exact ht.mul_const _
    · exact (ht.log ha.ne').add_const _
  apply le_of_tendsto_of_tendsto hobj htr
  apply Eventually.of_forall
  intro i
  obtain ⟨hai,hi⟩ := minimizer_full_comparison hμ hq (Aj i) (hAj i) b (gj i) (hm i) f
  rwa [hscale] at hi

/-- Every seminorm limit of actual minimizers is the actual minimizer in the
limiting range, including arbitrary drops of rank. -/
theorem minimizer_limit_identify (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 → objective b (gj i).toSeminorm≤ objective b q.toSeminorm)
    (gA : RelativeGauge (LinearMap.range A.toLinearMap)) (hgn : supportFunctional (μ.map A) gA.body=1)
    (hgm : ∀ q : RelativeGauge (LinearMap.range A.toLinearMap),supportFunctional (μ.map A) q.body=1 → objective b gA.toSeminorm≤ objective b q.toSeminorm)
    {g : Seminorm ℝ (Space n)} (hg : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x)))
    (hobj : Tendsto (fun i => objective b (gj i).toSeminorm) atTop (𝓝 (objective b g))) :
    g=gA.toSeminorm := by
  let V := LinearMap.range A.toLinearMap
  have hμA := norm_integrable_map hμ A
  have hqA := cosine_map_pos hμ hq A
  have hqle := normalized_limit_lower hμ hA gj hn hg
  obtain ⟨c,hc,hcb⟩ := seminorm_positive_subspace_bound V hAn (cosineSeminorm (μ.map A) hμA) hqA
  have hl (x : Space n) : c*‖V.starProjection x‖≤ g x := by
    have hh := hcb x
    rw [cosine_map_projection hμ] at hh
    exact hh.trans (hqle x)
  let p := project V g hc hl
  have hpnle : supportFunctional (μ.map A) p.body≤1 := by
    apply projected_limit_normalization hμ _ gj hn g hg hc hl
    intro x
    exact ((show Continuous (fun B : Space n →L[ℝ] Space n => B x) by fun_prop).tendsto A).comp hA
  have hp := p.functional_pos hAn hμA hqA
  let q := p.scale _ hp
  have hqn : supportFunctional (μ.map A) q.body=1 := by
    rw [functional_scale p _ hp (μ.map A),inv_mul_cancel₀ hp.ne']
  have hqg (x : Space n) : q x≤ g x := by
    exact (mul_le_of_le_one_left (apply_nonneg p.toSeminorm x) hpnle).trans (project_le V g hc hl x)
  have hg0 : g≠0 := by
    intro he
    have hzero : q.toSeminorm=0 := by ext x; exact le_antisymm (by simpa only [he,zero_apply] using hqg x) (apply_nonneg q.toSeminorm x)
    exact q.ne_zero hAn hzero
  have hupper : objective b g≤ objective b gA.toSeminorm := by
    apply ge_of_tendsto (gA.objective_thicken_tendsto hAn b)
    apply Eventually.of_forall
    intro i
    let ε : ℝ := 1/((i:ℝ)+1)
    have hε : 0<ε := by dsimp [ε]; positivity
    let f := gA.thicken ε hε
    obtain ⟨ha,hh⟩ := full_comparison_limit hμ hq hA hAn hAj b gj hm hobj f
    have hle : supportFunctional (μ.map A) f.body≤1 := by
      exact (functional_thicken_le hμ A gA hε).trans hgn.le
    apply hh.trans
    apply Spherical.objective_mono b ((f.scale _ ha).ne_zero top_ne_bot) (f.ne_zero top_ne_bot)
    intro x
    exact mul_le_of_le_one_left (apply_nonneg f.toSeminorm x) hle
  have hlower := hgm q hqn
  have hmid := Spherical.objective_mono b (q.ne_zero hAn) hg0 hqg
  have heq : objective b q.toSeminorm=objective b g := le_antisymm hmid (hupper.trans hlower)
  have hqeq := Spherical.objective_mono_eq b (q.ne_zero hAn) hg0 hqg heq
  have huniq := minimizer_unique hμA hAn b hgn hqn hgm (le_antisymm hlower (hmid.trans hupper))
  rw [← hqeq,← huniq]

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma full_functional_pos (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (A : Space n →L[ℝ] Space n) (hA : LinearMap.range A.toLinearMap≠⊥)
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) : 0< supportFunctional (μ.map A) f.body := by
  have hp := (projectFull (LinearMap.range A.toLinearMap) f).functional_pos hA
    (norm_integrable_map hμ A) (cosine_map_pos hμ hq A)
  rwa [functional_projectFull] at hp

lemma minimizers_uniform_bound (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 →
      objective b (gj i).toSeminorm≤ objective b q.toSeminorm) :
    ∃ R : ℝ,0< R ∧ ∀ i (u : Sphere n),gj i u≤ R := by
  let f := ball (⊤ : Submodule ℝ (Space n))
  let a : (Space n →L[ℝ] Space n) → ℝ := fun B => supportFunctional (μ.map B) f.body
  have ha := full_functional_pos hμ hq A hAn f
  have ht : Tendsto (fun i => a (Aj i)) atTop (𝓝 (a A)) :=
    ((functional_map_continuous hμ f.compact f.nonempty).tendsto A).comp hA
  let v : ℕ → ℝ := fun i => if b then Real.log (a (Aj i))+objective b f.toSeminorm
    else a (Aj i)*objective b f.toSeminorm
  have hvt : Tendsto v atTop (𝓝 (if b then Real.log (a A)+objective b f.toSeminorm else a A*objective b f.toSeminorm)) := by
    cases b
    · exact ht.mul_const _
    · exact (ht.log ha.ne').add_const _
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto v hvt).bddAbove
  obtain ⟨R,hR,hRb⟩ := Spherical.objective_coercive (n := n) b M
  refine ⟨R,hR,fun i u => hRb _ ((gj i).ne_zero (hAj i)) ?_ u⟩
  obtain ⟨hai,hh⟩ := minimizer_full_comparison hμ hq (Aj i) (hAj i) b (gj i) (hm i) f
  have he := Spherical.objective_scale b (g := f.toSeminorm) (f := (f.scale _ hai).toSeminorm)
    (f.ne_zero top_ne_bot) hai (fun _ => rfl)
  rw [he] at hh
  exact hh.trans (hM (mem_range_self i))

lemma objective_tendsto_of_pointwise {gj : ℕ → Seminorm ℝ (Space n)} {g : Seminorm ℝ (Space n)}
    (hg : g≠0) {R : ℝ} (hR : ∀ i (u : Sphere n),gj i u≤ R)
    (ht : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x))) (b : Bool) :
    Tendsto (fun i => objective b (gj i)) atTop (𝓝 (objective b g)) := by
  have hex : ∃ u : Sphere n,0< g u := by
    by_contra! hn
    have he : g=0 := by
      ext x
      rw [← Spherical.radialExtension_seminorm g x]
      have hz : (fun u : Sphere n => g u)=(fun _ => 0) := by
        funext u; exact le_antisymm (hn u) (apply_nonneg g _)
      rw [hz]
      unfold Spherical.radialExtension
      split_ifs <;> simp
    exact hg he
  obtain ⟨u,hu⟩ := hex
  have hh := (ht u).eventually (lt_mem_nhds (show g u/2< g u by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  apply (tendsto_add_atTop_iff_nat N).mp
  apply Spherical.objective_tendsto b (show 0< g u/2 by linarith)
    (fun i => ⟨u,(hN (i+N) (Nat.le_add_left N i)).le⟩) (fun i => hR (i+N)) hg
  intro v
  exact (ht v).comp (tendsto_add_atTop_nat N)

omit [NeZero n] in
lemma limit_ne_zero (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    {g : Seminorm ℝ (Space n)} (ht : ∀ x,Tendsto (fun i => gj i x) atTop (𝓝 (g x))) : g≠0 := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff _).mp hAn
  have hp := cosine_map_pos hμ hq A x hx hx0
  have hh := normalized_limit_lower hμ hA gj hn ht x
  intro he
  rw [he,zero_apply] at hh
  linarith

/-- Sequential uniform compactness, and identification, for the actual
optimizer family across all nonzero linear maps, without a rank restriction. -/
theorem minimizers_subsequence (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    {Aj : ℕ → Space n →L[ℝ] Space n} {A : Space n →L[ℝ] Space n}
    (hA : Tendsto Aj atTop (𝓝 A)) (hAn : LinearMap.range A.toLinearMap≠⊥)
    (hAj : ∀ i,LinearMap.range (Aj i).toLinearMap≠⊥) (b : Bool)
    (gj : ∀ i,RelativeGauge (LinearMap.range (Aj i).toLinearMap))
    (hn : ∀ i,supportFunctional (μ.map (Aj i)) (gj i).body=1)
    (hm : ∀ i (q : RelativeGauge (LinearMap.range (Aj i).toLinearMap)),supportFunctional (μ.map (Aj i)) q.body=1 →
      objective b (gj i).toSeminorm≤ objective b q.toSeminorm)
    (gA : RelativeGauge (LinearMap.range A.toLinearMap)) (hgn : supportFunctional (μ.map A) gA.body=1)
    (hgm : ∀ q : RelativeGauge (LinearMap.range A.toLinearMap),supportFunctional (μ.map A) q.body=1 →
      objective b gA.toSeminorm≤ objective b q.toSeminorm) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧
      TendstoUniformly (fun i (u : Sphere n) => gj (φ i) u) (fun u => gA u) atTop := by
  obtain ⟨R,hR,hRb⟩ := minimizers_uniform_bound hμ hq hA hAn hAj b gj hm
  obtain ⟨g,φ,hφ,hu,ht⟩ := Spherical.bounded_seminorm_subsequence (R := ⟨R,hR.le⟩)
    (fun i => (gj i).toSeminorm) hRb
  have hA' := hA.comp hφ.tendsto_atTop
  have hg := limit_ne_zero hμ hq hA' hAn (fun i => gj (φ i)) (fun i => hn (φ i)) ht
  have ho := objective_tendsto_of_pointwise hg (fun i => hRb (φ i)) ht b
  have he := minimizer_limit_identify hμ hq hA' hAn (fun i => hAj (φ i)) b
    (fun i => gj (φ i)) (fun i => hn (φ i)) (fun i => hm (φ i)) gA hgn hgm ht ho
  refine ⟨φ,hφ,?_⟩
  rwa [he] at hu

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.PositionMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

lemma optimizer_normalized (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n) :
    supportFunctional (μ.map A.val) (optimizer hμ hq b A).body=1 :=
  (exists_minimizer (norm_integrable_map hμ A) A.property (cosine_map_pos hμ hq A) b).choose_spec.1

lemma optimizer_minimal (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n)
    (g : RelativeGauge (LinearMap.range A.val.toLinearMap)) (hg : supportFunctional (μ.map A.val) g.body=1) :
    objective b (optimizer hμ hq b A).toSeminorm≤ objective b g.toSeminorm :=
  (exists_minimizer (norm_integrable_map hμ A) A.property (cosine_map_pos hμ hq A) b).choose_spec.2 g hg

/-- Rank-continuity of the actual canonical variational optimizer. The
codomain carries the uniform norm on the entire ambient sphere. -/
theorem optimizerSphere_continuous (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) :
    Continuous (optimizerSphere hμ hq b) := by
  apply continuous_iff_seqContinuous.mpr
  intro Aj A hA
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hAv : Tendsto (fun i => (Aj (ns i)).val) atTop (𝓝 A.val) :=
    (continuous_subtype_val.tendsto A).comp (hA.comp hns)
  obtain ⟨φ,_,ht⟩ := minimizers_subsequence hμ hq hAv A.property (fun i => (Aj (ns i)).property) b
    (fun i => optimizer hμ hq b (Aj (ns i))) (fun i => optimizer_normalized hμ hq b (Aj (ns i)))
    (fun i => optimizer_minimal hμ hq b (Aj (ns i))) (optimizer hμ hq b A)
    (optimizer_normalized hμ hq b A) (optimizer_minimal hμ hq b A)
  refine ⟨φ,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr ?_⟩
  exact ht

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma gaussian_real_second_moment :
    (∫ t : ℝ,t^2*Real.exp (-(t^2)))=(1/2:ℝ)*(∫ t : ℝ,Real.exp (-(t^2))) := by
  have h0 := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r : ℝ => Real.exp (-(r^2)))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r : ℝ => r^2*Real.exp (-(r^2)))
  simp only [Module.finrank_self,Nat.sub_self,pow_zero,one_smul,Real.norm_eq_abs,sq_abs] at h0 h2
  have he : (∫ r in Ioi (0:ℝ),Real.exp (-(r^2)))=gaussianRadial 0 := by simp [gaussianRadial]
  change _=volume.real (ball (0:ℝ) 1)*gaussianRadial 2 at h2
  rw [he] at h0
  change _=volume.real (ball (0:ℝ) 1)*gaussianRadial 0 at h0
  rw [h2,h0,show (2:ℕ)=0+2 from rfl,gaussianRadial_add_two]
  norm_num
  ring

lemma seminorm_add_kernel {n : ℕ} (g : Seminorm ℝ (Space n)) {e : Space n}
    (he : g e=0) (x : Space n) (t : ℝ) : g (x+t • e)=g x := by
  have h1 := map_add_le_add g x (t • e)
  have h2 := map_add_le_add g (x+t • e) (-(t • e))
  have hz : g (t • e)=0 := by rw [map_smul_eq_mul,he,mul_zero]
  rw [hz,add_zero] at h1
  rw [add_neg_cancel_right,map_neg_eq_map,hz,add_zero] at h2
  exact le_antisymm h1 h2

lemma gaussian_shadow_norm {n : ℕ} (e : Sphere n) (z : perpendicular (e:Space n)) (t : ℝ) :
    ‖(z:Space n)+t • (e:Space n)‖^2=‖z‖^2+t^2 := by
  rw [norm_add_sq_real,inner_smul_right,real_inner_comm,perpendicular_inner,norm_smul,
    Real.norm_eq_abs,mul_pow,norm_coe,one_pow,mul_one,sq_abs]
  simp

/-- Genuine Gaussian independence in a seminorm kernel, proved by the
measure-preserving orthogonal coordinate map and Fubini product integrals. -/
lemma gaussian_kernel_moment {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ)
    (e : Sphere n) (he : g e=0) :
    (∫ x : Space n,g x^k*⟪(e:Space n),x⟫^2*Real.exp (-(‖x‖^2)))=
      (1/2:ℝ)*(∫ x : Space n,g x^k*Real.exp (-(‖x‖^2))) := by
  let F : perpendicular (e:Space n) → ℝ := fun z => g z^k*Real.exp (-(‖z‖^2))
  have he0 : (fun z : perpendicular (e:Space n) × ℝ =>
      g (shadowMeasurableEquiv e z)^k*Real.exp (-(‖shadowMeasurableEquiv e z‖^2)))=
      (fun z => F z.1*Real.exp (-(z.2^2))) := by
    funext z
    change g ((z.1:Space n)+z.2 • (e:Space n))^k*Real.exp (-‖(z.1:Space n)+z.2 • (e:Space n)‖^2)=_
    rw [seminorm_add_kernel g he,gaussian_shadow_norm,neg_add,Real.exp_add]
    dsimp only [F]
    ring
  have he2 : (fun z : perpendicular (e:Space n) × ℝ =>
      g (shadowMeasurableEquiv e z)^k*⟪(e:Space n),shadowMeasurableEquiv e z⟫^2*
        Real.exp (-(‖shadowMeasurableEquiv e z‖^2)))=
      (fun z => F z.1*(z.2^2*Real.exp (-(z.2^2)))) := by
    funext z
    change g ((z.1:Space n)+z.2 • (e:Space n))^k*⟪(e:Space n),(z.1:Space n)+z.2 • (e:Space n)⟫^2*
      Real.exp (-‖(z.1:Space n)+z.2 • (e:Space n)‖^2)=_
    rw [seminorm_add_kernel g he,gaussian_shadow_norm,neg_add,Real.exp_add,
      inner_add_right,perpendicular_inner,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
    dsimp only [F]
    ring
  rw [← (shadowMeasurableEquiv_measurePreserving e).integral_comp (shadowMeasurableEquiv e).measurableEmbedding
    (fun x : Space n => g x^k*⟪(e:Space n),x⟫^2*Real.exp (-(‖x‖^2))),
    ← (shadowMeasurableEquiv_measurePreserving e).integral_comp (shadowMeasurableEquiv e).measurableEmbedding
    (fun x : Space n => g x^k*Real.exp (-(‖x‖^2)))]
  rw [he0,he2,Measure.volume_eq_prod,
    integral_prod_mul F (fun t : ℝ => t^2*Real.exp (-(t^2))),
    integral_prod_mul F (fun t : ℝ => Real.exp (-(t^2))),gaussian_real_second_moment]
  ring

/-- The boundary moment ratio, for every seminorm and every natural
homogeneity degree, including all singular and nonsmooth cases. -/
theorem sphere_kernel_moment {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) (k : ℕ)
    (e : Sphere n) (he : g e=0) :
    ((n:ℝ)+k)*mean (fun u : Sphere n => g u^k*⟪(e:Space n),(u:Space n)⟫^2)=
      mean (fun u : Sphere n => g u^k) := by
  have hh0 : ∀ r : ℝ,0<r → ∀ x : Space n,g (r • x)^k=r^k*g x^k := by
    intro r hr x
    rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le,mul_pow]
  have hh2 : ∀ r : ℝ,0<r → ∀ x : Space n,g (r • x)^k*⟪(e:Space n),r • x⟫^2=
      r^(k+2)*(g x^k*⟪(e:Space n),x⟫^2) := by
    intro r hr x
    rw [hh0 r hr,inner_smul_right,mul_pow,pow_add]
    ring
  have hG := gaussian_kernel_moment g k e he
  rw [homogeneous_gaussian_integral (k+2) _ hh2,homogeneous_gaussian_integral k _ hh0] at hG
  rw [show n-1+(k+2)=(n-1+k)+2 by omega,gaussianRadial_add_two] at hG
  have hn : ((n-1+k:ℕ):ℝ)+1=(n:ℝ)+k := by
    have hh : n-1+k+1=n+k := by have := NeZero.pos n;omega
    exact_mod_cast hh
  rw [hn] at hG
  have hc : (n:ℝ)*kappa n*gaussianRadial (n-1+k)≠0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)) (kappa_pos n).ne') (gaussianRadial_pos _).ne'
  apply (mul_left_cancel₀ hc)
  nlinarith only [hG]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
variable {n : ℕ}
lemma op_continuous : Continuous (op : Mat n → Space n →L[ℝ] Space n) := by
  let L : Mat n →ₗ[ℝ] (Space n →L[ℝ] Space n) :=
    { toFun := op
      map_add' := by intro A B; ext x i; simp [op_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a A; ext x i; simp [op_apply,Finset.mul_sum,mul_assoc] }
  exact L.continuous_of_finiteDimensional
lemma tr_continuous : Continuous (tr : Mat n → ℝ) := by
  unfold tr
  fun_prop
lemma quad_add (A B : Mat n) (x : Space n) : quad (A+B) x=quad A x+quad B x := by
  simp [quad_eq,add_mul,Finset.sum_add_distrib]
lemma quad_smul (a : ℝ) (A : Mat n) (x : Space n) : quad (a • A) x=a*quad A x := by
  simp [quad_eq,mul_assoc,Finset.mul_sum]
lemma quad_sub (A B : Mat n) (x : Space n) : quad (A-B) x=quad A x-quad B x := by
  simp [quad_eq,sub_mul,Finset.sum_sub_distrib]
lemma symmetric_op {A : Mat n} (hA : Symmetric A) : (op A).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact hA j i
lemma op_kernel_of_quad_zero {A : Mat n} (hA : PSD A) {x : Space n} (hx : quad A x=0) : op A x=0 := by
  have hs := symmetric_op hA.1
  have hxy (y : Space n) : ⟪y,op A x⟫=0 := by
    have hh (t : ℝ) := hA.2 (x+t • y)
    have he (t : ℝ) : quad A (x+t • y)=2*t*⟪y,op A x⟫+t^2*quad A y := by
      simp only [quad,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
        inner_smul_right,conj_trivial] at *
      have hi : ⟪x,op A y⟫=⟪y,op A x⟫ := by
        have h := hs x y
        change ⟪op A x,y⟫=⟪x,op A y⟫ at h
        rw [← h,real_inner_comm]
      rw [hx,hi]; ring
    simp_rw [he] at hh
    let a := quad A y
    let b := ⟪y,op A x⟫
    have ha : 0≤a := hA.2 y
    have han : a+1≠0 := by linarith
    have hv := mul_nonneg (hh (-b/(a+1))) (sq_nonneg (a+1))
    have heval : (2*(-b/(a+1))*b+(-b/(a+1))^2*a)*(a+1)^2= -b^2*(a+2) := by
      field_simp
      ring
    change 0≤(2*(-b/(a+1))*b+(-b/(a+1))^2*a)*(a+1)^2 at hv
    rw [heval] at hv
    change b=0
    nlinarith [sq_nonneg b,mul_nonneg ha (sq_nonneg b)]
  exact inner_self_eq_zero.mp (hxy (op A x))

lemma symmetric_closed : IsClosed {A : Mat n | Symmetric A} := by
  have he : {A : Mat n | Symmetric A}=⋂ i : Fin n,⋂ j : Fin n,{A : Mat n | A (i,j)=A (j,i)} := by
    ext A; simp [Symmetric]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq (by fun_prop) (by fun_prop)
lemma quad_nonneg_closed (x : Space n) : IsClosed {A : Mat n | 0≤quad A x} := by
  have hc : Continuous (fun A : Mat n => quad A x) :=
    by simp_rw [quad_eq]; fun_prop
  exact isClosed_le (continuous_const : Continuous (fun _ : Mat n => (0:ℝ))) hc
lemma psd_closed : IsClosed {A : Mat n | PSD A} := by
  have hq : IsClosed (⋂ x : Space n,{A : Mat n | 0≤quad A x}) :=
    isClosed_iInter (fun x : Space n => quad_nonneg_closed x)
  have h := (symmetric_closed (n := n)).inter hq
  convert h using 1
  ext A
  simp only [mem_inter_iff,mem_ofPred_eq,mem_iInter,PSD]
lemma domain_closed : IsClosed (domain n) :=
  (psd_closed (n := n)).inter (isClosed_eq (tr_continuous (n := n)) continuous_const)
lemma domain_convex : Convex ℝ (domain n) := by
  intro A hA B hB a b ha hb hab
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i j
    change a*A (i,j)+b*B (i,j)=a*A (j,i)+b*B (j,i)
    rw [hA.1.1 i j,hB.1.1 i j]
  · intro x
    rw [quad_add,quad_smul,quad_smul]
    exact add_nonneg (mul_nonneg ha (hA.1.2 x)) (mul_nonneg hb (hB.1.2 x))
  · change (∑ i,(a*A (i,i)+b*B (i,i)))=1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    change a*tr A+b*tr B=1
    rw [hA.2,hB.2,mul_one,mul_one,hab]

lemma quad_basis_add (A : Mat n) (i j : Fin n) (a b : ℝ) :
    quad A (a • EuclideanSpace.single i 1+b • EuclideanSpace.single j 1)=
      a^2*A (i,i)+a*b*(A (i,j)+A (j,i))+b^2*A (j,j) := by
  simp [quad_eq,add_mul,mul_add,Finset.sum_add_distrib]
  ring
lemma domain_entry_bound {A : Mat n} (hA : A∈domain n) (i j : Fin n) : |A (i,j)|≤1 := by
  have hd (i : Fin n) : 0≤A (i,i) := by simpa only [quad_basis] using hA.1.2 (EuclideanSpace.single i 1)
  have hd1 (i : Fin n) : A (i,i)≤1 := by
    rw [← hA.2]
    exact Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  have hp := hA.1.2 ((1:ℝ) • EuclideanSpace.single i 1+(1:ℝ) • EuclideanSpace.single j 1)
  have hm := hA.1.2 ((1:ℝ) • EuclideanSpace.single i 1+(-1:ℝ) • EuclideanSpace.single j 1)
  rw [quad_basis_add,hA.1.1 j i] at hp hm
  exact abs_le.mpr ⟨by nlinarith [hd1 i,hd1 j],by nlinarith [hd1 i,hd1 j]⟩
lemma domain_compact : IsCompact (domain n) := by
  apply (isCompact_closedBall (0:Mat n) (n:ℝ)).of_isClosed_subset domain_closed
  intro A hA
  rw [mem_closedBall,dist_zero_right]
  have hn : (0:ℝ)≤n := Nat.cast_nonneg _
  rw [← sq_le_sq₀ (norm_nonneg A) hn,EuclideanSpace.norm_sq_eq]
  calc
    ∑ i : Fin n × Fin n,‖A i‖^2 ≤ ∑ _ : Fin n × Fin n,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := domain_entry_bound hA i.1 i.2
      dsimp only [Real.norm_eq_abs]
      nlinarith [abs_nonneg (A i)]
    _ = (n:ℝ)^2 := by simp [sq]
lemma domain_nonempty [NeZero n] : (domain n).Nonempty := by
  let A : Mat n := WithLp.toLp 2 (fun ij => if ij.1=ij.2 then (n:ℝ)⁻¹ else 0)
  refine ⟨A,⟨?_,?_⟩,?_⟩
  · intro i j
    dsimp [A]
    simp only [eq_comm]
  · intro x
    rw [quad_eq]
    dsimp [A]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    apply Finset.sum_nonneg
    intro i _
    simpa only [sq,mul_assoc] using mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ)≤n)) (sq_nonneg (x i))
  · simp [tr,A,NeZero.ne n]
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere mean sigma norm_coe continuous_integrable seminorm_continuous)
variable {n : ℕ} [NeZero n]

lemma mean_power_pos (g : Seminorm ℝ (Space n)) (hg : g≠0) (k : ℕ) :
    0 < mean (fun u : Sphere n => g u^k) := by
  obtain ⟨R,e,hR,_,hb⟩ := Spherical.seminorm_coordinate_minorant g hg
  have he := hb e
  simp only [real_inner_self_eq_norm_sq,norm_coe,one_pow,abs_one,mul_one] at he
  have hc : Continuous (fun u : Sphere n => g u^k) := ((seminorm_continuous n g).comp continuous_subtype_val).pow k
  apply integral_pos_of_integrable_nonneg_nonzero (x := e) hc (continuous_integrable hc)
    (fun u => pow_nonneg (apply_nonneg g (u:Space n)) k)
  exact (pow_pos (hR.trans_le he) k).ne'

omit [NeZero n] in
lemma field_symmetric (g : Seminorm ℝ (Space n)) (k : ℕ) : Symmetric (momentField g k) := by
  intro i j
  change mean _ / _ - _ / _=mean _ / _ - _ / _
  congr 2
  · congr 1; funext u; ring
  · simp only [eq_comm]

lemma field_trace (g : Seminorm ℝ (Space n)) (hg : g≠0) (k : ℕ) : tr (momentField g k)=0 := by
  have hc (i : Fin n) : Continuous (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) i) := by
    exact (((seminorm_continuous n g).comp continuous_subtype_val).pow k).mul (by fun_prop) |>.mul (by fun_prop)
  have hsum : (∑ i : Fin n,mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) i))=
      mean (fun u : Sphere n => g u^k) := by
    rw [← Spherical.mean_sum _ (fun i _ => hc i)]
    congr 1
    funext u
    have hh := EuclideanSpace.real_norm_sq_eq (u:Space n)
    rw [norm_coe,one_pow] at hh
    calc
      (∑ i : Fin n,g u^k*(u:Space n) i*(u:Space n) i)=g u^k*(∑ i : Fin n,(u:Space n) i^2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = g u^k := by rw [← hh,mul_one]
  simp only [tr,momentField,ite_true]
  change (∑ i : Fin n,(mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) i)/mean (fun u : Sphere n => g u^k)-1/(n:ℝ)))=0
  rw [Finset.sum_sub_distrib,← Finset.sum_div,hsum,div_self (mean_power_pos g hg k).ne']
  simp [NeZero.ne n]

lemma field_quad (g : Seminorm ℝ (Space n)) (k : ℕ) (x : Space n) :
    quad (momentField g k) x=mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2)/
      mean (fun u : Sphere n => g u^k)-‖x‖^2/(n:ℝ) := by
  have hc (i j : Fin n) : Continuous (fun u : Sphere n =>
      g u^k*(u:Space n) i*(u:Space n) j*x i*x j) := by
    exact (((((seminorm_continuous n g).comp continuous_subtype_val).pow k).mul (by fun_prop)).mul (by fun_prop)).mul continuous_const |>.mul continuous_const
  have hnum : (∑ i : Fin n,∑ j : Fin n,
      mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)*x i*x j)=
      mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2) := by
    have hi (i : Fin n) : (∑ j : Fin n,mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)*x i*x j)=
        mean (fun u : Sphere n => ∑ j : Fin n,g u^k*(u:Space n) i*(u:Space n) j*x i*x j) := by
      simp_rw [mean,← integral_mul_const]
      exact (integral_finsetSum _ (fun j _ => continuous_integrable (hc i j))).symm
    simp_rw [hi]
    rw [← Spherical.mean_sum _ (fun i _ => continuous_finsetSum _ (fun j _ => hc i j))]
    congr 1
    funext u
    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,sq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [quad_eq]
  simp only [momentField,sub_mul,Finset.sum_sub_distrib]
  have hdiv : (∑ i : Fin n,∑ j : Fin n,
      mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)/mean (fun u : Sphere n => g u^k)*x i*x j)=
      mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2)/mean (fun u : Sphere n => g u^k) := by
    simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
    rw [hnum]
  rw [hdiv]
  congr 1
  simp only [ite_div,zero_div,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_div]
  simp only [one_div,sq]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma field_kernel {g : Seminorm ℝ (Space n)} (hg : g≠0) {k : ℕ} (hk : 0<k)
    (e : Sphere n) (he : g e=0) : quad (momentField g k) e<0 := by
  rw [field_quad,norm_coe,one_pow]
  have hm := sphere_kernel_moment g k e he
  have hp := mean_power_pos g hg k
  have hn : (0:ℝ)<n := Nat.cast_pos.mpr (NeZero.pos n)
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  apply sub_neg.mpr
  apply (div_lt_iff₀ hp).mpr
  rw [one_div,mul_comm,← div_eq_mul_inv,lt_div_iff₀ hn]
  have hnon : 0 < mean (fun u : Sphere n => g u^k*⟪(e:Space n),(u:Space n)⟫^2) := by nlinarith
  nlinarith
end PettyProjection.Position
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
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere norm_coe)

lemma compact_inward {X : Type uX} [TopologicalSpace X] [CompactSpace X]
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ x,0≤a x) (hab : ∀ x,a x=0 → b x<0) :
    ∃ ε : ℝ,0<ε ∧ ∀ x,0<a x-ε*b x := by
  let K : Set X := {x | 0≤b x}
  have hK : IsCompact K := (isClosed_le continuous_const hb).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne ha.continuousOn
    have hax : 0<a x := lt_of_le_of_ne (ha0 x) (fun h => (hab x h.symm).not_ge hx)
    obtain ⟨M,hM,hbound⟩ := (isCompact_univ.image hb).isBounded.exists_pos_norm_le
    let ε := a x/(2*M)
    have hε : 0<ε := div_pos hax (by positivity)
    refine ⟨ε,hε,fun y => ?_⟩
    by_cases hy : y∈K
    · have hmy : a x≤a y := hmin hy
      have hbM : b y≤M := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound (b y) ⟨y,mem_univ _,rfl⟩)
      have hh : ε*M=a x/2 := by dsimp [ε]; field_simp
      have hle := mul_le_mul_of_nonneg_left hbM hε.le
      rw [hh] at hle
      linarith
    · have hby : b y<0 := lt_of_not_ge hy
      have hneg := mul_neg_of_pos_of_neg hε hby
      linarith [ha0 y]
  · refine ⟨1,zero_lt_one,fun y => ?_⟩
    have hby : b y<0 := by
      by_contra h
      exact hne ⟨y,le_of_not_gt h⟩
    linarith [ha0 y]

lemma inward_perturbation {n : ℕ} [NeZero n] {A F : Mat n} (hA : A∈domain n)
    (hF : Symmetric F) (htr : tr F=0)
    (hker : ∀ e : Sphere n,op A e=0 → quad F e<0) :
    ∃ ε : ℝ,0<ε ∧ A-ε • F∈domain n ∧ ∀ x : Space n,x≠0 → 0<quad (A-ε • F) x := by
  have hca : Continuous (fun u : Sphere n => quad A u) :=
    by simp_rw [quad_eq]; fun_prop
  have hcf : Continuous (fun u : Sphere n => quad F u) :=
    by simp_rw [quad_eq]; fun_prop
  obtain ⟨ε,hε,hp⟩ := compact_inward hca hcf (fun u => hA.1.2 u)
    (fun u hu => hker u (op_kernel_of_quad_zero hA.1 hu))
  have hq : ∀ x : Space n,x≠0 → 0<quad (A-ε • F) x := by
    intro x hx
    let u : Sphere n := ⟨‖x‖⁻¹ • x,by rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
    have hh := hp u
    rw [← quad_smul,← quad_sub] at hh
    have he : quad (A-ε • F) u=‖x‖⁻¹^2*quad (A-ε • F) x := by
      simp only [quad,u,map_smul,inner_smul_left,inner_smul_right,conj_trivial]
      ring
    rw [he] at hh
    exact (mul_pos_iff.mp hh).resolve_right (fun h => (sq_nonneg ‖x‖⁻¹).not_gt h.1) |>.2
  refine ⟨ε,hε,⟨⟨?_,?_⟩,?_⟩,hq⟩
  · intro i j
    change A (i,j)-ε*F (i,j)=A (j,i)-ε*F (j,i)
    rw [hA.1.1 i j,hF i j]
  · intro x
    by_cases hx : x=0
    · simp [hx,quad]
    · exact (hq x hx).le
  · change (∑ i,(A (i,i)-ε*F (i,i)))=1
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    change tr A-ε*tr F=1
    rw [hA.2,htr,mul_zero,sub_zero]

/-- The topological mechanism. The field is genuine and continuous;
its negativity on every null direction forces an interior zero. -/
theorem traceOne_field_zero {n : ℕ} [NeZero n] (F : {A : Mat n // A∈domain n} → Mat n)
    (hFc : Continuous F) (hFs : ∀ A,Symmetric (F A)) (hFt : ∀ A,tr (F A)=0)
    (hFk : ∀ A (e : Sphere n),op A.val e=0 → quad (F A) e<0) :
    ∃ A : {A : Mat n // A∈domain n},F A=0 ∧ Function.Injective (op A.val) := by
  let p := FixedPoint.nearest (domain n) domain_nonempty domain_compact.isComplete domain_convex
  have hp (x : Mat n) : p x∈domain n := FixedPoint.nearest_mem _ _ _ _ x
  have hpc : Continuous p := (FixedPoint.nearest_lipschitz _ _ _ _).continuous
  let f : Mat n → Mat n := fun x => p (x-F ⟨p x,hp x⟩)
  have hfc : Continuous f := hpc.comp (continuous_id.sub (hFc.comp (hpc.subtype_mk hp)))
  obtain ⟨A,hA,hfix⟩ := FixedPoint.fixedPoint_compact_convex domain_nonempty domain_compact domain_convex
    hfc.continuousOn (fun x _ => hp _)
  let a : {A : Mat n // A∈domain n} := ⟨A,hA⟩
  have hpa : p A=A := FixedPoint.nearest_eq_of_mem _ _ _ _ hA
  have hfix' : p (A-F a)=A := by simpa only [f,hpa] using hfix
  have hi := FixedPoint.nearest_inner (domain n) domain_nonempty domain_compact.isComplete domain_convex (A-F a)
  change ∀ z∈domain n,⟪A-F a-p (A-F a),z-p (A-F a)⟫≤0 at hi
  rw [hfix'] at hi
  obtain ⟨ε,hε,hB,_⟩ := inward_perturbation hA (hFs a) (hFt a) (hFk a)
  have hh := hi (A-ε • F a) hB
  have hf0 : F a=0 := by
    simp only [sub_sub_cancel_left,inner_neg_left,inner_neg_right,inner_smul_right,real_inner_self_eq_norm_sq] at hh
    have hs : ‖F a‖^2≤0 := nonpos_of_mul_nonpos_left (by nlinarith only [hh]) hε
    have hn : ‖F a‖=0 := by nlinarith [norm_nonneg (F a)]
    exact norm_eq_zero.mp hn
  refine ⟨a,hf0,?_⟩
  apply (op A).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change op A x=0 at hx
  by_contra hx0
  let e : Sphere n := ⟨‖x‖⁻¹ • x,by rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]⟩
  have he : op A e=0 := by change op A (‖x‖⁻¹ • x)=0; rw [map_smul,hx,smul_zero]
  have hh := hFk a e he
  rw [hf0] at hh
  simp only [quad_eq] at hh
  simp at hh
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere mean seminorm_continuous)
open RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

instance domain_compactSpace : CompactSpace (Domain n) := isCompact_iff_compactSpace.mp domain_compact

omit [NeZero n] in
lemma domainMap_continuous : Continuous (domainMap : Domain n → NonzeroMap n) :=
  (op_continuous.comp continuous_subtype_val).subtype_mk _

lemma optimizer_kernel (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) (A : Domain n)
    (e : Space n) (he : op A.val e=0) : optimizer hμ hq b (domainMap A) e=0 := by
  let V := LinearMap.range (op A.val).toLinearMap
  have hp : V.starProjection e=0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (V.zero_mem)
    rintro y ⟨z,rfl⟩
    simp only [sub_zero]
    have hs := symmetric_op A.property.1.1 e z
    change ⟪op A.val e,z⟫=⟪e,op A.val z⟫ at hs
    rw [he,inner_zero_left] at hs
    exact hs.symm
  have hh := (optimizer hμ hq b (domainMap A)).projection e
  change (optimizer hμ hq b (domainMap A)) (V.starProjection e)=_ at hh
  rw [hp] at hh
  exact hh.symm.trans (map_zero _)

lemma optimizer_joint_continuous (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) :
    Continuous (fun p : Domain n × Sphere n => optimizer hμ hq b (domainMap p.1) p.2) := by
  exact ((optimizerSphere_continuous hμ hq b).comp domainMap_continuous).fst'.eval continuous_snd

lemma positionField_continuous (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) (k : ℕ) :
    Continuous (positionField hμ hq b k) := by
  have hg := optimizer_joint_continuous hμ hq b
  have hm : Continuous (fun A : Domain n => mean (fun u : Sphere n => optimizer hμ hq b (domainMap A) u^k)) := by
    simpa only [Measure.restrict_univ,mean] using
      (continuous_parametric_integral_of_continuous (μ := Spherical.sigma n) (hg.pow k) isCompact_univ)
  have hij (i j : Fin n) : Continuous (fun A : Domain n => mean (fun u : Sphere n =>
      optimizer hμ hq b (domainMap A) u^k*(u:Space n) i*(u:Space n) j)) := by
    have hc : Continuous (fun p : Domain n × Sphere n =>
        optimizer hμ hq b (domainMap p.1) p.2^k*(p.2:Space n) i*(p.2:Space n) j) :=
      (hg.pow k).mul (by fun_prop) |>.mul (by fun_prop)
    simpa only [Measure.restrict_univ,mean] using
      (continuous_parametric_integral_of_continuous (μ := Spherical.sigma n) hc isCompact_univ)
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact ((hij ij.1 ij.2).div hm (fun A =>
    (mean_power_pos _ ((optimizer hμ hq b (domainMap A)).ne_zero (domainMap A).property) k).ne')).sub continuous_const

/-- A genuine nonsingular affine position for the variational optimizer. The
trace-one representative is used here; determinant normalization is a scalar
change and is performed in the global assembly. -/
theorem exists_optimizer_position (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) {k : ℕ} (hk : 0<k) :
    ∃ A : Domain n,Function.Injective (op A.val) ∧
      momentField (optimizer hμ hq b (domainMap A)).toSeminorm k=0 := by
  obtain ⟨A,hA,hinj⟩ := traceOne_field_zero (positionField hμ hq b k)
    (positionField_continuous hμ hq b k)
    (fun A => field_symmetric _ k)
    (fun A => field_trace _ ((optimizer hμ hq b (domainMap A)).ne_zero (domainMap A).property) k)
    (fun A e he => field_kernel ((optimizer hμ hq b (domainMap A)).ne_zero (domainMap A).property)
      hk e (optimizer_kernel hμ hq b A e he))
  exact ⟨A,hinj,hA⟩
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma copy_minimizer {V : Submodule ℝ (Space n)} (hV : V=⊤)
    {μ : Measure (Space n)} {b : Bool} (g : RelativeGauge V)
    (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge V,supportFunctional μ q.body=1 →
      Spherical.objective b g.toSeminorm≤Spherical.objective b q.toSeminorm) :
    ∃ f : RelativeGauge (⊤ : Submodule ℝ (Space n)),f.toSeminorm=g.toSeminorm ∧ IsMinimizer μ b f := by
  subst V
  exact ⟨g,rfl,hgn,hmin⟩

/-- Actual full-dimensional position of the logarithmic/linear optimizer,
with no determinant normalization needed in the later weighted assembly. -/
theorem exists_symmetric_position_oai {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x) :
    ∃ T : Space n ≃L[ℝ] Space n,T.toLinearMap.IsSymmetric ∧
      ∃ g : RelativeGauge (⊤ : Submodule ℝ (Space n)),IsMinimizer (μ.map T) (regime n) g ∧
        Position.momentField g.toSeminorm (Scalar.exponent n)=0 := by
  obtain ⟨A,hinj,hF⟩ := Position.exists_optimizer_position hμ hq (regime n) (exponent_pos n)
  have hsurj : Function.Surjective (Position.op A.val) :=
    LinearMap.surjective_of_injective (f := (Position.op A.val).toLinearMap) hinj
  have hfull : LinearMap.range (Position.op A.val).toLinearMap=⊤ := LinearMap.range_eq_top.mpr hsurj
  let T : Space n ≃L[ℝ] Space n :=
    (LinearEquiv.ofBijective (Position.op A.val).toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv
  obtain ⟨g,hg,hmin⟩ := copy_minimizer hfull (optimizer hμ hq (regime n) (Position.domainMap A))
    (optimizer_normalized hμ hq (regime n) (Position.domainMap A))
    (optimizer_minimal hμ hq (regime n) (Position.domainMap A))
  refine ⟨T,Position.symmetric_op A.property.1.1,g,hmin,?_⟩
  rw [hg]
  exact hF

end RelativeGauge
end PettyProjection
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.RelativeGauge.exists_symmetric_position_oai := @OAI.PettyProjection.RelativeGauge.exists_symmetric_position_oai
