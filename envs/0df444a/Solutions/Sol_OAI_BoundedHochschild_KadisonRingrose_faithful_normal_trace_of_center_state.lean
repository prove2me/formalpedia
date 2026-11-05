-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.faithful_normal_trace_of_center_state
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:00:33.110193+00:00
-- url     : https://prove2.me/submissions/444e272e-523a-4415-9a34-a2d964885e51

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normal_positive_predual_orbit_compact

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_of_norm {a : I → M} {l : Filter I} {b : M}
    (h : Tendsto a l (𝓝 b)) : PredualTendsto e a l b := by
  intro z
  exact (((ContinuousLinearMap.apply ℂ ℂ) z).continuous.tendsto _).comp
    (e.symm.continuous.tendsto _ |>.comp h)
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder
namespace HochschildTraceNorm
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_mul_eq_abs_mul (b d : A) : ‖b*d‖=‖CFC.abs b*d‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two,pow_two,← CStarRing.norm_star_mul_self,← CStarRing.norm_star_mul_self]
  congr 1
  simp only [star_mul,(IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)).star_eq]
  rw [mul_assoc,← mul_assoc (star b),← CFC.abs_mul_abs b]
  simp only [mul_assoc]

theorem exists_approx_polar (b : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖v‖ ≤ 1 ∧ ‖b-v*CFC.abs b‖ ≤ ε ∧
      ‖CFC.abs b-star v*b‖ ≤ ε := by
  let a := CFC.abs b
  have ha0 : 0 ≤ a := CFC.abs_nonneg b
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  let f : ℝ → ℝ := fun t => (t+ε)⁻¹
  have hf : ContinuousOn f (spectrum ℝ a) := by
    apply ContinuousOn.inv₀ ((continuous_id.add continuous_const).continuousOn)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg ha0 ht
    exact (show 0 < t+ε from by linarith).ne'
  let q := cfc f a
  have hq : IsSelfAdjoint q := cfc_predicate f a
  have hqa : Commute q a := (Commute.refl a).cfc_real f
  have hab : a*a=star b*b := CFC.abs_mul_abs b
  have haq : a*q=cfc (fun t => t*f t) a := by
    change a*cfc f a = cfc (fun t => id t*f t) a
    rw [cfc_mul id f a continuousOn_id hf,cfc_id ℝ a ha]
  have hnormaq : ‖a*q‖ ≤ 1 := by
    rw [haq]
    apply norm_cfc_le (by positivity)
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    dsimp [f]
    rw [abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
    exact (mul_inv_le_iff₀ hp).mpr (by linarith)
  have hres : a-q*a*a=cfc (fun t => t-f t*t*t) a := by
    change a-cfc f a*a*a=cfc (fun t => id t - (fun s => f s * id s * id s) t) a
    rw [cfc_sub id (fun s => f s * id s * id s) a continuousOn_id ((hf.mul continuousOn_id).mul continuousOn_id),
      cfc_mul (fun t => f t * id t) id a (hf.mul continuousOn_id) continuousOn_id,
      cfc_mul f id a hf continuousOn_id,cfc_id ℝ a ha]
  have hresnorm : ‖a-q*a*a‖ ≤ ε := by
    rw [hres]
    apply norm_cfc_le hε.le
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    have heq : t-(t+ε)⁻¹*t*t=ε*t/(t+ε) := by field_simp; ring
    dsimp [f]
    rw [heq,abs_of_nonneg (div_nonneg (mul_nonneg hε.le ht0) hp.le)]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨b*q,?_,?_,?_⟩
  · have hh : ‖b*q‖^2 ≤ 1 := by
      rw [pow_two,← CStarRing.norm_star_mul_self]
      have heq : star (b*q)*(b*q)=(a*q)*(a*q) := by
        rw [star_mul,hq.star_eq]
        calc
          q*star b*(b*q)=q*(star b*b)*q := by simp only [mul_assoc]
          _ = q*(a*a)*q := by rw [hab]
          _ = (a*q)*(a*q) := by rw [← mul_assoc q a,hqa.eq]; simp only [mul_assoc]
      rw [heq]
      exact (norm_mul_le _ _).trans ((mul_le_mul hnormaq hnormaq (norm_nonneg _) (by positivity)).trans_eq (by norm_num))
    nlinarith [norm_nonneg (b*q)]
  · have heq : b-b*q*a=b*(1-q*a) := by simp only [mul_sub,mul_one,mul_assoc]
    rw [heq,norm_mul_eq_abs_mul]
    change ‖a*(1-q*a)‖ ≤ ε
    have heq' : a*(1-q*a)=a-q*a*a := by
      rw [mul_sub,mul_one,← mul_assoc,hqa.eq]
    rw [heq']
    exact hresnorm
  · simp only [star_mul,hq.star_eq]
    rw [mul_assoc q (star b),← hab]
    simpa only [mul_assoc] using hresnorm
end HochschildTraceNorm
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

theorem predual_tendsto_mul_left (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => a*b i) l (a*c) :=
  HasPreadjoint.tendsto e (mul_hasPreadjoint e a) hb

theorem predual_tendsto_mul_right (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => b i*a) l (c*a) :=
  HasPreadjoint.tendsto e (mul_right_hasPreadjoint e a) hb
end HochschildSakai
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (S : Set M) (hne : S.Nonempty)
    (hchain : IsChain (· ≤ ·) S) (hproj : ∀ q ∈ S, IsStarProjection q) :
    ∃ p : M, IsStarProjection p ∧ (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) ∧
      ∃ U : Ultrafilter S, (U : Filter S) ≤ atTop ∧
        PredualTendsto e (fun q : S => (q : M)) (U : Filter S) p := by
  classical
  let : Nonempty S := hne.to_subtype
  let : IsDirectedOrder S := ⟨fun a b => by
    rcases hchain.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter S := Ultrafilter.of atTop
  have hU : (U : Filter S) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨p, _, ht⟩ := exists_predual_ultralimit e U (fun q : S => (q : M)) 1
    (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  have hp : IsStarProjection p := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e p ht
      have heq : (fun q : S => (q : M) * p) = (fun q : S => (q : M)) :=
        funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun q : S => star (q : M)) = (fun q : S => (q : M)) := by
        funext q
        exact (hproj q q.property).isSelfAdjoint.star_eq
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨p, hp, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hu
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hu q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) :=
      funext fun q => ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
namespace BoundedHochschild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end BoundedHochschild

open Filter Topology
namespace HochschildPolar
open BoundedHochschild HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in

theorem exists_polar_contraction (b : M) :
    ∃ v : M, ‖v‖ ≤ 1 ∧ b=v*CFC.abs b ∧ CFC.abs b=star v*b := by
  classical
  have hpos (n : ℕ) : 0 < (1:ℝ)/((n:ℝ)+1) := by positivity
  choose v hv hleft hright using
    fun n : ℕ => HochschildTraceNorm.exists_approx_polar b _ (hpos n)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨w,hw,ht⟩ := exists_predual_ultralimit e U v 1 hv
  have hε : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n => v n*CFC.abs b) atTop (𝓝 b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hleft n
  have hr : Tendsto (fun n => star (v n)*b) atTop (𝓝 (CFC.abs b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hright n
  exact ⟨w,hw,
    predual_tendsto_unique e (predual_tendsto_of_norm e (hl.mono_left hU))
      (predual_tendsto_mul_right e _ ht),
    predual_tendsto_unique e (predual_tendsto_of_norm e (hr.mono_left hU))
      (predual_tendsto_mul_right e _ (predual_tendsto_star e ht))⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma support_right_annihilate {a p : M} (hp : IsSupportProjection a p)
    (ha : IsSelfAdjoint a) {x : M} (hx : x*a=0) : x*p=0 := by
  have hh := hp.annihilate (star x) (by
    simpa only [star_mul,ha.star_eq,star_zero] using congrArg star hx)
  simpa only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq,star_zero]
    using congrArg star hh

include e in

theorem exists_polar_partial_isometry (b : M) :
    ∃ v p q : M, IsSupportProjection (CFC.abs b) p ∧
      star v*v=p ∧ v*star v=q ∧ IsStarProjection q ∧ b=v*CFC.abs b ∧
      v*p=v ∧ q*b=b := by
  obtain ⟨w,hw,hb,ha⟩ := exists_polar_contraction e b
  obtain ⟨p,hp⟩ := HochschildSakai.exists_support_projection e (CFC.abs b) (CFC.abs_nonneg b)
  let v := w*p
  have hvp : v*p=v := by
    dsimp [v]
    rw [mul_assoc,hp.proj.isIdempotentElem.eq]
  have hvb : v*CFC.abs b=b := by
    dsimp [v]
    rw [mul_assoc,hp.left,← hb]
  have hv : star v*b=CFC.abs b := by
    dsimp [v]
    rw [star_mul,hp.proj.isSelfAdjoint.star_eq,mul_assoc,← ha,hp.left]
  have hinit : star v*v=p := by
    have hz : (star v*v-p)*CFC.abs b=0 := by
      rw [sub_mul,mul_assoc,hvb,hv,hp.left,sub_self]
    have hh := support_right_annihilate hp (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    rw [sub_mul,mul_assoc,hvp,hp.proj.isIdempotentElem.eq,sub_eq_zero] at hh
    exact hh
  have hfinal : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc
        _ = v*(star v*v)*star v := by simp only [mul_assoc]
        _ = v*star v := by rw [hinit,hvp]
    · exact IsSelfAdjoint.mul_star_self v
  refine ⟨v,p,v*star v,hp,hinit,rfl,hfinal,hvb.symm,hvp,?_⟩
  rw [mul_assoc,hv,hvb]
end HochschildPolar
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

namespace PartialIso

lemma final_proj (v : PartialIso M) : IsStarProjection v.final := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self _⟩
  change ((v : M) * star (v : M)) * ((v : M) * star (v : M)) = (v : M) * star (v : M)
  calc
    _ = ((v : M) * star (v : M) * v) * star (v : M) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]
end PartialIso
end HochschildComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildRigidity HochschildDiffuse HochschildComparison
open FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_orthogonal_of_le_complement {s c : M}
    (hs : IsStarProjection s) (hc : IsStarProjection c) (hcs : c ≤ 1-s) : s*c=0 := by
  have h := (hc.le_iff_mul_eq_right hs.one_sub).mp hcs
  rw [sub_mul,one_mul] at h
  exact sub_eq_self.mp h
end HochschildTypeII
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_trace_free_projection_join (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : PartialIso M, v.initial ≤ q ∧ p * v.final = 0 ∧
      IsStarProjection (p + v.final) ∧ p ≤ p + v.final ∧ q ≤ p + v.final ∧
      ∀ z : M, IsStarProjection z → p ≤ z → q ≤ z → p + v.final ≤ z := by
  let b := (1 - p) * q
  have hpb : (1 - p) * b = b := by
    dsimp [b]
    rw [← mul_assoc, hp.one_sub.isIdempotentElem.eq]
  have hbq : b * q = b := by
    dsimp [b]
    rw [mul_assoc, hq.isIdempotentElem.eq]
  obtain ⟨w, r, t, hr, hwi, hwf, ht, hb, hwr, htb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have hwabs : star w * b = CFC.abs b := by
    calc
      star w * b = star w * (w * CFC.abs b) := congrArg (star w * ·) hb
      _ = CFC.abs b := by rw [← mul_assoc, hwi, hr.left]
  have hw_support {z : M} (hz : IsStarProjection z) (hzb : z * b = b) : z * w = w := by
    have hzero : ((1 - z) * w) * CFC.abs b = 0 := by
      rw [mul_assoc, ← hb, sub_mul, one_mul, hzb, sub_self]
    have hzero' := HochschildPolar.support_right_annihilate hr
      (CFC.abs_nonneg b).isSelfAdjoint hzero
    rw [mul_assoc, hwr, sub_mul, one_mul, sub_eq_zero] at hzero'
    exact hzero'.symm
  have hpw : (1 - p) * w = w := hw_support hp.one_sub hpb
  let v : PartialIso M := ⟨w, by rw [mul_assoc, hwi, hwr]⟩
  have hiv : v.initial = r := hwi
  have hfv : v.final = t := hwf
  have hiq : v.initial ≤ q := by
    rw [hiv]
    apply (hr.proj.le_iff_mul_eq_left hq).mpr
    have hzero : CFC.abs b * (1 - q) = 0 := by
      rw [← hwabs, mul_assoc, mul_sub, mul_one, hbq, sub_self, mul_zero]
    have hzero' := hr.annihilate (1 - q) hzero
    simpa only [mul_sub, mul_one, sub_eq_zero, eq_comm] using hzero'
  have hfp : v.final ≤ 1 - p := by
    apply (v.final_proj.le_iff_mul_eq_right hp.one_sub).mpr
    change (1 - p) * (w * star w) = w * star w
    rw [← mul_assoc, hpw]
  have horth : p * v.final = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement hp v.final_proj hfp
  have horth' : v.final * p = 0 := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq,
      v.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star horth
  have hj : IsStarProjection (p + v.final) := hp.add v.final_proj horth
  have hvq : v.final * q = b := by
    have h : v.final * b = b := by rw [hfv]; exact htb
    dsimp [b] at h ⊢
    rwa [← mul_assoc, mul_sub, mul_one, horth', sub_zero] at h
  refine ⟨v, hiq, horth, hj, ?_, ?_, ?_⟩
  · exact le_add_of_nonneg_right v.final_proj.nonneg
  · apply (hq.le_iff_mul_eq_right hj).mpr
    rw [add_mul, hvq]
    dsimp [b]
    noncomm_ring
  · intro z hz hpz hqz
    have hzp : z * p = p := (hp.le_iff_mul_eq_right hz).mp hpz
    have hzq : z * q = q := (hq.le_iff_mul_eq_right hz).mp hqz
    have hzb : z * b = b := by
      dsimp [b]
      rw [← mul_assoc, mul_sub, mul_one, hzp, sub_mul, hzq, sub_mul, one_mul]
    have hzw : z * w = w := hw_support hz hzb
    apply (hj.le_iff_mul_eq_right hz).mpr
    change z * (p + w * star w) = p + w * star w
    rw [mul_add, hzp, ← mul_assoc, hzw]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma unitaryOrbitHull_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) :
    unitaryOrbitHull F ⊆ normalDual e := by
  apply closure_minimal _ (normalDual_closed e)
  apply convexHull_min _ ((normalDual e).restrictScalars ℝ).convex
  rintro _ ⟨u, rfl⟩
  apply normalDual_comp e _ _ (HochschildSakai.mul_hasPreadjoint e (u : M))
  exact normalDual_comp e hF _ ((HochschildSakai.abstract_multiplication_normal e).2 (star (u : M)))

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_eval_eq (F : StrongDual ℂ M) (a : M) (c : ℂ)
    (hbound : ∀ u : unitary M, unitaryPullback F u a = c) :
    ∀ G ∈ unitaryOrbitHull F, G a = c := by
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback F)) ⊆ {G | E G = c} := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      exact hbound u
    · intro G hG H hH r t _hr _ht hrt
      change r • E G + t • E H = c
      rw [hG, hH, ← add_smul, hrt, one_smul]
  exact closure_minimal hc (isClosed_eq E.continuous continuous_const)

lemma unitaryOrbitHull_positive (ψ : M →ₚ[ℂ] ℂ) :
    ∀ G ∈ unitaryOrbitHull (positiveFunctionalCLM ψ), ∀ a : M, 0 ≤ a → 0 ≤ G a := by
  intro G hG a ha
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback (positiveFunctionalCLM ψ))) ⊆
      E ⁻¹' Set.Ici 0 := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      exact ψ.map_nonneg (star_right_conjugate_nonneg ha (u : M))
    · intro F hF H hH r t hr ht _
      change 0 ≤ r • E F + t • E H
      exact add_nonneg (smul_nonneg hr hF) (smul_nonneg ht hH)
  exact (closure_minimal hc (isClosed_Ici.preimage E.continuous)) hG

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_central (F : StrongDual ℂ M) {a : M}
    (hc : ∀ b : M, a * b = b * a) :
    ∀ G ∈ unitaryOrbitHull F, G a = F a := by
  apply unitaryOrbitHull_eval_eq F a (F a)
  intro u
  rw [unitaryPullback_apply, ← hc (u : M), mul_assoc,
    (Unitary.mem_iff.mp u.property).2, mul_one]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [StarOrderedRing M] in
lemma weakFunctionalClosure_positive (K : Set (StrongDual ℂ M))
    (hpos : ∀ F ∈ K, ∀ a : M, 0 ≤ a → 0 ≤ F a)
    {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    ∀ a : M, 0 ≤ a → 0 ≤ F a := by
  intro a ha
  apply closure_minimal (t := {G : WeakDual ℂ M | 0 ≤ G a}) _
    (isClosed_le continuous_const (WeakDual.eval_continuous a)) hF
  rintro _ ⟨G, hGK, rfl⟩
  exact hpos G hGK a ha

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryPullback_norm_le (F : StrongDual ℂ M) (u : unitary M) :
    ‖unitaryPullback F u‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have hn : ‖(u : M) * a * star (u : M)‖ = ‖a‖ := by
    rw [show star (u : M) = (star u : unitary M) from rfl,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simpa only [unitaryPullback_apply, hn] using F.le_opNorm ((u : M) * a * star (u : M))
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma unitaryPullback_one (F : StrongDual ℂ M) : unitaryPullback F 1 = F := by
  ext a
  simp only [unitaryPullback_apply, OneMemClass.coe_one, star_one, one_mul, mul_one]

lemma unitaryPullback_mul (F : StrongDual ℂ M) (u v : unitary M) :
    unitaryPullback (unitaryPullback F u) v = unitaryPullback F (u * v) := by
  ext a
  simp only [unitaryPullback_apply, Submonoid.coe_mul, star_mul, mul_assoc]

def unitaryDualEquiv (u : unitary M) : StrongDual ℂ M ≃ₗᵢ[ℂ] StrongDual ℂ M where
  toFun F := unitaryPullback F u
  invFun F := unitaryPullback F (star u)
  left_inv F := by
    change unitaryPullback (unitaryPullback F u) (star u) = F
    rw [unitaryPullback_mul, Unitary.mul_star_self, unitaryPullback_one]
  right_inv F := by
    change unitaryPullback (unitaryPullback F (star u)) u = F
    rw [unitaryPullback_mul, Unitary.star_mul_self, unitaryPullback_one]
  map_add' F G := by ext a; rfl
  map_smul' c F := by ext a; rfl
  norm_map' F := by
    apply le_antisymm (unitaryPullback_norm_le F u)
    have h := unitaryPullback_norm_le (unitaryPullback F u) (star u)
    simpa only [unitaryPullback_mul, Unitary.mul_star_self, unitaryPullback_one] using h

variable [PartialOrder M] [StarOrderedRing M]

lemma unitaryPullback_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) (u : unitary M) :
    unitaryPullback F u ∈ normalDual e := by
  apply unitaryOrbitHull_normal e hF
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_range_self u))

def normalUnitaryEquiv (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (u : unitary M) :
    normalDual e ≃ₗᵢ[ℂ] normalDual e where
  toFun F := ⟨unitaryPullback F.val u, unitaryPullback_normal e F.property u⟩
  invFun F := ⟨unitaryPullback F.val (star u), unitaryPullback_normal e F.property (star u)⟩
  left_inv F := Subtype.ext ((unitaryDualEquiv u).left_inv F.val)
  right_inv F := Subtype.ext ((unitaryDualEquiv u).right_inv F.val)
  map_add' F G := Subtype.ext (by ext a; rfl)
  map_smul' c F := Subtype.ext (by ext a; rfl)
  norm_map' F := (unitaryDualEquiv u).norm_map F.val

def predualNormalEquiv (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : X ≃ₗᵢ⋆[ℂ] normalDual e :=
  (predualEmbedding e).equivRange

omit [CompleteSpace X] [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma predualNormalEquiv_coe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (x : X) :
    (predualNormalEquiv e x).val = predualEmbedding e x := rfl

def unitaryPredualAction (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (u : unitary M) : X ≃ₗᵢ[ℂ] X :=
  (predualNormalEquiv e).trans
    ((normalUnitaryEquiv e (star u)).trans (predualNormalEquiv e).symm)

lemma predualEmbedding_unitaryAction (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (u : unitary M) (x : X) :
    predualEmbedding e (unitaryPredualAction e u x) =
      unitaryPullback (predualEmbedding e x) (star u) := by
  have h := congrArg Subtype.val ((predualNormalEquiv e).apply_symm_apply
    (normalUnitaryEquiv e (star u) (predualNormalEquiv e x)))
  exact h

lemma unitaryPredualAction_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (x : X) :
    unitaryPredualAction e 1 x = x := by
  apply (predualEmbedding e).injective
  rw [predualEmbedding_unitaryAction, star_one, unitaryPullback_one]

lemma unitaryPredualAction_mul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (u v : unitary M) (x : X) :
    unitaryPredualAction e (u * v) x = unitaryPredualAction e u (unitaryPredualAction e v x) := by
  apply (predualEmbedding e).injective
  simp only [predualEmbedding_unitaryAction, unitaryPullback_mul, star_mul]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma weak_closedBall (a : E) (r : ℝ) :
    IsClosed ((toWeakSpace ℂ E) '' Metric.closedBall a r) := by
  rw [← closure_eq_iff_isClosed, ← (convex_closedBall a r).toWeakSpace_closure ℂ,
    Metric.isClosed_closedBall.closure_eq]

theorem weakCompact_small_open_piece (K : Set (WeakSpace ℂ E))
    (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (WeakSpace ℂ E), IsOpen U ∧ (K ∩ U).Nonempty ∧
      ∀ x ∈ K ∩ U, ∀ y ∈ K ∩ U,
        ‖(toWeakSpace ℂ E).symm x - (toWeakSpace ℂ E).symm y‖ < ε := by
  classical
  obtain ⟨S, _hSK, hcount, hdense⟩ := hsep.exists_countable_dense_subset
  have : Countable S := hcount.to_subtype
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Nonempty K := hne.to_subtype
  let B (a : S) : Set K := {x | (toWeakSpace ℂ E).symm x.val ∈ Metric.closedBall a.val (ε / 3)}
  have hc (a : S) : IsClosed (B a) := by
    have heq : B a = Subtype.val ⁻¹' ((toWeakSpace ℂ E) '' Metric.closedBall a.val (ε / 3)) := by
      ext x
      simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
      exact ⟨fun hx => ⟨_, hx, (toWeakSpace ℂ E).apply_symm_apply x.val⟩,
        fun ⟨z, hz, he⟩ => by simpa only [← he, LinearEquiv.symm_apply_apply] using hz⟩
    rw [heq]
    exact (weak_closedBall a.val (ε / 3)).preimage continuous_subtype_val
  have hcover : ⋃ a : S, B a = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : (toWeakSpace ℂ E).symm x.val ∈ closure S := hdense ⟨x.val, x.property, rfl⟩
    obtain ⟨a, haS, hdist⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
    exact Set.mem_iUnion.mpr ⟨⟨a, haS⟩, hdist.le⟩
  obtain ⟨a, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hc hcover
  obtain ⟨U, hU, heq⟩ := isOpen_induced_iff.mp (show IsOpen (interior (B a)) from isOpen_interior)
  refine ⟨U, hU, ⟨x.val, x.property, ?_⟩, ?_⟩
  · have : x ∈ Subtype.val ⁻¹' U := heq ▸ hx
    exact this
  · intro y hy z hz
    have hyB : (toWeakSpace ℂ E).symm y ∈ Metric.closedBall a.val (ε / 3) := by
      change (⟨y, hy.1⟩ : K) ∈ B a
      apply interior_subset (s := B a)
      rw [← heq]
      exact hy.2
    have hzB : (toWeakSpace ℂ E).symm z ∈ Metric.closedBall a.val (ε / 3) := by
      change (⟨z, hz.1⟩ : K) ∈ B a
      apply interior_subset (s := B a)
      rw [← heq]
      exact hz.2
    have hy' := Metric.mem_closedBall.mp hyB
    have hz' := Metric.mem_closedBall.mp hzB
    have hd := dist_triangle ((toWeakSpace ℂ E).symm y) a.val ((toWeakSpace ℂ E).symm z)
    rw [dist_comm a.val] at hd
    rw [← dist_eq_norm]
    linarith
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {A : Type u} [TopologicalSpace A] [T2Space A]
variable {G : Type v} [Group G]

omit [Group G] in

theorem exists_minimal_compact_invariant (T : G → A → A)
    (C : Set A) (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : ∀ g, Set.MapsTo (T g) C C) :
    ∃ K : Set A, K ⊆ C ∧ K.Nonempty ∧ IsClosed K ∧
      (∀ g, Set.MapsTo (T g) K K) ∧
      ∀ L : Set A, L ⊆ K → L.Nonempty → IsClosed L →
        (∀ g, Set.MapsTo (T g) L L) → K ⊆ L := by
  classical
  let S : Set (Set A) := {K | K ⊆ C ∧ K.Nonempty ∧ IsClosed K ∧
    ∀ g, Set.MapsTo (T g) K K}
  have hCS : C ∈ S := ⟨Set.Subset.rfl, hne, hC.isClosed, hinv⟩
  obtain ⟨K, hKC, hK⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun L hL J hJ => by
          rcases hchain.total hL hJ with h | h
          · exact ⟨L, hL, Set.Subset.rfl, h⟩
          · exact ⟨J, hJ, h, Set.Subset.rfl⟩)
        (fun L hL => (hc hL).2.1)
        (fun L hL => hC.of_isClosed_subset (hc hL).2.2.1 (hc hL).1)
        (fun L hL => (hc hL).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_⟩, fun L hL => Set.sInter_subset_of_mem hL⟩
    · obtain ⟨L, hL⟩ := hcne
      exact (Set.sInter_subset_of_mem hL).trans (hc hL).1
    · exact isClosed_sInter (fun L hL => (hc hL).2.2.1)
    · intro g x hx
      apply Set.mem_sInter.mpr
      intro L hL
      exact (hc hL).2.2.2 g (Set.mem_sInter.mp hx L hL)) C hCS
  refine ⟨K, hKC, hK.1.2.1, hK.1.2.2.1, hK.1.2.2.2, ?_⟩
  intro L hLK hLn hLc hLi
  exact hK.2 ⟨hLK.trans hKC, hLn, hLc, hLi⟩ hLK

omit [T2Space A] in

theorem minimal_invariant_open_cover (T : G → A → A)
    (hcont : ∀ g, Continuous (T g))
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set A) (hKc : IsClosed K) (hinv : ∀ g, Set.MapsTo (T g) K K)
    (hmin : ∀ L : Set A, L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (T g) L L) → K ⊆ L)
    (U : Set A) (hU : IsOpen U) (hne : (K ∩ U).Nonempty) :
    K ⊆ ⋃ g, (T g) ⁻¹' U := by
  classical
  intro x hx
  by_contra hnot
  have hxnone : ∀ g, T g x ∉ U := by simpa only [Set.mem_iUnion, Set.mem_preimage, not_exists] using hnot
  let L : Set A := K ∩ ⋂ g, (T g) ⁻¹' Uᶜ
  have hLK : L ⊆ K := Set.inter_subset_left
  have hLn : L.Nonempty := ⟨x, hx, Set.mem_iInter.mpr hxnone⟩
  have hLc : IsClosed L := hKc.inter (isClosed_iInter (fun g => hU.isClosed_compl.preimage (hcont g)))
  have hLi : ∀ g, Set.MapsTo (T g) L L := by
    intro g y hy
    refine ⟨hinv g hy.1, Set.mem_iInter.mpr (fun h => ?_)⟩
    change T h (T g y) ∉ U
    rw [← hmul]
    exact Set.mem_iInter.mp hy.2 (h * g)
  obtain ⟨y, hyK, hyU⟩ := hne
  have hyL := hmin L hLK hLn hLc hLi hyK
  have hyout := Set.mem_iInter.mp hyL.2 1
  apply hyout
  simpa only [hone] using hyU
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type v} [Group G]

def weakIsometry (T : E ≃ₗᵢ[ℂ] E) : WeakSpace ℂ E → WeakSpace ℂ E :=
  WeakSpace.map T.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma weakIsometry_apply (T : E ≃ₗᵢ[ℂ] E) (x : WeakSpace ℂ E) :
    (toWeakSpace ℂ E).symm (weakIsometry T x) = T ((toWeakSpace ℂ E).symm x) := rfl

theorem minimal_isometric_orbit_finite_net (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set (WeakSpace ℂ E)) (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) K K)
    (hmin : ∀ L : Set (WeakSpace ℂ E), L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) → K ⊆ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset E, (↑s : Set E) ⊆ (toWeakSpace ℂ E).symm '' K ∧
      ∀ x ∈ K, ∃ y ∈ s, ‖(toWeakSpace ℂ E).symm x - y‖ < ε := by
  classical
  obtain ⟨U, hU, hKU, hdiam⟩ := weakCompact_small_open_piece K hK hne hsep ε hε
  have hcov : K ⊆ ⋃ g, weakIsometry (T g) ⁻¹' U := by
    apply minimal_invariant_open_cover (fun g => weakIsometry (T g))
      (fun g => (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous)
      _ _ K hK.isClosed hinv hmin U hU hKU
    · intro x
      apply (toWeakSpace ℂ E).symm.injective
      exact hone _
    · intro g h x
      apply (toWeakSpace ℂ E).symm.injective
      exact hmul g h _
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun g => weakIsometry (T g) ⁻¹' U)
    (fun g => hU.preimage (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous) hcov
  obtain ⟨y, hyK, hyU⟩ := hKU
  let z (g : G) : E := T g⁻¹ ((toWeakSpace ℂ E).symm y)
  refine ⟨s.image z, ?_, ?_⟩
  · intro a ha
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨weakIsometry (T g⁻¹) y, hinv g⁻¹ hyK, rfl⟩
  · intro x hx
    obtain ⟨g, hgs, hxU⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine ⟨z g, Finset.mem_image.mpr ⟨g, hgs, rfl⟩, ?_⟩
    have hgzy : T g (z g) = (toWeakSpace ℂ E).symm y := by
      dsimp [z]
      rw [← hmul, mul_inv_cancel, hone]
    have hd := hdiam (weakIsometry (T g) x) ⟨hinv g hx, hxU⟩ y ⟨hyK, hyU⟩
    change ‖T g ((toWeakSpace ℂ E).symm x) - (toWeakSpace ℂ E).symm y‖ < ε at hd
    rwa [← hgzy, ← map_sub, (T g).norm_map] at hd

theorem minimal_isometric_orbit_normCompact [CompleteSpace E]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set (WeakSpace ℂ E)) (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) K K)
    (hmin : ∀ L : Set (WeakSpace ℂ E), L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) → K ⊆ L) :
    IsCompact ((toWeakSpace ℂ E).symm '' K) := by
  have hc : IsClosed ((toWeakSpace ℂ E).symm '' K) := by
    have heq : (toWeakSpace ℂ E).symm '' K = (toWeakSpace ℂ E) ⁻¹' K := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      exact ⟨fun ⟨y, hy, he⟩ => he ▸ by simpa using hy,
        fun hx => ⟨toWeakSpace ℂ E x, hx, rfl⟩⟩
    rw [heq]
    exact hK.isClosed.preimage (toWeakSpaceCLM ℂ E).continuous
  apply TotallyBounded.isCompact_of_isComplete _ hc.isComplete
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨s, _, hs⟩ := minimal_isometric_orbit_finite_net T hone hmul K hK hne hsep hinv hmin ε hε
  refine ⟨s, s.finite_toSet, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hdist⟩ := hs y hy
  apply Set.mem_iUnion₂.mpr
  exact ⟨z, hz, by simpa only [Metric.mem_ball, dist_eq_norm] using hdist⟩
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_convex_center (K : Set E) (hK : IsCompact K) (hnt : K.Nontrivial) :
    ∃ z ∈ convexHull ℝ K, ∃ r : ℝ, r < Metric.diam K ∧
      ∀ y ∈ K, ‖z - y‖ ≤ r := by
  classical
  have hne : K.Nonempty := hnt.nonempty
  have hD : 0 < Metric.diam K := Metric.diam_pos hnt hK.isBounded
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball x.val (Metric.diam K))
    (fun _ => Metric.isOpen_ball) (fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hD⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x, hxs, _⟩ := Set.mem_iUnion₂.mp (hs hy)
    exact ⟨x, hxs⟩
  have hN : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hsne
  let z : E := s.centerMass (fun _ => (1 : ℝ)) (fun x => x.val)
  have hz : z ∈ convexHull ℝ K := by
    apply s.centerMass_mem_convexHull (fun _ _ => zero_le_one) _ (fun x _ => x.property)
    simpa using hN
  have hzclose (y : E) (hy : y ∈ K) : ‖z - y‖ < Metric.diam K := by
    obtain ⟨a, has, hay⟩ := Set.mem_iUnion₂.mp (hs hy)
    have hsum : (∑ x ∈ s, ‖x.val - y‖) < (s.card : ℝ) * Metric.diam K := by
      calc
        (∑ x ∈ s, ‖x.val - y‖) < ∑ _x ∈ s, Metric.diam K := by
          apply Finset.sum_lt_sum
          · intro x _
            simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded x.property hy
          · refine ⟨a, has, ?_⟩
            simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hay
        _ = (s.card : ℝ) * Metric.diam K := by simp
    have heq : z - y = (s.card : ℝ)⁻¹ • ∑ x ∈ s, (x.val - y) := by
      dsimp [z, Finset.centerMass]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_smul, Finset.sum_sub_distrib,
        smul_sub]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN.ne', one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
    calc
      (s.card : ℝ)⁻¹ * ‖∑ x ∈ s, (x.val - y)‖ ≤
          (s.card : ℝ)⁻¹ * ∑ x ∈ s, ‖x.val - y‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN.le)
      _ < (s.card : ℝ)⁻¹ * ((s.card : ℝ) * Metric.diam K) :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hN)
      _ = Metric.diam K := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun y : E => ‖z - y‖) K from (continuous_const.sub continuous_id).norm.continuousOn)
  exact ⟨z, hz, ‖z - y‖, hzclose y hy, fun a ha => hmax ha⟩
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type v} [Group G]

omit [Group G] in
private theorem minimal_weak_convex_invariant (T : G → E ≃ₗᵢ[ℂ] E)
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ L : Set (WeakSpace ℂ E), L ⊆ C ∧ L.Nonempty ∧ IsClosed L ∧ Convex ℝ L ∧
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) ∧
      ∀ D : Set (WeakSpace ℂ E), D ⊆ L → D.Nonempty → IsClosed D → Convex ℝ D →
        (∀ g, Set.MapsTo (weakIsometry (T g)) D D) → L ⊆ D := by
  classical
  let S : Set (Set (WeakSpace ℂ E)) := {L | L ⊆ C ∧ L.Nonempty ∧ IsClosed L ∧
    Convex ℝ L ∧ ∀ g, Set.MapsTo (weakIsometry (T g)) L L}
  have hCS : C ∈ S := ⟨Set.Subset.rfl, hne, hC.isClosed, hconv, hinv⟩
  obtain ⟨L, hLC, hL⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun A hA B hB => by
          rcases hchain.total hA hB with h | h
          · exact ⟨A, hA, Set.Subset.rfl, h⟩
          · exact ⟨B, hB, h, Set.Subset.rfl⟩)
        (fun A hA => (hc hA).2.1)
        (fun A hA => hC.of_isClosed_subset (hc hA).2.2.1 (hc hA).1)
        (fun A hA => (hc hA).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_, ?_⟩, fun A hA => Set.sInter_subset_of_mem hA⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (Set.sInter_subset_of_mem hA).trans (hc hA).1
    · exact isClosed_sInter (fun A hA => (hc hA).2.2.1)
    · exact convex_sInter (fun A hA => (hc hA).2.2.2.1)
    · intro g x hx
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2.2.2 g (Set.mem_sInter.mp hx A hA)) C hCS
  refine ⟨L, hLC, hL.1.2.1, hL.1.2.2.1, hL.1.2.2.2.1, hL.1.2.2.2.2, ?_⟩
  intro D hDL hDn hDc hDv hDi
  exact hL.2 ⟨hDL.trans hLC, hDn, hDc, hDv, hDi⟩ hDL

theorem weakCompact_separable_isometric_fixedPoint [CompleteSpace E]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' C))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  obtain ⟨L, hLC, hLn, hLc, hLv, hLi, hLmin⟩ :=
    minimal_weak_convex_invariant T C hC hne hconv hinv
  have hLcompact : IsCompact L := hC.of_isClosed_subset hLc hLC
  obtain ⟨K, hKL, hKn, hKc, hKi, hKmin⟩ :=
    exists_minimal_compact_invariant (fun g => weakIsometry (T g)) L hLcompact hLn hLi
  have hKcompact : IsCompact K := hLcompact.of_isClosed_subset hKc hKL
  have hKsep : IsSeparable ((toWeakSpace ℂ E).symm '' K) :=
    hsep.mono (Set.image_mono (hKL.trans hLC))
  have hKnorm := minimal_isometric_orbit_normCompact T hone hmul K hKcompact hKn hKsep hKi hKmin
  have hsingle : K.Subsingleton := by
    by_contra hnonsingle
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hnonsingle
    have hnt : ((toWeakSpace ℂ E).symm '' K).Nontrivial :=
      ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, fun h => hxy ((toWeakSpace ℂ E).symm.injective h)⟩
    obtain ⟨z, hz, r, hr, hzr⟩ := compact_convex_center _ hKnorm hnt
    let B (y : K) : Set (WeakSpace ℂ E) :=
      (toWeakSpace ℂ E) '' Metric.closedBall ((toWeakSpace ℂ E).symm y.val) r
    let D : Set (WeakSpace ℂ E) := L ∩ ⋂ y : K, B y
    have hzL : toWeakSpace ℂ E z ∈ L := by
      have hcv : Convex ℝ ((toWeakSpace ℂ E).symm '' L) :=
        hLv.linear_image ((toWeakSpace ℂ E).symm.restrictScalars ℝ).toLinearMap
      obtain ⟨w, hw, heq⟩ := convexHull_min (Set.image_mono hKL) hcv hz
      simpa only [← heq, LinearEquiv.apply_symm_apply] using hw
    have hDz : toWeakSpace ℂ E z ∈ D := by
      refine ⟨hzL, Set.mem_iInter.mpr (fun y => ?_)⟩
      exact ⟨z, by simpa only [Metric.mem_closedBall, dist_eq_norm] using
        (hzr _ ⟨y.val, y.property, rfl⟩), rfl⟩
    have hDc : IsClosed D := hLc.inter (isClosed_iInter (fun y => weak_closedBall _ _))
    have hDv : Convex ℝ D := hLv.inter (convex_iInter (fun y =>
      (convex_closedBall ((toWeakSpace ℂ E).symm y.val) r).linear_image
        ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap))
    have hDi : ∀ g, Set.MapsTo (weakIsometry (T g)) D D := by
      intro g a ha
      refine ⟨hLi g ha.1, Set.mem_iInter.mpr (fun y => ?_)⟩
      let b : K := ⟨weakIsometry (T g⁻¹) y.val, hKi g⁻¹ y.property⟩
      obtain ⟨w, hw, heq⟩ := Set.mem_iInter.mp ha.2 b
      have hab : ‖(toWeakSpace ℂ E).symm a - (toWeakSpace ℂ E).symm b.val‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, ← heq, LinearEquiv.symm_apply_apply] using hw
      refine ⟨T g ((toWeakSpace ℂ E).symm a), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      change ‖T g ((toWeakSpace ℂ E).symm a) - (toWeakSpace ℂ E).symm y.val‖ ≤ r
      have hgb : T g ((toWeakSpace ℂ E).symm b.val) = (toWeakSpace ℂ E).symm y.val := by
        change T g (T g⁻¹ ((toWeakSpace ℂ E).symm y.val)) = _
        rw [← hmul, mul_inv_cancel, hone]
      rw [← hgb, ← map_sub, (T g).norm_map]
      exact hab
    have hLD : L ⊆ D := hLmin D Set.inter_subset_left ⟨_, hDz⟩ hDc hDv hDi
    have hdiam : Metric.diam ((toWeakSpace ℂ E).symm '' K) ≤ r := by
      apply Metric.diam_le_of_forall_dist_le_of_nonempty hnt.nonempty
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      obtain ⟨w, hw, heq⟩ := Set.mem_iInter.mp (hLD (hKL ha')).2 ⟨b', hb'⟩
      simpa only [Metric.mem_closedBall, ← heq, LinearEquiv.symm_apply_apply] using hw
    exact (not_le_of_gt hr) hdiam
  obtain ⟨x, hx⟩ := hKn
  exact ⟨x, hLC (hKL hx), fun g => hsingle (hKi g hx) hx⟩
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {G : Type v} [Group G]

theorem weakCompact_countable_isometric_fixedPoint [Countable G]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  obtain ⟨x, hx⟩ := hne
  let S : Set E := Set.range (fun g : G => T g ((toWeakSpace ℂ E).symm x))
  let D : Set E := closure (convexHull ℝ S)
  let W : Set (WeakSpace ℂ E) := (toWeakSpace ℂ E) '' D
  have hDc : IsClosed D := isClosed_closure
  have hDv : Convex ℝ D := (convex_convexHull ℝ S).closure
  have hWc : IsClosed W := by
    rw [show W = closure ((toWeakSpace ℂ E) '' convexHull ℝ S) from
      (convex_convexHull ℝ S).toWeakSpace_closure ℂ]
    exact isClosed_closure
  have hWC : W ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hsub : D ⊆ (toWeakSpace ℂ E) ⁻¹' C := by
      apply closure_minimal _ (hC.isClosed.preimage (toWeakSpaceCLM ℂ E).continuous)
      apply convexHull_min _ (hconv.linear_preimage ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap)
      rintro _ ⟨g, rfl⟩
      exact hinv g hx
    exact hsub hy
  have hWn : W.Nonempty := by
    refine ⟨x, (toWeakSpace ℂ E).symm x, ?_, (toWeakSpace ℂ E).apply_symm_apply x⟩
    apply subset_closure
    apply subset_convexHull ℝ S
    exact ⟨1, hone _⟩
  have hWs : IsSeparable ((toWeakSpace ℂ E).symm '' W) := by
    have hS : S.Countable := Set.countable_range _
    have hDsep : IsSeparable D := by
      apply (hS.isSeparable.span (R := ℝ)).closure.mono
      exact closure_mono (convexHull_min (Submodule.subset_span) (Submodule.span ℝ S).convex)
    have heq : (toWeakSpace ℂ E).symm '' W = D := by
      simp only [W, Set.image_image, LinearEquiv.symm_apply_apply, Set.image_id']
    rw [heq]
    exact hDsep
  have hWi : ∀ g, Set.MapsTo (weakIsometry (T g)) W W := by
    intro g a ha
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨T g y, ?_, rfl⟩
    have hsub : D ⊆ (T g) ⁻¹' D := by
      apply closure_minimal _ (hDc.preimage (T g).continuous)
      apply convexHull_min _ (hDv.linear_preimage ((T g).toLinearMap.restrictScalars ℝ))
      rintro _ ⟨h, rfl⟩
      apply subset_closure
      apply subset_convexHull ℝ S
      exact ⟨g * h, hmul g h _⟩
    exact hsub hy
  obtain ⟨y, hy, hfix⟩ := weakCompact_separable_isometric_fixedPoint T hone hmul W
    (hC.of_isClosed_subset hWc hWC) hWn
    (hDv.linear_image ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap) hWs hWi
  exact ⟨y, hWC hy, hfix⟩

theorem weakCompact_isometric_fixedPoint
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  have hfinite (s : Finset G) : ∃ x ∈ C, ∀ g ∈ s, weakIsometry (T g) x = x := by
    let ρ : FreeGroup s →* G := FreeGroup.lift (fun g : s => g.val)
    have : Countable (FreeGroup s) := inferInstanceAs (Countable (Quot _))
    obtain ⟨x, hx, hfix⟩ := weakCompact_countable_isometric_fixedPoint (fun g => T (ρ g))
      (fun x => by simpa only [map_one] using hone x)
      (fun g h x => by simpa only [map_mul] using hmul (ρ g) (ρ h) x)
      C hC hne hconv (fun g => hinv (ρ g))
    refine ⟨x, hx, fun g hg => ?_⟩
    simpa only [ρ, FreeGroup.lift_apply_of] using hfix (FreeGroup.of ⟨g, hg⟩)
  let F (g : G) : Set (WeakSpace ℂ E) := {x | weakIsometry (T g) x = x}
  have hc (g) : IsClosed (F g) := isClosed_eq
    (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous continuous_id
  obtain ⟨x, hx, hfix⟩ := hC.inter_iInter_nonempty F hc (fun s => by
    obtain ⟨x, hx, hfix⟩ := hfinite s
    exact ⟨x, hx, Set.mem_iInter₂.mpr hfix⟩)
  exact ⟨x, hx, fun g => Set.mem_iInter.mp hfix g⟩
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakUnitaryPullback (u : unitary M) : WeakDual ℂ M →L[ℂ] WeakDual ℂ M where
  toFun F := StrongDual.toWeakDual (unitaryPullback (WeakDual.toStrongDual F) u)
  map_add' F G := by apply WeakDual.toStrongDual.injective; ext a; rfl
  map_smul' c F := by apply WeakDual.toStrongDual.injective; ext a; rfl
  cont := WeakDual.continuous_of_continuous_eval (fun a =>
    WeakDual.eval_continuous ((u : M) * a * star (u : M)))

lemma unitaryOrbitHull_invariant (F : StrongDual ℂ M) (u : unitary M)
    {H : StrongDual ℂ M} (hH : H ∈ unitaryOrbitHull F) :
    unitaryPullback H u ∈ unitaryOrbitHull F := by
  have hconv : Convex ℝ (unitaryOrbitHull F) := (convex_convexHull ℝ _).closure
  have hclosed : IsClosed (unitaryOrbitHull F) := isClosed_closure
  apply closure_minimal (t := (unitaryDualEquiv u) ⁻¹' unitaryOrbitHull F) _
    (hclosed.preimage (unitaryDualEquiv u).continuous) hH
  apply convexHull_min _
    (hconv.linear_preimage ((unitaryDualEquiv u).toLinearEquiv.restrictScalars ℝ).toLinearMap)
  rintro _ ⟨v, rfl⟩
  change unitaryPullback (unitaryPullback F v) u ∈ unitaryOrbitHull F
  rw [unitaryPullback_mul]
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_range_self (v * u)))

lemma weakOrbitClosure_invariant (F : StrongDual ℂ M) (u : unitary M)
    {H : WeakDual ℂ M} (hH : H ∈ weakFunctionalClosure (unitaryOrbitHull F)) :
    weakUnitaryPullback u H ∈ weakFunctionalClosure (unitaryOrbitHull F) := by
  apply closure_minimal (t := (weakUnitaryPullback u) ⁻¹'
    weakFunctionalClosure (unitaryOrbitHull F)) _
    (isClosed_closure.preimage (weakUnitaryPullback u).continuous) hH
  rintro _ ⟨G, hG, rfl⟩
  exact subset_closure ⟨unitaryPullback G u, unitaryOrbitHull_invariant F u hG, rfl⟩

lemma weakOrbitClosure_convex (F : StrongDual ℂ M) :
    Convex ℝ (weakFunctionalClosure (unitaryOrbitHull F)) := by
  have hsmul : ContinuousConstSMul ℝ (WeakDual ℂ M) :=
    ⟨fun r => WeakDual.continuous_of_continuous_eval (fun a =>
      (WeakDual.eval_continuous a).const_smul r)⟩
  have hHull : Convex ℝ (unitaryOrbitHull F) :=
    (convex_convexHull ℝ (Set.range (unitaryPullback F))).closure
  let L : StrongDual ℂ M →ₗ[ℝ] WeakDual ℂ M :=
    { toFun := StrongDual.toWeakDual
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hImage : Convex ℝ (L '' unitaryOrbitHull F) := hHull.linear_image L
  have hClosed : Convex ℝ (closure (L '' unitaryOrbitHull F)) :=
    @Convex.closure ℝ (WeakDual ℂ M) _ _ _ _ _ _ hsmul _ hImage
  exact hClosed

def weakPredualRealMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    WeakSpace ℂ X →ₗ[ℝ] WeakDual ℂ M where
  toFun := weakPredualMap e
  map_add' x y := by
    apply WeakDual.toStrongDual.injective
    ext a
    change star (e.symm a ((toWeakSpace ℂ X).symm (x + y))) = _
    simp only [map_add, star_add]
    rfl
  map_smul' r x := by
    apply WeakDual.toStrongDual.injective
    ext a
    change star (e.symm a ((r : ℂ) • (toWeakSpace ℂ X).symm x)) =
      (r : ℂ) • star (e.symm a ((toWeakSpace ℂ X).symm x))
    rw [map_smul, star_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]

variable [PartialOrder M] [StarOrderedRing M]

omit [CompleteSpace X] [PartialOrder M] [StarOrderedRing M] in
lemma weakPredualOrbit_convex (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M) :
    Convex ℝ ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F)) := by
  intro x hx y hy a b ha hb hab
  have heq : weakPredualMap e (a • x + b • y) =
      a • weakPredualMap e x + b • weakPredualMap e y := by
    exact (weakPredualRealMap e).map_add (a • x) (b • y) |>.trans
      (congrArg₂ (· + ·) ((weakPredualRealMap e).map_smul a x)
        ((weakPredualRealMap e).map_smul b y))
  change weakPredualMap e (a • x + b • y) ∈ weakFunctionalClosure (unitaryOrbitHull F)
  rw [heq]
  exact (weakOrbitClosure_convex F) hx hy ha hb hab

lemma weakPredualOrbit_invariant (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M)
    (u : unitary M) :
    Set.MapsTo (weakIsometry (unitaryPredualAction e u))
      ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F))
      ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F)) := by
  intro x hx
  have heq : weakPredualMap e (weakIsometry (unitaryPredualAction e u) x) =
      weakUnitaryPullback (star u) (weakPredualMap e x) := by
    apply WeakDual.toStrongDual.injective
    exact predualEmbedding_unitaryAction e u ((toWeakSpace ℂ X).symm x)
  change weakPredualMap e (weakIsometry (unitaryPredualAction e u) x) ∈
    weakFunctionalClosure (unitaryOrbitHull F)
  rw [heq]
  exact weakOrbitClosure_invariant F (star u) hx

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakFunctionalClosure_eval_eq (K : Set (StrongDual ℂ M)) (a : M) (c : ℂ)
    (h : ∀ G ∈ K, G a = c) {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    F a = c := by
  apply closure_minimal (t := {G : WeakDual ℂ M | G a = c}) _
    (isClosed_eq (WeakDual.eval_continuous a) continuous_const) hF
  rintro _ ⟨G, hG, rfl⟩
  exact h G hG
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma tracial_of_unitary_invariant (F : StrongDual ℂ M)
    (hinv : ∀ (u : unitary M) (a : M), F ((u : M) * a * star (u : M)) = F a) :
    ∀ a b : M, F (a * b) = F (b * a) := by
  classical
  have hu (u : unitary M) (b : M) : F ((u : M) * b) = F (b * (u : M)) := by
    calc
      F ((u : M) * b) = F ((u : M) * (b * (u : M)) * star (u : M)) := by
        simp only [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]
      _ = F (b * (u : M)) := hinv u _
  intro a b
  obtain ⟨u, c, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  rw [ha, Finset.sum_mul, Finset.mul_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, hu]

variable [PartialOrder M] [StarOrderedRing M]

theorem exists_normal_tracial_average (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    ∃ τ : M →ₚ[ℂ] ℂ, TraceInPredual e τ ∧ τ 1 = ψ 1 ∧
      (∀ a b : M, τ (a * b) = τ (b * a)) ∧
      ∀ a : M, (∀ b : M, a * b = b * a) → τ a = ψ a := by
  classical
  let C : Set (WeakSpace ℂ X) := (weakPredualMap e) ⁻¹'
    weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))
  have hC : IsCompact C := normal_positive_predual_orbit_compact e hfinite ψ hψ
  obtain ⟨z, hz⟩ := hψ
  have hemb : predualEmbedding e z = positiveFunctionalCLM ψ := by
    ext a
    exact (hz a).symm
  have hn : C.Nonempty := by
    refine ⟨toWeakSpace ℂ X z, ?_⟩
    change StrongDual.toWeakDual (predualEmbedding e z) ∈
      weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))
    rw [hemb]
    apply subset_closure
    refine ⟨positiveFunctionalCLM ψ, ?_, rfl⟩
    have hmem := subset_closure (subset_convexHull ℝ
      (Set.range (unitaryPullback (positiveFunctionalCLM ψ))) (Set.mem_range_self 1))
    simpa only [unitaryPullback_one, unitaryOrbitHull] using hmem
  obtain ⟨x, hx, hfix⟩ := weakCompact_isometric_fixedPoint (unitaryPredualAction e)
    (unitaryPredualAction_one e) (unitaryPredualAction_mul e) C hC hn
    (weakPredualOrbit_convex e _) (weakPredualOrbit_invariant e _)
  let F := weakPredualMap e x
  have hFpos : ∀ a : M, 0 ≤ a → 0 ≤ F a :=
    weakFunctionalClosure_positive _ (unitaryOrbitHull_positive ψ) hx
  let τ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (WeakDual.toStrongDual F).toLinearMap
      monotone' := (monotone_iff_map_nonneg _).mpr hFpos }
  have hτnormal : TraceInPredual e τ := by
    exact ⟨(toWeakSpace ℂ X).symm x, fun _ => rfl⟩
  have hτcenter (a : M) (ha : ∀ b : M, a * b = b * a) : τ a = ψ a :=
    weakFunctionalClosure_eval_eq _ a (ψ a)
      (unitaryOrbitHull_central (positiveFunctionalCLM ψ) ha) hx
  have hτinv : ∀ (u : unitary M) (a : M), τ ((u : M) * a * star (u : M)) = τ a := by
    intro u a
    have hxfix : unitaryPredualAction e (star u) ((toWeakSpace ℂ X).symm x) =
        (toWeakSpace ℂ X).symm x := congrArg (toWeakSpace ℂ X).symm (hfix (star u))
    have heq := congrArg (predualEmbedding e) hxfix
    rw [predualEmbedding_unitaryAction, star_star] at heq
    exact congrArg (fun f : StrongDual ℂ M => f a) heq
  exact ⟨τ, hτnormal, hτcenter 1 (fun b => by rw [one_mul, mul_one]),
    tracial_of_unitary_invariant (positiveFunctionalCLM τ) hτinv, hτcenter⟩
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma positive_contraction_zero_mul (ψ : M →ₚ[ℂ] ℂ) {c : M}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hψc : ψ c = 0) (b : M) : ψ (c * b) = 0 := by
  have hcc : c * c ≤ c := by
    simpa only [pow_two, pow_one] using
      CStarAlgebra.pow_antitone hc0 hc1 (by omega : 1 ≤ 2)
  have hψcc : ψ (c * c) = 0 := le_antisymm
    ((ψ.monotone hcc).trans_eq hψc)
    (ψ.map_nonneg hc0.isSelfAdjoint.mul_self_nonneg)
  have h := Compat.norm_map_star_mul_sq_le ψ c b
  rw [hc0.isSelfAdjoint.star_eq, hψcc, norm_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ψ (c * b))])

lemma exists_null_support_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) {c : M}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hψc : ψ c = 0) :
    ∃ r : M, IsSupportProjection c r ∧ ψ r = 0 := by
  obtain ⟨r, hr, ht⟩ := HochschildSakai.exists_support_contraction e c hc0 hc1
  have hpow (n : ℕ) : ψ ((1 - c) ^ n) = ψ 1 := by
    induction n with
    | zero => simp only [pow_zero]
    | succ n ih =>
      rw [pow_succ', sub_mul, one_mul, map_sub,
        positive_contraction_zero_mul ψ hc0 hc1 hψc, sub_zero, ih]
  have hzero (n : ℕ) : ψ (1 - (1 - c) ^ n) = 0 := by
    rw [map_sub, hpow, sub_self]
  refine ⟨r, hr, ?_⟩
  have hl := trace_predual_tendsto e ψ hψ ht
  have heq : (fun n : ℕ => ψ (1 - (1 - c) ^ n)) = (fun _ : ℕ => (0 : ℂ)) := funext hzero
  rw [heq] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma normal_tracial_null_projection_join (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htp : τ p = 0) (htq : τ q = 0) :
    ∃ r : M, IsStarProjection r ∧ p ≤ r ∧ q ≤ r ∧ τ r = 0 := by
  obtain ⟨v, hvq, _, hr, hpr, hqr, _⟩ := exists_trace_free_projection_join e p q hp hq
  have hvi : τ v.initial = 0 := le_antisymm ((τ.monotone hvq).trans_eq htq)
    (τ.map_nonneg v.initial_proj.nonneg)
  have hvf : τ v.final = 0 := (htr v.val (star v.val)).trans hvi
  exact ⟨p + v.final, hr, hpr, hqr, by rw [map_add, htp, hvf, add_zero]⟩

theorem normal_trace_largest_null_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a)) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ τ p = 0 ∧
      ∀ q : M, IsStarProjection q → τ q = 0 → q ≤ p := by
  classical
  let S : Set M := {p | IsStarProjection p ∧ τ p = 0}
  obtain ⟨p, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨p, hp, hu, _, _, U, _, ht⟩ :=
      exists_projection_chain_supremum_with_limit e c ⟨a, ha⟩ hchain
        (fun q hq => (hc hq).1)
    refine ⟨p, ⟨hp, ?_⟩, hu⟩
    have heq : (fun q : c => τ (q : M)) = (fun _ : c => (0 : ℂ)) :=
      funext (fun q => (hc q.property).2)
    have hlim := trace_predual_tendsto e τ hτ ht
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds) 0
      (show (0 : M) ∈ S from ⟨IsStarProjection.zero M, map_zero τ⟩)
  have hp := hmax.1.1
  have hnull := hmax.1.2
  have hgreat (q : M) (hq : IsStarProjection q) (htq : τ q = 0) : q ≤ p := by
    obtain ⟨r, hr, hpr, hqr, htr0⟩ := normal_tracial_null_projection_join e τ htr hp hq hnull htq
    exact hqr.trans (hmax.2 ⟨hr, htr0⟩ hpr)
  have hconj (u : unitary M) : (u : M) * p * star (u : M) ≤ p := by
    apply hgreat
    · constructor
      · change ((u : M) * p * star (u : M)) * ((u : M) * p * star (u : M)) =
          (u : M) * p * star (u : M)
        calc
          _ = (u : M) * (p * ((star (u : M) * (u : M)) * p)) * star (u : M) := by
            noncomm_ring
          _ = _ := by rw [Unitary.star_mul_self_of_mem u.property, one_mul, hp.isIdempotentElem.eq]
      · change star ((u : M) * p * star (u : M)) = (u : M) * p * star (u : M)
        simp only [star_mul, star_star, hp.isSelfAdjoint.star_eq, mul_assoc]
    · rw [htr, ← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul, hnull]
  have hfix (u : unitary M) : (u : M) * p * star (u : M) = p := by
    apply le_antisymm (hconj u)
    have h := star_right_conjugate_le_conjugate (hconj (star u)) (u : M)
    simp only [Unitary.coe_star, star_star, mul_assoc,
      Unitary.mul_star_self_of_mem u.property, mul_one] at h
    have huus : (u : M) * (star (u : M) * p) = p := by
      rw [← mul_assoc, Unitary.mul_star_self_of_mem u.property, one_mul]
    rw [huus] at h
    simpa only [mul_assoc] using h
  have hcomm (u : unitary M) : p * (u : M) = (u : M) * p := by
    have h := congrArg (fun a : M => a * (u : M)) (hfix u)
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using h.symm
  refine ⟨p, hp, ?_, hnull, hgreat⟩
  intro a
  obtain ⟨u, c, rfl, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm, smul_mul_assoc, hcomm]

theorem normal_trace_faithful_of_center (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hcenter : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) →
      τ p = 0 → p = 0) : ∀ a : M, τ (star a * a) = 0 → a = 0 := by
  obtain ⟨p, hp, hpc, hnull, hgreat⟩ := normal_trace_largest_null_projection e τ hτ htr
  have hp0 : p = 0 := hcenter p hp hpc hnull
  intro a ha
  let t : ℝ := ‖star a * a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let c : M := t⁻¹ • (star a * a)
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr ht.le) (star_mul_self_nonneg a)
  have hcn : ‖c‖ ≤ 1 := by
    rw [show c = t⁻¹ • (star a * a) from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_one₀ ht).mpr (by dsimp [t]; linarith)
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  have hτc : τ c = 0 := by
    rw [show c = t⁻¹ • (star a * a) from rfl, τ.map_smul_of_tower, ha, smul_zero]
  obtain ⟨q, hq, hτq⟩ := exists_null_support_projection e τ hτ hc0 hc1 hτc
  have hq0 : q = 0 := le_antisymm (hp0 ▸ hgreat q hq.proj hτq) hq.proj.nonneg
  have hc : c = 0 := by simpa only [hq0, zero_mul] using hq.left.symm
  have haa : star a * a = 0 := (smul_eq_zero.mp hc).resolve_left (inv_ne_zero ht.ne')
  apply norm_eq_zero.mp
  have hn := congrArg norm haa
  rw [CStarRing.norm_star_mul_self, norm_zero] at hn
  nlinarith [norm_nonneg a]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem faithful_normal_trace_of_center_state (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hψ1 : ψ 1 = 1)
    (hfaith : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) → ψ p = 0 → p = 0) :
    ∃ τ : M →ₚ[ℂ] ℂ, TraceInPredual e τ ∧ τ 1 = 1 ∧
      (∀ a b : M, τ (a * b) = τ (b * a)) ∧
      ∀ a : M, τ (star a * a) = 0 → a = 0 := by
  obtain ⟨τ, hτ, hτ1, htr, hc⟩ := exists_normal_tracial_average e hfinite ψ hψ
  refine ⟨τ, hτ, hτ1.trans hψ1, htr, ?_⟩
  apply normal_trace_faithful_of_center e τ hτ htr
  intro p hp hpc hτp
  apply hfaith p hp hpc
  rwa [hc p hpc] at hτp
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.faithful_normal_trace_of_center_state.{u} := @OAI.BoundedHochschild.KadisonRingrose.faithful_normal_trace_of_center_state.{u}
