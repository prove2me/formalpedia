-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.normal_positive_uniform_orbit_hull
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:51:16.429212+00:00
-- url     : https://prove2.me/submissions/d51474f5-50fa-49f5-b1a6-d5506e7c51d2

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

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
open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

lemma central_mul_assoc (z : M) (hz : ∀ a, z*a=a*z) (a b : M) :
    a*(z*b) = z*(a*b) := by rw [← mul_assoc, ← hz, mul_assoc]

lemma central_idempotent_mul (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z) (a b : M) :
    (z*a)*(z*b) = z*(a*b) := by
  rw [mul_assoc, central_mul_assoc z hz, ← mul_assoc z z, hi]
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
open Filter Topology
namespace BoundedHochschild
namespace WeakSubspace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def preannihilator (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ X where
  carrier := {z | ∀ f ∈ S, f z=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy f hf; simp [map_add,hx f hf,hy f hf]
  smul_mem' := by intro c x hx f hf; simp [map_smul,hx f hf]

lemma preannihilator_closed (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := by
  change IsClosed {z | ∀ f, f ∈ S → f z=0}
  simpa only [Set.ofPred_forall,WeakDual.toStrongDual_apply] using
    (isClosed_iInter fun (f : WeakDual ℂ X) => isClosed_iInter fun (_ : f ∈ S) =>
      isClosed_eq (WeakDual.toStrongDual f).continuous (continuous_const (y := (0 : ℂ))))

lemma mem_iff_annihilates (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) (f : WeakDual ℂ X) :
    f ∈ S ↔ ∀ z ∈ preannihilator S, f z=0 := by
  let : IsScalarTower ℝ ℂ (WeakDual ℂ X) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ X))
  let hc : LocallyConvexSpace ℝ (WeakDual ℂ X) :=
    @WeakBilin.locallyConvexSpace ℂ (StrongDual ℂ X) X _ _ _ _ _ _ _ _ _
  constructor
  · intro hf z hz
    exact hz f hf
  · intro hf
    by_contra hnot
    obtain ⟨F,c,hFc,hcf⟩ := @RCLike.geometric_hahn_banach_closed_point ℂ (WeakDual ℂ X)
      _ _ _ (S : Set (WeakDual ℂ X)) f _ _ _ _ _ hc
      (S.restrictScalars ℝ).convex hS hnot
    have hzero (a : WeakDual ℂ X) (ha : a ∈ S) : F a=0 := by
      by_contra hne
      have hb := hFc ((((c+1 : ℝ) : ℂ) / F a) • a) (S.smul_mem _ ha)
      rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hne] at hb
      simp only [RCLike.re_to_complex,Complex.ofReal_re] at hb
      linarith
    obtain ⟨z,hz⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ X) F
    have heval (a : WeakDual ℂ X) : F a=a z := by
      rw [← hz]
      rfl
    have hmem : z ∈ preannihilator S := by
      intro a ha
      rw [← heval]
      exact hzero a ha
    have hf0 := hf z hmem
    have hc0 := hFc 0 S.zero_mem
    simp only [map_zero] at hc0
    rw [heval,hf0] at hcf
    simp only [RCLike.zero_re] at hcf
    linarith

def strong (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ (StrongDual ℂ X) :=
  S.map WeakDual.toStrongDual.toLinearMap

lemma mem_strong (S : Submodule ℂ (WeakDual ℂ X)) (f : StrongDual ℂ X) :
    f ∈ strong S ↔ StrongDual.toWeakDual f ∈ S := by
  constructor
  · rintro ⟨g,hg,hgf⟩
    change WeakDual.toStrongDual g=f at hgf
    rw [← hgf]
    exact hg
  · intro hf
    exact ⟨StrongDual.toWeakDual f,hf,rfl⟩

instance preannihilator_closed_instance (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := preannihilator_closed S

lemma quotient_dual_norm (K : Submodule ℂ X) [IsClosed (K : Set X)]
    (F : StrongDual ℂ (X ⧸ K)) : ‖F.comp K.mkQL‖=‖F‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (F.comp K.mkQL) (norm_nonneg F)
    intro x
    exact (F.le_opNorm (K.mkQL x)).trans
      (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le K x) (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro q
    apply le_of_forall_pos_le_add
    intro ε hε
    let C := ‖F.comp K.mkQL‖
    have hC : 0 ≤ C := norm_nonneg _
    obtain ⟨x,hx,hxn⟩ := Submodule.Quotient.norm_mk_lt q (show 0 < ε/(C+1) by positivity)
    have hb := (F.comp K.mkQL).le_opNorm x
    change ‖F (Submodule.Quotient.mk x)‖ ≤ C*‖x‖ at hb
    rw [hx] at hb
    have hd : C*(ε/(C+1)) ≤ ε := by
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      nlinarith
    calc
      ‖F q‖ ≤ C*‖x‖ := hb
      _ ≤ C*(‖q‖+ε/(C+1)) := mul_le_mul_of_nonneg_left hxn.le hC
      _ ≤ C*‖q‖+ε := by nlinarith

def quotientDual (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) →ₗᵢ[ℂ] strong S where
  toFun F := ⟨F.comp (preannihilator S).mkQL,by
    rw [mem_strong,mem_iff_annihilates S hS]
    intro z hz
    change F (Submodule.Quotient.mk z)=0
    rw [(Submodule.Quotient.mk_eq_zero (preannihilator S)).mpr hz,map_zero]⟩
  map_add' F G := by ext z; rfl
  map_smul' c F := by ext z; rfl
  norm_map' F := quotient_dual_norm (preannihilator S) F

lemma quotientDual_surjective (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    Function.Surjective (quotientDual S hS) := by
  intro f
  have hk : preannihilator S ≤ f.val.ker := by
    intro z hz
    exact hz (StrongDual.toWeakDual f.val) ((mem_strong S f.val).mp f.property)
  refine ⟨(preannihilator S).liftQL f.val hk,?_⟩
  apply Subtype.ext
  ext z
  rfl

def quotientDualEquiv (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) ≃ₗᵢ[ℂ] strong S :=
  { LinearEquiv.ofBijective (quotientDual S hS).toLinearMap
      ⟨by
        intro a b hab
        ext q
        obtain ⟨z,rfl⟩ := (preannihilator S).mkQ_surjective q
        exact congrArg (fun f : strong S => f.val z) hab,
       quotientDual_surjective S hS⟩ with
    norm_map' := (quotientDual S hS).norm_map }
end WeakSubspace
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

lemma final_mul (v : PartialIso M) : v.final * (v : M) = v := v.mul_star_mul

lemma final_proj (v : PartialIso M) : IsStarProjection v.final := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self _⟩
  change ((v : M) * star (v : M)) * ((v : M) * star (v : M)) = (v : M) * star (v : M)
  calc
    _ = ((v : M) * star (v : M) * v) * star (v : M) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]
lemma norm_le_one (v : PartialIso M) : ‖(v : M)‖ ≤ 1 := by
  have hi := v.initial_proj.norm_le _
  have he : ‖(v : M)‖ * ‖(v : M)‖ = ‖v.initial‖ := by
    exact CStarRing.norm_star_mul_self.symm
  nlinarith [norm_nonneg (v : M)]

variable [PartialOrder M]

variable [StarOrderedRing M]

omit [StarOrderedRing M] in
lemma initial_mono {v w : PartialIso M} (h : v ≤ w) : v.initial ≤ w.initial := h.1

lemma star_mul_of_le {v w : PartialIso M} (h : v ≤ w) : star (v : M) * w = v.initial := by
  have hv := congrArg star h.2
  simp only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] at hv
  calc
    star (v : M) * w = (v.initial * star (w : M)) * w := by rw [hv]
    _ = v.initial * w.initial := by simp only [initial,mul_assoc]
    _ = v.initial := (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp h.1
lemma star_mul_of_ge {v w : PartialIso M} (h : v ≤ w) : star (w : M) * v = v.initial := by
  simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
    using congrArg star (star_mul_of_le h)
lemma final_mono {v w : PartialIso M} (h : v ≤ w) : v.final ≤ w.final := by
  apply (v.final_proj.le_iff_mul_eq_right w.final_proj).mpr
  calc
    w.final * v.final = (w : M) * (star (w : M) * v) * star (v : M) := by
      simp only [final,mul_assoc]
    _ = (w : M) * v.initial * star (v : M) := by rw [star_mul_of_ge h]
    _ = v.final := by rw [h.2]; rfl

section
omit [PartialOrder M] [StarOrderedRing M]

lemma star_mul_eq_zero_of_final_orthogonal {v w : PartialIso M}
    (h : v.final*w.final=0) : star (v : M)*w=0 := by
  have hv : star (v : M)*v.final=star (v : M) := by
    simpa only [star_mul,star_star,v.final_proj.isSelfAdjoint.star_eq]
      using congrArg star v.final_mul
  calc
    star (v : M)*w = (star (v : M)*v.final)*(w.final*(w : M)) := by
      rw [hv,w.final_mul]
    _ = star (v : M)*(v.final*w.final)*(w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma mul_star_eq_zero_of_initial_orthogonal {v w : PartialIso M}
    (h : v.initial*w.initial=0) : (v : M)*star (w : M)=0 := by
  have hw : w.initial*star (w : M)=star (w : M) := by
    simpa only [star_mul,star_star,w.initial_proj.isSelfAdjoint.star_eq]
      using congrArg star w.mul_initial
  calc
    (v : M)*star (w : M) = ((v : M)*v.initial)*(w.initial*star (w : M)) := by
      rw [v.mul_initial,hw]
    _ = (v : M)*(v.initial*w.initial)*star (w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma orthogonal_initial_symm {v w : PartialIso M} (h : v.initial*w.initial=0) :
    w.initial*v.initial=0 := by
  simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
    w.initial_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h
lemma orthogonal_final_symm {v w : PartialIso M} (h : v.final*w.final=0) :
    w.final*v.final=0 := by
  simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : PartialIso M where
  val := (v : M)+w
  mul_star_mul := by
    have hab := mul_star_eq_zero_of_initial_orthogonal hi
    have hba := mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi)
    have hab' := star_mul_eq_zero_of_final_orthogonal hf
    have hba' := star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf)
    simp only [star_add,mul_add,add_mul,hab,hba,zero_add,add_zero]
    rw [v.mul_star_mul,w.mul_star_mul,mul_assoc,mul_assoc,hab',hba',mul_zero,mul_zero]
    abel

lemma orthogonalSum_initial (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).initial=v.initial+w.initial := by
  change star ((v : M)+w)*((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,star_mul_eq_zero_of_final_orthogonal hf,
    star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf),zero_add,add_zero,initial]
lemma orthogonalSum_final (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).final=v.final+w.final := by
  change ((v : M)+w)*star ((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,mul_star_eq_zero_of_initial_orthogonal hi,
    mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi),zero_add,add_zero,final]
end

lemma le_orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : v ≤ orthogonalSum v w hi hf := by
  constructor
  · rw [orthogonalSum_initial]
    exact le_add_of_nonneg_right w.initial_proj.nonneg
  · change ((v : M)+w)*v.initial=v
    rw [add_mul,v.mul_initial]
    have hh : (w : M)*v.initial=0 := by
      calc
        (w : M)*v.initial = ((w : M)*w.initial)*v.initial := by rw [w.mul_initial]
        _ = 0 := by rw [mul_assoc,orthogonal_initial_symm hi,mul_zero]
    rw [hh,add_zero]

end PartialIso
end HochschildComparison

open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity HochschildDixmier
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

namespace PartialIso

end PartialIso

include e in
lemma partialIso_of_nonzero_corner [CompleteSpace X]
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (b : M) (hb : b ≠ 0) (hpb : p*b=b) (hbq : b*q=b) :
    ∃ v : PartialIso M, (v : M) ≠ 0 ∧ v.initial ≤ q ∧ v.final ≤ p := by
  obtain ⟨v,r,s,hr,hvr,hvs,hs,hbabs,hvrv,_hsb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have hva : star v*b=CFC.abs b := by
    calc
      star v*b = star v*(v*CFC.abs b) := congrArg (star v * ·) hbabs
      _ = CFC.abs b := by rw [← mul_assoc,hvr,hr.left]
  have hvp : p*v=v := by
    have hz : ((1-p)*v)*CFC.abs b=0 := by
      rw [mul_assoc,← hbabs,sub_mul,one_mul,hpb,sub_self]
    have hz' := HochschildPolar.support_right_annihilate hr
      (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    rw [mul_assoc,hvrv,sub_mul,one_mul,sub_eq_zero] at hz'
    exact hz'.symm
  have hrq : r*q=r := by
    have ha : CFC.abs b*(1-q)=0 := by
      rw [← hva,mul_assoc,mul_sub,mul_one,hbq,sub_self,mul_zero]
    have hz := hr.annihilate (1-q) ha
    simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hz
  have hvpartial : v*star v*v=v := by rw [mul_assoc,hvr,hvrv]
  let w : PartialIso M := ⟨v,hvpartial⟩
  refine ⟨w,?_,?_,?_⟩
  · intro hv0
    change v=0 at hv0
    apply hb
    simpa only [hv0,zero_mul] using hbabs
  · change star v*v ≤ q
    rw [hvr]
    exact (hr.proj.le_iff_mul_eq_left hq).mpr hrq
  · apply (w.final_proj.le_iff_mul_eq_right hp).mpr
    change p*(v*star v)=v*star v
    rw [← mul_assoc,hvp]
end HochschildComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_partialIso_chain_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ w : PartialIso M, (∀ v ∈ c, v ≤ w) ∧
      (∀ z : PartialIso M, (∀ v ∈ c, v ≤ z) → w ≤ z) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.initial ≤ r) → w.initial ≤ r) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.final ≤ r) → w.final ≤ r) := by
  classical
  let S : Set M := PartialIso.initial '' c
  have hSne : S.Nonempty := hne.image _
  have hSchain : IsChain (· ≤ ·) S := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ _
    exact (hc.total hv hw).imp PartialIso.initial_mono PartialIso.initial_mono
  have hSproj : ∀ r ∈ S, IsStarProjection r := by
    rintro _ ⟨v, _, rfl⟩
    exact v.initial_proj
  obtain ⟨p, hp, hupper, hleast, hann, _⟩ :=
    exists_projection_chain_supremum_with_limit e S hSne hSchain hSproj
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := ⟨fun a b => by
    rcases hc.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter c := Ultrafilter.of atTop
  have hU : (U : Filter c) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨V, _, ht⟩ := exists_predual_ultralimit e U
    (fun v : c => ((v : PartialIso M) : M)) 1 (fun v => v.val.norm_le_one)
  have hVi (v : c) : V * v.val.initial = (v.val : M) := by
    have hm := HochschildSakai.predual_tendsto_mul_right e v.val.initial ht
    have heq : (fun w : c => (w.val : M) * v.val.initial) =ᶠ[U]
        (fun _ => (v.val : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact hvw.2
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hstarVi (v : c) : star V * (v.val : M) = v.val.initial := by
    have hm := HochschildSakai.predual_tendsto_mul_right e (v.val : M)
      (HochschildSakai.predual_tendsto_star e ht)
    have heq : (fun w : c => star (w.val : M) * (v.val : M)) =ᶠ[U]
        (fun _ => v.val.initial) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact PartialIso.star_mul_of_ge hvw
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hVp : V * p = V := by
    have hm := HochschildSakai.predual_tendsto_mul_right e p ht
    have heq : (fun v : c => (v.val : M) * p) =
        (fun v : c => (v.val : M)) := by
      funext v
      calc
        (v.val : M) * p = ((v.val : M) * v.val.initial) * p := by
          rw [v.val.mul_initial]
        _ = (v.val : M) := by
          rw [mul_assoc, (v.val.initial_proj.le_iff_mul_eq_left hp).mp
            (hupper _ ⟨v.val, v.property, rfl⟩), v.val.mul_initial]
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  have hpstar : p * star V = star V := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hVp
  have hVV : star V * V = p := by
    have hann' : p * (star V * V - p) = 0 := by
      apply hann
      rintro _ ⟨v, hv, rfl⟩
      have hfixed : v.initial * (star V * V) = v.initial := by
        have hs : v.initial * star V = star (v : M) := by
          simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] using
            congrArg star (hVi ⟨v, hv⟩)
        calc
          v.initial * (star V * V) = star (v : M) * V := by rw [← mul_assoc, hs]
          _ = v.initial := by
            simpa only [star_mul, star_star, v.initial_proj.isSelfAdjoint.star_eq]
              using congrArg star (hstarVi ⟨v, hv⟩)
      rw [mul_sub, hfixed, (v.initial_proj.le_iff_mul_eq_left hp).mp
        (hupper _ ⟨v, hv, rfl⟩), sub_self]
    rw [mul_sub, ← mul_assoc, hpstar, hp.isIdempotentElem.eq] at hann'
    exact sub_eq_zero.mp hann'
  let w : PartialIso M := ⟨V, by rw [mul_assoc, hVV, hVp]⟩
  have hwi : w.initial = p := hVV
  have hwupper : ∀ v ∈ c, v ≤ w := by
    intro v hv
    exact ⟨by rw [hwi]; exact hupper _ ⟨v, hv, rfl⟩, hVi ⟨v, hv⟩⟩
  refine ⟨w, hwupper, ?_, ?_, ?_⟩
  · intro z hz
    have hpz : p ≤ z.initial := by
      apply hleast z.initial z.initial_proj
      rintro _ ⟨v, hv, rfl⟩
      exact (hz v hv).1
    have hzp : (z : M) * p = V := by
      have ha : p * star ((z : M) - V) = 0 := by
        apply hann
        rintro _ ⟨v, hv, rfl⟩
        have heq : ((z : M) - V) * v.initial = 0 := by
          rw [sub_mul, (hz v hv).2, hVi ⟨v, hv⟩, sub_self]
        simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq, star_zero]
          using congrArg star heq
      have ha' : ((z : M) - V) * p = 0 := by
        simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq, star_zero]
          using congrArg star ha
      rwa [sub_mul, hVp, sub_eq_zero] at ha'
    exact ⟨by rw [hwi]; exact hpz, by change (z : M) * w.initial = V; rw [hwi, hzp]⟩
  · intro r hr hb
    rw [hwi]
    apply hleast r hr
    rintro _ ⟨v, hv, rfl⟩
    exact hb v hv
  · intro r hr hb
    have hrV : r * V = V := by
      have hm := HochschildSakai.predual_tendsto_mul_left e r ht
      have heq : (fun v : c => r * (v.val : M)) =
          (fun v : c => (v.val : M)) := by
        funext v
        calc
          r * (v.val : M) = r * (v.val.final * (v.val : M)) := by rw [v.val.final_mul]
          _ = (v.val : M) := by
            rw [← mul_assoc, (v.val.final_proj.le_iff_mul_eq_right hr).mp
              (hb v.val v.property), v.val.final_mul]
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    apply (w.final_proj.le_iff_mul_eq_right hr).mpr
    change r * (V * star V) = V * star V
    rw [← mul_assoc, hrV]

theorem partialIso_chain_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ v ∈ c, v.initial ≤ p ∧ v.final ≤ q) :
    ∃ w : PartialIso M, w.initial ≤ p ∧ w.final ≤ q ∧ ∀ v ∈ c, v ≤ w := by
  obtain ⟨w, hupper, _, hi, hf⟩ := exists_partialIso_chain_supremum e c hc hne
  exact ⟨w, hi p hp (fun v hv => (hs v hv).1),
    hf q hq (fun v hv => (hs v hv).2), hupper⟩
end KadisonRingrose
end BoundedHochschild
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

theorem exists_increasing_projection_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : ℕ → M) (hp : ∀ n, IsStarProjection (p n)) (hm : Monotone p) :
    ∃ s : M, IsStarProjection s ∧ IsLUB (Set.range p) s ∧
      PredualTendsto e p atTop s := by
  obtain ⟨s, _, hlub, ht⟩ := HochschildSakai.exists_monotone_predual_limit e p hm
    1 zero_le_one (fun n => (hp n).norm_le _)
  have hfixed (n : ℕ) : p n * s = p n := by
    have hm' := HochschildSakai.predual_tendsto_mul_left e (p n) ht
    have heq : (fun m => p n * p m) =ᶠ[atTop] (fun _ => p n) := by
      filter_upwards [eventually_ge_atTop n] with m hnm
      exact ((hp n).le_iff_mul_eq_left (hp m)).mp (hm hnm)
    apply predual_tendsto_unique e hm'
    intro x
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a x) h.symm)
  have hmul : s * s = s := by
    have hs := HochschildSakai.predual_tendsto_mul_right e s ht
    have heq : (fun n => p n * s) = p := funext hfixed
    rw [heq] at hs
    exact predual_tendsto_unique e hs ht
  have hstar : star s = s := by
    have hs := HochschildSakai.predual_tendsto_star e ht
    have heq : (fun n => star (p n)) = p := funext fun n => (hp n).isSelfAdjoint.star_eq
    rw [heq] at hs
    exact predual_tendsto_unique e hs ht
  exact ⟨s, ⟨hmul, hstar⟩, hlub, ht⟩

theorem exists_decreasing_projection_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : ℕ → M) (hp : ∀ n, IsStarProjection (p n)) (hm : Antitone p) :
    ∃ s : M, IsStarProjection s ∧ IsGLB (Set.range p) s ∧
      PredualTendsto e p atTop s := by
  obtain ⟨s, hs, _, ht⟩ := exists_increasing_projection_limit e (fun n => 1 - p n)
    (fun n => (hp n).one_sub) (fun i j hij => sub_le_sub_left (hm hij) 1)
  have ht' : PredualTendsto e p atTop (1 - s) := by
    have hh := predual_tendsto_sub e (predual_tendsto_const e 1 atTop) ht
    simpa only [sub_sub_cancel] using hh
  exact ⟨1 - s, hs.one_sub,
    HochschildSakai.isGLB_of_antitone_predual_limit e p hm ht' 1 zero_le_one
      (fun n => (hp n).norm_le _), ht'⟩
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
open Filter Topology
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakEquiv : WeakDual ℂ X ≃ₗ⋆[ℂ] M :=
  WeakDual.toStrongDual.trans e.toLinearEquiv

lemma normal_continuous (A : M →L[ℂ] M) (hA : HasPreadjoint e A) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (A (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  obtain ⟨w,hw⟩ := hA z
  change Continuous (fun f : WeakDual ℂ X => e.symm (A (weakEquiv e f)) z)
  simp_rw [hw]
  simpa [weakEquiv] using WeakDual.eval_continuous (𝕜 := ℂ) w

variable (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

end WeakAlgebra
end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
open HochschildTraceNorm
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
  (hτ : TraceInPredual e τ)

end WeakAlgebra
end BoundedHochschild

namespace BoundedHochschild
open TopologicalSpace
variable {M : Type*}

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

instance closedSubalgebra_starOrderedRing (B : StarSubalgebra ℂ M)
    [IsClosed (B : Set M)] [StarOrderedRing M] : StarOrderedRing B := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ B := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)
end WeakAlgebra
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
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end HochschildCorners

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

section Predual
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakCorner : Submodule ℂ (WeakDual ℂ X) where
  carrier := {f | weakEquiv e f ∈ corner p hp}
  zero_mem' := by
    change weakEquiv e 0 ∈ corner p hp
    rw [map_zero]
    exact (corner p hp).zero_mem
  add_mem' := by
    intro a b ha hb
    change weakEquiv e (a+b) ∈ corner p hp
    rw [map_add]
    exact (corner p hp).add_mem ha hb
  smul_mem' := by
    intro c a ha
    change weakEquiv e (c • a) ∈ corner p hp
    rw [LinearEquiv.map_smulₛₗ]
    exact (corner p hp).smul_mem (star c) ha

lemma weakCorner_closed : IsClosed (weakCorner p hp e : Set (WeakDual ℂ X)) := by
  have hL := mul_hasPreadjoint e p
  have hR := mul_right_hasPreadjoint e p
  have hLeft := isClosed_eq (normal_continuous e _ hL) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  have hRight := isClosed_eq (normal_continuous e _ hR) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  change IsClosed {f | (weakEquiv e).symm (p*weakEquiv e f)=f} at hLeft
  change IsClosed {f | (weakEquiv e).symm (weakEquiv e f*p)=f} at hRight
  convert hLeft.inter hRight using 1
  ext f
  change (p*weakEquiv e f=weakEquiv e f ∧ weakEquiv e f*p=weakEquiv e f) ↔
    ((weakEquiv e).symm (p*weakEquiv e f)=f ∧ (weakEquiv e).symm (weakEquiv e f*p)=f)
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨by rw [h,LinearEquiv.symm_apply_apply],by rw [h',LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨h,h'⟩
    exact ⟨by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h,
      by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h'⟩

def CornerPredual := X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)
instance : NormedAddCommGroup (CornerPredual p hp e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : NormedSpace ℂ (CornerPredual p hp e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : CompleteSpace (CornerPredual p hp e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))

def cornerStrongEquiv : WeakSubspace.strong (weakCorner p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp where
  toFun f := ⟨e f.val,by
    have hf := (WeakSubspace.mem_strong (weakCorner p hp e) f.val).mp f.property
    exact hf⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ corner p hp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using a.property⟩
  left_inv f := Subtype.ext (e.symm_apply_apply f.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)
  map_add' f g := Subtype.ext (map_add e f.val g.val)
  map_smul' c f := Subtype.ext (e.map_smulₛₗ c f.val)
  norm_map' f := e.norm_map f.val

def cornerPredualEquiv : StrongDual ℂ (CornerPredual p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp :=
  (WeakSubspace.quotientDualEquiv (weakCorner p hp e) (weakCorner_closed p hp e)).trans
    (cornerStrongEquiv p hp e)
end Predual
end HochschildCorners
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def FiniteCorner (p : M) : Prop :=
  ∀ a : M, p * a = a → a * p = a → star a * a = p → a * star a = p

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_iff (p : M) (hp : IsStarProjection p) :
    FiniteCorner p ↔ FiniteAlgebra (HochschildCorners.Corner p hp) := by
  constructor
  · intro h a ha
    apply Subtype.ext
    exact h a a.property.1 a.property.2 (congrArg Subtype.val ha)
  · intro h a hL hR ha
    let b : HochschildCorners.Corner p hp := ⟨a, hL, hR⟩
    exact congrArg Subtype.val (h b (Subtype.ext ha))

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_of_finiteAlgebra (hfinite : FiniteAlgebra M)
    (p : M) (hp : IsStarProjection p) : FiniteCorner p := by
  intro a hL hR haa
  have hsL : star a * p = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hL
  have hsR : p * star a = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hR
  have hca : (1 - p) * a = 0 := by rw [sub_mul, one_mul, hL, sub_self]
  have hac : a * (1 - p) = 0 := by rw [mul_sub, mul_one, hR, sub_self]
  have hcsa : (1 - p) * star a = 0 := by rw [sub_mul, one_mul, hsR, sub_self]
  have hsac : star a * (1 - p) = 0 := by rw [mul_sub, mul_one, hsL, sub_self]
  have hin : star (a + (1 - p)) * (a + (1 - p)) = 1 := by
    simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      add_mul, mul_add, hsac, hca, zero_add, add_zero, haa,
      hp.one_sub.isIdempotentElem.eq]
    abel
  have hout := hfinite (a + (1 - p)) hin
  simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
    add_mul, mul_add, hac, hcsa, zero_add, add_zero,
    hp.one_sub.isIdempotentElem.eq] at hout
  have hp1 : p + (1 - p) = 1 := by abel
  exact add_right_cancel (hout.trans hp1.symm)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_trace_free_central_separator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (_hq : IsStarProjection q)
    (hpq : ∀ a : M, p * a * q = 0) :
    ∃ z : M, CentralProjection z ∧ p ≤ z ∧ z * q = 0 := by
  classical
  let S : Set M := {r | IsStarProjection r ∧ ∀ a : M, r * a * q = 0}
  have hpS : p ∈ S := ⟨hp, hpq⟩
  obtain ⟨r, hpr, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s, hs, hu, _, ha, _⟩ := exists_projection_chain_supremum_with_limit e c
      ⟨y, hy⟩ hchain (fun t ht => (hc ht).1)
    refine ⟨s, ⟨hs, ?_⟩, hu⟩
    intro a
    rw [mul_assoc]
    apply ha
    intro t ht
    exact (mul_assoc t a q) ▸ (hc ht).2 a) p hpS
  have hr : IsStarProjection r := hmax.1.1
  have hrq : ∀ a : M, r * a * q = 0 := hmax.1.2
  have hcross (a : M) : (1 - r) * a * r = 0 := by
    let b : M := (1 - r) * a * r
    have hbq : ∀ d : M, b * d * q = 0 := by
      intro d
      calc
        b * d * q = (1 - r) * a * (r * d * q) := by simp only [b, mul_assoc]
        _ = 0 := by rw [hrq d, mul_zero]
    have hrb : r * b = 0 := by
      change r * ((1 - r) * a * r) = 0
      rw [← mul_assoc, ← mul_assoc, hr.mul_one_sub_self, zero_mul, zero_mul]
    obtain ⟨t, ht⟩ := HochschildSakai.exists_support_projection e (b * star b)
      (mul_star_self_nonneg b)
    have hrt : r * t = 0 := HochschildPolar.support_right_annihilate ht
      (IsSelfAdjoint.mul_star_self b) (by rw [← mul_assoc, hrb, zero_mul])
    have htq : ∀ d : M, t * d * q = 0 := by
      intro d
      rw [mul_assoc]
      apply ht.annihilate
      calc
        (b * star b) * (d * q) = b * (star b * d) * q := by simp only [mul_assoc]
        _ = 0 := hbq (star b * d)
    have hsum : r + t ∈ S := ⟨hr.add ht.proj hrt, fun d => by
      rw [add_mul, add_mul, hrq d, htq d, zero_add]⟩
    have hle : r ≤ r + t := le_add_of_nonneg_right ht.proj.nonneg
    have heq : r + t = r := le_antisymm (hmax.2 hsum hle) hle
    have ht0 : t = 0 := add_eq_left.mp heq
    have hb0 : b * star b = 0 := by
      have hh := ht.left
      rw [ht0, zero_mul] at hh
      exact hh.symm
    exact (CStarRing.mul_star_self_eq_zero_iff b).mp hb0
  have hcentral : ∀ a : M, Commute r a := by
    intro a
    have hright : a * r = r * a * r := by
      have h := hcross a
      rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at h
      exact h
    have hleft : r * a = r * a * r := by
      have h := congrArg star (hcross (star a))
      simp only [star_mul, star_sub, star_one, star_star, hr.isSelfAdjoint.star_eq,
        star_zero] at h
      rw [mul_sub, mul_one, mul_sub, ← mul_assoc, sub_eq_zero] at h
      exact h
    exact hleft.trans hright.symm
  refine ⟨r, ⟨hr, hcentral⟩, hpr, ?_⟩
  simpa only [mul_one] using hrq 1
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

open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialIso

lemma restrict_square (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : star ((v:M)*p)*((v:M)*p)=p := by
  calc
    star ((v:M)*p)*((v:M)*p) = p*v.initial*p := by
      simp only [star_mul,hp.isSelfAdjoint.star_eq,initial,mul_assoc]
    _ = p := by rw [(hp.le_iff_mul_eq_left v.initial_proj).mp hpv,hp.isIdempotentElem.eq]

def restrict (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : PartialIso M :=
  ⟨(v:M)*p,by rw [mul_assoc,restrict_square v hp hpv,mul_assoc,hp.isIdempotentElem.eq]⟩
@[simp] lemma restrict_coe (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : ((v.restrict hp hpv : PartialIso M):M)=(v:M)*p := rfl
@[simp] lemma restrict_initial (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : (v.restrict hp hpv).initial=p := restrict_square v hp hpv
lemma restrict_le (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : v.restrict hp hpv ≤ v := by
  exact ⟨by simpa only [restrict_initial] using hpv,by simp only [restrict_initial,restrict_coe]⟩
end PartialIso

lemma projection_orthogonal_mono {p q r s : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hs : IsStarProjection s)
    (hpr : p ≤ r) (hqs : q ≤ s) (hrs : r*s=0) : p*q=0 := by
  calc
    p*q = (p*r)*(s*q) := by
      rw [(hp.le_iff_mul_eq_left hr).mp hpr,(hq.le_iff_mul_eq_right hs).mp hqs]
    _ = p*(r*s)*q := by simp only [mul_assoc]
    _ = 0 := by rw [hrs,mul_zero,zero_mul]
end HochschildComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralComparison
open BoundedHochschild HochschildRigidity HochschildComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma orthogonal_of_le_sub {p r t : M}
    (hp : IsStarProjection p) (hr : IsStarProjection r) (ht : IsStarProjection t)
    (hrp : r ≤ p) (htr : t ≤ p-r) : r*t=0 := by
  have hpr := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,sub_self,zero_mul]
end HochschildCentralComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_maximal_partialIso (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : PartialIso M, v.initial ≤ p ∧ v.final ≤ q ∧
      ∀ a : M, (q - v.final) * a * (p - v.initial) = 0 := by
  classical
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.nonneg, by simpa using hq.nonneg⟩
  obtain ⟨v, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s, hsp, hsq, hu⟩ := partialIso_chain_upper e hp hq c hchain ⟨y, hy⟩
      (fun z hz => hc hz)
    exact ⟨s, ⟨hsp, hsq⟩, hu⟩) 0 hz
  have hvp : v.initial ≤ p := hmax.1.1
  have hvq : v.final ≤ q := hmax.1.2
  refine ⟨v, hvp, hvq, fun a => ?_⟩
  by_contra ha
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  obtain ⟨w, hw0, hwp, hwq⟩ := partialIso_of_nonzero_corner e hq' hp'
    ((q - v.final) * a * (p - v.initial)) ha
    (by rw [← mul_assoc, ← mul_assoc, hq'.isIdempotentElem.eq])
    (by rw [mul_assoc, hp'.isIdempotentElem.eq])
  have hi := HochschildCentralComparison.orthogonal_of_le_sub
    hp v.initial_proj w.initial_proj hvp hwp
  have hf := HochschildCentralComparison.orthogonal_of_le_sub
    hq v.final_proj w.final_proj hvq hwq
  have hs : v.orthogonalSum w hi hf ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial + w.initial ≤ v.initial + (p - v.initial) := add_le_add_right hwp _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final + w.final ≤ v.final + (q - v.final) := add_le_add_right hwq _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hi hf
  have he := le_antisymm (hmax.2 hs hle) hle
  have hvw : (v : M) + w = v := congrArg (fun z : PartialIso M => (z : M)) he
  exact hw0 (add_eq_left.mp hvw)

theorem trace_free_central_comparison (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ (z : M) (v : PartialIso M), CentralProjection z ∧ v.initial ≤ p ∧ v.final ≤ q ∧
      z * v.final = z * q ∧ (1 - z) * v.initial = (1 - z) * p := by
  obtain ⟨v, hvp, hvq, horth⟩ := exists_maximal_partialIso e hp hq
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  have horth' : ∀ a : M, (p - v.initial) * a * (q - v.final) = 0 := by
    intro a
    have h := congrArg star (horth (star a))
    simpa only [star_mul, star_star, star_zero, hp'.isSelfAdjoint.star_eq,
      hq'.isSelfAdjoint.star_eq, mul_assoc] using h
  obtain ⟨z, hz, hpz, hzq⟩ := exists_trace_free_central_separator e hp' hq' horth'
  have hzp : z * (p - v.initial) = p - v.initial :=
    (hp'.le_iff_mul_eq_right hz.1).mp hpz
  refine ⟨z, v, hz, hvp, hvq, ?_, ?_⟩
  · exact (sub_eq_zero.mp (by simpa only [mul_sub] using hzq)).symm
  · have h : (1 - z) * (p - v.initial) = 0 := by
      rw [sub_mul, one_mul, hzp, sub_self]
    exact (sub_eq_zero.mp (by simpa only [mul_sub] using h)).symm
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

open HochschildComparison FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def adjointPartialIso (v : PartialIso M) : PartialIso M :=
  ⟨star (v : M), by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star v.mul_star_mul⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma adjointPartialIso_initial (v : PartialIso M) :
    (adjointPartialIso v).initial = v.final := by simp [adjointPartialIso, PartialIso.initial, PartialIso.final]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma adjointPartialIso_final (v : PartialIso M) :
    (adjointPartialIso v).final = v.initial := by simp [adjointPartialIso, PartialIso.initial, PartialIso.final]

def centralCutPartialIso (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) : PartialIso M where
  val := z * (v : M)
  mul_star_mul := by
    have hstar : star (z * (v : M)) = z * star (v : M) := by
      rw [star_mul, hz.isSelfAdjoint.star_eq, hc]
    rw [hstar, central_idempotent_mul z hz.isIdempotentElem.eq hc,
      central_idempotent_mul z hz.isIdempotentElem.eq hc, v.mul_star_mul]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma centralCutPartialIso_initial (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) :
    (centralCutPartialIso z hz hc v).initial = z * v.initial := by
  change star (z * (v : M)) * (z * (v : M)) = z * (star (v : M) * v)
  rw [star_mul, hz.isSelfAdjoint.star_eq, ← hc (star (v : M)),
    central_idempotent_mul z hz.isIdempotentElem.eq hc]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma centralCutPartialIso_final (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) :
    (centralCutPartialIso z hz hc v).final = z * v.final := by
  change (z * (v : M)) * star (z * (v : M)) = z * ((v : M) * star (v : M))
  rw [star_mul, hz.isSelfAdjoint.star_eq, ← hc (star (v : M)),
    central_idempotent_mul z hz.isIdempotentElem.eq hc]

omit [PartialOrder M] [StarOrderedRing M] in

lemma finite_central_initial_iff_final (hfinite : FiniteAlgebra M)
    (z : M) (hz : IsStarProjection z) (hc : ∀ a : M, z * a = a * z)
    (v : PartialIso M) : z * v.initial = z ↔ z * v.final = z := by
  have forward (w : PartialIso M) (hi : z * w.initial = z) : z * w.final = z := by
    let a := centralCutPartialIso z hz hc w
    have hL : z * (a : M) = a := by
      change z * (z * (w : M)) = z * (w : M)
      rw [← mul_assoc, hz.isIdempotentElem.eq]
    have hR : (a : M) * z = a := by rw [← hc, hL]
    have hin : star (a : M) * a = z := by
      change a.initial = z
      change (centralCutPartialIso z hz hc w).initial = z
      rw [centralCutPartialIso_initial, hi]
    have hout := finiteCorner_of_finiteAlgebra hfinite z hz (a : M) hL hR hin
    change a.final = z at hout
    simpa only [a, centralCutPartialIso_final] using hout
  exact ⟨forward v, fun h => by simpa using forward (adjointPartialIso v) (by simpa using h)⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_partialIso_extends_unitary (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (v : PartialIso M) :
    ∃ u : unitary M, (u : M) * v.initial = v := by
  classical
  obtain ⟨z, w, hz, hwi, hwf, hzf, hzi⟩ := trace_free_central_comparison e
    v.initial_proj.one_sub v.final_proj.one_sub
  have hi : v.initial * w.initial = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement v.initial_proj w.initial_proj hwi
  have hf : v.final * w.final = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement v.final_proj w.final_proj hwf
  let t := v.orthogonalSum w hi hf
  have hti : t.initial = v.initial + w.initial := PartialIso.orthogonalSum_initial v w hi hf
  have htf : t.final = v.final + w.final := PartialIso.orthogonalSum_final v w hi hf
  have hzc : ∀ a : M, z * a = a * z := fun a => (hz.2 a).eq
  have hzc' : ∀ a : M, (1 - z) * a = a * (1 - z) := by
    intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hzc]
  have hzfinal : z * t.final = z := by
    rw [htf, mul_add, hzf, mul_sub, mul_one]
    abel
  have hczinitial : (1 - z) * t.initial = 1 - z := by
    rw [hti, mul_add, hzi, mul_sub, mul_one]
    abel
  have hzinitial := (finite_central_initial_iff_final hfinite z hz.1 hzc t).mpr hzfinal
  have hczfinal := (finite_central_initial_iff_final hfinite (1 - z) hz.1.one_sub hzc' t).mp hczinitial
  have hsplit (a : M) : z * a + (1 - z) * a = a := by noncomm_ring
  have htinitial : t.initial = 1 := by
    rw [← hsplit t.initial, hzinitial, hczinitial]
    abel
  have htfinal : t.final = 1 := by
    rw [← hsplit t.final, hzfinal, hczfinal]
    abel
  let u : unitary M := ⟨(t : M), by
    rw [Unitary.mem_iff]
    exact ⟨htinitial, htfinal⟩⟩
  refine ⟨u, ?_⟩
  change ((v : M) + (w : M)) * v.initial = v
  have hwv : (w : M) * v.initial = 0 := by
    calc
      (w : M) * v.initial = ((w : M) * w.initial) * v.initial := by rw [w.mul_initial]
      _ = 0 := by
        rw [mul_assoc]
        have hzero : w.initial * v.initial = 0 := by
          simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq,
            w.initial_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star hi
        rw [hzero, mul_zero]
  rw [add_mul, v.mul_initial, hwv, add_zero]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma partialIso_left_support {q : M} (hq : IsStarProjection q)
    (v : PartialIso M) (hv : v.final ≤ q) : q * (v : M) = v := by
  calc
    q * (v : M) = q * (v.final * (v : M)) := by rw [v.final_mul]
    _ = (v : M) := by
      rw [← mul_assoc, (v.final_proj.le_iff_mul_eq_right hq).mp hv, v.final_mul]

lemma partialIso_right_support {q : M} (hq : IsStarProjection q)
    (v : PartialIso M) (hv : v.initial ≤ q) : (v : M) * q = v := by
  calc
    (v : M) * q = ((v : M) * v.initial) * q := by rw [v.mul_initial]
    _ = (v : M) := by
      rw [mul_assoc, (v.initial_proj.le_iff_mul_eq_left hq).mp hv, v.mul_initial]

theorem finite_partialIso_extends_in_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (v : PartialIso M) (hi : v.initial ≤ q) (hf : v.final ≤ q) :
    ∃ u : M, q * u = u ∧ u * q = u ∧ star u * u = q ∧ u * star u = q ∧
      u * v.initial = v := by
  let vC : PartialIso (Corner q hq) :=
    ⟨⟨(v : M), partialIso_left_support hq v hf, partialIso_right_support hq v hi⟩,
      Subtype.ext v.mul_star_mul⟩
  obtain ⟨u, hu⟩ := finite_partialIso_extends_unitary (cornerPredualEquiv q hq e)
    ((finiteCorner_iff q hq).mp hfinite) vC
  refine ⟨((u : Corner q hq) : M), (u : Corner q hq).property.1,
    (u : Corner q hq).property.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val ((Unitary.mem_iff.mp u.property).1)
  · exact congrArg Subtype.val ((Unitary.mem_iff.mp u.property).2)
  · exact congrArg Subtype.val hu

theorem finite_partialIso_extension (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (v w : PartialIso M) (hvw : v.initial ≤ w.initial)
    (hvq : v.final ≤ q) (hwq : w.final ≤ q) :
    ∃ t : PartialIso M, v ≤ t ∧ t.initial = w.initial ∧ t.final ≤ q := by
  have hvp : (v : M) * w.initial = v := partialIso_right_support w.initial_proj v hvw
  have hqw : q * (w : M) = w := partialIso_left_support hq w hwq
  have hqv : q * (v : M) = v := partialIso_left_support hq v hvq
  let a : PartialIso M := ⟨(v : M) * star (w : M), by
    calc
      ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) *
          ((v : M) * star (w : M)) =
          ((v : M) * w.initial) * star (v : M) * (v : M) * star (w : M) := by
        simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
      _ = (v : M) * star (w : M) := by rw [hvp, v.mul_star_mul]⟩
  have haf : a.final = v.final := by
    change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = v.final
    simp only [star_mul, star_star]
    calc
      _ = ((v : M) * w.initial) * star (v : M) := by
        simp only [PartialIso.initial, mul_assoc]
      _ = v.final := by rw [hvp]; rfl
  have hai : a.initial = (w : M) * v.initial * star (w : M) := by
    simp only [a, PartialIso.initial, star_mul, star_star, mul_assoc]
  have haiq : a.initial ≤ q := by
    apply (a.initial_proj.le_iff_mul_eq_right hq).mpr
    rw [hai, ← mul_assoc, ← mul_assoc, hqw]
  obtain ⟨u, hqu, huq, huu, _, hua⟩ := finite_partialIso_extends_in_corner e hq
    hfinite a haiq (by rw [haf]; exact hvq)
  have huwi : u * (w : M) * v.initial = v := by
    have h := congrArg (fun b : M => b * (w : M)) hua
    rw [hai] at h
    change u * ((w : M) * v.initial * star (w : M)) * (w : M) =
      ((v : M) * star (w : M)) * (w : M) at h
    have hiv : v.initial * w.initial = v.initial :=
      (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp hvw
    calc
      u * (w : M) * v.initial =
          u * ((w : M) * v.initial * star (w : M)) * (w : M) := by
        simp only [mul_assoc]
        change u * ((w : M) * v.initial) =
          u * ((w : M) * (v.initial * w.initial))
        rw [hiv]
      _ = (v : M) := by
        rw [h]
        simpa only [PartialIso.initial, mul_assoc] using hvp
  have hti : star (u * (w : M)) * (u * (w : M)) = w.initial := by
    calc
      _ = star (w : M) * (star u * u) * (w : M) := by
        simp only [star_mul, mul_assoc]
      _ = w.initial := by rw [huu, mul_assoc, hqw]; rfl
  let t : PartialIso M := ⟨u * (w : M), by
    rw [mul_assoc, hti]
    change u * (w : M) * w.initial = u * (w : M)
    rw [mul_assoc, w.mul_initial]⟩
  refine ⟨t, ⟨?_, huwi⟩, hti, ?_⟩
  · change v.initial ≤ star (u * (w : M)) * (u * (w : M))
    rw [hti]
    exact hvw
  · apply (t.final_proj.le_iff_mul_eq_right hq).mpr
    change q * ((u * (w : M)) * star (u * (w : M))) = _
    rw [← mul_assoc, ← mul_assoc, hqu]
    rfl
end KadisonRingrose
end BoundedHochschild
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

theorem finite_increasing_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (p : ℕ → M) (hmono : Monotone p)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q) :
    ∃ v : PartialIso M, v.final ≤ q ∧ (∀ n, p n ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → v.initial ≤ r := by
  classical
  choose b hb using hembed
  let S (n : ℕ) := {v : PartialIso M // v.initial = p n ∧ v.final ≤ q}
  have hnext (n : ℕ) (v : S n) : ∃ w : S (n + 1), v.val ≤ w.val := by
    have hle : v.val.initial ≤ (b (n + 1)).initial := by
      rw [v.property.1, (hb (n + 1)).1]
      exact hmono (Nat.le_succ n)
    obtain ⟨w, hvw, hwi, hwf⟩ := finite_partialIso_extension e hq hfinite
      v.val (b (n + 1)) hle v.property.2 (hb (n + 1)).2
    exact ⟨⟨w, hwi.trans (hb (n + 1)).1, hwf⟩, hvw⟩
  choose step hstep using hnext
  let a : (n : ℕ) → S n := fun n => Nat.rec ⟨b 0, hb 0⟩ (fun n v => step n v) n
  let f : ℕ → PartialIso M := fun n => (a n).val
  have hfmono : Monotone f := monotone_nat_of_le_succ fun n => hstep n (a n)
  have hfi (n : ℕ) : (f n).initial = p n := (a n).property.1
  have hff (n : ℕ) : (f n).final ≤ q := (a n).property.2
  obtain ⟨v, hupper, _, hi, hf⟩ := exists_partialIso_chain_supremum e (Set.range f)
    hfmono.isChain_range (Set.range_nonempty f)
  refine ⟨v, hf q hq (by rintro _ ⟨n, rfl⟩; exact hff n), ?_, ?_⟩
  · intro n
    rw [← hfi n]
    exact (hupper _ ⟨n, rfl⟩).1
  · intro r hr hb
    apply hi r hr
    rintro _ ⟨n, rfl⟩
    rw [hfi n]
    exact hb n

theorem finite_subequivalence_at_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q s : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (hs : IsStarProjection s) (p : ℕ → M) (hmono : Monotone p)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q)
    (hupper : ∀ n, p n ≤ s)
    (hleast : ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → s ≤ r) :
    ∃ v : PartialIso M, v.initial = s ∧ v.final ≤ q := by
  obtain ⟨v, hvq, hvupper, hvleast⟩ := finite_increasing_subequivalence e hq hfinite
    p hmono hembed
  exact ⟨v, le_antisymm (hvleast s hs hupper)
    (hleast v.initial v.initial_proj hvupper), hvq⟩
end KadisonRingrose
end BoundedHochschild
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

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma partialIso_product_initial (v w : PartialIso M) (h : w.final ≤ v.initial) :
    star ((v : M) * w) * ((v : M) * w) = w.initial := by
  calc
    _ = star (w : M) * (v.initial * (w : M)) := by
      simp only [star_mul, PartialIso.initial, mul_assoc]
    _ = w.initial := by rw [partialIso_left_support v.initial_proj w h]; rfl

def composePartialIso (v w : PartialIso M) (h : w.final ≤ v.initial) : PartialIso M :=
  ⟨(v : M) * w, by
    rw [mul_assoc, partialIso_product_initial v w h, mul_assoc, w.mul_initial]⟩

@[simp] lemma composePartialIso_initial (v w : PartialIso M) (h : w.final ≤ v.initial) :
    (composePartialIso v w h).initial = w.initial := partialIso_product_initial v w h

lemma composePartialIso_final_le (v w : PartialIso M) (h : w.final ≤ v.initial) :
    (composePartialIso v w h).final ≤ v.final := by
  apply ((composePartialIso v w h).final_proj.le_iff_mul_eq_right v.final_proj).mpr
  change v.final * (((v : M) * w) * star ((v : M) * w)) = _
  rw [← mul_assoc, ← mul_assoc, v.final_mul]
  rfl

theorem finite_complement_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (v : PartialIso M)
    (hi : v.initial = p) (hf : v.final ≤ q) :
    ∃ w : PartialIso M, w.initial = 1 - q ∧ w.final ≤ 1 - p := by
  obtain ⟨u, hu⟩ := finite_partialIso_extends_unitary e hfinite v
  rw [hi] at hu
  have huunit : star (u : M) * u = 1 ∧ (u : M) * star (u : M) = 1 :=
    Unitary.mem_iff.mp u.property
  have hvq : q * (v : M) = v := partialIso_left_support hq v hf
  have hzero : (1 - q) * (u : M) * p = 0 := by
    rw [mul_assoc, hu, sub_mul, one_mul, hvq, sub_self]
  have hzero' : p * star (u : M) * (1 - q) = 0 := by
    simpa only [star_mul, star_sub, star_one, star_star, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, star_zero, mul_assoc] using congrArg star hzero
  let a := star (u : M) * (1 - q)
  have hai : star a * a = 1 - q := by
    dsimp [a]
    rw [star_mul, star_sub, star_one, hq.isSelfAdjoint.star_eq, star_star]
    calc
      _ = (1 - q) * ((u : M) * star (u : M)) * (1 - q) := by simp only [mul_assoc]
      _ = 1 - q := by rw [huunit.2, mul_one, hq.one_sub.isIdempotentElem.eq]
  have hap : a * (1 - q) = a := by
    dsimp [a]
    rw [mul_assoc, hq.one_sub.isIdempotentElem.eq]
  let w : PartialIso M := ⟨a, by rw [mul_assoc, hai, hap]⟩
  refine ⟨w, hai, ?_⟩
  have hpa : (1 - p) * a = a := by
    change (1 - p) * (star (u : M) * (1 - q)) = _
    rw [sub_mul, one_mul, ← mul_assoc, hzero', sub_zero]
  apply (w.final_proj.le_iff_mul_eq_right hp.one_sub).mpr
  change (1 - p) * (a * star a) = a * star a
  rw [← mul_assoc, hpa]
end KadisonRingrose
end BoundedHochschild
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

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_sum_range (q : ℕ → M)
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (n : ℕ) :
    IsStarProjection (∑ i ∈ Finset.range n, q i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      apply ih.add (hq n)
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      exact horth i n (Nat.ne_of_lt (Finset.mem_range.mp hi))

theorem projection_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p₁ p₂ q₁ q₂ : M} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (hq₁ : IsStarProjection q₁) (hq₂ : IsStarProjection q₂) (hqorth : q₁ * q₂ = 0)
    (a b : PartialIso M) (hai : a.initial = p₁) (haf : a.final ≤ q₁)
    (hbi : b.initial = p₂) (hbf : b.final ≤ q₂) :
    ∃ t : PartialIso M, t.final ≤ q₁ + q₂ ∧ p₁ ≤ t.initial ∧ p₂ ≤ t.initial ∧
      ∀ r : M, IsStarProjection r → p₁ ≤ r → p₂ ≤ r → t.initial ≤ r := by
  obtain ⟨v, hvi, horth, hj, hpj, hqj, hleast⟩ :=
    exists_trace_free_projection_join e p₁ p₂ hp₁ hp₂
  have hcomp : (adjointPartialIso v).final ≤ b.initial := by simpa [hbi] using hvi
  let c := composePartialIso b (adjointPartialIso v) hcomp
  have hci : c.initial = v.final := by simp [c]
  have hcf : c.final ≤ q₂ := (composePartialIso_final_le b _ hcomp).trans hbf
  have haci : a.initial * c.initial = 0 := by rw [hai, hci]; exact horth
  have hacf : a.final * c.final = 0 :=
    projection_orthogonal_mono a.final_proj c.final_proj hq₁ hq₂ haf hcf hqorth
  let t := a.orthogonalSum c haci hacf
  have hti : t.initial = p₁ + v.final := by
    rw [show t.initial = a.initial + c.initial from PartialIso.orthogonalSum_initial _ _ _ _,
      hai, hci]
  refine ⟨t, ?_, by rw [hti]; exact hpj, by rw [hti]; exact hqj, ?_⟩
  · rw [show t.final = a.final + c.final from PartialIso.orthogonalSum_final _ _ _ _]
    exact add_le_add haf hcf
  · intro r hr hpr hqr
    rw [hti]
    exact hleast r hr hpr hqr

theorem finite_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n)
    (n : ℕ) :
    ∃ v : PartialIso M, v.final ≤ ∑ i ∈ Finset.range n, q i ∧
      (∀ i < n, p i ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ i < n, p i ≤ r) → v.initial ≤ r := by
  classical
  induction n with
  | zero =>
      refine ⟨0, by simp, by simp, ?_⟩
      intro r hr _
      simpa using hr.nonneg
  | succ n ih =>
      obtain ⟨a, haf, hau, hal⟩ := ih
      obtain ⟨b, hbi, hbf⟩ := hembed n
      have hsum : IsStarProjection (∑ i ∈ Finset.range n, q i) := by
        exact orthogonal_projection_sum_range q hq horth n
      have hsumorth : (∑ i ∈ Finset.range n, q i) * q n = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        exact horth i n (Nat.ne_of_lt (Finset.mem_range.mp hi))
      obtain ⟨t, htf, hat, hpt, hleast⟩ := projection_join_subequivalence e
        a.initial_proj (hp n) hsum (hq n) hsumorth a b rfl haf hbi hbf
      refine ⟨t, ?_, ?_, ?_⟩
      · simpa only [Finset.sum_range_succ] using htf
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hin | rfl
        · exact (hau i hin).trans hat
        · exact hpt
      · intro r hr hpr
        exact hleast r hr (hal r hr (fun i hi => hpr i (Nat.lt_succ_of_lt hi)))
          (hpr n (Nat.lt_succ_self n))
end KadisonRingrose
end BoundedHochschild
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

theorem countable_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {Q : M} (hQ : IsStarProjection Q) (hfinite : FiniteCorner Q)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (hqQ : ∀ n, q n ≤ Q)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    ∃ v : PartialIso M, v.final ≤ Q ∧ (∀ n, p n ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → v.initial ≤ r := by
  classical
  choose a haf hau hal using finite_join_subequivalence e p q hp hq horth hembed
  have hsumQ (n : ℕ) : (∑ i ∈ Finset.range n, q i) ≤ Q := by
    apply ((orthogonal_projection_sum_range q hq horth n).le_iff_mul_eq_right hQ).mpr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hq i).le_iff_mul_eq_right hQ).mp (hqQ i)
  have ham : Monotone (fun n => (a n).initial) := monotone_nat_of_le_succ fun n => by
    apply hal n (a (n + 1)).initial (a (n + 1)).initial_proj
    intro i hi
    exact hau (n + 1) i (Nat.lt_succ_of_lt hi)
  have haQ (n : ℕ) : (a n).final ≤ Q := (haf n).trans (hsumQ n)
  obtain ⟨v, hvQ, hvupper, hvleast⟩ := finite_increasing_subequivalence e hQ hfinite
    (fun n => (a n).initial) ham (fun n => ⟨a n, rfl, haQ n⟩)
  refine ⟨v, hvQ, ?_, ?_⟩
  · intro n
    exact (hau (n + 1) n (Nat.lt_succ_self n)).trans (hvupper (n + 1))
  · intro r hr hpr
    apply hvleast r hr
    intro n
    exact hal n r hr (fun i _ => hpr i)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_orthogonal_projection_tails (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) :
    ∃ T : ℕ → M, (∀ n, IsStarProjection (T n)) ∧ Antitone T ∧
      (∀ n i, n ≤ i → q i ≤ T n) ∧ PredualTendsto e T atTop 0 := by
  let s (n : ℕ) : M := ∑ i ∈ Finset.range n, q i
  have hs (n : ℕ) : IsStarProjection (s n) := orthogonal_projection_sum_range q hq horth n
  have hsm : Monotone s := monotone_nat_of_le_succ fun n => by
    dsimp [s]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hq n).nonneg
  obtain ⟨Q, hQ, hlub, ht⟩ := exists_increasing_projection_limit e s hs hsm
  have hsQ (n : ℕ) : s n ≤ Q := hlub.1 ⟨n, rfl⟩
  have hqQ (i : ℕ) : q i ≤ Q := by
    apply le_trans _ (hsQ (i + 1))
    dsimp [s]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => (hq j).nonneg)
  refine ⟨fun n => Q - s n, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ((hs n).le_iff_sub hQ).mp (hsQ n)
  · intro i j hij
    exact sub_le_sub_left (hsm hij) Q
  · intro n i hni
    have hTail : IsStarProjection (Q - s n) := ((hs n).le_iff_sub hQ).mp (hsQ n)
    apply ((hq i).le_iff_mul_eq_right hTail).mpr
    rw [sub_mul, ((hq i).le_iff_mul_eq_right hQ).mp (hqQ i)]
    have hzero : s n * q i = 0 := by
      dsimp [s]
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth j i (Nat.ne_of_lt ((Finset.mem_range.mp hj).trans_le hni))
    rw [hzero, sub_zero]
  · simpa only [sub_self] using
      predual_tendsto_sub e (predual_tendsto_const e Q atTop) ht
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_subequivalent_orthogonal_tails (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (p q : ℕ → M)
    (hp : ∀ n, IsStarProjection (p n)) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    ∃ R : ℕ → M, (∀ n, IsStarProjection (R n)) ∧ Antitone R ∧
      (∀ n, p n ≤ R n) ∧ PredualTendsto e R atTop 0 := by
  classical
  obtain ⟨T, hT, hTm, hTq, hTlim⟩ := exists_orthogonal_projection_tails e q hq horth
  have hjoins (n : ℕ) : ∃ v : PartialIso M, v.final ≤ T n ∧
      (∀ i, p (n + i) ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ i, p (n + i) ≤ r) → v.initial ≤ r := by
    apply countable_join_subequivalence e (hT n)
      (finiteCorner_of_finiteAlgebra hfinite _ (hT n))
      (fun i => p (n + i)) (fun i => q (n + i))
      (fun i => hp (n + i)) (fun i => hq (n + i))
    · intro i j hij
      exact horth _ _ (fun h => hij (Nat.add_left_cancel h))
    · intro i
      exact hTq n (n + i) (Nat.le_add_right n i)
    · intro i
      exact hembed (n + i)
  choose v hvf hvu hvl using hjoins
  let R (n : ℕ) : M := (v n).initial
  have hR (n : ℕ) : IsStarProjection (R n) := (v n).initial_proj
  have hRm : Antitone R := antitone_nat_of_succ_le fun n => by
    apply hvl (n + 1) (R n) (hR n)
    intro i
    simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hvu n (i + 1)
  obtain ⟨s, hs, hglb, hRlim⟩ := exists_decreasing_projection_limit e R hR hRm
  have hsR (n : ℕ) : s ≤ (v n).initial := hglb.1 ⟨n, rfl⟩
  have hembedS (n : ℕ) : ∃ w : PartialIso M, w.initial = s ∧ w.final ≤ T n := by
    let w := (v n).restrict hs (hsR n)
    exact ⟨w, PartialIso.restrict_initial _ _ _,
      (PartialIso.final_mono (PartialIso.restrict_le _ _ _)).trans (hvf n)⟩
  have hcomp (n : ℕ) : ∃ w : PartialIso M, w.initial = 1 - T n ∧ w.final ≤ 1 - s := by
    obtain ⟨w, hwi, hwf⟩ := hembedS n
    exact finite_complement_subequivalence e hfinite hs (hT n) w hwi hwf
  have hcomplim : PredualTendsto e (fun n => 1 - T n) atTop 1 := by
    simpa only [sub_zero] using predual_tendsto_sub e
      (predual_tendsto_const e 1 atTop) hTlim
  have hcomleast (r : M) (_hr : IsStarProjection r)
      (hb : ∀ n, 1 - T n ≤ r) : (1 : M) ≤ r := by
    apply HochschildSakai.le_of_bounded_predual_limit e 1 zero_le_one
      (Eventually.of_forall fun n => (hT n).one_sub.norm_le _) ?_ hcomplim
    exact Eventually.of_forall hb
  obtain ⟨w, hwi, hwf⟩ := finite_subequivalence_at_supremum e hs.one_sub
    (finiteCorner_of_finiteAlgebra hfinite _ hs.one_sub) (IsStarProjection.one M)
    (fun n => 1 - T n) (fun i j hij => sub_le_sub_left (hTm hij) 1) hcomp
    (fun n => (hT n).one_sub.le_one) hcomleast
  have hwfull : w.final = 1 := hfinite (w : M) hwi
  have hs0 : s = 0 := by
    rw [hwfull] at hwf
    exact sub_eq_self.mp (le_antisymm hs.one_sub.le_one hwf)
  refine ⟨R, hR, hRm, ?_, ?_⟩
  · intro n
    simpa only [Nat.add_zero] using hvu n 0
  · simpa only [hs0] using hRlim
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

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normal_positive_subequivalent_tendsto_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    Tendsto (fun n => ψ (p n)) atTop (𝓝 0) := by
  obtain ⟨R, _, _, hle, ht⟩ := finite_subequivalent_orthogonal_tails e hfinite p q
    hp hq horth hembed
  have hRt : Tendsto (fun n => ‖ψ (R n)‖) atTop (𝓝 0) := by
    simpa only [map_zero, norm_zero] using (trace_predual_tendsto e ψ hψ ht).norm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hRt
  exact Compat.norm_le_norm_of_le_of_nonneg (ψ.monotone (hle n))
    (ψ.map_nonneg (hp n).nonneg)

theorem normal_positive_unitary_orbit_tendsto_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (u : ℕ → unitary M) :
    Tendsto (fun n => ψ ((u n : M) * q n * star (u n : M))) atTop (𝓝 0) := by
  let w (n : ℕ) : PartialIso M := ⟨(u n : M) * q n, by
    have hu := (Unitary.mem_iff.mp (u n).property).1
    simp only [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      ((u n : M) * q n) * (q n * star (u n : M)) * ((u n : M) * q n) =
          (u n : M) * (q n * q n) * (star (u n : M) * (u n : M)) * q n := by
        simp only [mul_assoc]
      _ = (u n : M) * q n := by
        rw [(hq n).isIdempotentElem.eq, hu, mul_one, mul_assoc,
          (hq n).isIdempotentElem.eq]⟩
  have hwi (n : ℕ) : (w n).initial = q n := by
    change star ((u n : M) * q n) * ((u n : M) * q n) = q n
    rw [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      _ = q n * (star (u n : M) * (u n : M)) * q n := by simp only [mul_assoc]
      _ = q n := by rw [(Unitary.mem_iff.mp (u n).property).1, mul_one,
        (hq n).isIdempotentElem.eq]
  have hwf (n : ℕ) : (w n).final = (u n : M) * q n * star (u n : M) := by
    change ((u n : M) * q n) * star ((u n : M) * q n) = _
    rw [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      _ = (u n : M) * (q n * q n) * star (u n : M) := by simp only [mul_assoc]
      _ = _ := by rw [(hq n).isIdempotentElem.eq]
  have ht := normal_positive_subequivalent_tendsto_zero e hfinite ψ hψ
    (fun n => (w n).final) q (fun n => (w n).final_proj) hq horth
    (fun n => ⟨adjointPartialIso (w n), by simp, by simp [hwi]⟩)
  simpa only [hwf] using ht

theorem normal_positive_uniform_unitary_orbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u : unitary M, ‖ψ ((u : M) * q n * star (u : M))‖ < ε := by
  classical
  let u (n : ℕ) : unitary M := if h : ∃ v : unitary M,
      ε ≤ ‖ψ ((v : M) * q n * star (v : M))‖ then h.choose else 1
  have ht := normal_positive_unitary_orbit_tendsto_zero e hfinite ψ hψ q hq horth u
  have hlt : ∀ᶠ n in atTop, ‖ψ ((u n : M) * q n * star (u n : M))‖ < ε :=
    (tendsto_order.1 (by simpa only [norm_zero] using ht.norm)).2 ε hε
  filter_upwards [hlt] with n hn v
  by_contra hv
  have hex : ∃ v : unitary M, ε ≤ ‖ψ ((v : M) * q n * star (v : M))‖ :=
    ⟨v, le_of_not_gt hv⟩
  have hu : ε ≤ ‖ψ ((u n : M) * q n * star (u n : M))‖ := by
    simpa only [u, dite_eq_left hex] using hex.choose_spec
  exact (not_le_of_gt hn) hu
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

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_eval_bound (F : StrongDual ℂ M) (a : M) (C : ℝ)
    (hbound : ∀ u : unitary M, ‖unitaryPullback F u a‖ ≤ C) :
    ∀ G ∈ unitaryOrbitHull F, ‖G a‖ ≤ C := by
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback F)) ⊆
      E ⁻¹' Metric.closedBall 0 C := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, E, ContinuousLinearMap.apply_apply] using hbound u
    · exact (convex_closedBall (0 : ℂ) C).linear_preimage (E.restrictScalars ℝ).toLinearMap
  have hh := closure_minimal hc (Metric.isClosed_closedBall.preimage E.continuous)
  intro G hG
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, E, ContinuousLinearMap.apply_apply] using hh hG

theorem normal_positive_uniform_orbit_hull (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ G ∈ unitaryOrbitHull (positiveFunctionalCLM ψ), ‖G (q n)‖ < ε := by
  have heps : 0 < ε / 2 := half_pos hε
  filter_upwards [normal_positive_uniform_unitary_orbit e hfinite ψ hψ q hq horth
    (ε / 2) heps] with n hn G hG
  exact (unitaryOrbitHull_eval_bound (positiveFunctionalCLM ψ) (q n) (ε / 2)
    (fun u => (hn u).le) G hG).trans_lt (half_lt_self hε)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.normal_positive_uniform_orbit_hull.{u} := @OAI.BoundedHochschild.KadisonRingrose.normal_positive_uniform_orbit_hull.{u}
