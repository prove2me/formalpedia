-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.exists_countable_isometries
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:47:32.841954+00:00
-- url     : https://prove2.me/submissions/77f97963-4718-40b3-a163-e58c0263005c

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

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_projection_coe {q : Corner p hp} (hq : IsStarProjection q) :
    IsStarProjection (q:M) := ⟨congrArg (fun a : Corner p hp => (a:M)) hq.isIdempotentElem.eq,
      congrArg (fun a : Corner p hp => (a:M)) hq.isSelfAdjoint.star_eq⟩

lemma corner_projection_le {q : Corner p hp} (hq : IsStarProjection q) : (q:M) ≤ p :=
  ((corner_projection_coe p hp hq).le_iff_mul_eq_left hp).mpr q.property.2
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

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_trans {p : M} (hp : IsStarProjection p)
    (q : HochschildCorners.Corner p hp) (hfinite : FiniteCorner q) :
    FiniteCorner (q : M) := by
  intro a hL hR haa
  have hpL : p * a = a := by
    calc
      p * a = p * ((q : M) * a) := by rw [hL]
      _ = a := by rw [← mul_assoc, q.property.1, hL]
  have hpR : a * p = a := by
    calc
      a * p = (a * (q : M)) * p := by rw [hR]
      _ = a := by rw [mul_assoc, q.property.2, hR]
  let b : HochschildCorners.Corner p hp := ⟨a, hpL, hpR⟩
  exact congrArg Subtype.val
    (hfinite b (Subtype.ext hL) (Subtype.ext hR) (Subtype.ext haa))

lemma finiteCorner_mono {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p ≤ q) (hfinite : FiniteCorner q) :
    FiniteCorner p := by
  let pC : HochschildCorners.Corner q hq :=
    ⟨p, (hp.le_iff_mul_eq_right hq).mp hpq, (hp.le_iff_mul_eq_left hq).mp hpq⟩
  have hpC : IsStarProjection pC :=
    ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩
  exact finiteCorner_trans hq pC
    (finiteCorner_of_finiteAlgebra ((finiteCorner_iff q hq).mp hfinite) pC hpC)
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

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v}

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_finset_sum (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (s : Finset I) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply (hp i).add ih
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j (fun hij => his (hij ▸ hj))

theorem exists_orthogonal_projection_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) :
    ∃ P : M, IsStarProjection P ∧ (∀ i, p i ≤ P) ∧
      (∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r) ∧
      PredualTendsto e (fun s : Finset I => ∑ i ∈ s, p i) atTop P := by
  classical
  let f (s : Finset I) : M := ∑ i ∈ s, p i
  have hf (s : Finset I) : IsStarProjection (f s) := orthogonal_projection_finset_sum p hp horth s
  have hfm : Monotone f := by
    intro s t hst
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (hp i).nonneg)
  obtain ⟨P, _, hlub, ht⟩ := HochschildSakai.exists_monotone_predual_limit e f hfm
    1 zero_le_one (fun s => (hf s).norm_le _)
  have hfixed (s : Finset I) : f s * P = f s := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (f s) ht
    have heq : (fun t => f s * f t) =ᶠ[atTop] (fun _ => f s) := by
      filter_upwards [eventually_ge_atTop s] with t hst
      exact ((hf s).le_iff_mul_eq_left (hf t)).mp (hfm hst)
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a x) h.symm)
  have hP : IsStarProjection P := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e P ht
      have heq : (fun s => f s * P) = f := funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hm := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun s => star (f s)) = f := funext fun s => (hf s).isSelfAdjoint.star_eq
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
  refine ⟨P, hP, ?_, ?_, ht⟩
  · intro i
    have h := hlub.1 (Set.mem_range_self ({i} : Finset I))
    simpa only [f, Finset.sum_singleton] using h
  · intro r hr hpr
    apply hlub.2
    rintro _ ⟨s, rfl⟩
    apply ((hf s).le_iff_mul_eq_right hr).mpr
    change r * (∑ i ∈ s, p i) = ∑ i ∈ s, p i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hp i).le_iff_mul_eq_right hr).mp (hpr i)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*}

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIso_finset_sum_data (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) :
    ∃ w : PartialIso M, (w : M) = ∑ i ∈ s, (v i : M) ∧
      w.initial = ∑ i ∈ s, (v i).initial ∧ w.final = ∑ i ∈ s, (v i).final := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | @insert i s his ih =>
      obtain ⟨w, hw, hwi, hwf⟩ := ih
      have hI : (v i).initial * w.initial = 0 := by
        rw [hwi, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hi i j (fun h => his (h ▸ hj)))
      have hF : (v i).final * w.final = 0 := by
        rw [hwf, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hf i j (fun h => his (h ▸ hj)))
      refine ⟨(v i).orthogonalSum w hI hF, ?_, ?_, ?_⟩
      · change (v i : M) + (w : M) = _
        rw [hw, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_initial, hwi, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_final, hwf, Finset.sum_insert his]

def partialIsoFinsetSum (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) : PartialIso M :=
  (partialIso_finset_sum_data v hi hf s).choose

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_coe (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s : M) = ∑ i ∈ s, (v i : M) :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_initial (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).initial = ∑ i ∈ s, (v i).initial :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_final (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).final = ∑ i ∈ s, (v i).final :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.2

lemma partialIsoFinsetSum_mono (v : I → PartialIso M) (hi hf)
    {s t : Finset I} (hst : s ⊆ t) :
    partialIsoFinsetSum v hi hf s ≤ partialIsoFinsetSum v hi hf t := by
  classical
  constructor
  · rw [partialIsoFinsetSum_initial, partialIsoFinsetSum_initial]
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (v i).initial_proj.nonneg)
  · rw [partialIsoFinsetSum_coe, partialIsoFinsetSum_initial, Finset.mul_sum,
      partialIsoFinsetSum_coe]
    apply Finset.sum_congr rfl
    intro i his
    rw [Finset.sum_mul]
    calc
      _ = (v i : M) * (v i).initial := Finset.sum_eq_single i (fun j _ hji => ?_)
        (fun hit => (hit (hst his)).elim)
      _ = (v i : M) := (v i).mul_initial
    calc
        (v j : M) * (v i).initial = ((v j : M) * (v j).initial) * (v i).initial := by
          rw [(v j).mul_initial]
        _ = 0 := by rw [mul_assoc, hi j i hji, mul_zero]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_countable_partialIso_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (v : ℕ → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    ∃ w : PartialIso M, (∀ i, (v i).initial ≤ w.initial) ∧
      (∀ i, (v i).final ≤ w.final) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).initial ≤ p) → w.initial ≤ p) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).final ≤ p) → w.final ≤ p) := by
  classical
  let V (n : ℕ) := partialIsoFinsetSum v hi hf (Finset.range n)
  have hm : Monotone V := fun _ _ h => partialIsoFinsetSum_mono v hi hf (Finset.range_mono h)
  have hc : IsChain (· ≤ ·) (Set.range V) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact (le_total i j).imp (fun h => hm h) (fun h => hm h)
  obtain ⟨w, hw, _, hwi, hwf⟩ := exists_partialIso_chain_supremum e (Set.range V) hc
    ⟨V 0, Set.mem_range_self 0⟩
  have hsumI (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).initial ≤ p) (n : ℕ) :
      (V n).initial ≤ p := by
    apply ((V n).initial_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_initial, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).initial_proj.le_iff_mul_eq_right hp).mp (h i))
  have hsumF (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).final ≤ p) (n : ℕ) :
      (V n).final ≤ p := by
    apply ((V n).final_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_final, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).final_proj.le_iff_mul_eq_right hp).mp (h i))
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i
    apply le_trans _ (hw (V (i + 1)) (Set.mem_range_self _)).1
    rw [partialIsoFinsetSum_initial]
    exact Finset.single_le_sum (fun j _ => (v j).initial_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro i
    apply le_trans _ (PartialIso.final_mono (hw (V (i + 1)) (Set.mem_range_self _)))
    rw [partialIsoFinsetSum_final]
    exact Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro p hp h
    apply hwi p hp
    rintro _ ⟨n, rfl⟩
    exact hsumI p hp h n
  · intro p hp h
    apply hwf p hp
    rintro _ ⟨n, rfl⟩
    exact hsumF p hp h n
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

lemma isometry_pow_initial {v : M} (hv : star v * v = 1) (n : ℕ) :
    star (v ^ n) * v ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, star_mul]
      calc
        _ = star v * (star (v ^ n) * v ^ n) * v := by simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hv]

lemma isometry_pow_cancel {v : M} (hv : star v * v = 1) (n k : ℕ) :
    star (v ^ n) * v ^ (n + k) = v ^ k := by
  rw [pow_add, ← mul_assoc, isometry_pow_initial hv, one_mul]

def isometryDefect (v : M) : M := 1 - v * star v

lemma isometryDefect_projection {v : M} (hv : star v * v = 1) :
    IsStarProjection (isometryDefect v) := by
  apply IsStarProjection.one_sub
  refine ⟨?_, IsSelfAdjoint.mul_star_self v⟩
  calc
    (v * star v) * (v * star v) = v * (star v * v) * star v := by simp only [mul_assoc]
    _ = v * star v := by rw [hv, mul_one]

lemma isometryDefect_mul {v : M} (hv : star v * v = 1) :
    isometryDefect v * v = 0 := by
  rw [isometryDefect, sub_mul, one_mul, mul_assoc, hv, mul_one, sub_self]

lemma isometry_column_initial {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (n : ℕ) :
    star (v ^ n * p) * (v ^ n * p) = p := by
  rw [star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = p * (star (v ^ n) * v ^ n) * p := by simp only [mul_assoc]
    _ = p := by rw [isometry_pow_initial hv, mul_one, hp.isIdempotentElem.eq]

def isometryColumn (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) : PartialIso M :=
  ⟨v ^ n * p, by
    rw [mul_assoc, isometry_column_initial hv hp, mul_assoc, hp.isIdempotentElem.eq]⟩

@[simp] lemma isometryColumn_initial (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) :
    (isometryColumn v hv p hp n).initial = p := isometry_column_initial hv hp n

@[simp] lemma isometryColumn_coe (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) :
    (isometryColumn v hv p hp n : M) = v ^ n * p := rfl

lemma isometryColumn_star_mul_of_lt {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i < j) :
    star (isometryColumn v hv p hp i : M) * (isometryColumn v hv p hp j : M) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hpk : p * v ^ (k + 1) = 0 := by
    rw [pow_succ', ← mul_assoc, hpv, zero_mul]
  simp only [isometryColumn_coe, star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = p * (star (v ^ i) * v ^ (i + (k + 1))) * p := by
      simp only [mul_assoc, Nat.add_assoc]
    _ = 0 := by rw [isometry_pow_cancel hv, hpk, zero_mul]

lemma isometryColumn_star_mul_of_ne {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i ≠ j) :
    star (isometryColumn v hv p hp i : M) * (isometryColumn v hv p hp j : M) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact isometryColumn_star_mul_of_lt hv hp hpv h
  · simpa only [star_mul, star_star, star_zero] using
      congrArg star (isometryColumn_star_mul_of_lt hv hp hpv h)

lemma isometryColumn_final_orthogonal {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i ≠ j) :
    (isometryColumn v hv p hp i).final * (isometryColumn v hv p hp j).final = 0 := by
  change (((isometryColumn v hv p hp i : M) * star (isometryColumn v hv p hp i : M)) *
    ((isometryColumn v hv p hp j : M) * star (isometryColumn v hv p hp j : M))) = 0
  rw [mul_assoc, ← mul_assoc (star (isometryColumn v hv p hp i : M)),
    isometryColumn_star_mul_of_ne hv hp hpv hij, zero_mul, mul_zero]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def ProperlyInfiniteProjection (p : M) : Prop :=
  ∃ v w : PartialIso M, v.initial = p ∧ w.initial = p ∧
    v.final ≤ p ∧ w.final ≤ p ∧ v.final * w.final = 0

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_transition_initial (v w : PartialIso M) (h : v.initial = w.initial) :
    star ((v : M) * star (w : M)) * ((v : M) * star (w : M)) = w.final := by
  calc
    _ = (w : M) * v.initial * star (w : M) := by
      simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
    _ = w.final := by rw [h, w.mul_initial]; rfl

def columnTransition (v w : PartialIso M) (h : v.initial = w.initial) : PartialIso M :=
  ⟨(v : M) * star (w : M), by
    rw [mul_assoc, column_transition_initial v w h]
    have hw : star (w : M) * w.final = star (w : M) := by
      simpa only [star_mul, star_star, w.final_proj.isSelfAdjoint.star_eq] using
        congrArg star w.final_mul
    rw [mul_assoc, hw]⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_initial (v w : PartialIso M) (h) :
    (columnTransition v w h).initial = w.final := column_transition_initial v w h

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_final (v w : PartialIso M) (h) :
    (columnTransition v w h).final = v.final := by
  change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = _
  rw [star_mul, star_star]
  calc
    _ = (v : M) * w.initial * star (v : M) := by simp only [PartialIso.initial, mul_assoc]
    _ = v.final := by rw [← h, v.mul_initial]; rfl

lemma projection_le_complement_of_mul_zero {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) : p ≤ 1 - q := by
  apply (hp.le_iff_mul_eq_left hq.one_sub).mpr
  rw [mul_sub, mul_one, hpq, sub_zero]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem properlyInfinite_of_columns (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = p)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) :
    ∃ q : M, IsStarProjection q ∧ ProperlyInfiniteProjection q ∧
      (∀ i, (c i).final ≤ q) ∧
      (∀ r : M, IsStarProjection r → (∀ i, (c i).final ≤ r) → q ≤ r) := by
  obtain ⟨q, hq, hqi, hqmin, _⟩ := exists_orthogonal_projection_sum e
    (fun i => (c i).final) (fun i => (c i).final_proj) ho
  let a (i : ℕ) := columnTransition (c (2 * i)) (c i) ((hi _).trans (hi _).symm)
  let b (i : ℕ) := columnTransition (c (2 * i + 1)) (c i) ((hi _).trans (hi _).symm)
  have hai (i) : (a i).initial = (c i).final := columnTransition_initial ..
  have hbi (i) : (b i).initial = (c i).final := columnTransition_initial ..
  have haf (i) : (a i).final = (c (2 * i)).final := columnTransition_final ..
  have hbf (i) : (b i).final = (c (2 * i + 1)).final := columnTransition_final ..
  obtain ⟨v, hvi, _, hvi_min, hvf_min⟩ := exists_countable_partialIso_sum e a
    (fun i j hij => by rw [hai, hai]; exact ho i j hij)
    (fun i j hij => by rw [haf, haf]; exact ho _ _ (by omega))
  obtain ⟨w, hwi, _, hwi_min, hwf_min⟩ := exists_countable_partialIso_sum e b
    (fun i j hij => by rw [hbi, hbi]; exact ho i j hij)
    (fun i j hij => by rw [hbf, hbf]; exact ho _ _ (by omega))
  have hvq : v.initial = q := le_antisymm
    (hvi_min q hq (fun i => by rw [hai]; exact hqi i))
    (hqmin _ v.initial_proj (fun i => by rw [← hai]; exact hvi i))
  have hwq : w.initial = q := le_antisymm
    (hwi_min q hq (fun i => by rw [hbi]; exact hqi i))
    (hqmin _ w.initial_proj (fun i => by rw [← hbi]; exact hwi i))
  refine ⟨q, hq, ⟨v, w, hvq, hwq,
    hvf_min q hq (fun i => by rw [haf]; exact hqi _),
    hwf_min q hq (fun i => by rw [hbf]; exact hqi _), ?_⟩, hqi, hqmin⟩
  have hw_even (i : ℕ) : w.final ≤ 1 - (a i).final := by
    apply hwf_min _ (a i).final_proj.one_sub
    intro j
    apply projection_le_complement_of_mul_zero (b j).final_proj (a i).final_proj
    rw [hbf, haf]
    exact ho _ _ (by omega)
  have hav (i : ℕ) : (a i).final ≤ 1 - w.final := by
    apply projection_le_complement_of_mul_zero (a i).final_proj w.final_proj
    exact HochschildTypeII.projection_orthogonal_of_le_complement (a i).final_proj
      w.final_proj (hw_even i)
  have h := HochschildTypeII.projection_orthogonal_of_le_complement w.final_proj
    v.final_proj (hvf_min _ w.final_proj.one_sub hav)
  simpa only [star_mul, v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h

theorem nonunitary_isometry_has_properlyInfinite_projection
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {v : M} (hv : star v * v = 1)
    (hnot : v * star v ≠ 1) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ ProperlyInfiniteProjection q := by
  let p := isometryDefect v
  have hp : IsStarProjection p := isometryDefect_projection hv
  let c := isometryColumn v hv p hp
  obtain ⟨q, hq, hproper, hqi, _⟩ := properlyInfinite_of_columns e c
    (fun i => isometryColumn_initial ..)
    (fun i j hij => isometryColumn_final_orthogonal hv hp (isometryDefect_mul hv) hij)
  refine ⟨q, hq, ?_, hproper⟩
  intro hq0
  have hp0 : p = 0 := by
    have h : p ≤ q := by
      simpa only [c, isometryColumn, PartialIso.final, pow_zero, one_mul,
        hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using hqi 0
    exact le_antisymm (hq0 ▸ h) hp.nonneg
  exact hnot (sub_eq_zero.mp hp0).symm
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def partialIsoCornerEquiv (v : PartialIso M) :
    PopaCorner.algebra v.initial_proj ≃⋆ₐ[ℂ] PopaCorner.algebra v.final_proj where
  toFun a := ⟨(v : M) * (a : M) * star (v : M), by
    constructor
    · rw [← mul_assoc, ← mul_assoc, v.final_mul]
    · have hs : star (v : M) * v.final = star (v : M) := by
        simpa only [star_mul, star_star, v.final_proj.isSelfAdjoint.star_eq] using
          congrArg star v.final_mul
      change ((v : M) * (a : M) * star (v : M)) * v.final = _
      rw [mul_assoc, hs]⟩
  invFun b := ⟨star (v : M) * (b : M) * (v : M), by
    constructor
    · have hs : v.initial * star (v : M) = star (v : M) := by
        simpa only [star_mul, star_star, v.initial_proj.isSelfAdjoint.star_eq] using
          congrArg star v.mul_initial
      change v.initial * (star (v : M) * (b : M) * (v : M)) = _
      rw [← mul_assoc, ← mul_assoc, hs]
    · rw [mul_assoc, v.mul_initial]⟩
  left_inv a := by
    apply Subtype.ext
    change star (v : M) * ((v : M) * (a : M) * star (v : M)) * (v : M) = (a : M)
    calc
      _ = v.initial * (a : M) * v.initial := by simp only [PartialIso.initial, mul_assoc]
      _ = (a : M) := by rw [a.property.1, a.property.2]
  right_inv b := by
    apply Subtype.ext
    change (v : M) * (star (v : M) * (b : M) * (v : M)) * star (v : M) = (b : M)
    calc
      _ = v.final * (b : M) * v.final := by simp only [PartialIso.final, mul_assoc]
      _ = (b : M) := by rw [b.property.1, b.property.2]
  map_add' a b := by
    apply Subtype.ext
    change (v : M) * ((a : M) + (b : M)) * star (v : M) =
      (v : M) * (a : M) * star (v : M) + (v : M) * (b : M) * star (v : M)
    simp only [mul_add, add_mul]
  map_mul' a b := by
    apply Subtype.ext
    change (v : M) * ((a : M) * (b : M)) * star (v : M) =
      ((v : M) * (a : M) * star (v : M)) * ((v : M) * (b : M) * star (v : M))
    symm
    calc
      _ = (v : M) * ((a : M) * v.initial * (b : M)) * star (v : M) := by
        simp only [PartialIso.initial, mul_assoc]
      _ = _ := by rw [a.property.2]
  map_smul' c a := by
    apply Subtype.ext
    change (v : M) * (c • (a : M)) * star (v : M) =
      c • ((v : M) * (a : M) * star (v : M))
    simp only [mul_smul_comm, smul_mul_assoc]
  map_star' a := by
    apply Subtype.ext
    change (v : M) * star (a : M) * star (v : M) =
      star ((v : M) * (a : M) * star (v : M))
    simp only [star_mul, star_star, mul_assoc]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoCornerEquiv_apply (v : PartialIso M)
    (a : PopaCorner.algebra v.initial_proj) :
    (partialIsoCornerEquiv v a : M) = (v : M) * (a : M) * star (v : M) := rfl
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildCorners FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def partialIsoFromCorner {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) : PartialIso M :=
  ⟨((v : Corner p hp) : M), congrArg Subtype.val v.mul_star_mul⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoFromCorner_initial {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) :
    (partialIsoFromCorner hp v).initial = ((v.initial : Corner p hp) : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoFromCorner_final {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) :
    (partialIsoFromCorner hp v).final = ((v.final : Corner p hp) : M) := rfl

omit [StarOrderedRing M] in
lemma properlyInfinite_from_corner {p : M} (hp : IsStarProjection p)
    {q : Corner p hp} (h : ProperlyInfiniteProjection q) : ProperlyInfiniteProjection (q : M) := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := h
  exact ⟨partialIsoFromCorner hp v, partialIsoFromCorner hp w,
    congrArg Subtype.val hvi, congrArg Subtype.val hwi,
    hvf, hwf, congrArg Subtype.val ho⟩

lemma properlyInfinite_finite_eq_zero {p : M} (hp : IsStarProjection p)
    (hproper : ProperlyInfiniteProjection p) (hfinite : FiniteCorner p) : p = 0 := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := hproper
  have hv : v.final = p := hfinite (v : M) (partialIso_left_support hp v hvf)
    (partialIso_right_support hp v (hvi ▸ le_rfl)) hvi
  have hw : w.final = p := hfinite (w : M) (partialIso_left_support hp w hwf)
    (partialIso_right_support hp w (hwi ▸ le_rfl)) hwi
  rw [hv, hw, hp.isIdempotentElem.eq] at ho
  exact ho

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteAlgebra_of_equiv {N : Type*} [CStarAlgebra N]
    (φ : M ≃⋆ₐ[ℂ] N) (h : FiniteAlgebra N) : FiniteAlgebra M := by
  intro a ha
  apply φ.injective
  change φ (a * star a) = φ 1
  rw [map_mul, map_star, map_one]
  exact h (φ a) (by rw [← map_star, ← map_mul, ha, map_one])

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_of_equivalent (v : PartialIso M) (h : FiniteCorner v.final) :
    FiniteCorner v.initial := by
  apply (finiteCorner_iff v.initial v.initial_proj).mpr
  exact finiteAlgebra_of_equiv (partialIsoCornerEquiv v)
    ((finiteCorner_iff v.final v.final_proj).mp h)

lemma properlyInfinite_central_cut {p z : M} (hp : IsStarProjection p)
    (hz : CentralProjection z) (h : ProperlyInfiniteProjection p) :
    ProperlyInfiniteProjection (z * p) := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := h
  let v' := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) v
  let w' := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) w
  have hzp : IsStarProjection (z * p) := hz.1.mul hp (hz.2 p)
  have hvle : v'.final ≤ z * p := by
    apply (v'.final_proj.le_iff_mul_eq_left hzp).mpr
    rw [centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      (v.final_proj.le_iff_mul_eq_left hp).mp hvf]
  have hwle : w'.final ≤ z * p := by
    apply (w'.final_proj.le_iff_mul_eq_left hzp).mpr
    rw [centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      (w.final_proj.le_iff_mul_eq_left hp).mp hwf]
  refine ⟨v', w', ?_, ?_, hvle, hwle, ?_⟩
  · rw [centralCutPartialIso_initial, hvi]
  · rw [centralCutPartialIso_initial, hwi]
  · rw [centralCutPartialIso_final, centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq), ho, mul_zero]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_properlyInfinite_subprojection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (h : ¬ FiniteCorner p) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ ProperlyInfiniteProjection q := by
  have hn : ¬ FiniteAlgebra (Corner p hp) := fun hfin => h ((finiteCorner_iff p hp).mpr hfin)
  simp only [FiniteAlgebra, not_forall] at hn
  obtain ⟨v, hvi, hvf⟩ := hn
  obtain ⟨q, hq, hq0, hproper⟩ := nonunitary_isometry_has_properlyInfinite_projection
    (cornerPredualEquiv p hp e) hvi hvf
  exact ⟨(q : M), corner_projection_coe p hp hq, corner_projection_le p hp hq,
    fun hz => hq0 (Subtype.ext hz), properlyInfinite_from_corner hp hproper⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def IsInfinitePair (a : PartialIso M × PartialIso M) : Prop :=
  a.1.initial = a.2.initial ∧ a.1.final ≤ a.1.initial ∧
    a.2.final ≤ a.1.initial ∧ a.1.final * a.2.final = 0

lemma infinitePair_cross_orthogonal {C : Set (PartialIso M × PartialIso M)}
    (hC : ∀ a ∈ C, IsInfinitePair a) (hchain : IsChain (· ≤ ·) C)
    {a b : PartialIso M × PartialIso M} (ha : a ∈ C) (hb : b ∈ C) :
    a.1.final * b.2.final = 0 := by
  rcases hchain.total ha hb with h | h
  · calc
      _ = (a.1.final * b.1.final) * b.2.final := by
        rw [(a.1.final_proj.le_iff_mul_eq_left b.1.final_proj).mp (PartialIso.final_mono h.1)]
      _ = 0 := by rw [mul_assoc, (hC b hb).2.2.2, mul_zero]
  · calc
      _ = a.1.final * (a.2.final * b.2.final) := by
        rw [(b.2.final_proj.le_iff_mul_eq_right a.2.final_proj).mp (PartialIso.final_mono h.2)]
      _ = 0 := by rw [← mul_assoc, (hC a ha).2.2.2, zero_mul]

theorem infinitePair_chain_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (C : Set (PartialIso M × PartialIso M)) (hC : ∀ a ∈ C, IsInfinitePair a)
    (hchain : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    ∃ a : PartialIso M × PartialIso M, IsInfinitePair a ∧ ∀ b ∈ C, b ≤ a := by
  let L := Prod.fst '' C
  let R := Prod.snd '' C
  have hL : IsChain (· ≤ ·) L := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact (hchain.total ha hb).imp (fun h => h.1) (fun h => h.1)
  have hR : IsChain (· ≤ ·) R := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact (hchain.total ha hb).imp (fun h => h.2) (fun h => h.2)
  obtain ⟨v, hv, _, hvi, hvf⟩ := exists_partialIso_chain_supremum e L hL (hne.image _)
  obtain ⟨w, hw, _, hwi, hwf⟩ := exists_partialIso_chain_supremum e R hR (hne.image _)
  have hV (a) (ha : a ∈ C) : a.1 ≤ v := hv a.1 ⟨a, ha, rfl⟩
  have hW (a) (ha : a ∈ C) : a.2 ≤ w := hw a.2 ⟨a, ha, rfl⟩
  have hi : v.initial = w.initial := by
    apply le_antisymm
    · apply hvi _ w.initial_proj
      rintro _ ⟨a, ha, rfl⟩
      rw [(hC a ha).1]
      exact (hW a ha).1
    · apply hwi _ v.initial_proj
      rintro _ ⟨a, ha, rfl⟩
      rw [← (hC a ha).1]
      exact (hV a ha).1
  have hfv : v.final ≤ v.initial := by
    apply hvf _ v.initial_proj
    rintro _ ⟨a, ha, rfl⟩
    exact (hC a ha).2.1.trans (hV a ha).1
  have hfw : w.final ≤ v.initial := by
    apply hwf _ v.initial_proj
    rintro _ ⟨a, ha, rfl⟩
    exact (hC a ha).2.2.1.trans (hV a ha).1
  have hcross (a) (ha : a ∈ C) : a.1.final * w.final = 0 := by
    have hbound : w.final ≤ 1 - a.1.final := by
      apply hwf _ a.1.final_proj.one_sub
      rintro _ ⟨b, hb, rfl⟩
      have ho := infinitePair_cross_orthogonal hC hchain ha hb
      apply projection_le_complement_of_mul_zero b.2.final_proj a.1.final_proj
      simpa only [star_mul, a.1.final_proj.isSelfAdjoint.star_eq,
        b.2.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star ho
    exact HochschildTypeII.projection_orthogonal_of_le_complement a.1.final_proj
      w.final_proj hbound
  have hfinal : v.final ≤ 1 - w.final := by
    apply hvf _ w.final_proj.one_sub
    rintro _ ⟨a, ha, rfl⟩
    exact projection_le_complement_of_mul_zero a.1.final_proj w.final_proj (hcross a ha)
  have ho : v.final * w.final = 0 := by
    have h := (v.final_proj.le_iff_mul_eq_left w.final_proj.one_sub).mp hfinal
    rw [mul_sub, mul_one] at h
    exact sub_eq_self.mp h
  exact ⟨(v, w), ⟨hi, hfv, hfw, ho⟩, fun a ha => ⟨hV a ha, hW a ha⟩⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_mul_zero_of_bounds {p q r s : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hs : IsStarProjection s)
    (hpq : p * q = 0) (hrp : r ≤ p) (hsq : s ≤ q) : r * s = 0 := by
  calc
    r * s = (r * p) * (q * s) := by
      rw [(hr.le_iff_mul_eq_left hp).mp hrp, (hs.le_iff_mul_eq_right hq).mp hsq]
    _ = r * (p * q) * s := by simp only [mul_assoc]
    _ = 0 := by rw [hpq, mul_zero, zero_mul]

theorem exists_properlyInfinite_with_finite_complement (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ p : M, IsStarProjection p ∧ ProperlyInfiniteProjection p ∧ FiniteCorner (1 - p) := by
  classical
  let S : Set (PartialIso M × PartialIso M) := {a | IsInfinitePair a}
  have hzero : ((0, 0) : PartialIso M × PartialIso M) ∈ S := by
    simp only [S, Set.mem_ofPred_eq, IsInfinitePair, PartialIso.initial_zero,
      PartialIso.final_zero, le_refl, mul_zero, and_self]
  obtain ⟨a, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain b hb => by
    obtain ⟨c, hc, hu⟩ := infinitePair_chain_upper e C (fun a ha => hC ha) hchain ⟨b, hb⟩
    exact ⟨c, hc, hu⟩) (0, 0) hzero
  have ha : IsInfinitePair a := hm.1
  let p := a.1.initial
  have hp : IsStarProjection p := a.1.initial_proj
  refine ⟨p, hp, ⟨a.1, a.2, rfl, ha.1.symm, ha.2.1, ha.2.2.1, ha.2.2.2⟩, ?_⟩
  by_contra hn
  obtain ⟨q, hq, hqp, hq0, u, w, hui, hwi, huf, hwf, huw⟩ :=
    exists_properlyInfinite_subprojection e hp.one_sub hn
  have hpq : p * q = 0 := HochschildTypeII.projection_orthogonal_of_le_complement hp hq hqp
  have hi1 : a.1.initial * u.initial = 0 := by rw [hui]; exact hpq
  have hi2 : a.2.initial * w.initial = 0 := by rw [← ha.1, hwi]; exact hpq
  have hf1 : a.1.final * u.final = 0 :=
    projection_mul_zero_of_bounds hp hq a.1.final_proj u.final_proj hpq ha.2.1 huf
  have hf2 : a.2.final * w.final = 0 :=
    projection_mul_zero_of_bounds hp hq a.2.final_proj w.final_proj hpq ha.2.2.1 hwf
  let b := (a.1.orthogonalSum u hi1 hf1, a.2.orthogonalSum w hi2 hf2)
  have hbi : b.1.initial = p + q := by rw [PartialIso.orthogonalSum_initial, hui]
  have hbii : b.2.initial = p + q := by rw [PartialIso.orthogonalSum_initial, ← ha.1, hwi]
  have hbf : b.1.final = a.1.final + u.final := by
    exact PartialIso.orthogonalSum_final a.1 u hi1 hf1
  have hbff : b.2.final = a.2.final + w.final := by
    exact PartialIso.orthogonalSum_final a.2 w hi2 hf2
  have hb : b ∈ S := by
    refine ⟨hbi.trans hbii.symm, ?_, ?_, ?_⟩
    · rw [hbf, hbi]
      exact add_le_add ha.2.1 huf
    · rw [hbff, hbi]
      exact add_le_add ha.2.2.1 hwf
    · have hcross1 : a.1.final * w.final = 0 :=
        projection_mul_zero_of_bounds hp hq a.1.final_proj w.final_proj hpq ha.2.1 hwf
      have hcross2 : u.final * a.2.final = 0 := by
        have h := projection_mul_zero_of_bounds hp hq a.2.final_proj u.final_proj
          hpq ha.2.2.1 huf
        simpa only [star_mul, a.2.final_proj.isSelfAdjoint.star_eq,
          u.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h
      rw [hbf, hbff]
      simp only [add_mul, mul_add, ha.2.2.2, huw, hcross1, hcross2, zero_add]
  have hab : a ≤ b := ⟨a.1.le_orthogonalSum u hi1 hf1, a.2.le_orthogonalSum w hi2 hf2⟩
  have he := le_antisymm (hm.2 hb hab) hab
  have hip : p + q = p := by
    have h := congrArg (fun b : PartialIso M × PartialIso M => b.1.initial) he
    exact hbi.symm.trans h
  exact hq0 (add_eq_left.mp hip)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison FinitePathMain

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma finite_complement_embeds_properlyInfinite (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) {p : M} (hp : IsStarProjection p)
    (hproper : ProperlyInfiniteProjection p) (hfin : FiniteCorner (1 - p)) :
    ∃ t : PartialIso M, t.initial = 1 - p ∧ t.final ≤ p := by
  obtain ⟨z, t, hz, hti, htf, hzf, hzi⟩ := trace_free_central_comparison e hp.one_sub hp
  let s := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) t
  have hsi : s.initial ≤ t.initial := by
    apply (s.initial_proj.le_iff_mul_eq_left t.initial_proj).mpr
    rw [centralCutPartialIso_initial, mul_assoc, t.initial_proj.isIdempotentElem.eq]
  have hsi_fin : FiniteCorner s.initial :=
    finiteCorner_mono s.initial_proj hp.one_sub (hsi.trans hti) hfin
  have hsf_fin : FiniteCorner s.final := by
    simpa only [adjointPartialIso_initial, adjointPartialIso_final] using
      finiteCorner_of_equivalent (adjointPartialIso s) (by
        simpa only [adjointPartialIso_final] using hsi_fin)
  have hzpfin : FiniteCorner (z * p) := by
    simpa only [s, centralCutPartialIso_final, hzf] using hsf_fin
  have hzp : IsStarProjection (z * p) := hz.1.mul hp (hz.2 p)
  have hzp0 : z * p = 0 := properlyInfinite_finite_eq_zero hzp
    (properlyInfinite_central_cut hp hz hproper) hzpfin
  have hzfin : FiniteCorner z := finiteCorner_mono hz.1 hp.one_sub
    (projection_le_complement_of_mul_zero hz.1 hp hzp0) hfin
  have hz0 : z = 0 := hno z hz.1 (fun a => (hz.2 a).eq)
    ((finiteCorner_iff z hz.1).mp hzfin)
  refine ⟨t, ?_, htf⟩
  simpa only [hz0, sub_zero, one_mul] using hzi

theorem properlyInfinite_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) : ProperlyInfiniteProjection (1 : M) := by
  obtain ⟨p, hp, hproper, hfin⟩ := exists_properlyInfinite_with_finite_complement e
  obtain ⟨t, hti, htf⟩ := finite_complement_embeds_properlyInfinite e hno hp hproper hfin
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := hproper
  let b := composePartialIso w t (by rw [hwi]; exact htf)
  have hbi : b.initial = 1 - p := by rw [composePartialIso_initial, hti]
  have hbf : b.final ≤ w.final := composePartialIso_final_le ..
  have hi : v.initial * b.initial = 0 := by rw [hvi, hbi, hp.mul_one_sub_self]
  have hf : v.final * b.final = 0 := projection_mul_zero_of_bounds v.final_proj w.final_proj
    v.final_proj b.final_proj ho le_rfl hbf
  let a := v.orthogonalSum b hi hf
  have hai : a.initial = 1 := by
    rw [PartialIso.orthogonalSum_initial, hvi, hbi]
    abel
  have haf : a.final ≤ p := by
    apply (a.final_proj.le_iff_mul_eq_right hp).mpr
    rw [PartialIso.orthogonalSum_final, mul_add,
      (v.final_proj.le_iff_mul_eq_right hp).mp hvf,
      (b.final_proj.le_iff_mul_eq_right hp).mp (hbf.trans hwf)]
  let V := composePartialIso v a (by rw [hvi]; exact haf)
  let W := composePartialIso w a (by rw [hwi]; exact haf)
  have hV : V.final ≤ v.final := composePartialIso_final_le ..
  have hW : W.final ≤ w.final := composePartialIso_final_le ..
  exact ⟨V, W, (composePartialIso_initial ..).trans hai,
    (composePartialIso_initial ..).trans hai, V.final_proj.le_one, W.final_proj.le_one,
    projection_mul_zero_of_bounds v.final_proj w.final_proj V.final_proj W.final_proj ho hV hW⟩

theorem exists_two_orthogonal_isometries (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) :
    ∃ v w : M, star v * v = 1 ∧ star w * w = 1 ∧ star v * w = 0 := by
  obtain ⟨v, w, hvi, hwi, _, _, ho⟩ := properlyInfinite_one e hno
  exact ⟨(v : M), (w : M), hvi, hwi, PartialIso.star_mul_eq_zero_of_final_orthogonal ho⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem isometry_onto_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {v p : M} (hv : star v * v = 1) (hp : IsStarProjection p) (hpv : p * v = v) :
    ∃ w : PartialIso M, w.initial = 1 ∧ w.final = p := by
  let r := 1 - p
  have hr : IsStarProjection r := hp.one_sub
  have hrv : r * v = 0 := by rw [sub_mul, one_mul, hpv, sub_self]
  let c := isometryColumn v hv r hr
  have hci (i) : (c i).initial = r := isometryColumn_initial ..
  have hco (i j) (hij : i ≠ j) : (c i).final * (c j).final = 0 :=
    isometryColumn_final_orthogonal hv hr hrv hij
  have hc0 : (c 0).final = r := by
    change (v ^ 0 * r) * star (v ^ 0 * r) = r
    rw [pow_zero, one_mul, hr.isSelfAdjoint.star_eq, hr.isIdempotentElem.eq]
  obtain ⟨q, hq, hcq, hqmin, _⟩ := exists_orthogonal_projection_sum e
    (fun i => (c i).final) (fun i => (c i).final_proj) hco
  let a (i : ℕ) := columnTransition (c (i + 1)) (c i) ((hci _).trans (hci _).symm)
  have hai (i) : (a i).initial = (c i).final := columnTransition_initial ..
  have haf (i) : (a i).final = (c (i + 1)).final := columnTransition_final ..
  obtain ⟨s, hsi, hsf, hsi_min, hsf_min⟩ := exists_countable_partialIso_sum e a
    (fun i j hij => by rw [hai, hai]; exact hco i j hij)
    (fun i j hij => by rw [haf, haf]; exact hco _ _ (by omega))
  have hsq : s.initial = q := le_antisymm
    (hsi_min q hq (fun i => by rw [hai]; exact hcq i))
    (hqmin _ s.initial_proj (fun i => by rw [← hai]; exact hsi i))
  have hstq : s.final ≤ q := hsf_min q hq (fun i => by rw [haf]; exact hcq _)
  have hrt : r * s.final = 0 := by
    have hb : s.final ≤ 1 - r := by
      apply hsf_min _ hr.one_sub
      intro i
      apply projection_le_complement_of_mul_zero (a i).final_proj hr
      rw [haf, ← hc0]
      exact hco _ _ (by omega)
    exact HochschildTypeII.projection_orthogonal_of_le_complement hr s.final_proj hb
  have hrq : r ≤ q := by rw [← hc0]; exact hcq 0
  have hrs : IsStarProjection (r + s.final) := hr.add s.final_proj hrt
  have hqrs : q = r + s.final := by
    apply le_antisymm
    · apply hqmin _ hrs
      intro i
      cases i with
      | zero => rw [hc0]; exact le_add_of_nonneg_right s.final_proj.nonneg
      | succ i =>
          calc
            (c (i + 1)).final = (a i).final := (haf i).symm
            _ ≤ s.final := hsf i
            _ ≤ r + s.final := le_add_of_nonneg_left hr.nonneg
    · apply (hrs.le_iff_mul_eq_right hq).mpr
      rw [mul_add, (hr.le_iff_mul_eq_right hq).mp hrq,
        (s.final_proj.le_iff_mul_eq_right hq).mp hstq]
  let t : PartialIso M := ⟨1 - q, by
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq,
      hq.one_sub.isIdempotentElem.eq]⟩
  have hti : t.initial = 1 - q := by
    change star (1 - q) * (1 - q) = _
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq]
  have htf : t.final = 1 - q := by
    change (1 - q) * star (1 - q) = _
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq]
  have hi : s.initial * t.initial = 0 := by rw [hsq, hti, hq.mul_one_sub_self]
  have hf : s.final * t.final = 0 := by
    rw [htf, mul_sub, mul_one, (s.final_proj.le_iff_mul_eq_left hq).mp hstq, sub_self]
  refine ⟨s.orthogonalSum t hi hf, ?_, ?_⟩
  · rw [PartialIso.orthogonalSum_initial, hsq, hti]
    abel
  · rw [PartialIso.orthogonalSum_final, htf, hqrs]
    change s.final + (1 - ((1 - p) + s.final)) = p
    abel
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_countable_isometries_of_two (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {v w : M} (hv : star v * v = 1) (hw : star w * w = 1) (hvw : star v * w = 0) :
    ∃ c : ℕ → PartialIso M, (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1 := by
  have hwi (i : ℕ) : star (v ^ i * w) * (v ^ i * w) = 1 := by
    rw [star_mul]
    calc
      _ = star w * (star (v ^ i) * v ^ i) * w := by simp only [mul_assoc]
      _ = 1 := by rw [isometry_pow_initial hv, mul_one, hw]
  let c (i : ℕ) : PartialIso M := ⟨v ^ i * w, by rw [mul_assoc, hwi, mul_one]⟩
  have hci (i) : (c i).initial = 1 := hwi i
  let p := (c 0).final
  have hp : IsStarProjection p := (c 0).final_proj
  have hpw : p = w * star w := by simp only [p, c, PartialIso.final, pow_zero, one_mul]
  have hpv : p * v = 0 := by
    have h : star w * v = 0 := by
      simpa only [star_mul, star_star, star_zero] using congrArg star hvw
    rw [hpw, mul_assoc, h, mul_zero]
  have hcfin (i) : (c i).final = (isometryColumn v hv p hp i).final := by
    change (v ^ i * w) * star (v ^ i * w) = (v ^ i * p) * star (v ^ i * p)
    rw [star_mul, star_mul, hp.isSelfAdjoint.star_eq]
    calc
      _ = v ^ i * (w * star w) * star (v ^ i) := by simp only [mul_assoc]
      _ = v ^ i * p * star (v ^ i) := by rw [hpw]
      _ = _ := by simp only [mul_assoc, ← mul_assoc p p, hp.isIdempotentElem.eq]
  have hco (i j) (hij : i ≠ j) : (c i).final * (c j).final = 0 := by
    rw [hcfin, hcfin]
    exact isometryColumn_final_orthogonal hv hp hpv hij
  obtain ⟨q, hq, hcq, hqmin, _⟩ := exists_orthogonal_projection_sum e
    (fun i => (c i).final) (fun i => (c i).final_proj) hco
  have hpq : p ≤ q := hcq 0
  have hpR : p * (1 - q) = 0 := by
    rw [mul_sub, mul_one, (hp.le_iff_mul_eq_left hq).mp hpq, sub_self]
  have hP : IsStarProjection (p + (1 - q)) := hp.add hq.one_sub hpR
  have hPw : (p + (1 - q)) * w = w := by
    have hqw : q * w = w := by
      have hh := partialIso_left_support hq (c 0) hpq
      simpa only [c, pow_zero, one_mul] using hh
    rw [add_mul, hpw, mul_assoc, hw, mul_one, sub_mul, one_mul, hqw, sub_self, add_zero]
  obtain ⟨b, hbi, hbf⟩ := isometry_onto_projection e hw hP hPw
  let d : ℕ → PartialIso M
    | 0 => b
    | n + 1 => c (n + 1)
  have hdi (i) : (d i).initial = 1 := by
    cases i with
    | zero => exact hbi
    | succ i => exact hci (i + 1)
  have hb_orth (i : ℕ) : b.final * (c (i + 1)).final = 0 := by
    have hR : (1 - q) * (c (i + 1)).final = 0 := by
      rw [sub_mul, one_mul, ((c (i + 1)).final_proj.le_iff_mul_eq_right hq).mp (hcq _), sub_self]
    rw [hbf, add_mul, hco 0 (i + 1) (by omega), hR, zero_add]
  have hdo (i j) (hij : i ≠ j) : (d i).final * (d j).final = 0 := by
    cases i with
    | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ j => exact hb_orth j
    | succ i =>
        cases j with
        | zero =>
            simpa only [star_mul, b.final_proj.isSelfAdjoint.star_eq,
              (c (i + 1)).final_proj.isSelfAdjoint.star_eq, star_zero] using
              congrArg star (hb_orth i)
        | succ j => exact hco (i + 1) (j + 1) hij
  obtain ⟨P, hPproj, hdP, hPmin, ht⟩ := exists_orthogonal_projection_sum e
    (fun i => (d i).final) (fun i => (d i).final_proj) hdo
  have hpP : p ≤ P := by
    calc
      p ≤ p + (1 - q) := le_add_of_nonneg_right hq.one_sub.nonneg
      _ = b.final := hbf.symm
      _ ≤ P := hdP 0
  have hqP : q ≤ P := by
    apply hqmin P hPproj
    intro i
    cases i with
    | zero => exact hpP
    | succ i => exact hdP (i + 1)
  have hRP : 1 - q ≤ P := by
    calc
      1 - q ≤ p + (1 - q) := le_add_of_nonneg_left hp.nonneg
      _ = b.final := hbf.symm
      _ ≤ P := hdP 0
  have h1P : 1 ≤ P := by
    apply ((IsStarProjection.one M).le_iff_mul_eq_right hPproj).mpr
    calc
      P * 1 = P * (q + (1 - q)) := by congr 1; abel
      _ = q + (1 - q) := by
        rw [mul_add, (hq.le_iff_mul_eq_right hPproj).mp hqP,
          (hq.one_sub.le_iff_mul_eq_right hPproj).mp hRP]
      _ = 1 := by abel
  have hPeq : P = 1 := le_antisymm hPproj.le_one h1P
  exact ⟨d, hdi, hdo, hPeq ▸ ht⟩

theorem exists_countable_isometries (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) :
    ∃ c : ℕ → PartialIso M, (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1 := by
  obtain ⟨v, w, hv, hw, hvw⟩ := exists_two_orthogonal_isometries e hno
  exact exists_countable_isometries_of_two e hv hw hvw
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.exists_countable_isometries.{u} := @OAI.BoundedHochschild.KadisonRingrose.exists_countable_isometries.{u}
