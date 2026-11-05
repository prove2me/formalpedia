-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.exists_homogeneous_piece_of_abelian_trace
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:47:28.911993+00:00
-- url     : https://prove2.me/submissions/82bd2007-01b7-495e-8ddd-a393d83d2a12

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
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)

lemma projection_trace_pos (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) : 0 < (τ p).re := by
  have hpos : 0 ≤ τ p := τ.map_nonneg hp.nonneg
  have hre : 0 ≤ (τ p).re := Complex.nonneg_iff.mp hpos |>.1
  apply lt_of_le_of_ne hre
  intro hz
  have he : τ p=0 := Complex.ext hz.symm (Complex.nonneg_iff.mp hpos).2.symm
  apply hp0
  apply hfaith p
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using he
end HochschildDiffuse
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

theorem exists_central_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
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
  obtain ⟨p, _hpnorm, ht⟩ := exists_predual_ultralimit e U
    (fun q : S => (q : M)) 1 (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ hr => congrArg (fun a : M => e.symm a z) hr.symm)
  have hpcentral (a : M) : p * a = a * p := by
    have hl := HochschildSakai.predual_tendsto_mul_left e a ht
    have hr := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => a * (q : M)) = (fun q : S => (q : M) * a) := by
      funext q
      exact (hcentral q q.property a).symm
    rw [heq] at hl
    exact predual_tendsto_unique e hr hl
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
  refine ⟨p, hp, hpcentral, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hub
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hub q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) := by
      funext q
      exact ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))

theorem exists_central_projection_chain_supremum
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) := by
  obtain ⟨p, hp, hc, hu, hl, ha, _⟩ :=
    exists_central_projection_chain_supremum_with_limit e S hne hchain hproj hcentral
  exact ⟨p, hp, hc, hu, hl, ha⟩
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

lemma projection_mem_corner {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) : q ∈ corner p hp :=
  ⟨(hq.le_iff_mul_eq_right hp).mp hqp,(hq.le_iff_mul_eq_left hp).mp hqp⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_mem_corner {p : M} (hp : IsStarProjection p) (a : M) :
    p*a*p ∈ corner p hp := by
  exact ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],
    by rw [mul_assoc,hp.isIdempotentElem.eq]⟩

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

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def cornerTrace : Corner p hp →ₚ[ℂ] ℂ where
  toLinearMap := ((τ p).re : ℂ)⁻¹ • (τ.toLinearMap.comp (corner p hp).subtype)
  monotone' := fun _ _ h => mul_le_mul_of_nonneg_left (τ.monotone h)
    (inv_nonneg.mpr (Complex.zero_le_real.mpr
      (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1))

@[simp] lemma cornerTrace_apply (a : Corner p hp) :
    cornerTrace p hp τ a = ((τ p).re : ℂ)⁻¹ * τ (a:M) := rfl

lemma cornerTrace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (a b : Corner p hp) : cornerTrace p hp τ (a*b)=cornerTrace p hp τ (b*a) := by
  simp only [cornerTrace_apply,corner_coe_mul,htr a.val b.val]

lemma cornerTrace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0)
    (a : Corner p hp) (ha : cornerTrace p hp τ (star a*a)=0) : a=0 := by
  have hne : ((τ p).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'
  have hh := (mul_eq_zero.mp ha).resolve_left (inv_ne_zero hne)
  exact Subtype.ext (hfaith a.val hh)
end HochschildCorners
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace CentralCorner

open HochschildCorners

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)

def includeMap : Corner p hp →L[ℂ] M :=
  (corner p hp).toNonUnitalSubalgebra.toSubmodule.subtypeL

def compressMap : M →L[ℂ] Corner p hp :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨p * a, by
        constructor
        · rw [← mul_assoc, hp.isIdempotentElem.eq]
        · calc
            (p * a) * p = p * (a * p) := mul_assoc _ _ _
            _ = p * (p * a) := by rw [← hc a]
            _ = p * a := by rw [← mul_assoc, hp.isIdempotentElem.eq]⟩
      map_add' := fun a b => Subtype.ext (mul_add p a b)
      map_smul' := fun c a => Subtype.ext (by
        change p * (c • a) = c • (p * a)
        rw [mul_smul_comm]) }
    1 (fun a => by
      change ‖p * a‖ ≤ 1 * ‖a‖
      exact (norm_mul_le p a).trans (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma includeMap_apply (a : Corner p hp) : includeMap p hp a = (a : M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_coe (a : M) :
    (compressMap p hp hc a : M) = p * a := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_includeMap (a : Corner p hp) :
    compressMap p hp hc (includeMap p hp a) = a := Subtype.ext a.property.1
end CentralCorner
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

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralCorner_central {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : HochschildCorners.Corner p hp)
    (hqc : ∀ b : HochschildCorners.Corner p hp, q * b = b * q) :
    ∀ a : M, (q : M) * a = a * (q : M) := by
  intro a
  have h := congrArg Subtype.val (hqc (CentralCorner.compressMap p hp hc a))
  change (q : M) * (p * a) = (p * a) * (q : M) at h
  calc
    (q : M) * a = ((q : M) * p) * a := by rw [q.property.2]
    _ = (q : M) * (p * a) := mul_assoc _ _ _
    _ = (p * a) * (q : M) := h
    _ = a * (p * (q : M)) := by rw [hc a, mul_assoc]
    _ = a * (q : M) := by rw [q.property.1]
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

lemma abelian_of_le {p q : M} (hp : AbelianProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p) : AbelianProjection q := by
  refine ⟨hq,?_⟩
  intro a b
  have he (x : M) : p*(q*x*q)*p=q*x*q := by
    rw [← mul_assoc,← mul_assoc,(hq.le_iff_mul_eq_right hp.1).mp hqp,
      mul_assoc,mul_assoc,(hq.le_iff_mul_eq_left hp.1).mp hqp,← mul_assoc]
  simpa only [he] using hp.2 (q*a*q) (q*b*q)
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

lemma central_annihilator_chain (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : M) (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, CentralProjection q ∧ q * p = 0) :
    ∃ s : M, CentralProjection s ∧ s * p = 0 ∧ ∀ q ∈ c, q ≤ s := by
  obtain ⟨s, hsp, hsc, hub, _hleast, hann⟩ :=
    exists_central_projection_chain_supremum e c hne hc
      (fun q hq => (hs q hq).1.1) (fun q hq a => ((hs q hq).1.2 a).eq)
  exact ⟨s, ⟨hsp, fun a => hsc a⟩, hann p (fun q hq => (hs q hq).2), hub⟩
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

open FinitePathMain HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in

lemma finitePath_abelian_of_popa {p : M} (hp : IsStarProjection p)
    (h : PopaTypeII.AbelianProjection hp) : AbelianProjection p := by
  refine ⟨hp, fun a b => ?_⟩
  let A : PopaCorner.algebra hp := ⟨p * a * p, compress_mem_corner hp a⟩
  let B : PopaCorner.algebra hp := ⟨p * b * p, compress_mem_corner hp b⟩
  exact congrArg Subtype.val (h A B).eq
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

open HochschildCorners

section Nested
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def nestedCornerEquiv {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) :
    Corner q hq ≃⋆ₐ[ℂ] Corner (q : M) (corner_projection_coe p hp hq) where
  toFun a := ⟨((a : Corner p hp) : M),
    congrArg Subtype.val a.property.1, congrArg Subtype.val a.property.2⟩
  invFun b := ⟨⟨(b : M), by
      constructor
      · calc
          p * (b : M) = p * ((q : M) * (b : M)) := by rw [b.property.1]
          _ = (b : M) := by rw [← mul_assoc, q.property.1, b.property.1]
      · calc
          (b : M) * p = ((b : M) * (q : M)) * p := by rw [b.property.2]
          _ = (b : M) := by rw [mul_assoc, q.property.2, b.property.2]⟩,
    Subtype.ext b.property.1, Subtype.ext b.property.2⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma nestedCornerEquiv_apply {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) (a : Corner q hq) :
    ((nestedCornerEquiv hp q hq a : Corner (q : M) (corner_projection_coe p hp hq)) : M) =
      ((a : Corner p hp) : M) := rfl

end Nested

section Transport
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]
  [PartialOrder M] [StarOrderedRing M] [PartialOrder N] [StarOrderedRing N]

def popaCornerEquiv (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : IsStarProjection p) :
    PopaCorner.algebra hp ≃⋆ₐ[ℂ] PopaCorner.algebra (hp.map φ) where
  toFun a := ⟨φ (a : M), by
    constructor
    · change φ p * φ (a : M) = φ (a : M)
      rw [← map_mul, a.property.1]
    · change φ (a : M) * φ p = φ (a : M)
      rw [← map_mul, a.property.2]⟩
  invFun b := ⟨φ.symm (b : N), by
    constructor
    · apply φ.injective
      change φ (p * φ.symm (b : N)) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.1
    · apply φ.injective
      change φ (φ.symm (b : N) * p) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.2⟩
  left_inv a := Subtype.ext (φ.symm_apply_apply (a : M))
  right_inv b := Subtype.ext (φ.apply_symm_apply (b : N))
  map_add' a b := Subtype.ext (map_add φ (a : M) (b : M))
  map_mul' a b := Subtype.ext (map_mul φ (a : M) (b : M))
  map_smul' c a := Subtype.ext (map_smul φ c (a : M))
  map_star' a := Subtype.ext (map_star φ (a : M))

lemma abelianProjection_map_equiv (φ : M ≃⋆ₐ[ℂ] N) {p : M}
    (hp : IsStarProjection p) (hab : PopaTypeII.AbelianProjection hp) :
    PopaTypeII.AbelianProjection (hp.map φ) := by
  let E := popaCornerEquiv φ hp
  intro a b
  simpa only [E.apply_symm_apply] using (hab (E.symm a) (E.symm b)).map E
end Transport
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

omit [PartialOrder M] [StarOrderedRing M] in

lemma abelianProjection_partialIso (v : PartialIso M)
    (hab : PopaTypeII.AbelianProjection v.initial_proj) :
    PopaTypeII.AbelianProjection v.final_proj := by
  let E := partialIsoCornerEquiv v
  intro a b
  simpa only [E.apply_symm_apply] using (hab (E.symm a) (E.symm b)).map E
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] {n : ℕ} {p : M}

def matrixSystemOfColumns (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1) : MatrixSystem M n where
  entry i j := (v i : M) * star (v j : M)
  star_entry i j := by simp only [star_mul, star_star]
  entry_mul i j k l := by
    classical
    by_cases h : j = k
    · subst k
      rw [ite_eq_left rfl]
      calc
        _ = (v i : M) * (v j).initial * star (v l : M) := by
          simp only [PartialIso.initial, mul_assoc]
        _ = (v i : M) * (v i).initial * star (v l : M) := by rw [hi, hi]
        _ = _ := by rw [(v i).mul_initial]
    · rw [ite_eq_right h]
      calc
        _ = (v i : M) * (star (v j : M) * (v k : M)) * star (v l : M) := by
          simp only [mul_assoc]
        _ = 0 := by rw [PartialIso.star_mul_eq_zero_of_final_orthogonal (ho j k h),
          mul_zero, zero_mul]
  sum_diagonal := hs

@[simp] lemma matrixSystemOfColumns_diagonal (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1) (i : Fin n) :
    (matrixSystemOfColumns v hi ho hs).entry i i = (v i).final := rfl

variable [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma matrixSystemOfColumns_abelian (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1)
    (hp : IsStarProjection p) (hpa : PopaTypeII.AbelianProjection hp) (i : Fin n) :
    FinitePathMain.AbelianProjection ((matrixSystemOfColumns v hi ho hs).entry i i) := by
  have hinit : PopaTypeII.AbelianProjection (v i).initial_proj := by
    simpa only [hi] using hpa
  exact finitePath_abelian_of_popa (v i).final_proj (abelianProjection_partialIso (v i) hinit)
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
open BoundedHochschild HochschildComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma abelian_orthogonal_mul {p r t : M} (hp : AbelianProjection p)
    (hr : IsStarProjection r) (ht : IsStarProjection t) (hrp : r ≤ p) (htp : t ≤ p)
    (hrt : r*t=0) (a : M) : r*a*t=0 := by
  have hpr := (hr.le_iff_mul_eq_right hp.1).mp hrp
  have hrp' := (hr.le_iff_mul_eq_left hp.1).mp hrp
  have hpt := (ht.le_iff_mul_eq_right hp.1).mp htp
  have he : p*r*p=r := by rw [hpr,hrp']
  have hc := hp.2 r a
  rw [he] at hc
  calc
    r*a*t = r*(p*a*p)*t := by rw [← mul_assoc,← mul_assoc,hrp',mul_assoc,mul_assoc,hpt,← mul_assoc]
    _ = (p*a*p)*(r*t) := by rw [hc.eq,mul_assoc]
    _ = 0 := by rw [hrt,mul_zero]
end HochschildTypeII
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) : ∃ z : M, IsCentralSupport p z := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hzero : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain a ha => by
    obtain ⟨t, ht, htp, hu⟩ := central_annihilator_chain e p C hchain ⟨a, ha⟩
      (fun q hq => hC hq)
    exact ⟨t, ⟨ht, htp⟩, hu⟩) 0 hzero
  have hs := hm.1.1
  have hsp := hm.1.2
  let z := 1 - s
  have hz : CentralProjection z :=
    ⟨hs.1.one_sub, fun a => (Commute.one_left a).sub_left (hs.2 a)⟩
  refine ⟨z, hz, (hp.le_iff_mul_eq_right hz.1).mpr ?_, ?_⟩
  · change (1 - s) * p = p
    rw [sub_mul, one_mul, hsp, sub_zero]
  · intro c hc hcp
    let t := z * c
    have ht : CentralProjection t :=
      ⟨hz.1.mul hc.1 (hz.2 c), fun a => (hz.2 a).mul_left (hc.2 a)⟩
    have hst : s * t = 0 := by
      change s * ((1 - s) * c) = 0
      rw [← mul_assoc, hs.1.mul_one_sub_self, zero_mul]
    have htp : t * p = 0 := by
      change z * c * p = 0
      rw [mul_assoc, hcp, mul_zero]
    have hnew : s + t ∈ S :=
      ⟨⟨hs.1.add ht.1 hst, fun a => (hs.2 a).add_left (ht.2 a)⟩,
        by rw [add_mul, hsp, htp, zero_add]⟩
    have hle : s ≤ s + t := le_add_of_nonneg_right ht.1.nonneg
    have ht0 : t = 0 := add_eq_left.mp (le_antisymm (hm.2 hnew hle) hle)
    exact (hc.2 z).eq.trans ht0

theorem central_support_full (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p z r : M} (hp : IsStarProjection p) (hz : IsCentralSupport p z)
    (hr : IsStarProjection r) (hrz : r ≤ z) (hr0 : r ≠ 0) :
    ∃ a : M, p * a * r ≠ 0 := by
  by_contra hn
  push Not at hn
  have hrp (a : M) : r * a * p = 0 := by
    simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq,
      hr.isSelfAdjoint.star_eq, star_zero, mul_assoc] using congrArg star (hn (star a))
  obtain ⟨c, hc, hrc, hcp⟩ := exists_trace_free_central_separator e hr hp hrp
  have hcz := hz.2.2 c hc hcp
  have he : c * z * r = r := by
    rw [mul_assoc, (hr.le_iff_mul_eq_right hz.1.1).mp hrz,
      (hr.le_iff_mul_eq_right hc.1).mp hrc]
  rw [hcz, zero_mul] at he
  exact hr0 he.symm

theorem trace_free_abelian_subequivalent (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : AbelianProjection p) (hq : IsStarProjection q)
    (hfull : ∀ r : M, IsStarProjection r → r ≤ p → r ≠ 0 → ∃ a : M, q * a * r ≠ 0) :
    ∃ v : PartialIso M, v.initial = p ∧ v.final ≤ q := by
  classical
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.1.nonneg, by simpa using hq.nonneg⟩
  obtain ⟨v, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain a ha => by
    obtain ⟨w, hwp, hwq, hu⟩ := partialIso_chain_upper e hp.1 hq C hchain ⟨a, ha⟩
      (fun t ht => hC ht)
    exact ⟨w, ⟨hwp, hwq⟩, hu⟩) 0 hz
  have hvp := hm.1.1
  have hvq := hm.1.2
  have hr := (v.initial_proj.le_iff_sub hp.1).mp hvp
  have hs := (v.final_proj.le_iff_sub hq).mp hvq
  have hir : v.initial * (p - v.initial) = 0 := by
    rw [mul_sub, (v.initial_proj.le_iff_mul_eq_left hp.1).mp hvp,
      v.initial_proj.isIdempotentElem.eq, sub_self]
  have hvr (a : M) : v.final * a * (p - v.initial) = 0 := by
    have h := HochschildTypeII.abelian_orthogonal_mul hp v.initial_proj hr hvp
      (sub_le_self _ v.initial_proj.nonneg) hir (star (v : M) * a)
    calc
      _ = (v : M) * (v.initial * (star (v : M) * a) * (p - v.initial)) := by
        simp only [← mul_assoc, v.mul_initial, PartialIso.final]
      _ = 0 := by rw [h, mul_zero]
  refine ⟨v, ?_, hvq⟩
  by_contra hi
  obtain ⟨a, ha⟩ := hfull (p - v.initial) hr (sub_le_self _ v.initial_proj.nonneg)
    (sub_ne_zero.mpr (Ne.symm hi))
  have hba : (q - v.final) * a * (p - v.initial) ≠ 0 := by
    simpa only [sub_mul, hvr a, sub_zero] using ha
  obtain ⟨w, hw0, hwi, hwf⟩ := partialIso_of_nonzero_corner e hs hr
    ((q - v.final) * a * (p - v.initial)) hba
    (by rw [← mul_assoc, ← mul_assoc, hs.isIdempotentElem.eq])
    (by rw [mul_assoc, hr.isIdempotentElem.eq])
  have hio := HochschildCentralComparison.orthogonal_of_le_sub hp.1 v.initial_proj
    w.initial_proj hvp hwi
  have hfo := HochschildCentralComparison.orthogonal_of_le_sub hq v.final_proj
    w.final_proj hvq hwf
  have hnew : v.orthogonalSum w hio hfo ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial + w.initial ≤ v.initial + (p - v.initial) := add_le_add_right hwi _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final + w.final ≤ v.final + (q - v.final) := add_le_add_right hwf _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hio hfo
  have he := congrArg (fun t : PartialIso M => (t : M))
    (le_antisymm (hm.2 hnew hle) hle)
  exact hw0 (add_eq_left.mp he)
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

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_initial_zero_iff_final_zero (v : PartialIso M)
    {c : M} (hc : ∀ a : M, c * a = a * c) :
    c * v.initial = 0 ↔ c * v.final = 0 := by
  have hf (w : PartialIso M) (hi : c * w.initial = 0) : c * w.final = 0 := by
    have hv : c * (w : M) = 0 := by
      calc
        _ = c * ((w : M) * w.initial) := by rw [w.mul_initial]
        _ = (w : M) * (c * w.initial) := by rw [← mul_assoc, hc, mul_assoc]
        _ = 0 := by rw [hi, mul_zero]
    change c * ((w : M) * star (w : M)) = 0
    rw [← mul_assoc, hv, zero_mul]
  exact ⟨hf v, fun h => by simpa using hf (adjointPartialIso v) (by simpa using h)⟩

lemma IsCentralSupport.partialIso (v : PartialIso M) {z : M}
    (h : IsCentralSupport v.initial z) : IsCentralSupport v.final z := by
  have hzv : z * (v : M) = v := by
    calc
      _ = z * ((v : M) * v.initial) := by rw [v.mul_initial]
      _ = (v : M) * (z * v.initial) := by rw [← mul_assoc, (h.1.2 (v : M)).eq, mul_assoc]
      _ = v := by rw [(v.initial_proj.le_iff_mul_eq_right h.1.1).mp h.2.1, v.mul_initial]
  refine ⟨h.1, (v.final_proj.le_iff_mul_eq_right h.1.1).mpr ?_, ?_⟩
  · change z * ((v : M) * star (v : M)) = _
    rw [← mul_assoc, hzv]
    rfl
  · intro c hc hc0
    exact h.2.2 c hc ((central_initial_zero_iff_final_zero v (fun a => (hc.2 a).eq)).mpr hc0)

theorem abelian_subprojection_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : AbelianProjection p) (hq : IsStarProjection q) (hqp : q ≤ p) :
    ∃ c : M, CentralProjection c ∧ c * p = q := by
  have hr := (hq.le_iff_sub hp.1).mp hqp
  have hqr : q * (p - q) = 0 := by
    rw [mul_sub, (hq.le_iff_mul_eq_left hp.1).mp hqp, hq.isIdempotentElem.eq, sub_self]
  obtain ⟨c, hc, hqc, hcr⟩ := exists_trace_free_central_separator e hq hr
    (HochschildTypeII.abelian_orthogonal_mul hp hq hr hqp
      (sub_le_self _ hq.nonneg) hqr)
  refine ⟨c, hc, ?_⟩
  have hcq := (hq.le_iff_mul_eq_right hc.1).mp hqc
  rw [mul_sub, hcq, sub_eq_zero] at hcr
  exact hcr

theorem abelian_equivalent_of_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q z : M} (hp : AbelianProjection p) (hq : AbelianProjection q)
    (hpz : IsCentralSupport p z) (hqz : IsCentralSupport q z) :
    ∃ v : PartialIso M, v.initial = p ∧ v.final = q := by
  obtain ⟨v, hvp, hvq⟩ := trace_free_abelian_subequivalent e hp hq.1
    (fun r hr hrp hr0 => central_support_full e hq.1 hqz hr (hrp.trans hpz.2.1) hr0)
  have hvz : IsCentralSupport v.final z :=
    IsCentralSupport.partialIso v (by simpa only [hvp] using hpz)
  have hr := (v.final_proj.le_iff_sub hq.1).mp hvq
  have hrq : q - v.final ≤ q := sub_le_self _ v.final_proj.nonneg
  obtain ⟨c, hc, hcr⟩ := abelian_subprojection_central_cut e hq hr hrq
  have hcf : c * v.final = 0 := by
    have horth : (q - v.final) * v.final = 0 := by
      rw [sub_mul, (v.final_proj.le_iff_mul_eq_right hq.1).mp hvq,
        v.final_proj.isIdempotentElem.eq, sub_self]
    calc
      _ = (c * q) * v.final := by rw [mul_assoc,
        (v.final_proj.le_iff_mul_eq_right hq.1).mp hvq]
      _ = 0 := by rw [hcr, horth]
  have hcz := hvz.2.2 c hc hcf
  have hr0 : q - v.final = 0 := by
    calc
      _ = c * q := hcr.symm
      _ = c * (z * q) := by rw [(hq.1.le_iff_mul_eq_right hqz.1.1).mp hqz.2.1]
      _ = 0 := by rw [← mul_assoc, hcz, zero_mul]
  exact ⟨v, hvp, (sub_eq_zero.mp hr0).symm⟩
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

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma IsCentralSupport.eq_zero_iff {p z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p z) : p = 0 ↔ z = 0 := by
  constructor
  · intro hp0
    have hz := h.2.2 1 ⟨IsStarProjection.one M, fun _ => Commute.one_left _⟩ (by simp [hp0])
    simpa only [one_mul] using hz
  · intro hz0
    exact le_antisymm (hz0 ▸ h.2.1) hp.nonneg

lemma IsCentralSupport.centralCut {p t z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p t) (hz : CentralProjection z) :
    IsCentralSupport (z * p) (z * t) := by
  have hzp := hz.1.mul hp (hz.2 p)
  have hzt : CentralProjection (z * t) :=
    ⟨hz.1.mul h.1.1 (hz.2 t), fun a => (hz.2 a).mul_left (h.1.2 a)⟩
  refine ⟨hzt, (hzp.le_iff_mul_eq_left hzt.1).mpr ?_, ?_⟩
  · calc
      z * p * (z * t) = z * (p * t) :=
        central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq) p t
      _ = z * p := by rw [(hp.le_iff_mul_eq_left h.1.1).mp h.2.1]
  · intro c hc hcp
    have hcz : CentralProjection (c * z) :=
      ⟨hc.1.mul hz.1 (hc.2 z), fun a => (hc.2 a).mul_left (hz.2 a)⟩
    have hh := h.2.2 (c * z) hcz (by simpa only [mul_assoc] using hcp)
    simpa only [mul_assoc] using hh

lemma IsCentralSupport.centralCut_one {p z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p 1) (hz : CentralProjection z) :
    IsCentralSupport (z * p) z := by
  simpa only [mul_one] using h.centralCut hp hz
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners HochschildComparison HochschildMatrixSystems FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def partialIsoInCorner {z : M} (hz : IsStarProjection z) (v : PartialIso M)
    (hi : v.initial ≤ z) (hf : v.final ≤ z) : PartialIso (Corner z hz) where
  val := ⟨(v : M), partialIso_left_support hz v hf, partialIso_right_support hz v hi⟩
  mul_star_mul := Subtype.ext v.mul_star_mul

@[simp] lemma partialIsoInCorner_initial {z : M} (hz : IsStarProjection z)
    (v : PartialIso M) (hi : v.initial ≤ z) (hf : v.final ≤ z) :
    ((partialIsoInCorner hz v hi hf).initial : M) = v.initial := rfl

@[simp] lemma partialIsoInCorner_final {z : M} (hz : IsStarProjection z)
    (v : PartialIso M) (hi : v.initial ≤ z) (hf : v.final ≤ z) :
    ((partialIsoInCorner hz v hi hf).final : M) = v.final := rfl

theorem homogeneousCorner_of_columns {z p : M} (hz : IsStarProjection z)
    (hp : AbelianProjection p) (hpz : p ≤ z) {n : ℕ} (i : Fin n)
    (v : Fin n → PartialIso M) (hi : ∀ j, (v j).initial = p)
    (hf : ∀ j, (v j).final ≤ z)
    (ho : ∀ j k, j ≠ k → (v j).final * (v k).final = 0)
    (hs : ∑ j, (v j).final = z) : HomogeneousTypeICorner z := by
  let pC : Corner z hz := ⟨p, (hp.1.le_iff_mul_eq_right hz).mp hpz,
    (hp.1.le_iff_mul_eq_left hz).mp hpz⟩
  have hpC : IsStarProjection pC :=
    ⟨Subtype.ext hp.1.isIdempotentElem.eq, Subtype.ext hp.1.isSelfAdjoint.star_eq⟩
  let w (j : Fin n) := partialIsoInCorner hz (v j) (by rw [hi]; exact hpz) (hf j)
  have hwi (j : Fin n) : (w j).initial = pC := Subtype.ext (hi j)
  have hwo (j k : Fin n) (hjk : j ≠ k) : (w j).final * (w k).final = 0 :=
    Subtype.ext (ho j k hjk)
  have hws : ∑ j, (w j).final = 1 := by
    apply Subtype.ext
    change CentralCorner.includeMap z hz (∑ j, (w j).final) = z
    rw [map_sum]
    exact hs
  let E := matrixSystemOfColumns w hwi hwo hws
  refine ⟨hz, n, E, i, matrixSystemOfColumns_abelian w hwi hwo hws hpC ?_ i⟩
  intro a b
  apply Subtype.ext
  apply Subtype.ext
  have hcut (c : PopaCorner.algebra hpC) : p * ((c : Corner z hz) : M) * p =
      ((c : Corner z hz) : M) := by
    have hl := congrArg (fun a : Corner z hz => (a : M)) c.property.1
    have hr := congrArg (fun a : Corner z hz => (a : M)) c.property.2
    change p * ((c : Corner z hz) : M) = ((c : Corner z hz) : M) at hl
    change ((c : Corner z hz) : M) * p = ((c : Corner z hz) : M) at hr
    rw [hl, hr]
  change ((a : Corner z hz) : M) * ((b : Corner z hz) : M) =
    ((b : Corner z hz) : M) * ((a : Corner z hz) : M)
  simpa only [hcut] using (hp.2 ((a : Corner z hz) : M) ((b : Corner z hz) : M)).eq
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

theorem homogeneousCorner_of_annihilated_residual {p z : M} (hp : AbelianProjection p)
    (hz : CentralProjection z) (hz0 : z ≠ 0) {n : ℕ}
    (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hann : z * (1 - ∑ i, (v i).final) = 0) : HomogeneousTypeICorner z := by
  classical
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    exact hz0 (by simpa using hann)
  let w (i : Fin n) := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) (v i)
  have hzp : IsStarProjection (z * p) := hz.1.mul hp.1 (hz.2 p)
  have hzpp : z * p ≤ p := (hzp.le_iff_mul_eq_left hp.1).mpr
    (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
  have hpz : z * p ≤ z := (hzp.le_iff_mul_eq_right hz.1).mpr
    (by rw [← mul_assoc, hz.1.isIdempotentElem.eq])
  have hwi (i : Fin n) : (w i).initial = z * p := by
    simp only [w, centralCutPartialIso_initial, hi]
  have hwf (i : Fin n) : (w i).final ≤ z := by
    apply ((w i).final_proj.le_iff_mul_eq_right hz.1).mpr
    simp only [w, centralCutPartialIso_final]
    rw [← mul_assoc, hz.1.isIdempotentElem.eq]
  have hwo (i j : Fin n) (hij : i ≠ j) : (w i).final * (w j).final = 0 := by
    simp only [w, centralCutPartialIso_final]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      ho i j hij, mul_zero]
  have hws : ∑ i, (w i).final = z := by
    simp only [w, centralCutPartialIso_final, ← Finset.mul_sum]
    rw [mul_sub, mul_one, sub_eq_zero] at hann
    exact hann.symm
  exact homogeneousCorner_of_columns hz.1 (HochschildTypeII.abelian_of_le hp hzp hzpp)
    hpz ⟨0, hn⟩ w hwi hwf hwo hws
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {n : ℕ} {p : M}

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_sum_projection (v : Fin n → PartialIso M)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    IsStarProjection (∑ i, (v i).final) :=
  orthogonal_projection_finset_sum (fun i => (v i).final) (fun i => (v i).final_proj)
    ho Finset.univ

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_mul_residual (v : Fin n → PartialIso M)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (i : Fin n) :
    (v i).final * (1 - ∑ j, (v j).final) = 0 := by
  classical
  rw [mul_sub, mul_one, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [(v i).final_proj.isIdempotentElem.eq, sub_self]
  · intro j _ hji
    exact ho i j hji.symm
  · simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma exists_append_columns (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (w : PartialIso M) (hwi : w.initial = p)
    (hwo : ∀ i, (v i).final * w.final = 0) :
    ∃ u : Fin (n + 1) → PartialIso M,
      (∀ i, (u i).initial = p) ∧
      (∀ i j, i ≠ j → (u i).final * (u j).final = 0) ∧
      (∑ i, (u i).final) = w.final + ∑ i, (v i).final := by
  let u : Fin (n + 1) → PartialIso M := Fin.cons w v
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    exact Fin.cases hwi hi i
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (h rfl).elim
    · intro _
      exact PartialIso.orthogonal_final_symm (hwo j)
    · intro _
      exact hwo i
    · intro h
      exact ho i j (fun he => h (congrArg Fin.succ he))
  · simp only [u, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma column_count_trace_le (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    (n : ℝ) * (τ p).re ≤ (τ 1).re := by
  have ht (i : Fin n) : τ (v i).final = τ p := by
    change τ ((v i : M) * star (v i : M)) = τ p
    rw [htr]
    exact congrArg τ (hi i)
  have h := Complex.re_le_re (τ.monotone (column_sum_projection v ho).le_one)
  change (τ.toLinearMap (∑ i, (v i).final)).re ≤ (τ 1).re at h
  rw [map_sum] at h
  change Complex.reCLM (∑ i, τ (v i).final) ≤ (τ 1).re at h
  rw [map_sum] at h
  simpa only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Complex.reCLM_apply] using h
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

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma popa_abelian_of_finitePath {p : M} (hp : AbelianProjection p) :
    PopaTypeII.AbelianProjection hp.1 := by
  have hc (a : PopaCorner.algebra hp.1) : p * (a : M) * p = (a : M) := by
    rw [a.property.1, a.property.2]
  intro a b
  apply Subtype.ext
  change (a : M) * (b : M) = (b : M) * (a : M)
  simpa only [hc] using (hp.2 (a : M) (b : M)).eq

omit [PartialOrder M] [StarOrderedRing M] in
lemma abelian_partialIso (v : PartialIso M) (hp : AbelianProjection v.initial) :
    AbelianProjection v.final :=
  finitePath_abelian_of_popa v.final_proj
    (abelianProjection_partialIso v (popa_abelian_of_finitePath hp))
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem extend_columns_of_no_homogeneous_piece (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : ∀ z : M, CentralProjection z → z ≠ 0 → ¬ HomogeneousTypeICorner z)
    {p : M} (hp : AbelianProjection p) (hpfull : IsCentralSupport p 1)
    {n : ℕ} (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    ∃ w : PartialIso M, w.initial = p ∧ w.final ≤ 1 - ∑ i, (v i).final := by
  let r := 1 - ∑ i, (v i).final
  have hr : IsStarProjection r := (column_sum_projection v ho).one_sub
  obtain ⟨t, ht⟩ := exists_central_support e hr
  have ht1 : t = 1 := by
    by_contra ht1
    have hz : CentralProjection (1 - t) :=
      ⟨ht.1.1.one_sub, fun a => (Commute.one_left a).sub_left (ht.1.2 a)⟩
    have hz0 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    apply hno (1 - t) hz hz0
    apply homogeneousCorner_of_annihilated_residual hp hz hz0 v hi ho
    change (1 - t) * r = 0
    rw [sub_mul, one_mul, (hr.le_iff_mul_eq_right ht.1.1).mp ht.2.1, sub_self]
  have hrfull : IsCentralSupport r 1 := by simpa only [ht1] using ht
  obtain ⟨z, u, hz, hui, huf, hzf, hzi⟩ := trace_free_central_comparison e hp.1 hr
  by_cases hz0 : z = 0
  · refine ⟨u, ?_, huf⟩
    simpa only [hz0, sub_zero, one_mul] using hzi
  exfalso
  apply hno z hz hz0
  let c := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) u
  have hci : c.initial ≤ p := by
    apply le_trans _ hui
    apply (c.initial_proj.le_iff_mul_eq_left u.initial_proj).mpr
    simp only [c, centralCutPartialIso_initial, mul_assoc, u.initial_proj.isIdempotentElem.eq]
  have hcf : c.final = z * r := by
    simpa only [c, centralCutPartialIso_final] using hzf
  have habelr : AbelianProjection (z * r) := by
    rw [← hcf]
    exact abelian_partialIso c (HochschildTypeII.abelian_of_le hp c.initial_proj hci)
  have hzp : IsStarProjection (z * p) := hz.1.mul hp.1 (hz.2 p)
  have hzple : z * p ≤ p := (hzp.le_iff_mul_eq_left hp.1).mpr
    (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
  have habelp := HochschildTypeII.abelian_of_le hp hzp hzple
  obtain ⟨w, hwi, hwf⟩ := abelian_equivalent_of_central_support e habelp habelr
    (hpfull.centralCut_one hp.1 hz) (hrfull.centralCut_one hr hz)
  let a (i : Fin n) := centralCutPartialIso z hz.1 (fun b => (hz.2 b).eq) (v i)
  have hai (i : Fin n) : (a i).initial = z * p := by
    simp only [a, centralCutPartialIso_initial, hi]
  have hao (i j : Fin n) (hij : i ≠ j) : (a i).final * (a j).final = 0 := by
    simp only [a, centralCutPartialIso_final]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun b => (hz.2 b).eq),
      ho i j hij, mul_zero]
  have haw (i : Fin n) : (a i).final * w.final = 0 := by
    simp only [a, centralCutPartialIso_final, hwf]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun b => (hz.2 b).eq),
      column_mul_residual v ho i, mul_zero]
  obtain ⟨b, hbi, hbo, hbs⟩ := exists_append_columns a hai hao w hwi haw
  have hsum : ∑ i, (b i).final = z := by
    rw [hbs, hwf]
    simp only [a, centralCutPartialIso_final, ← Finset.mul_sum]
    change z * (1 - ∑ i, (v i).final) + z * ∑ i, (v i).final = z
    noncomm_ring
  apply homogeneousCorner_of_annihilated_residual habelp hz hz0 b hbi hbo
  rw [hsum]
  exact hz.1.mul_one_sub_self
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_homogeneous_piece_of_full_abelian_trace
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) (hfull : IsCentralSupport p 1) :
    ∃ z : M, CentralProjection z ∧ z ≠ 0 ∧ HomogeneousTypeICorner z := by
  classical
  by_contra hfail
  push Not at hfail
  have hno : ∀ z : M, CentralProjection z → z ≠ 0 → ¬ HomogeneousTypeICorner z := hfail
  have hpτ : τ p ≠ 0 := by
    intro hzero
    apply hp0
    apply hfaith p
    simpa only [hp.1.isSelfAdjoint.star_eq, hp.1.isIdempotentElem.eq] using hzero
  have hpτpos : 0 < (τ p).re := by
    have hn := Complex.nonneg_iff.mp (τ.map_nonneg hp.1.nonneg)
    have hne : (τ p).re ≠ 0 := by
      intro hzero
      apply hpτ
      apply Complex.ext
      · exact hzero
      · exact hn.2.symm
    exact lt_of_le_of_ne hn.1 (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_nat_gt ((τ 1).re / (τ p).re)
  have hbound : (τ 1).re < (N : ℝ) * (τ p).re := (div_lt_iff₀ hpτpos).mp hN
  have hcolumns (n : ℕ) : ∃ v : Fin n → PartialIso M,
      (∀ i, (v i).initial = p) ∧
      (∀ i j, i ≠ j → (v i).final * (v j).final = 0) := by
    induction n with
    | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨v, hi, ho⟩ := ih
      obtain ⟨w, hwi, hwf⟩ := extend_columns_of_no_homogeneous_piece e hno hp hfull v hi ho
      have hcross (i : Fin n) : (v i).final * w.final = 0 := by
        have he := (w.final_proj.le_iff_mul_eq_right (column_sum_projection v ho).one_sub).mp hwf
        calc
          _ = (v i).final * ((1 - ∑ j, (v j).final) * w.final) := by rw [he]
          _ = 0 := by rw [← mul_assoc, column_mul_residual v ho i, zero_mul]
      obtain ⟨u, hui, huo, _⟩ := exists_append_columns v hi ho w hwi hcross
      exact ⟨u, hui, huo⟩
  obtain ⟨v, hi, ho⟩ := hcolumns N
  exact (not_le_of_gt hbound) (column_count_trace_le τ htr v hi ho)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace HochschildMatrixSystems.MatrixSystem

variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N] {n : ℕ}

def mapEquiv (E : HochschildMatrixSystems.MatrixSystem M n) (φ : M ≃⋆ₐ[ℂ] N) :
    HochschildMatrixSystems.MatrixSystem N n where
  entry i j := φ (E.entry i j)
  star_entry i j := by rw [← map_star, E.star_entry]
  entry_mul i j k l := by rw [← map_mul, E.entry_mul]; split_ifs <;> simp
  sum_diagonal := by rw [← map_sum, E.sum_diagonal, map_one]

end HochschildMatrixSystems.MatrixSystem

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners HochschildMatrixSystems FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma abelian_map_equiv {N : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
    (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : AbelianProjection p) : AbelianProjection (φ p) :=
  finitePath_abelian_of_popa (hp.1.map φ)
    (abelianProjection_map_equiv φ hp.1 (popa_abelian_of_finitePath hp))

def projectionInCorner {z p : M} (hz : IsStarProjection z) (hp : IsStarProjection p)
    (hpz : p ≤ z) : Corner z hz := ⟨p, projection_mem_corner hz hp hpz⟩

lemma projectionInCorner_abelian {z p : M} (hz : IsStarProjection z)
    (hp : AbelianProjection p) (hpz : p ≤ z) :
    AbelianProjection (projectionInCorner hz hp.1 hpz) := by
  refine ⟨⟨Subtype.ext hp.1.isIdempotentElem.eq, Subtype.ext hp.1.isSelfAdjoint.star_eq⟩, ?_⟩
  intro a b
  exact Subtype.ext (hp.2 (a : M) (b : M)).eq

lemma centralSupport_in_corner {z p : M} (hz : IsStarProjection z)
    (hzc : ∀ a : M, z * a = a * z) (hp : IsStarProjection p) (h : IsCentralSupport p z) :
    IsCentralSupport (projectionInCorner hz hp h.2.1) (1 : Corner z hz) := by
  refine ⟨⟨IsStarProjection.one _, fun _ => Commute.one_left _⟩, ?_, ?_⟩
  · exact (show IsStarProjection (projectionInCorner hz hp h.2.1) from
      ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩).le_one
  · intro c hc hcp
    have hcM : CentralProjection (c : M) :=
      ⟨corner_projection_coe z hz hc.1,
        fun a => centralCorner_central hz hzc c (fun b => (hc.2 b).eq) a⟩
    have hcpM : (c : M) * p = 0 := congrArg Subtype.val hcp
    have hcz := h.2.2 (c : M) hcM hcpM
    have hc0 : c = 0 := by
      apply Subtype.ext
      change (c : M) = 0
      simpa only [c.property.2] using hcz
    simp only [hc0, zero_mul]

lemma homogeneousCorner_to_ambient {z : M} (hz : IsStarProjection z)
    (q : Corner z hz) (hq : HomogeneousTypeICorner q) :
    HomogeneousTypeICorner (q : M) := by
  obtain ⟨hqp, n, E, i, hi⟩ := hq
  let φ := nestedCornerEquiv hz q hqp
  exact ⟨corner_projection_coe z hz hqp, n, E.mapEquiv φ, i, abelian_map_equiv φ hi⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners FinitePathMain

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_homogeneous_piece_of_abelian_trace
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) :
    ∃ z : M, CentralProjection z ∧ z ≠ 0 ∧ HomogeneousTypeICorner z := by
  obtain ⟨c, hc⟩ := exists_central_support e hp.1
  have hc0 : c ≠ 0 := fun h => hp0 ((hc.eq_zero_iff hp.1).mpr h)
  let eC := cornerPredualEquiv c hc.1.1 e
  let τC := cornerTrace c hc.1.1 τ
  have hpC := projectionInCorner_abelian hc.1.1 hp hc.2.1
  have hpC0 : projectionInCorner hc.1.1 hp.1 hc.2.1 ≠ 0 :=
    fun h => hp0 (congrArg Subtype.val h)
  obtain ⟨q, hq, hq0, hhom⟩ := exists_homogeneous_piece_of_full_abelian_trace eC τC
    (cornerTrace_tracial c hc.1.1 τ htr) (cornerTrace_faithful c hc.1.1 τ hfaith hc0)
    hpC hpC0 (centralSupport_in_corner hc.1.1 (fun a => (hc.1.2 a).eq) hp.1 hc)
  exact ⟨(q : M), ⟨corner_projection_coe c hc.1.1 hq.1,
    fun a => centralCorner_central hc.1.1 (fun a => (hc.1.2 a).eq) q
      (fun b => (hq.2 b).eq) a⟩,
    (fun h => hq0 (Subtype.ext h)), homogeneousCorner_to_ambient hc.1.1 q hhom⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.exists_homogeneous_piece_of_abelian_trace.{u} := @OAI.BoundedHochschild.KadisonRingrose.exists_homogeneous_piece_of_abelian_trace.{u}
