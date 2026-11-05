-- Prove2me | solution 1 for OAI.BoundedHochschild.arbitrary_typeII_last_normal_primitive
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:12:15.718841+00:00
-- url     : https://prove2.me/submissions/3c5b689f-dbdc-4272-a1d0-9e843547887f

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_primitive_of_separable_normal_finite_paths
import Theorems.Thm_OAI_PopaCenter_exists_homogeneous_system
import Theorems.Thm_OAI_PopaTypeII_noAbelianCorners_of_matrices
import Theorems.Thm_OAI_PopaCenter_produced_finite_paths

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

theorem bounded_cochain_ultralimit {n : ℕ} (u : Ultrafilter I)
    (F : I → Cochain M n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i, ‖F i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧
      ∀ x, PredualTendsto e (fun i => F i x) u (G x) := by
  classical
  have hex (x : Fin n → M) : ∃ b : M, ‖b‖ ≤ C * ∏ k, ‖x k‖ ∧
      PredualTendsto e (fun i => F i x) u b :=
    exists_predual_ultralimit e u (fun i => F i x) _ (fun i =>
      (F i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hF i)
        (Finset.prod_nonneg (fun k _ => norm_nonneg (x k)))))
  choose b hb ht using hex
  let G₀ : MultilinearMap ℂ (fun _ : Fin n => M) M :=
    { toFun := b
      map_update_add' := fun x k a c => by
        apply predual_tendsto_unique e (ht (Function.update x k (a+c)))
        simpa only [ContinuousMultilinearMap.map_update_add] using
          predual_tendsto_add e (ht (Function.update x k a)) (ht (Function.update x k c))
      map_update_smul' := fun x k c a => by
        apply predual_tendsto_unique e (ht (Function.update x k (c • a)))
        simpa only [ContinuousMultilinearMap.map_update_smul] using
          predual_tendsto_smul e (ht (Function.update x k a)) c }
  exact ⟨G₀.mkContinuous C hb, G₀.mkContinuous_norm_le hC hb, ht⟩

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

lemma predual_tendsto_sum {a : I → J → M} {b : J → M} (l : Filter I) (s : Finset J)
    (h : ∀ j ∈ s, PredualTendsto e (fun i => a i j) l (b j)) :
    PredualTendsto e (fun i => ∑ j ∈ s, a i j) l (∑ j ∈ s, b j) := by
  intro z
  simpa only [map_sum,sum_apply] using
    tendsto_finsetSum s (fun j hj => h j hj z)
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
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

lemma norm_trace_le (a : A) : ‖τ a‖ ≤ ‖τ.toPreGNS a‖ := by
  have hin : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS a) = τ a := by
    simp [PositiveLinearMap.preGNS_inner_def]
  rw [← hin]
  have hone : ‖τ.toPreGNS 1‖ = 1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [hone,one_mul] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS 1) (τ.toPreGNS a)
end HochschildUltrapower
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
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include h1 htr

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]

end HochschildWalk

namespace BoundedHochschild
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_differential
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    {n : ℕ} {F : I → Cochain M n} {G : Cochain M n} {l : Filter I}
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x))
    (x : Fin (n+1) → M) :
    PredualTendsto e (fun i => differentialValue (F i) x) l (differentialValue G x) := by
  simp only [differentialValue]
  apply predual_tendsto_add e
  · apply predual_tendsto_add e
    · exact (hL (x 0)).tendsto e (ht _)
    · apply predual_tendsto_sum e l Finset.univ
      intro j _
      exact predual_tendsto_smul e (ht _) _
  · exact predual_tendsto_smul e ((hR (x (Fin.last n))).tendsto e (ht _)) _

theorem primitive_of_finite_exactness
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    {n : ℕ} (f : Cochain M (n+1)) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ E : Finset M, ∃ g : Cochain M n, ‖g‖ ≤ C ∧
      ∀ x : Fin (n+1) → M, (∀ i, x i ∈ E) → differentialValue g x = f x) :
    ∃ g : Cochain M n, ‖g‖ ≤ C ∧ ∀ x : Fin (n+1) → M, differentialValue g x = f x := by
  classical
  choose F hF hFE using hlocal
  let U : Ultrafilter (Finset M) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset M)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨g,hg,ht⟩ := bounded_cochain_ultralimit e U F C hC hF
  refine ⟨g,hg,fun x => ?_⟩
  have hd := predual_tendsto_differential e hL hR ht x
  have hex : (fun E => differentialValue (F E) x) =ᶠ[U] (fun _ => f x) := by
    apply hU
    filter_upwards [eventually_ge_atTop (Finset.univ.image x)] with E hE
    exact hFE E x fun i => hE (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  apply predual_tendsto_unique e hd
  intro z
  exact tendsto_const_nhds.congr' (hex.mono fun _ h => congrArg (fun a : M => e.symm a z) h.symm)
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
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]

structure ExpectedEmbedding (N M : Type*) [CStarAlgebra N] [CStarAlgebra M] where
  includeMap : N →L[ℂ] M
  expectMap : M →L[ℂ] N
  include_mul : ∀ a b, includeMap (a*b)=includeMap a*includeMap b
  include_one : includeMap 1=1
  include_star : ∀ a, includeMap (star a)=star (includeMap a)
  include_norm : ∀ a, ‖includeMap a‖=‖a‖
  expect_norm : ∀ a, ‖expectMap a‖ ≤ ‖a‖
  retract : ∀ a, expectMap (includeMap a)=a
  left_module : ∀ a x, expectMap (includeMap a*x)=a*expectMap x
  right_module : ∀ x a, expectMap (x*includeMap a)=expectMap x*a

namespace ExpectedEmbedding
variable (E : ExpectedEmbedding N M)

def restrict {n : ℕ} (f : Cochain M n) : Cochain N n :=
  E.expectMap.compContinuousMultilinearMap (f.compContinuousLinearMap (fun _ => E.includeMap))

def extend {n : ℕ} (g : Cochain N n) : Cochain M n :=
  E.includeMap.compContinuousMultilinearMap (g.compContinuousLinearMap (fun _ => E.expectMap))

@[simp] lemma restrict_apply {n : ℕ} (f : Cochain M n) (x : Fin n → N) :
    E.restrict f x=E.expectMap (f (fun i => E.includeMap (x i))) := rfl
@[simp] lemma extend_apply {n : ℕ} (g : Cochain N n) (x : Fin n → M) :
    E.extend g x=E.includeMap (g (fun i => E.expectMap (x i))) := rfl

lemma restrict_norm {n : ℕ} (f : Cochain M n) : ‖E.restrict f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  change ‖E.expectMap (f (fun i => E.includeMap (x i)))‖ ≤ _
  exact (E.expect_norm _).trans (by
    simpa only [E.include_norm] using (f.le_opNorm (fun i => E.includeMap (x i))))

lemma extend_norm {n : ℕ} (g : Cochain N n) : ‖E.extend g‖ ≤ ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  rw [extend_apply,E.include_norm]
  exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => E.expect_norm _)) (norm_nonneg _))

lemma merge_include {n : ℕ} (x : Fin (n+1) → N) (j : Fin n) :
    mergeInputs (fun i => E.includeMap (x i)) j =
      fun i => E.includeMap (mergeInputs x j i) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> simp only [E.include_mul]

lemma differential_restrict {n : ℕ} (f : Cochain M n) (x : Fin (n+1) → N) :
    differentialValue (E.restrict f) x =
      E.expectMap (differentialValue f (fun i => E.includeMap (x i))) := by
  simp only [differentialValue,restrict_apply,map_add,map_sum,map_smul,
    E.left_module,E.right_module,E.merge_include]

lemma restrict_cocycle {n : ℕ} (f : Cochain M n)
    (hf : ∀ x, differentialValue f x=0) :
    ∀ x, differentialValue (E.restrict f) x=0 := by
  intro x
  rw [E.differential_restrict,hf,map_zero]

lemma differential_extend_on_include {n : ℕ} (g : Cochain N n) (x : Fin (n+1) → N) :
    differentialValue (E.extend g) (fun i => E.includeMap (x i))=
      E.includeMap (differentialValue g x) := by
  simp only [differentialValue,extend_apply,E.merge_include,E.retract,map_add,map_sum,
    map_smul,E.include_mul]

theorem finite_exactness {n : ℕ} (f : Cochain M (n+1)) (g : Cochain N n)
    (hg : ∀ x, differentialValue g x=E.restrict f x)
    (S : Set M) (hS : ∀ a ∈ S, ∃ b, E.includeMap b=a)
    (hfS : ∀ x : Fin (n+1) → M, (∀ i, x i ∈ S) →
      ∃ b, E.includeMap b=f x)
    (x : Fin (n+1) → M) (hx : ∀ i, x i ∈ S) :
    differentialValue (E.extend g) x=f x := by
  classical
  choose y hy using fun i => hS (x i) (hx i)
  have hxy : (fun i => E.includeMap (y i))=x := funext hy
  obtain ⟨a,ha⟩ := hfS x hx
  rw [← hxy,E.differential_extend_on_include,hg,restrict_apply,hxy,← ha,E.retract]
end ExpectedEmbedding
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

open scoped ComplexOrder
namespace HochschildTraceNorm
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b)=τ (b*a))

def traceCLM : A →L[ℂ] ℂ where
  toLinearMap := τ.toLinearMap
  cont := map_continuous τ

@[simp] lemma traceCLM_apply (a : A) : traceCLM τ a=τ a := rfl

include htr in
lemma positive_weight_trace_bound (a x : A) (ha : 0 ≤ a) :
    ‖τ (a*x)‖ ≤ (τ a).re * ‖x‖ := by
  let r := CFC.sqrt a
  have hr : IsSelfAdjoint r := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have hrr : r*r=a := CFC.sqrt_mul_sqrt_self a ha
  have hin : inner ℂ (τ.toPreGNS r) (τ.toPreGNS (x*r)) = τ (a*x) := by
    simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,hr.star_eq]
    rw [htr r (x*r),mul_assoc,hrr,htr x a]
  have hh : ‖τ.toPreGNS r‖^2=(τ a).re := by
    have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS r))
    simpa only [← Complex.ofReal_pow,Complex.ofReal_re,
      PositiveLinearMap.ofPreGNS_toPreGNS,hr.star_eq,hrr] using h
  calc
    _ = ‖inner ℂ (τ.toPreGNS r) (τ.toPreGNS (x*r))‖ := congrArg norm hin.symm
    _ ≤ ‖τ.toPreGNS r‖*‖τ.toPreGNS (x*r)‖ := norm_inner_le_norm _ _
    _ ≤ ‖τ.toPreGNS r‖*(‖x‖*‖τ.toPreGNS r‖) :=
      mul_le_mul_of_nonneg_left (preGNS_norm_mul_le τ x r) (norm_nonneg _)
    _ = (τ a).re*‖x‖ := by rw [← hh]; ring

include htr in

lemma trace_pair_bound (b x : A) :
    ‖τ (b*x)‖ ≤ (τ (CFC.abs b)).re * ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro η hη
  let C := ‖(traceCLM τ)‖*‖x‖
  let ε := η/(C+1)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hε : 0 < ε := div_pos hη (by positivity)
  obtain ⟨v,hv,he,_⟩ := exists_approx_polar b ε hε
  have hdiff : ‖τ ((b-v*CFC.abs b)*x)‖ ≤ C*ε := by
    apply ((traceCLM τ).le_opNorm _).trans
    have ht := (norm_mul_le (b-v*CFC.abs b) x).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg x))
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (by dsimp [C]; ring)
  have hmain : ‖τ (v*CFC.abs b*x)‖ ≤ (τ (CFC.abs b)).re * ‖x‖ := by
    have heq : τ (v*CFC.abs b*x)=τ (CFC.abs b*(x*v)) := by
      rw [mul_assoc,htr v (CFC.abs b*x),mul_assoc]
    rw [heq]
    apply (positive_weight_trace_bound τ htr _ _ (CFC.abs_nonneg b)).trans
    apply mul_le_mul_of_nonneg_left _ (τ.map_nonneg (CFC.abs_nonneg b)).1
    simpa only [mul_one] using (norm_mul_le x v).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg x))
  have hsum : τ (b*x)=τ ((b-v*CFC.abs b)*x)+τ (v*CFC.abs b*x) := by
    rw [← map_add,← add_mul,sub_add_cancel]
  rw [hsum]
  apply (norm_add_le _ _).trans
  have hεeq : ε*(C+1)=η := div_mul_cancel₀ _ (by positivity)
  linarith [add_le_add hdiff hmain]

def tracePair (b : A) : A →L[ℂ] ℂ :=
  (traceCLM τ).comp (ContinuousLinearMap.mul ℂ A b)

@[simp] lemma tracePair_apply (b x : A) : tracePair τ b x=τ (b*x) := rfl

include htr in

theorem norm_tracePair (b : A) : ‖tracePair τ b‖=(τ (CFC.abs b)).re := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (τ.map_nonneg (CFC.abs_nonneg b)).1
    exact trace_pair_bound τ htr b
  · apply le_of_forall_pos_le_add
    intro η hη
    let C := ‖(traceCLM τ)‖
    let ε := η/(C+1)
    have hC : 0 ≤ C := norm_nonneg _
    have hε : 0 < ε := div_pos hη (by positivity)
    obtain ⟨v,hv,_,he⟩ := exists_approx_polar b ε hε
    have hτpos := τ.map_nonneg (CFC.abs_nonneg b)
    have hτreal : (τ (CFC.abs b)).re=‖τ (CFC.abs b)‖ := by
      have heq : τ (CFC.abs b) = ((τ (CFC.abs b)).re : ℂ) := by
        exact Complex.ext rfl hτpos.2.symm
      rw [heq]
      exact (Complex.norm_of_nonneg hτpos.1).symm
    rw [hτreal]
    have hdiff : ‖τ (CFC.abs b-star v*b)‖ ≤ C*ε :=
      ((traceCLM τ).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left he hC)
    have hmain : ‖τ (star v*b)‖ ≤ ‖tracePair τ b‖ := by
      rw [htr]
      exact ((tracePair τ b).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (by simpa only [norm_star] using hv) (norm_nonneg _)).trans_eq (mul_one _))
    have hsum : τ (CFC.abs b)=τ (CFC.abs b-star v*b)+τ (star v*b) := by
      rw [← map_add,sub_add_cancel]
    rw [hsum]
    apply (norm_add_le _ _).trans
    have hεeq : ε*(C+1)=η := div_mul_cancel₀ _ (by positivity)
    linarith [add_le_add hdiff hmain]
end HochschildTraceNorm

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTraceNorm
variable {N X : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (τ : N →ₚ[ℂ] ℂ)

omit [PartialOrder N] [StarOrderedRing N] in
lemma predual_vector_ext (z w : X) (h : ∀ a : N, e.symm a z=e.symm a w) : z=w := by
  apply (NormedSpace.inclusionInDoubleDualLi ℂ).injective
  ext f
  change f z=f w
  simpa only [e.symm_apply_apply] using h (e f)

variable (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
  (hτ : TraceInPredual e τ)

omit [StarOrderedRing N] in
include hL hτ in
lemma exists_trace_vector (b : N) : ∃ z : X, ∀ a : N, e.symm a z=star (τ (star b*a)) := by
  obtain ⟨z,hz⟩ := hτ
  obtain ⟨w,hw⟩ := hL (star b) z
  refine ⟨w,fun a => ?_⟩
  rw [hz,star_star,← hw]
  rfl

def traceVector (b : N) : X := Classical.choose (exists_trace_vector e τ hL hτ b)

omit [StarOrderedRing N] in
lemma traceVector_spec (b a : N) : e.symm a (traceVector e τ hL hτ b)=star (τ (star b*a)) :=
  Classical.choose_spec (exists_trace_vector e τ hL hτ b) a

def traceVectorLinear : N →ₗ[ℂ] X where
  toFun := traceVector e τ hL hτ
  map_add' b c := by
    apply predual_vector_ext e
    intro a
    simp only [map_add,traceVector_spec,star_add,add_mul]
  map_smul' r b := by
    apply predual_vector_ext e
    intro a
    simp only [traceVector_spec,map_smul,star_smul,smul_mul_assoc,star_star,RingHom.id_apply]

omit [StarOrderedRing N] in
@[simp] lemma traceVectorLinear_apply (b : N) :
    traceVectorLinear e τ hL hτ b=traceVector e τ hL hτ b := rfl

lemma norm_traceVector (b : N) :
    ‖traceVector e τ hL hτ b‖=‖tracePair τ (star b)‖ := by
  apply le_antisymm
  · apply NormedSpace.norm_le_dual_bound ℂ _ (norm_nonneg _)
    intro f
    have hs := congrArg norm (traceVector_spec e τ hL hτ b (e f))
    simp only [e.symm_apply_apply,norm_star] at hs
    rw [hs]
    simpa only [e.norm_map,tracePair_apply] using (tracePair τ (star b)).le_opNorm (e f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    have hs := congrArg norm (traceVector_spec e τ hL hτ b a)
    simp only [norm_star] at hs
    change ‖τ (star b*a)‖ ≤ _
    rw [← hs]
    simpa only [e.symm.norm_map,mul_comm] using (e.symm a).le_opNorm (traceVector e τ hL hτ b)

omit [StarOrderedRing N] in
lemma traceVector_injective (hfaith : ∀ b : N, τ (star b*b)=0 → b=0) :
    Function.Injective (traceVectorLinear e τ hL hτ) := by
  intro b c hbc
  have hb : traceVector e τ hL hτ (b-c)=0 := by
    change traceVectorLinear e τ hL hτ (b-c)=0
    rw [map_sub,hbc,sub_self]
  apply sub_eq_zero.mp
  apply hfaith
  have hs := traceVector_spec e τ hL hτ (b-c) (b-c)
  rw [hb,map_zero] at hs
  exact star_eq_zero.mp hs.symm

end BoundedHochschild

open scoped ComplexOrder
namespace HochschildTraceNorm
variable {N M : Type*} [CStarAlgebra N] [CStarAlgebra M]
  [PartialOrder N] [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M]

lemma map_cstar_abs (I : N →⋆ₐ[ℂ] M) (b : N) : I (CFC.abs b)=CFC.abs (I b) := by
  symm
  apply CFC.sqrt_unique _ (map_nonneg I (CFC.abs_nonneg b))
  rw [← map_mul,CFC.abs_mul_abs,map_mul,map_star]

variable (τN : N →ₚ[ℂ] ℂ) (τM : M →ₚ[ℂ] ℂ)
  (htrN : ∀ a b : N, τN (a*b)=τN (b*a)) (htrM : ∀ a b : M, τM (a*b)=τM (b*a))

include htrN htrM in
lemma norm_tracePair_embedding (I : N →⋆ₐ[ℂ] M) (hp : ∀ a : N, τM (I a)=τN a) (b : N) :
    ‖tracePair τM (I b)‖=‖tracePair τN b‖ := by
  rw [norm_tracePair τM htrM,norm_tracePair τN htrN,← map_cstar_abs,hp]

end HochschildTraceNorm

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTraceNorm
variable {N M X : Type*} [CStarAlgebra N] [CStarAlgebra M]
  [PartialOrder N] [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
  (τN : N →ₚ[ℂ] ℂ) (τM : M →ₚ[ℂ] ℂ)
  (htrN : ∀ a b : N, τN (a*b)=τN (b*a)) (htrM : ∀ a b : M, τM (a*b)=τM (b*a))
  (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
  (hτ : TraceInPredual e τN) (hfaith : ∀ b : N, τN (star b*b)=0 → b=0)
  (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b)

include htrN htrM hL hτ hfaith hp in

theorem exists_trace_expectation_value (x : M) :
    ∃ y : N, ‖y‖ ≤ ‖x‖ ∧ ∀ b : N, τN (star b*y)=τM (star (I b)*x) := by
  let J := traceVectorLinear e τN hL hτ
  let j : N ≃ₗ[ℂ] LinearMap.range J := LinearEquiv.ofInjective J
    (traceVector_injective e τN hL hτ hfaith)
  let L : N →ₗ[ℂ] ℂ := {
    toFun := fun b => star (τM (star (I b)*x))
    map_add' := fun b c => by simp only [map_add,star_add,add_mul]
    map_smul' := fun r b => by
      simp only [map_smul,star_smul,smul_mul_assoc,star_star,RingHom.id_apply] }
  let L0 : LinearMap.range J →ₗ[ℂ] ℂ := L.comp j.symm.toLinearMap
  have hbound (z : LinearMap.range J) : ‖L0 z‖ ≤ ‖x‖*‖z‖ := by
    let b := j.symm z
    have hj : J b=(z:X) := congrArg Subtype.val (j.apply_symm_apply z)
    change ‖star (τM (star (I b)*x))‖ ≤ _
    rw [norm_star,← map_star I]
    calc
      _ = ‖tracePair τM (I (star b)) x‖ := rfl
      _ ≤ ‖tracePair τM (I (star b))‖*‖x‖ := (tracePair τM (I (star b))).le_opNorm x
      _ = ‖tracePair τN (star b)‖*‖x‖ := by rw [norm_tracePair_embedding τN τM htrN htrM I hp]
      _ = ‖traceVector e τN hL hτ b‖*‖x‖ := by rw [norm_traceVector]
      _ = ‖x‖*‖z‖ := by change ‖J b‖*‖x‖=‖x‖*‖z‖; rw [hj]; exact mul_comm _ _
  let f := L0.mkContinuous ‖x‖ hbound
  obtain ⟨F,hF,hFn⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨e F,?_,fun b => ?_⟩
  · rw [e.norm_map,hFn]
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg x) _
  · apply star_injective
    rw [← traceVector_spec e τN hL hτ b (e F),e.symm_apply_apply]
    change F (J b) = _
    calc
      _ = f (j b) := hF (j b)
      _ = L (j.symm (j b)) := rfl
      _ = star (τM (star (I b)*x)) := by rw [j.symm_apply_apply]; rfl

omit [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M] in
include hfaith in
lemma trace_pair_separates (y z : N)
    (h : ∀ b : N, τN (star b*y)=τN (star b*z)) : y=z := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,h,sub_self]

end BoundedHochschild

open scoped ComplexOrder
namespace BoundedHochschild
variable {N M X : Type*} [CStarAlgebra N] [CStarAlgebra M]
  [PartialOrder N] [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
  (τN : N →ₚ[ℂ] ℂ) (τM : M →ₚ[ℂ] ℂ)

theorem exists_expected_embedding
    (htrN : ∀ a b : N, τN (a*b)=τN (b*a)) (htrM : ∀ a b : M, τM (a*b)=τM (b*a))
    (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
    (hτ : TraceInPredual e τN) (hfaith : ∀ b : N, τN (star b*b)=0 → b=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b)
    (hI : ∀ b : N, ‖I b‖=‖b‖) :
    ∃ E : ExpectedEmbedding N M, (∀ b : N, E.includeMap b=I b) ∧
      ∀ x : M, ∀ b : N, τN (star b*E.expectMap x)=τM (star (I b)*x) := by
  choose E hEn hE using exists_trace_expectation_value e τN τM htrN htrM hL hτ hfaith I hp
  have hadd (x y : M) : E (x+y)=E x+E y := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE,mul_add,map_add,mul_add,map_add,hE,hE]
  have hsmul (r : ℂ) (x : M) : E (r • x)=r • E x := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE,mul_smul_comm,map_smul,mul_smul_comm,map_smul,hE]
  let El : M →ₗ[ℂ] N := {
    toFun := E
    map_add' := hadd
    map_smul' := hsmul }
  let Ec : M →L[ℂ] N := El.mkContinuous 1 (fun x => by change ‖E x‖ ≤ (1:ℝ)*‖x‖; simpa only [one_mul] using hEn x)
  let Ic : N →L[ℂ] M := I.toAlgHom.toLinearMap.mkContinuous 1
    (fun b => by change ‖I b‖ ≤ (1:ℝ)*‖b‖; rw [one_mul,hI])
  have hretract (a : N) : E (I a)=a := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE,← map_star I,← map_mul,hp]
  have hleft (a : N) (x : M) : E (I a*x)=a*E x := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE]
    calc
      τM (star (I b)*(I a*x)) = τM (star (I (star a*b))*x) := by
        simp only [map_mul,map_star,star_mul,star_star,mul_assoc]
      _ = τN (star (star a*b)*E x) := (hE x (star a*b)).symm
      _ = τN (star b*(a*E x)) := by simp only [star_mul,star_star,mul_assoc]
  have hright (x : M) (a : N) : E (x*I a)=E x*a := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE]
    calc
      τM (star (I b)*(x*I a)) = τM (I a*(star (I b)*x)) := by
        rw [← mul_assoc,htrM]
      _ = τM (star (I (b*star a))*x) := by
        simp only [map_mul,map_star,star_mul,star_star,mul_assoc]
      _ = τN (star (b*star a)*E x) := (hE x (b*star a)).symm
      _ = τN (star b*(E x*a)) := by
        simp only [star_mul,star_star]
        rw [mul_assoc,htrN a (star b*E x),mul_assoc]
  refine ⟨{
    includeMap := Ic
    expectMap := Ec
    include_mul := fun a b => map_mul I a b
    include_one := map_one I
    include_star := fun a => map_star I a
    include_norm := hI
    expect_norm := hEn
    retract := hretract
    left_module := hleft
    right_module := hright },fun _ => rfl,hE⟩
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
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildRare
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

omit [StarOrderedRing M] in

lemma denseRange_traceVector (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    DenseRange (traceVectorLinear e τ hL hτ) := by
  let J := traceVectorLinear e τ hL hτ
  let S := (LinearMap.range J).topologicalClosure
  let : IsClosed (S : Set X) := (LinearMap.range J).isClosed_topologicalClosure
  have hzero (f : StrongDual ℂ X) (hf : ∀ b : M, f (J b)=0) : f=0 := by
    have ha : e f=0 := by
      apply hfaith
      apply star_eq_zero.mp
      rw [← traceVector_spec e τ hL hτ (e f) (e f), e.symm_apply_apply]
      exact hf (e f)
    exact e.injective (ha.trans (map_zero e).symm)
  change Dense (Set.range J)
  rw [← LinearMap.coe_range]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro f
  have hf : f.comp S.mkQL=0 := by
    apply hzero
    intro b
    have hb : J b ∈ S := (LinearMap.range J).le_topologicalClosure ⟨b,rfl⟩
    have hh : (Submodule.Quotient.mk (p := S) (J b) : X ⧸ S)=0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hb
    change f (Submodule.Quotient.mk (J b))=0
    rw [hh,map_zero]
  exact congrArg (fun F : StrongDual ℂ X => F z) hf

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M N X Y : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)
  (τM : M →ₚ[ℂ] ℂ) (τN : N →ₚ[ℂ] ℂ)
  (hLM : ∀ b : M, HasPreadjoint eM (ContinuousLinearMap.mul ℂ M b))
  (hLN : ∀ b : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N b))
  (hτM : TraceInPredual eM τM) (hτN : TraceInPredual eN τN)

omit [StarOrderedRing M] [StarOrderedRing N] in
include hLM hLN hτM hτN in

theorem exists_preadjoint_of_trace_adjoint
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (A : M →L[ℂ] N) (B : N →L[ℂ] M)
    (hadj : ∀ a b, τN (star b*A a)=τM (star (B b)*a)) :
    ∃ P : Y →L[ℂ] X, ‖P‖ ≤ ‖A‖ ∧
      ∀ a z, eN.symm (A a) z=eM.symm a (P z) := by
  let JM := traceVectorLinear eM τM hLM hτM
  let JN := traceVectorLinear eN τN hLN hτN
  let F := JM.comp B.toLinearMap
  have hd : DenseRange JN := denseRange_traceVector eN τN hLN hτN hfaithN
  have hb (b : N) : ‖F b‖ ≤ ‖A‖*‖JN b‖ := by
    apply NormedSpace.norm_le_dual_bound ℂ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro f
    have hs : f (F b)=eN.symm (A (eM f)) (JN b) := by
      change f (traceVector eM τM hLM hτM (B b))=_
      have hs0 := traceVector_spec eM τM hLM hτM (B b) (eM f)
      simp only [eM.symm_apply_apply] at hs0
      rw [hs0]
      change _=eN.symm (A (eM f)) (traceVector eN τN hLN hτN b)
      rw [traceVector_spec,hadj]
    rw [hs]
    calc
      _ ≤ ‖eN.symm (A (eM f))‖*‖JN b‖ := (eN.symm (A (eM f))).le_opNorm _
      _ = ‖A (eM f)‖*‖JN b‖ := by rw [eN.symm.norm_map]
      _ ≤ (‖A‖*‖eM f‖)*‖JN b‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
      _ = (‖A‖*‖JN b‖)*‖f‖ := by rw [eM.norm_map]; ring
  let P : Y →L[ℂ] X := F.extendOfNorm JN
  refine ⟨P,LinearMap.opNorm_extendOfNorm_le hd (norm_nonneg _) hb,fun a z => ?_⟩
  have heq : (fun z => eN.symm (A a) z)=(fun z => eM.symm a (P z)) := by
    apply hd.equalizer (eN.symm (A a)).continuous ((eM.symm a).continuous.comp P.continuous)
    funext b
    change eN.symm (A a) (JN b)=eM.symm a (F.extendOfNorm JN (JN b))
    rw [LinearMap.extendOfNorm_eq hd ⟨‖A‖,hb⟩]
    change eN.symm (A a) (traceVector eN τN hLN hτN b)=
      eM.symm a (traceVector eM τM hLM hτM (B b))
    rw [traceVector_spec,traceVector_spec,hadj]
  exact congrFun heq z

omit [StarOrderedRing M] in
include hLM hτM in

lemma right_hasPreadjoint_of_left
    (hfaith : ∀ a : M, τM (star a*a)=0 → a=0)
    (htr : ∀ a b : M, τM (a*b)=τM (b*a))
    (b : M) : HasPreadjoint eM ((ContinuousLinearMap.mul ℂ M).flip b) := by
  obtain ⟨P,_,hP⟩ := exists_preadjoint_of_trace_adjoint eM eM τM τM hLM hLM hτM hτM
    hfaith ((ContinuousLinearMap.mul ℂ M).flip b)
    ((ContinuousLinearMap.mul ℂ M).flip (star b)) (by
      intro a c
      change τM (star c*(a*b))=τM (star (c*star b)*a)
      simp only [star_mul,star_star]
      rw [← mul_assoc,htr,mul_assoc])
  intro z
  exact ⟨P z,fun a => hP a z⟩

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M N X Y : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
variable (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)
  (τM : M →ₚ[ℂ] ℂ) (τN : N →ₚ[ℂ] ℂ)

omit [StarOrderedRing M] [StarOrderedRing N] in
lemma trace_preserving_norm
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b) (b : N) :
    ‖I b‖=‖b‖ := by
  apply NonUnitalStarAlgHom.norm_map I
  intro a c hac
  apply sub_eq_zero.mp
  apply hfaithN
  rw [← hp,map_mul,map_star,map_sub,hac,sub_self,star_zero,zero_mul,map_zero]

theorem exists_normal_expected_embedding
    (htrM : ∀ a b : M, τM (a*b)=τM (b*a)) (htrN : ∀ a b : N, τN (a*b)=τN (b*a))
    (hLM : ∀ b : M, HasPreadjoint eM (ContinuousLinearMap.mul ℂ M b))
    (hLN : ∀ b : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N b))
    (hτM : TraceInPredual eM τM) (hτN : TraceInPredual eN τN)
    (hfaithM : ∀ a : M, τM (star a*a)=0 → a=0)
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b) :
    ∃ E : ExpectedEmbedding N M, (∀ b : N, E.includeMap b=I b) ∧
      (∀ x : M, ∀ b : N, τN (star b*E.expectMap x)=τM (star (I b)*x)) ∧
      (∃ P : Y →L[ℂ] X, ‖P‖ ≤ 1 ∧ ∀ a z, eN.symm (E.expectMap a) z=eM.symm a (P z)) ∧
      (∃ Q : X →L[ℂ] Y, ‖Q‖ ≤ 1 ∧ ∀ a z, eM.symm (E.includeMap a) z=eN.symm a (Q z)) := by
  have hI := trace_preserving_norm τM τN hfaithN I hp
  obtain ⟨E,hEi,hE⟩ := exists_expected_embedding eN τN τM htrN htrM hLN hτN hfaithN I hp hI
  have hEn : ‖E.expectMap‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simpa only [one_mul] using E.expect_norm x)
  have hIn : ‖E.includeMap‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by rw [one_mul,E.include_norm])
  obtain ⟨P,hPn,hP⟩ := exists_preadjoint_of_trace_adjoint eM eN τM τN
    hLM hLN hτM hτN hfaithN E.expectMap E.includeMap (by
      intro a b
      rw [hEi,hE])
  obtain ⟨Q,hQn,hQ⟩ := exists_preadjoint_of_trace_adjoint eN eM τN τM
    hLN hLM hτN hτM hfaithM E.includeMap E.expectMap (by
      intro a b
      have hh := congrArg star (hE b a)
      simp only [← map_star,star_mul,star_star] at hh
      rw [hEi]
      exact hh.symm)
  exact ⟨E,hEi,hE,⟨P,hPn.trans hEn,hP⟩,⟨Q,hQn.trans hIn,hQ⟩⟩

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M N X Y : Type*} [CStarAlgebra M] [CStarAlgebra N]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)

namespace ExpectedEmbedding
variable (E : ExpectedEmbedding N M)

lemma restrict_curryRight {n : ℕ} (f : Cochain M (n+1))
    (a : Fin n → N) (b : N) :
    (E.restrict f).curryRight a b =
      E.expectMap (f.curryRight (fun i => E.includeMap (a i)) (E.includeMap b)) := by
  simp only [ContinuousMultilinearMap.curryRight_apply,restrict_apply]
  congr 2
  funext i
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]
  | cast i => simp only [Fin.snoc_castSucc]

lemma restrict_last_normal
    (P : Y →L[ℂ] X) (hP : ∀ a z, eN.symm (E.expectMap a) z=eM.symm a (P z))
    (Q : X →L[ℂ] Y) (hQ : ∀ a z, eM.symm (E.includeMap a) z=eN.symm a (Q z))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ a : Fin n → M, HasPreadjoint eM (f.curryRight a)) :
    ∀ a : Fin n → N, HasPreadjoint eN ((E.restrict f).curryRight a) := by
  intro a z
  obtain ⟨w,hw⟩ := hf (fun i => E.includeMap (a i)) (P z)
  refine ⟨Q w,fun b => ?_⟩
  rw [E.restrict_curryRight,hP,hw,hQ]

end ExpectedEmbedding

section FiniteExactness
variable [PartialOrder M] [StarOrderedRing M] [PartialOrder N] [StarOrderedRing N]
  [CompleteSpace X] [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
variable (τM : M →ₚ[ℂ] ℂ) (τN : N →ₚ[ℂ] ℂ)

theorem finite_exactness_of_separable_subalgebra
    (h1N : τN 1=1)
    (htrM : ∀ a b : M, τM (a*b)=τM (b*a)) (htrN : ∀ a b : N, τN (a*b)=τN (b*a))
    (hLM : ∀ b : M, HasPreadjoint eM (ContinuousLinearMap.mul ℂ M b))
    (hLN : ∀ b : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N b))
    (hτM : TraceInPredual eM τM) (hτN : TraceInPredual eN τN)
    (hfaithM : ∀ a : M, τM (star a*a)=0 → a=0)
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b)
    (hpaths : HochschildRare.FinitePathTests τN)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint eM (f.curryRight a))
    (S : Set M) (hS : ∀ a ∈ S, ∃ b, I b=a)
    (hfS : ∀ x : Fin (n+1) → M, (∀ i, x i ∈ S) → ∃ b, I b=f x) :
    ∃ G : Cochain M n, ‖G‖ ≤ ‖f‖ ∧
      ∀ x : Fin (n+1) → M, (∀ i, x i ∈ S) → differentialValue G x=f x := by
  obtain ⟨E,hEi,hE,⟨P,_,hP⟩,⟨Q,_,hQ⟩⟩ := exists_normal_expected_embedding
    eM eN τM τN htrM htrN hLM hLN hτM hτN hfaithM hfaithN I hp
  have hRN := right_hasPreadjoint_of_left eN τN hLN hτN hfaithN htrN
  obtain ⟨g,hgn,hg⟩ := primitive_of_separable_normal_finite_paths eN τN h1N htrN
    hfaithN hLN hRN hτN hpaths (E.restrict f) (E.restrict_cocycle f hf)
    (E.restrict_last_normal eM eN P hP Q hQ f hnormal)
  refine ⟨E.extend g,(E.extend_norm g).trans (hgn.trans (E.restrict_norm f)),?_⟩
  apply E.finite_exactness f g hg S
  · intro a ha
    obtain ⟨b,hb⟩ := hS a ha
    exact ⟨b,(hEi b).trans hb⟩
  · intro x hx
    obtain ⟨b,hb⟩ := hfS x hx
    exact ⟨b,(hEi b).trans hb⟩
end FiniteExactness
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

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

omit [CompleteSpace X] in
lemma traceVector_star_pairing (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (a b : M) :
    e.symm (star a) (traceVector e τ hL hτ b)=
      star (e.symm a (traceVector e τ hL hτ (star b))) := by
  rw [traceVector_spec,traceVector_spec,star_star,star_star,← map_star,star_mul,
    star_star,star_star,htr]

include hL hτ in

theorem exists_star_preadjoint (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) :
    ∃ P : X →L⋆[ℂ] X, ‖P‖ ≤ 1 ∧
      ∀ a z, e.symm (star a) z=star (e.symm a (P z)) := by
  let J := traceVectorLinear e τ hL hτ
  let F : M →ₗ⋆[ℂ] X := J.comp (starLinearEquiv ℂ).toLinearMap
  have hd : DenseRange J := denseRange_traceVector e τ hL hτ hfaith
  have hb (b : M) : ‖F b‖ ≤ 1*‖J b‖ := by
    rw [one_mul]
    apply NormedSpace.norm_le_dual_bound ℂ _ (norm_nonneg _)
    intro f
    have hs := traceVector_star_pairing e τ hL hτ htr (e f) b
    simp only [e.symm_apply_apply] at hs
    have hn := congrArg norm hs
    simp only [norm_star] at hn
    change ‖f (traceVector e τ hL hτ (star b))‖ ≤ _
    rw [← hn]
    simpa only [e.symm.norm_map,norm_star,e.norm_map,mul_comm,J,traceVectorLinear_apply] using
      (e.symm (star (e f))).le_opNorm (J b)
  let P : X →L⋆[ℂ] X := F.extendOfNorm J
  refine ⟨P,LinearMap.opNorm_extendOfNorm_le hd zero_le_one hb,fun a z => ?_⟩
  have heq : (fun z => e.symm (star a) z)=(fun z => star (e.symm a (P z))) := by
    apply hd.equalizer (e.symm (star a)).continuous
      (((e.symm a).continuous.comp P.continuous).star)
    funext b
    change e.symm (star a) (traceVector e τ hL hτ b)=
      star (e.symm a (F.extendOfNorm J (J b)))
    rw [LinearMap.extendOfNorm_eq hd ⟨1,hb⟩]
    exact traceVector_star_pairing e τ hL hτ htr a b
  exact congrFun heq z
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
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end Hilbert

omit [StarOrderedRing M] in
lemma trace_conjugate (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (u : unitary M) (a : M) : τ (conjugate u a)=τ a := by
  rw [conjugate_apply,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]
end HochschildDixmier
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

lemma weakEquiv_symm_continuous : Continuous (weakEquiv e).symm :=
  NormedSpace.Dual.toWeakDual_continuous.comp e.symm.continuous

lemma normal_continuous (A : M →L[ℂ] M) (hA : HasPreadjoint e A) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (A (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  obtain ⟨w,hw⟩ := hA z
  change Continuous (fun f : WeakDual ℂ X => e.symm (A (weakEquiv e f)) z)
  simp_rw [hw]
  simpa [weakEquiv] using WeakDual.eval_continuous (𝕜 := ℂ) w

lemma star_continuous (P : X →L⋆[ℂ] X)
    (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (star (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  change Continuous (fun f : WeakDual ℂ X => e.symm (star (weakEquiv e f)) z)
  simp_rw [hP]
  simpa [weakEquiv] using (WeakDual.eval_continuous (𝕜 := ℂ) (P z)).star

def linearClosure (A : StarSubalgebra ℂ M) : Submodule ℂ (WeakDual ℂ X) :=
  (A.toSubalgebra.toSubmodule.map (weakEquiv e).symm.toLinearMap).topologicalClosure

lemma linearClosure_closed (A : StarSubalgebra ℂ M) :
    IsClosed (linearClosure e A : Set (WeakDual ℂ X)) :=
  Submodule.isClosed_topologicalClosure _

lemma mem_linearClosure (A : StarSubalgebra ℂ M) {a : M} (ha : a ∈ A) :
    (weakEquiv e).symm a ∈ linearClosure e A :=
  Submodule.le_topologicalClosure _ ⟨a,ha,rfl⟩

lemma closure_stable (A : StarSubalgebra ℂ M) (T : WeakDual ℂ X → WeakDual ℂ X)
    (hT : Continuous T)
    (h : ∀ a ∈ A, T ((weakEquiv e).symm a) ∈ linearClosure e A) :
    ∀ f ∈ linearClosure e A, T f ∈ linearClosure e A := by
  apply closure_minimal _ ((linearClosure_closed e A).preimage hT)
  rintro f ⟨a,ha,rfl⟩
  exact h a ha

lemma mul_mem (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    {a b : M} (ha : (weakEquiv e).symm a ∈ linearClosure e A)
    (hb : (weakEquiv e).symm b ∈ linearClosure e A) :
    (weakEquiv e).symm (a*b) ∈ linearClosure e A := by
  have hleft (c : M) (hc : c ∈ A) :
      (weakEquiv e).symm (c*b) ∈ linearClosure e A := by
    have hs := closure_stable e A _ (normal_continuous e _ (hL c))
      (fun d hd => by
        simpa using mem_linearClosure e A (A.mul_mem hc hd))
      ((weakEquiv e).symm b) hb
    simpa using hs
  have hs := closure_stable e A _ (normal_continuous e _ (hR b))
    (fun c hc => by simpa using hleft c hc) ((weakEquiv e).symm a) ha
  simpa using hs

lemma star_mem (A : StarSubalgebra ℂ M)
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
    {a : M} (ha : (weakEquiv e).symm a ∈ linearClosure e A) :
    (weakEquiv e).symm (star a) ∈ linearClosure e A := by
  have hs := closure_stable e A _ (star_continuous e P hP)
    (fun c hc => by simpa using mem_linearClosure e A (A.star_mem' hc))
    ((weakEquiv e).symm a) ha
  simpa using hs

def closure (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    StarSubalgebra ℂ M where
  carrier := {a | (weakEquiv e).symm a ∈ linearClosure e A}
  zero_mem' := by simp [map_zero]
  one_mem' := mem_linearClosure e A A.one_mem
  add_mem' := by intro a b ha hb; simpa using (linearClosure e A).add_mem ha hb
  mul_mem' := mul_mem e A hL hR
  algebraMap_mem' c := mem_linearClosure e A (A.algebraMap_mem c)
  star_mem' := star_mem e A P hP

instance closure_closed (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    IsClosed (closure e A hL hR P hP : Set M) :=
  (linearClosure_closed e A).preimage (weakEquiv_symm_continuous e)

variable (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

def strongEquiv : WeakSubspace.strong (linearClosure e A) ≃ₗᵢ⋆[ℂ]
    closure e A hL hR P hP where
  toFun f := ⟨e f.val, by
    change (weakEquiv e).symm (e f.val) ∈ linearClosure e A
    simpa [weakEquiv] using (WeakSubspace.mem_strong (linearClosure e A) f.val).mp f.property⟩
  invFun a := ⟨e.symm a.val, by
    rw [WeakSubspace.mem_strong]
    exact a.property⟩
  left_inv f := by apply Subtype.ext; exact e.symm_apply_apply f.val
  right_inv a := by apply Subtype.ext; exact e.apply_symm_apply a.val
  map_add' f g := by apply Subtype.ext; exact map_add e f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smulₛₗ c f.val
  norm_map' f := e.norm_map f.val

def predualEquiv :
    StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) ≃ₗᵢ⋆[ℂ]
      closure e A hL hR P hP :=
  (WeakSubspace.quotientDualEquiv (linearClosure e A) (linearClosure_closed e A)).trans
    (strongEquiv e A hL hR P hP)

instance closure_wstar [CompleteSpace X] : WStarAlgebra (closure e A hL hR P hP) :=
  ⟨⟨X ⧸ WeakSubspace.preannihilator (linearClosure e A),inferInstance,inferInstance,
    inferInstance,⟨predualEquiv e A hL hR P hP⟩⟩⟩

lemma predualEquiv_apply (F : StrongDual ℂ
      (X ⧸ WeakSubspace.preannihilator (linearClosure e A))) (z : X) :
    e.symm ((predualEquiv e A hL hR P hP F : closure e A hL hR P hP) : M) z=
      F (Submodule.Quotient.mk z) := by
  change e.symm (e (F.comp (WeakSubspace.preannihilator (linearClosure e A)).mkQL)) z=_
  rw [e.symm_apply_apply]
  rfl

lemma predualEquiv_symm_apply_mk (a : closure e A hL hR P hP) (z : X) :
    (predualEquiv e A hL hR P hP).symm a (Submodule.Quotient.mk z)=e.symm a.val z := by
  have hs := predualEquiv_apply e A hL hR P hP
    ((predualEquiv e A hL hR P hP).symm a) z
  rw [LinearIsometryEquiv.apply_symm_apply] at hs
  exact hs.symm

lemma inherited_left_normal (b : closure e A hL hR P hP) :
    HasPreadjoint (predualEquiv e A hL hR P hP)
      (ContinuousLinearMap.mul ℂ (closure e A hL hR P hP) b) := by
  intro q
  obtain ⟨z,rfl⟩ := (WeakSubspace.preannihilator (linearClosure e A)).mkQ_surjective q
  obtain ⟨w,hw⟩ := hL b.val z
  refine ⟨Submodule.Quotient.mk w,fun a => ?_⟩
  change (predualEquiv e A hL hR P hP).symm _ (Submodule.Quotient.mk z)=_
  rw [predualEquiv_symm_apply_mk,predualEquiv_symm_apply_mk]
  exact hw a.val

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

lemma traceVector_norm_bound (b : M) :
    ‖traceVectorLinear e τ hL hτ b‖ ≤ ‖traceCLM τ‖*‖b‖ := by
  rw [traceVectorLinear_apply,norm_traceVector]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    ‖tracePair τ (star b) a‖ ≤ ‖traceCLM τ‖*‖star b*a‖ := (traceCLM τ).le_opNorm _
    _ ≤ ‖traceCLM τ‖*(‖b‖*‖a‖) := mul_le_mul_of_nonneg_left
      (by simpa using norm_mul_le (star b) a) (norm_nonneg _)
    _ = (‖traceCLM τ‖*‖b‖)*‖a‖ := (mul_assoc _ _ _).symm

def traceRestriction : A →L[ℂ] (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) :=
  (WeakSubspace.preannihilator (linearClosure e A)).mkQL.comp
    (((traceVectorLinear e τ hL hτ).mkContinuous ‖traceCLM τ‖
      (traceVector_norm_bound e τ hL hτ)).comp
      { toLinearMap := A.toSubalgebra.toSubmodule.subtype
        cont := continuous_subtype_val })

@[simp] lemma traceRestriction_apply (a : A) :
    traceRestriction e τ A hL hτ a=
      Submodule.Quotient.mk (traceVectorLinear e τ hL hτ (a:M)) := rfl

include hR P hP in

lemma denseRange_traceRestriction (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    DenseRange (traceRestriction e τ A hL hτ) := by
  let Y := X ⧸ WeakSubspace.preannihilator (linearClosure e A)
  let J := traceRestriction e τ A hL hτ
  let S := (LinearMap.range J.toLinearMap).topologicalClosure
  let : IsClosed (S : Set Y) := (LinearMap.range J.toLinearMap).isClosed_topologicalClosure
  have hzero (F : StrongDual ℂ Y) (hF : ∀ a : A, F (J a)=0) : F=0 := by
    let b := predualEquiv e A hL hR P hP F
    have ha (a : M) (ha : a ∈ A) :
        (weakEquiv e).symm a (traceVector e τ hL hτ b.val)=0 := by
      have hs := hF ⟨a,ha⟩
      change F (Submodule.Quotient.mk (traceVector e τ hL hτ a))=0 at hs
      rw [← predualEquiv_apply e A hL hR P hP,traceVector_spec] at hs
      have ht : τ (star a*b.val)=0 := star_eq_zero.mp hs
      change e.symm a (traceVector e τ hL hτ b.val)=0
      rw [traceVector_spec]
      apply star_eq_zero.mpr
      have hh := congrArg star ht
      simpa only [← map_star,star_mul,star_star,star_zero] using hh
    have heval : ∀ f ∈ linearClosure e A,
        f (traceVector e τ hL hτ b.val)=0 := by
      apply closure_minimal _ (isClosed_eq
        (WeakDual.eval_continuous (𝕜 := ℂ) _) continuous_const)
      rintro f ⟨a,ha0,rfl⟩
      exact ha a ha0
    have hz : b.val=0 := by
      apply hfaith
      apply star_eq_zero.mp
      rw [← traceVector_spec e τ hL hτ b.val b.val]
      exact heval ((weakEquiv e).symm b.val) b.property
    ext q
    obtain ⟨z,rfl⟩ := (WeakSubspace.preannihilator (linearClosure e A)).mkQ_surjective q
    change F (Submodule.Quotient.mk z)=0
    rw [← predualEquiv_apply e A hL hR P hP]
    change e.symm b.val z=0
    rw [hz,map_zero]
    rfl
  change Dense (Set.range J.toLinearMap)
  rw [← LinearMap.coe_range]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro f
  have hf : f.comp S.mkQL=0 := by
    apply hzero
    intro a
    have ha : J a ∈ S := (LinearMap.range J.toLinearMap).le_topologicalClosure ⟨a,rfl⟩
    change f (Submodule.Quotient.mk (J a))=0
    rw [(Submodule.Quotient.mk_eq_zero S).mpr ha,map_zero]
  exact congrArg (fun F : StrongDual ℂ Y => F z) hf

include hL hR P hP hτ in

theorem separablePredual_of_separable [TopologicalSpace.SeparableSpace A]
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    TopologicalSpace.SeparableSpace
      (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) :=
  (denseRange_traceRestriction e τ A hL hR P hP hτ hfaith).separableSpace
    (traceRestriction e τ A hL hτ).continuous

end WeakAlgebra
end BoundedHochschild

namespace BoundedHochschild
open TopologicalSpace
variable {M : Type*}

lemma countable_submonoidClosure [Monoid M] (s : Set M) (hs : s.Countable) :
    (Submonoid.closure s : Set M).Countable := by
  let : Countable s := hs.to_subtype
  apply (Set.countable_range (fun l : List s => (l.map Subtype.val).prod)).mono
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem a ha => exact ⟨[⟨a,ha⟩],by simp⟩
  | one => exact ⟨[],rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨l,rfl⟩ := ha
    obtain ⟨k,rfl⟩ := hb
    exact ⟨l++k,by simp⟩

lemma separable_starAdjoin [CStarAlgebra M] (s : Set M) (hs : s.Countable) :
    SeparableSpace (StarAlgebra.adjoin ℂ s) := by
  have hstar : (star s).Countable := by simpa only [Set.image_star] using hs.image star
  have hcount := countable_submonoidClosure (s ∪ star s) (hs.union hstar)
  have hspan : IsSeparable
      (Submodule.span ℂ (Submonoid.closure (s ∪ star s) : Set M) : Set M) :=
    hcount.isSeparable.span
  rw [← StarAlgebra.adjoin_eq_span (R := ℂ) s] at hspan
  exact hspan.separableSpace

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

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

def inheritedTrace : closure e A hL hR P hP →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (closure e A hL hR P hP).subtype.toLinearMap
  monotone' := fun _ _ h => OrderHomClass.mono τ h

@[simp] lemma inheritedTrace_apply (a : closure e A hL hR P hP) :
    inheritedTrace e τ A hL hR P hP a=τ (a:M) := rfl

include hL hR P hP in
lemma inheritedTrace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (predualEquiv e A hL hR P hP) (inheritedTrace e τ A hL hR P hP) := by
  obtain ⟨z,hz⟩ := hτ
  refine ⟨Submodule.Quotient.mk z,fun a => ?_⟩
  rw [predualEquiv_symm_apply_mk]
  exact hz a.val

lemma inheritedTrace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (a : closure e A hL hR P hP)
    (ha : inheritedTrace e τ A hL hR P hP (star a*a)=0) : a=0 := by
  apply Subtype.ext
  exact hfaith a.val ha

lemma inheritedTrace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (a b : closure e A hL hR P hP) :
    inheritedTrace e τ A hL hR P hP (a*b)=inheritedTrace e τ A hL hR P hP (b*a) :=
  htr a.val b.val

lemma inheritedTrace_one (h1 : τ 1=1) : inheritedTrace e τ A hL hR P hP 1=1 := h1
end WeakAlgebra
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_star {a : M} (ha : Central a) : Central (star a) := by
  intro x
  change star a*x=x*star a
  have h := congrArg star (ha (star x)).eq
  simpa only [star_mul,star_star] using h.symm
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_sub {a b : M} (ha : Central a) (hb : Central b) : Central (a-b) :=
  fun x => (ha x).sub_left (hb x)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma average_central (a : M) : Central (average e τ hτ htr hfaith a) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.1
lemma average_orbit (a : M) :
    gnsVector τ (average e τ hτ htr hfaith a) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.2

variable (h1 : τ 1=1)
include htr in
omit [StarOrderedRing M] in
lemma central_pair_hull {z : M} (hz : Central z) (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      {b | τ (z*b)=τ (z*a)} := by
  apply convexHull_min
  · rintro _ ⟨v,rfl⟩
    change τ (z*conjugate v a)=τ (z*a)
    rw [conjugate_apply]
    have he : z*((v:M)*a*star (v:M))=(v:M)*(z*a)*star (v:M) := by
      calc
        _=(z*(v:M))*a*star (v:M) := by simp only [mul_assoc]
        _=((v:M)*z)*a*star (v:M) := by rw [(hz (v:M)).eq]
        _=_ := by simp only [mul_assoc]
    rw [he]
    exact trace_conjugate τ htr v (z*a)
  · intro x hx y hy r s _hr _hs hrs
    change τ (z*(r • x+s • y))=τ (z*a)
    rw [mul_add,mul_smul_comm,mul_smul_comm,map_add,τ.map_smul_of_tower,
      τ.map_smul_of_tower,hx,hy,←add_smul,hrs,one_smul]

include htr h1 in
lemma central_pair_closure {z : M} (hz : Central z) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) : τ (z*b)=τ (z*a) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have htc : ∀ n, τ (z*c n)=τ (z*a) := fun n => central_pair_hull τ htr hz a (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n-b)‖) atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [←hcy,←map_sub,gnsVector_norm] using hh
  have htt : Tendsto (fun n => ‖τ (z*(c n-b))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (HochschildUltrapower.norm_trace_le τ h1 _).trans
        (preGNS_norm_mul_le τ z _))
    simpa only [mul_zero] using ht.const_mul ‖z‖
  have he : ‖τ (z*a)-τ (z*b)‖=0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [mul_sub,map_sub,htc] using htt)
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

include h1
lemma average_pair {z : M} (hz : Central z) (a : M) :
    τ (z*average e τ hτ htr hfaith a)=τ (z*a) :=
  central_pair_closure τ htr h1 hz a _ (average_orbit e τ hτ htr hfaith a)

omit h1 in
include hfaith in
omit [StarOrderedRing M] in
lemma central_unique {b c : M} (hb : Central b) (hc : Central c)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*c)) : b=c := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,h _ (central_star (central_sub hb hc)),sub_self]

lemma average_eq (a b : M) (hb : Central b)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*a)) : average e τ hτ htr hfaith a=b := by
  apply central_unique τ hfaith (average_central e τ hτ htr hfaith a) hb
  intro z hz
  rw [average_pair e τ hτ htr hfaith h1 hz,h z hz]

lemma average_id {a : M} (ha : Central a) : average e τ hτ htr hfaith a=a :=
  average_eq e τ hτ htr hfaith h1 a a ha (fun _ _ => rfl)
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)

include e τ hτ htr hfaith h1 hII

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace PopaSeparable
open BoundedHochschild PopaCenter PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
variable (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

include hτ htr hfaith h1 in

theorem typeII_seed (hII : NoAbelianCorners M) (S : Set M) (hS : S.Countable) :
    ∃ R : Set M, R.Countable ∧ S ⊆ R ∧
      NoAbelianCorners (WeakAlgebra.closure e (StarAlgebra.adjoin ℂ R) hL hR P hP) := by
  classical
  have hE1 : Homogeneous e τ hτ htr hfaith (1:M) := by
    change average e τ hτ htr hfaith 1=(τ 1).re • (1:M)
    rw [average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x),h1,Complex.one_re,one_smul]
  have hm (k : ℕ) := exists_homogeneous_system e τ hτ htr hfaith h1 hII
    (2^(k+1)) (pow_pos (by decide) _) (IsStarProjection.one M) hE1
  let s (k : ℕ) : System (2^(k+1)) (1:M) := Classical.choice (hm k)
  let T (k : ℕ) : Set M := Set.range (fun ij : Fin (2^(k+1)) × Fin (2^(k+1)) => (s k).entry ij.1 ij.2)
  let R := S ∪ ⋃ k, T k
  have hRcount : R.Countable := hS.union (Set.countable_iUnion (fun k => Set.countable_range _))
  refine ⟨R,hRcount,Set.subset_union_left,?_⟩
  let A := StarAlgebra.adjoin ℂ R
  let N := WeakAlgebra.closure e A hL hR P hP
  let eN := WeakAlgebra.predualEquiv e A hL hR P hP
  let τN := WeakAlgebra.inheritedTrace e τ A hL hR P hP
  apply noAbelianCorners_of_matrices eN τN
    (WeakAlgebra.inheritedTrace_normal e τ A hL hR P hP hτ)
    (WeakAlgebra.inheritedTrace_tracial e τ A hL hR P hP htr)
    (WeakAlgebra.inheritedTrace_faithful e τ A hL hR P hP hfaith)
    (WeakAlgebra.inheritedTrace_one e τ A hL hR P hP h1)
  intro k
  have hmem (i j : Fin (2^(k+1))) : (s k).entry i j ∈ N :=
    WeakAlgebra.mem_linearClosure e A (StarAlgebra.subset_adjoin ℂ R
      (Or.inr (Set.mem_iUnion.mpr ⟨k,⟨(i,j),rfl⟩⟩)))
  let sN : System (2^(k+1)) (1:N) := {
    entry := fun i j => ⟨(s k).entry i j,hmem i j⟩
    star_entry := fun i j => Subtype.ext ((s k).star_entry i j)
    mul_entry := fun i j a b => by
      apply Subtype.ext
      change (s k).entry i j*(s k).entry a b=(↑(if j=a then (⟨(s k).entry i b,hmem i b⟩:N) else 0):M)
      split <;> simp_all only [(s k).mul_entry,ite_true,ite_false]
      rfl
    sum_diag := by
      apply Subtype.ext
      change (N.subtype (∑ i, (⟨(s k).entry i i,hmem i i⟩:N)))=(1:M)
      rw [map_sum]
      exact (s k).sum_diag }
  exact ⟨sN⟩
end PopaSeparable

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)
include e hτ htr hfaith h1 hII

theorem arbitrary_typeII_last_normal_primitive {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v, differentialValue f v=0)
    (hn : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  classical
  obtain ⟨hL,hR⟩ := HochschildSakai.abstract_multiplication_normal e
  obtain ⟨P,_,hP⟩ := exists_star_preadjoint e τ hL hτ hfaith htr
  apply primitive_of_finite_exactness e hL hR f ‖f‖ (norm_nonneg _)
  intro E
  let images : Finset M := Finset.univ.image (fun x : Fin (n+1) → E => f (fun i => x i))
  let S : Set M := (E : Set M) ∪ (images : Set M)
  have hS : S.Countable := E.countable_toSet.union images.countable_toSet
  obtain ⟨R,hRcount,hSR,hIIN⟩ := PopaSeparable.typeII_seed
    e τ hτ htr hfaith h1 hL hR P hP hII S hS
  let A := StarAlgebra.adjoin ℂ R
  let N := WeakAlgebra.closure e A hL hR P hP
  let Y := X ⧸ WeakSubspace.preannihilator (WeakAlgebra.linearClosure e A)
  let eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N := WeakAlgebra.predualEquiv e A hL hR P hP
  let τN : N →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ A hL hR P hP
  let : TopologicalSpace.SeparableSpace A := separable_starAdjoin R hRcount
  let : TopologicalSpace.SeparableSpace Y :=
    WeakAlgebra.separablePredual_of_separable e τ A hL hR P hP hτ hfaith
  have h1N : τN 1=1 := h1
  have htrN : ∀ a b : N, τN (a*b)=τN (b*a) := fun a b => htr a.val b.val
  have hLN : ∀ a : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N a) :=
    WeakAlgebra.inherited_left_normal e A hL hR P hP
  have hτN : TraceInPredual eN τN :=
    WeakAlgebra.inheritedTrace_normal e τ A hL hR P hP hτ
  have hfaithN : ∀ a : N, τN (star a*a)=0 → a=0 :=
    WeakAlgebra.inheritedTrace_faithful e τ A hL hR P hP hfaith
  have hmem (a : M) (ha : a ∈ S) : a ∈ N :=
    WeakAlgebra.mem_linearClosure e A (StarAlgebra.subset_adjoin ℂ R (hSR ha))
  have hpaths := PopaCenter.produced_finite_paths eN τN hτN htrN hfaithN h1N hIIN
  apply finite_exactness_of_separable_subalgebra e eN τ τN h1N htr htrN hL hLN
    hτ hτN hfaith hfaithN N.subtype (fun _ => rfl) hpaths f hf hn (E : Set M)
  · intro a ha
    exact ⟨⟨a,hmem a (Or.inl ha)⟩,rfl⟩
  · intro x hx
    have hm : f x ∈ images := by
      apply Finset.mem_image.mpr
      exact ⟨fun i => ⟨x i,hx i⟩,Finset.mem_univ _,rfl⟩
    exact ⟨⟨f x,hmem (f x) (Or.inr hm)⟩,rfl⟩
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.arbitrary_typeII_last_normal_primitive.{u} := @OAI.BoundedHochschild.arbitrary_typeII_last_normal_primitive.{u}
