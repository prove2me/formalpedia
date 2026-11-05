-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.normal_positive_predual_orbit_compact
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:55:03.317821+00:00
-- url     : https://prove2.me/submissions/bc434a89-5666-4afc-95c4-0a62b4faa966

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_fixes_normal
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_sum
import Theorems.Thm_OAI_HochschildNormalPart_functionalModel_nonempty
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normal_positive_uniform_orbit_hull

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
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [CompleteSpace X]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma coefficient_norm (η ξ : H) : ‖coefficient π η ξ‖ ≤ ‖η‖*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := by gcongr; exact (π a).le_opNorm ξ
    _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

lemma projection_commutes (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : ∀ ξ ∈ K, T ξ ∈ K) (hTstar : ∀ ξ ∈ K, star T ξ ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext ξ
  change K.starProjection (T ξ)=T (K.starProjection ξ)
  apply Submodule.eq_starProjection_of_mem_orthogonal (hT _ (by simp))
  intro η hη
  change ⟪η,T ξ-T (K.starProjection ξ)⟫_ℂ=0
  rw [← map_sub]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact K.sub_starProjection_mem_orthogonal ξ _ (hTstar η hη)

lemma normalProjection_mul (a : M) :
    normalProjection e π*π a=π a*normalProjection e π := by
  apply projection_commutes
  · intro ξ hξ; exact normalVectors_mul e π hξ a
  · intro ξ hξ
    rw [← map_star]
    exact normalVectors_mul e π hξ (star a)

end HochschildNormalPart

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma coefficient_sum (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (η ξ : WithLp 2 (H×K)) :
    coefficient (sumRepresentation π ρ) η ξ=
      coefficient π η.fst ξ.fst+coefficient ρ η.snd ξ.snd := by
  ext a; rfl

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma coefficient_normal_eq_of_eq
    (η ξ : H) (ζ ω : K) (h : coefficient π η ξ=coefficient ρ ζ ω) :
    coefficient π η (normalProjection e π ξ)=coefficient ρ ζ (normalProjection e ρ ω) := by
  let A : WithLp 2 (H×K) := WithLp.toLp 2 (η,ζ)
  let B : WithLp 2 (H×K) := WithLp.toLp 2 (ξ,-ω)
  have hz : coefficient (sumRepresentation π ρ) A B=0 := by
    rw [coefficient_sum]
    change coefficient π η ξ+coefficient ρ ζ (-ω)=0
    rw [map_neg,h,add_neg_cancel]
  have hn : coefficient (sumRepresentation π ρ) A B ∈ normalDual e := hz ▸ (normalDual e).zero_mem
  have hp := normalProjection_fixes_normal e (sumRepresentation π ρ) A B hn
  rw [hz,normalProjection_sum,coefficient_sum] at hp
  change coefficient π η (normalProjection e π ξ)+coefficient ρ ζ (normalProjection e ρ (-ω))=0 at hp
  rw [map_neg,map_neg] at hp
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hp)
end HochschildNormalPart
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

namespace BoundedHochschild
namespace CentralCorner

open HochschildCorners

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)

def includeMap : Corner p hp →L[ℂ] M :=
  (corner p hp).toNonUnitalSubalgebra.toSubmodule.subtypeL

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma includeMap_apply (a : Corner p hp) : includeMap p hp a = (a : M) := rfl
end CentralCorner
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
namespace HochschildNormalPart
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def positiveVector (ψ : M →ₚ[ℂ] ℂ) : ψ.GNS := (ψ.toPreGNS 1 : ψ.PreGNS)

lemma positiveVector_coefficient (ψ : M →ₚ[ℂ] ℂ) (a : M) :
    coefficient ψ.gnsStarAlgHom (positiveVector ψ) (positiveVector ψ) a=ψ a := by
  change ⟪(ψ.toPreGNS 1 : ψ.GNS),ψ.gnsNonUnitalStarAlgHom a (ψ.toPreGNS 1)⟫_ℂ=ψ a
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,UniformSpace.Completion.inner_coe]
  simp [PositiveLinearMap.preGNS_inner_def]

attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

end HochschildNormalPart

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def functionalModel (φ : StrongDual ℂ M) : FunctionalModel φ := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact Classical.choice (functionalModel_nonempty φ)

def normalPartRaw (φ : StrongDual ℂ M) : StrongDual ℂ M :=
  coefficient (functionalModel φ).representation (functionalModel φ).leftVector
    (normalProjection e (functionalModel φ).representation (functionalModel φ).rightVector)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalPartRaw_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    normalPartRaw e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) := by
  exact coefficient_normal_eq_of_eq e _ π _ _ η ξ (functionalModel _).realizes

lemma normalPartRaw_add (φ ψ : StrongDual ℂ M) :
    normalPartRaw e (φ+ψ)=normalPartRaw e φ+normalPartRaw e ψ := by
  let m := functionalModel φ
  let n := functionalModel ψ
  let π := sumRepresentation m.representation n.representation
  let η : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.leftVector,n.leftVector)
  let ξ : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.rightVector,n.rightVector)
  have hc : coefficient π η ξ=φ+ψ := by
    rw [coefficient_sum]
    change coefficient m.representation m.leftVector m.rightVector+
      coefficient n.representation n.leftVector n.rightVector=φ+ψ
    rw [m.realizes,n.realizes]
  rw [← hc,normalPartRaw_coefficient,normalProjection_sum,coefficient_sum]
  rfl

lemma normalPartRaw_smul (r : ℂ) (φ : StrongDual ℂ M) :
    normalPartRaw e (r • φ)=r • normalPartRaw e φ := by
  let m := functionalModel φ
  have hc : coefficient m.representation m.leftVector (r • m.rightVector)=r • φ := by
    rw [map_smul,m.realizes]
  rw [← hc,normalPartRaw_coefficient,map_smul,map_smul]
  rfl

lemma normalPartRaw_norm (φ : StrongDual ℂ M) : ‖normalPartRaw e φ‖≤4*‖φ‖ := by
  let m := functionalModel φ
  exact (coefficient_norm _ _ _).trans
    ((mul_le_mul_of_nonneg_left ((normalVectors e m.representation).norm_starProjection_apply_le _)
      (norm_nonneg m.leftVector)).trans m.bound)

def scalarNormalPart : StrongDual ℂ M →L[ℂ] StrongDual ℂ M :=
  LinearMap.mkContinuous
    { toFun := normalPartRaw e
      map_add' := normalPartRaw_add e
      map_smul' := normalPartRaw_smul e } 4 (normalPartRaw_norm e)

@[simp] lemma scalarNormalPart_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    scalarNormalPart e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) :=
  normalPartRaw_coefficient e π η ξ

lemma scalarNormalPart_mem (φ : StrongDual ℂ M) : scalarNormalPart e φ ∈ normalDual e := by
  apply (mem_normalVectors e (functionalModel φ).representation _).mp
  simp [normalProjection]

lemma scalarNormalPart_fixes {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e) :
    scalarNormalPart e φ=φ := by
  let m := functionalModel φ
  change coefficient m.representation m.leftVector (normalProjection e m.representation m.rightVector)=φ
  rw [normalProjection_fixes_normal e _ _ _ (m.realizes.symm ▸ hφ),m.realizes]

lemma scalarNormalPart_comp_left (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp (ContinuousLinearMap.mul ℂ M b))=
      (scalarNormalPart e φ).comp (ContinuousLinearMap.mul ℂ M b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      (ContinuousLinearMap.mul ℂ M b)=coefficient m.representation (m.representation (star b) m.leftVector) ξ := by
    ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',coefficient_apply,
      map_mul,mul_apply_eq_comp,map_star,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]

lemma scalarNormalPart_comp_right (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp ((ContinuousLinearMap.mul ℂ M).flip b))=
      (scalarNormalPart e φ).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      ((ContinuousLinearMap.mul ℂ M).flip b)=coefficient m.representation m.leftVector (m.representation b ξ) := by
    ext a
    simp [map_mul]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]
  exact congrArg (coefficient m.representation m.leftVector)
    (congrArg (fun T : m.H →L[ℂ] m.H => T m.rightVector) (normalProjection_mul e m.representation b))
end HochschildNormalPart
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

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorPositiveFunctional (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : M →ₚ[ℂ] ℂ where
  toLinearMap := (coefficient π ξ ξ).toLinearMap
  monotone' := by
    change Monotone (coefficient π ξ ξ)
    apply (monotone_iff_map_nonneg _).mpr
    intro a ha
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (map_nonneg π ha)).inner_nonneg_right ξ

@[simp] lemma vectorPositiveFunctional_apply (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (a : M) : vectorPositiveFunctional π ξ a = inner ℂ ξ (π a ξ) := rfl

omit [CompleteSpace X] in
lemma vectorPositiveFunctional_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {ξ : H} (hξ : ξ ∈ normalVectors e π) :
    TraceInPredual e (vectorPositiveFunctional π ξ) := by
  exact (mem_normalDual e _).mp ((mem_normalVectors e π ξ).mp hξ ξ)

theorem exists_normal_state_on_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ ψ : M →ₚ[ℂ] ℂ, TraceInPredual e ψ ∧ ψ 1 = 1 ∧ ψ p = 1 ∧
      ∀ a : M, ψ (p * a * p) = ψ a := by
  classical
  have hex : ∃ z : X, e.symm p z ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hp0
    apply e.symm.injective
    ext z
    simpa only [map_zero, zero_apply] using hn z
  obtain ⟨z, hz⟩ := hex
  let φ := predualEmbedding e z
  let m := functionalModel φ
  let π := m.representation
  let η := m.leftVector
  let ξ := normalProjection e π m.rightVector
  have hφ : φ ∈ normalDual e := ⟨z, rfl⟩
  have hreal : coefficient π η ξ = φ := by
    exact (normalProjection_fixes_normal e π η m.rightVector
      (m.realizes.symm ▸ hφ)).trans m.realizes
  have hξ : ξ ∈ normalVectors e π := by simp [ξ, normalProjection]
  let ζ := π p ξ
  have hζ : ζ ∈ normalVectors e π := normalVectors_mul e π hξ p
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have he := congrArg (fun f : StrongDual ℂ M => f p) hreal
    have hφp : φ p ≠ 0 := by simpa only [φ, predualEmbedding_apply, star_ne_zero] using hz
    apply hφp
    change inner ℂ η ζ = φ p at he
    rw [hzero, inner_zero_right] at he
    exact he.symm
  have hfix : π p ζ = ζ := by
    change π p (π p ξ) = π p ξ
    rw [← mul_apply_eq_comp, ← map_mul, hp.isIdempotentElem.eq]
  let w := (‖ζ‖⁻¹ : ℂ) • ζ
  have hwn : ‖w‖ = 1 := norm_smul_inv_norm hζ0
  have hw : w ∈ normalVectors e π := (normalVectors e π).smul_mem _ hζ
  have hwfix : π p w = w := by simp only [w, map_smul, hfix]
  let ψ := vectorPositiveFunctional π w
  have hψ1 : ψ 1 = 1 := by
    simp only [ψ, vectorPositiveFunctional_apply, map_one, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, hwn]
    norm_num
  refine ⟨ψ, vectorPositiveFunctional_normal e π hw, hψ1, ?_, ?_⟩
  · simpa only [ψ, vectorPositiveFunctional_apply, hwfix, map_one, one_apply_eq_self]
      using hψ1
  · intro a
    change inner ℂ w (π (p * a * p) w) = inner ℂ w (π a w)
    rw [map_mul, map_mul]
    change inner ℂ w (π p (π a (π p w))) = inner ℂ w (π a w)
    rw [hwfix, ← ContinuousLinearMap.adjoint_inner_left]
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, hp.isSelfAdjoint.star_eq, hwfix]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

section Representation
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder M] [StarOrderedRing M] in
lemma normalComplement_diagonal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    coefficient π ξ ξ - scalarNormalPart e (coefficient π ξ ξ) =
      coefficient π (ξ - normalProjection e π ξ) (ξ - normalProjection e π ξ) := by
  rw [scalarNormalPart_coefficient]
  ext a
  let P := normalProjection e π
  let δ := ξ - P ξ
  have hPP : P (P ξ) = P ξ :=
    Submodule.starProjection_eq_self_iff.mpr (by simp [P, normalProjection])
  have hPδ : P δ = 0 := by dsimp [δ]; rw [map_sub, hPP, sub_self]
  have hcomm : P (π a δ) = π a (P δ) :=
    congrArg (fun T : H →L[ℂ] H => T δ) (normalProjection_mul e π a)
  have hzero : inner ℂ (P ξ) (π a δ) = 0 := by
    calc
      _ = inner ℂ ξ (P (π a δ)) :=
        (normalVectors e π).inner_starProjection_left_eq_right ξ (π a δ)
      _ = 0 := by rw [hcomm, hPδ, map_zero, inner_zero_right]
  change inner ℂ ξ (π a ξ) - inner ℂ ξ (π a (P ξ)) = inner ℂ δ (π a δ)
  calc
    _ = inner ℂ ξ (π a δ) := by dsimp [δ]; rw [map_sub, inner_sub_right]
    _ = inner ℂ (P ξ + δ) (π a δ) := by simp only [δ, add_sub_cancel]
    _ = inner ℂ δ (π a δ) := by rw [inner_add_left, hzero, zero_add]

end Representation

def positiveSingularPart (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    M →ₚ[ℂ] ℂ :=
  vectorPositiveFunctional ψ.gnsStarAlgHom
    (positiveVector ψ - normalProjection e ψ.gnsStarAlgHom (positiveVector ψ))

lemma positiveSingularPart_eq (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (positiveSingularPart e ψ) =
      positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) := by
  have hψ : positiveFunctionalCLM ψ = coefficient ψ.gnsStarAlgHom (positiveVector ψ)
      (positiveVector ψ) := by ext a; exact (positiveVector_coefficient ψ a).symm
  rw [hψ, normalComplement_diagonal]
  rfl

theorem positive_normal_of_dominated (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (χ ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hle : ∀ a : M, 0 ≤ a → χ a ≤ ψ a) : TraceInPredual e χ := by
  let θ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := ψ.toLinearMap - χ.toLinearMap
      monotone' := (monotone_iff_map_nonneg (ψ.toLinearMap - χ.toLinearMap)).mpr (fun a ha => sub_nonneg.mpr (hle a ha)) }
  have hsum : positiveFunctionalCLM χ + positiveFunctionalCLM θ = positiveFunctionalCLM ψ := by
    ext a
    change χ a + (ψ a - χ a) = ψ a
    abel
  have hψnormal : positiveFunctionalCLM ψ ∈ normalDual e := (mem_normalDual e _).mpr hψ
  have hS : positiveFunctionalCLM (positiveSingularPart e χ) +
      positiveFunctionalCLM (positiveSingularPart e θ) = 0 := by
    rw [positiveSingularPart_eq, positiveSingularPart_eq]
    calc
      _ = (positiveFunctionalCLM χ + positiveFunctionalCLM θ) -
          (scalarNormalPart e (positiveFunctionalCLM χ) +
            scalarNormalPart e (positiveFunctionalCLM θ)) := by abel
      _ = positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) := by
        rw [← map_add, hsum]
      _ = 0 := by rw [scalarNormalPart_fixes e hψnormal, sub_self]
  have hzero : positiveFunctionalCLM (positiveSingularPart e χ) = 0 := by
    apply HochschildSakai.dual_zero_of_projection_zero e
    intro p hp
    have he := congrArg (fun F : StrongDual ℂ M => F p) hS
    change positiveSingularPart e χ p + positiveSingularPart e θ p = 0 at he
    apply le_antisymm _ ((positiveSingularPart e χ).map_nonneg hp.nonneg)
    calc
      positiveSingularPart e χ p ≤
          positiveSingularPart e χ p + positiveSingularPart e θ p :=
        le_add_of_nonneg_right ((positiveSingularPart e θ).map_nonneg hp.nonneg)
      _ = 0 := he
  rw [positiveSingularPart_eq] at hzero
  have hχnormal : positiveFunctionalCLM χ ∈ normalDual e := by
    rw [sub_eq_zero] at hzero
    rw [hzero]
    exact scalarNormalPart_mem e _
  exact (mem_normalDual e _).mp hχnormal
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

lemma positive_contraction_eval_nonneg_of_projection_nonneg
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M)
    (hreal : ∀ a : M, IsSelfAdjoint a → (F a).im = 0)
    (hproj : ∀ p : M, IsStarProjection p → 0 ≤ F p)
    (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ F a := by
  have hbound (n : ℕ) : ∀ b : M, 0 ≤ b → b ≤ 1 →
      -((1 / 2 : ℝ) ^ n) * ‖F‖ ≤ (F b).re := by
    induction n with
    | zero =>
        intro b hb0 hb1
        have hn : ‖F b‖ ≤ ‖F‖ := (F.le_opNorm b).trans
          (mul_le_of_le_one_right (norm_nonneg _) ((CStarAlgebra.norm_le_one_iff_of_nonneg b hb0).mpr hb1))
        have hr := Complex.abs_re_le_norm (F b)
        simp only [pow_zero, neg_mul, one_mul]
        linarith [neg_le_abs (F b).re]
    | succ n ih =>
        intro b hb0 hb1
        obtain ⟨p, hp, hlow, hupp⟩ := HochschildSakai.exists_dyadic_projection e b hb0 hb1
        have hh := ih ((2 : ℝ) • b - p) hlow hupp
        have he : F ((2 : ℝ) • b - p) = (2 : ℝ) • F b - F p := by simp
        rw [he] at hh
        have hp0 : 0 ≤ (F p).re := (Complex.nonneg_iff.mp (hproj p hp)).1
        simp at hh
        have hpow : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by simp [one_div]
        rw [← hpow] at hh
        rw [pow_succ]
        nlinarith
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hreal a ha0.isSelfAdjoint).symm⟩
  have ht : Tendsto (fun n : ℕ => -((1 / 2 : ℝ) ^ n) * ‖F‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).neg.mul_const ‖F‖)
  exact le_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)

theorem eval_nonneg_of_projection_nonneg (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : StrongDual ℂ M) (hreal : ∀ a : M, IsSelfAdjoint a → (F a).im = 0)
    (hproj : ∀ p : M, IsStarProjection p → 0 ≤ F p) :
    ∀ a : M, 0 ≤ a → 0 ≤ F a := by
  intro a ha
  let t : ℝ := ‖a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let c : M := t⁻¹ • a
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr ht.le) ha
  have hcn : ‖c‖ ≤ 1 := by
    rw [show c = t⁻¹ • a from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_one₀ ht).mpr (by dsimp [t]; linarith)
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  have hh := smul_nonneg ht.le
    (positive_contraction_eval_nonneg_of_projection_nonneg e F hreal hproj c hc0 hc1)
  have hca : t • c = a := by
    dsimp [c]
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have he : (t : ℝ) • F c = F a := by
    calc
      (t : ℝ) • F c = F ((t : ℝ) • c) := by simp
      _ = F a := congrArg F hca
  rwa [he] at hh
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

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def CompletelyAdditive (F : StrongDual ℂ M) : Prop :=
  ∀ (I : Type u) (p : I → M), (∀ i, IsStarProjection (p i)) →
    (∀ i j, i ≠ j → p i * p j = 0) →
    ∀ P : M, IsStarProjection P → (∀ i, p i ≤ P) →
      (∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r) →
      Tendsto (fun s : Finset I => ∑ i ∈ s, F (p i)) atTop (𝓝 (F P))

lemma normal_completelyAdditive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) : CompletelyAdditive F := by
  classical
  intro I p hp horth P hP hu hl
  obtain ⟨Q, hQ, hqu, hql, ht⟩ := exists_orthogonal_projection_sum e p hp horth
  have hQP : Q = P := le_antisymm (hql P hP hu) (hl Q hQ hqu)
  subst Q
  obtain ⟨z, hz⟩ := (mem_normalDual e F).mp hF
  have hconv : Tendsto (fun s : Finset I => F (∑ i ∈ s, p i)) atTop (𝓝 (F P)) := by
    simpa only [hz] using (ht z).star
  simpa only [map_sum] using hconv

omit [StarOrderedRing M] in
lemma CompletelyAdditive.sub {F G : StrongDual ℂ M} (hF : CompletelyAdditive F)
    (hG : CompletelyAdditive G) : CompletelyAdditive (F - G) := by
  classical
  intro I p hp ho P hP hu hl
  simpa only [sub_apply, Finset.sum_sub_distrib] using
    (hF I p hp ho P hP hu hl).sub (hG I p hp ho P hP hu hl)

theorem exists_nonnegative_projection_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : StrongDual ℂ M) (hF : CompletelyAdditive F) {E : M} (hE : IsStarProjection E) :
    ∃ p : M, IsStarProjection p ∧ p ≤ E ∧ (F E).re ≤ (F p).re ∧
      ∀ q : M, IsStarProjection q → q ≤ p → 0 ≤ (F q).re := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧ p ≤ E ∧ (F p).re < 0) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p * q = 0}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro p hp
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      exact (hc hs).1 p hps
    · intro p hp q hq hpq
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 p (hst hps) q hqt hpq
      · exact (hc hs).2 p hps q (hts hqt) hpq)
  let f : S → M := Subtype.val
  have hp (i : S) : IsStarProjection (f i) := (hS.1.1 i i.property).1
  have ho (i j : S) (hij : i ≠ j) : f i * f j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨P, hP, hPu, hPl, _⟩ := exists_orthogonal_projection_sum e f hp ho
  have hPE : P ≤ E := hPl E hE (fun i => (hS.1.1 i i.property).2.1)
  have hsum := hF S f hp ho P hP hPu hPl
  have hPneg : (F P).re ≤ 0 := by
    apply le_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hsum)
    apply Eventually.of_forall
    intro s
    change (∑ i ∈ s, F (f i)).re ≤ 0
    change Complex.reCLM (∑ i ∈ s, F (f i)) ≤ 0
    rw [map_sum]
    exact Finset.sum_nonpos (fun i _ => (hS.1.1 i i.property).2.2.le)
  have hEP : IsStarProjection (E - P) := (hP.le_iff_sub hE).mp hPE
  refine ⟨E - P, hEP, ?_, ?_, ?_⟩
  · exact sub_le_self E hP.nonneg
  · rw [map_sub, Complex.sub_re]
    linarith
  · intro q hq hqEP
    by_contra hqneg
    have hqn : (F q).re < 0 := lt_of_not_ge hqneg
    have hqE : q ≤ E := hqEP.trans (sub_le_self E hP.nonneg)
    have hPq : P * q = 0 := HochschildCentralComparison.orthogonal_of_le_sub hE hP hq hPE hqEP
    have hfq (i : S) : f i * q = 0 := by
      calc
        f i * q = (f i * P) * q := by rw [((hp i).le_iff_mul_eq_left hP).mp (hPu i)]
        _ = 0 := by rw [mul_assoc, hPq, mul_zero]
    have hqf (i : S) : q * f i = 0 := by
      simpa only [star_mul, (hp i).isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_zero] using congrArg star (hfq i)
    have hnew : insert q S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hq, hqE, hqn⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact hqf ⟨b, hb⟩
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hfq ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert q S ⊆ S := hS.2 hnew (Set.subset_insert q S)
    have hqin : q ∈ S := hsubset (Set.mem_insert q S)
    have hq0 : q = 0 := by simpa only [f, hq.isIdempotentElem.eq] using hfq ⟨q, hqin⟩
    simp only [hq0, map_zero, Complex.zero_re, lt_self_iff_false] at hqn
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

theorem exists_additive_positive_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : CompletelyAdditive (positiveFunctionalCLM ψ)) :
    ∃ p : M, IsStarProjection p ∧ ψ p = ψ 1 ∧
      ∀ q : M, IsStarProjection q → q ≤ p → ψ q = 0 → q = 0 := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧ p ≠ 0 ∧ ψ p = 0) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p * q = 0}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro p hp
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      exact (hc hs).1 p hps
    · intro p hp q hq hpq
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 p (hst hps) q hqt hpq
      · exact (hc hs).2 p hps q (hts hqt) hpq)
  let f : S → M := Subtype.val
  have hf (i : S) : IsStarProjection (f i) := (hS.1.1 i i.property).1
  have ho (i j : S) (hij : i ≠ j) : f i * f j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨P, hP, hPu, hPl, _⟩ := exists_orthogonal_projection_sum e f hf ho
  have hPnull : ψ P = 0 := by
    have ht := hψ S f hf ho P hP hPu hPl
    have heq : (fun s : Finset S => ∑ i ∈ s, positiveFunctionalCLM ψ (f i)) =
        (fun _ : Finset S => (0 : ℂ)) := by
      funext s
      apply Finset.sum_eq_zero
      intro i _
      exact (hS.1.1 i i.property).2.2
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨1 - P, hP.one_sub, ?_, ?_⟩
  · rw [map_sub, hPnull, sub_zero]
  · intro q hq hqP hnull
    by_contra hq0
    have hPq : P * q = 0 :=
      HochschildTypeII.projection_orthogonal_of_le_complement hP hq hqP
    have hfq (i : S) : f i * q = 0 := by
      calc
        f i * q = (f i * P) * q := by rw [((hf i).le_iff_mul_eq_left hP).mp (hPu i)]
        _ = 0 := by rw [mul_assoc, hPq, mul_zero]
    have hqf (i : S) : q * f i = 0 := by
      simpa only [star_mul, (hf i).isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_zero] using congrArg star (hfq i)
    have hnew : insert q S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hq, hq0, hnull⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact hqf ⟨b, hb⟩
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hfq ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert q S ⊆ S := hS.2 hnew (Set.subset_insert q S)
    have hqin : q ∈ S := hsubset (Set.mem_insert q S)
    exact hq0 (by simpa only [f, hq.isIdempotentElem.eq] using hfq ⟨q, hqin⟩)
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

open HochschildNormalPart HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def compressionPositive {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) : M →ₚ[ℂ] ℂ where
  toLinearMap :=
    { toFun := fun a => ψ (p * a * p)
      map_add' := by intro a b; simp only [mul_add, add_mul, map_add]
      map_smul' := by intro c a; simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply] }
  monotone' := fun _ _ hab => ψ.monotone (by
    simpa only [hp.isSelfAdjoint.star_eq] using star_right_conjugate_le_conjugate hab p)

lemma compressionPositive_clm {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (compressionPositive hp ψ) =
      ((positiveFunctionalCLM ψ).comp ((ContinuousLinearMap.mul ℂ M).flip p)).comp
        (ContinuousLinearMap.mul ℂ M p) := rfl

@[simp] lemma compressionPositive_one {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) :
    compressionPositive hp ψ 1 = ψ p := by
  change ψ (p * 1 * p) = ψ p
  rw [mul_one, hp.isIdempotentElem.eq]

lemma compressionPositive_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    TraceInPredual e (compressionPositive hp ψ) := by
  apply (mem_normalDual e (positiveFunctionalCLM (compressionPositive hp ψ))).mp
  rw [compressionPositive_clm]
  apply normalDual_comp e _ _ (HochschildSakai.mul_hasPreadjoint e p)
  exact normalDual_comp e ((mem_normalDual e (positiveFunctionalCLM ψ)).mpr hψ) _
    ((HochschildSakai.abstract_multiplication_normal e).2 p)

theorem singular_zero_of_normal_compression (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ)
    (hs : scalarNormalPart e (positiveFunctionalCLM ψ) = 0)
    (hn : TraceInPredual e (compressionPositive hp ψ)) : ψ p = 0 := by
  have hfix := scalarNormalPart_fixes e ((mem_normalDual e (positiveFunctionalCLM (compressionPositive hp ψ))).mpr hn)
  rw [compressionPositive_clm, scalarNormalPart_comp_left, scalarNormalPart_comp_right, hs] at hfix
  have hc : positiveFunctionalCLM (compressionPositive hp ψ) = 0 := by
    rw [compressionPositive_clm]
    simpa only [ContinuousLinearMap.zero_comp] using hfix.symm
  have he := congrArg (fun F : StrongDual ℂ M => F 1) hc
  change ψ (p * 1 * p) = 0 at he
  simpa only [mul_one, hp.isIdempotentElem.eq] using he

theorem compression_normal_of_projection_dominance (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (χ ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hle : ∀ q : M, IsStarProjection q → q ≤ p → χ q ≤ ψ q) :
    TraceInPredual e (compressionPositive hp χ) := by
  let L := CentralCorner.includeMap p hp
  let F := (positiveFunctionalCLM ψ - positiveFunctionalCLM χ).comp L
  have hreal : ∀ a : Corner p hp, IsSelfAdjoint a → (F a).im = 0 := by
    intro a ha
    have haM : IsSelfAdjoint (a : M) := congrArg Subtype.val ha.star_eq
    have hψa : (ψ (a : M)).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (haM.map ψ)
    have hχa : (χ (a : M)).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (haM.map χ)
    change (ψ (a : M) - χ (a : M)).im = 0
    rw [Complex.sub_im, hψa, hχa, sub_self]
  have hproj : ∀ q : Corner p hp, IsStarProjection q → 0 ≤ F q := by
    intro q hq
    change 0 ≤ ψ (q : M) - χ (q : M)
    exact sub_nonneg.mpr (hle q (corner_projection_coe p hp hq) (corner_projection_le p hp hq))
  apply positive_normal_of_dominated e (compressionPositive hp χ) (compressionPositive hp ψ)
    (compressionPositive_normal e hp ψ hψ)
  intro a ha
  let c : Corner p hp := ⟨p * a * p, by
    constructor
    · rw [← mul_assoc, ← mul_assoc, hp.isIdempotentElem.eq]
    · rw [mul_assoc, hp.isIdempotentElem.eq]⟩
  have hc : 0 ≤ c := by
    change 0 ≤ p * a * p
    simpa only [hp.isSelfAdjoint.star_eq] using star_right_conjugate_nonneg ha p
  have hh := eval_nonneg_of_projection_nonneg (cornerPredualEquiv p hp e) F hreal hproj c hc
  exact sub_nonneg.mp hh
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

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma positiveFunctional_zero_of_one_zero (ψ : M →ₚ[ℂ] ℂ) (hψ : ψ 1 = 0) :
    positiveFunctionalCLM ψ = 0 := by
  ext a
  change ψ a = 0
  have h := Compat.norm_map_star_mul_sq_le ψ (1 : M) a
  simp only [star_one, one_mul, hψ, norm_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ψ a)])

lemma exists_normal_positive_larger_on_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {E : M} (hE : IsStarProjection E) (hE0 : E ≠ 0) (c : ℝ) :
    ∃ φ : M →ₚ[ℂ] ℂ, TraceInPredual e φ ∧ c < (φ E).re := by
  obtain ⟨ρ, hρ, _, hρE, _⟩ := exists_normal_state_on_projection e hE hE0
  let C : ℝ := max c 0 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let φ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (C : ℂ) • ρ.toLinearMap
      monotone' := fun _ _ hab => mul_le_mul_of_nonneg_left (ρ.monotone hab)
        (Complex.zero_le_real.mpr hC) }
  refine ⟨φ, ?_, ?_⟩
  · have hφ : positiveFunctionalCLM φ = (C : ℂ) • positiveFunctionalCLM ρ := rfl
    apply (mem_normalDual e (positiveFunctionalCLM φ)).mp
    rw [hφ]
    exact (normalDual e).smul_mem _ ((mem_normalDual e (positiveFunctionalCLM ρ)).mpr hρ)
  · change c < ((C : ℂ) * ρ E).re
    rw [hρE, mul_one, Complex.ofReal_re]
    dsimp [C]
    linarith [le_max_left c 0]

theorem positive_normal_of_completelyAdditive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : CompletelyAdditive (positiveFunctionalCLM ψ)) :
    TraceInPredual e ψ := by
  classical
  let χ := positiveSingularPart e ψ
  have hχeq : positiveFunctionalCLM χ =
      positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) :=
    positiveSingularPart_eq e ψ
  have hχadd : CompletelyAdditive (positiveFunctionalCLM χ) := by
    rw [hχeq]
    exact hψ.sub (normal_completelyAdditive e (scalarNormalPart_mem e _))
  have hχsing : scalarNormalPart e (positiveFunctionalCLM χ) = 0 := by
    rw [hχeq, map_sub, scalarNormalPart_fixes e (scalarNormalPart_mem e _), sub_self]
  have hχzero : positiveFunctionalCLM χ = 0 := by
    by_contra hχne
    have hχ1 : χ 1 ≠ 0 := fun hz => hχne (positiveFunctional_zero_of_one_zero χ hz)
    obtain ⟨E, hE, hχE, hfaith⟩ := exists_additive_positive_support e χ hχadd
    have hE0 : E ≠ 0 := by
      intro hE0
      apply hχ1
      rw [← hχE, hE0, map_zero]
    obtain ⟨φ, hφ, hlarge⟩ := exists_normal_positive_larger_on_projection e hE hE0 (χ E).re
    let F := positiveFunctionalCLM φ - positiveFunctionalCLM χ
    have hF : CompletelyAdditive F := (normal_completelyAdditive e
      ((mem_normalDual e (positiveFunctionalCLM φ)).mpr hφ)).sub hχadd
    obtain ⟨p, hp, hpE, hEp, hnonneg⟩ := exists_nonnegative_projection_corner e F hF hE
    have hFE : 0 < (F E).re := by
      change 0 < (φ E - χ E).re
      rw [Complex.sub_re]
      exact sub_pos.mpr hlarge
    have hp0 : p ≠ 0 := by
      intro hp0
      rw [hp0, map_zero, Complex.zero_re] at hEp
      linarith
    have hdom : ∀ q : M, IsStarProjection q → q ≤ p → χ q ≤ φ q := by
      intro q hq hqp
      apply sub_nonneg.mp
      apply Complex.nonneg_iff.mpr
      constructor
      · exact hnonneg q hq hqp
      · have hχq : (χ q).im = 0 := (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
          (hq.isSelfAdjoint.map χ)
        have hφq : (φ q).im = 0 := (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
          (hq.isSelfAdjoint.map φ)
        simp only [Complex.sub_im, hφq, hχq, sub_self]
    have hn := compression_normal_of_projection_dominance e hp χ φ hφ hdom
    have hpnull := singular_zero_of_normal_compression e hp χ hχsing hn
    exact hp0 (hfaith p hp hpE hpnull)
  have hfix : scalarNormalPart e (positiveFunctionalCLM ψ) = positiveFunctionalCLM ψ := by
    rw [hχeq] at hχzero
    exact (sub_eq_zero.mp hχzero).symm
  apply (mem_normalDual e (positiveFunctionalCLM ψ)).mp
  rw [← hfix]
  exact scalarNormalPart_mem e _
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

universe u v

private lemma disjoint_finset_sequence {I : Type v} (B : Finset I → Prop)
    (hB : ∀ s : Finset I, ∃ t : Finset I, Disjoint s t ∧ B t) :
    ∃ b : ℕ → Finset I, (∀ m n, m ≠ n → Disjoint (b m) (b n)) ∧ ∀ n, B (b n) := by
  classical
  let next (s : Finset I) := (hB s).choose
  have hn (s) : Disjoint s (next s) ∧ B (next s) := (hB s).choose_spec
  let c : ℕ → Finset I := Nat.rec ∅ (fun _ s => s ∪ next s)
  have hc (n) : c (n + 1) = c n ∪ next (c n) := rfl
  have hm : Monotone c := monotone_nat_of_le_succ (fun n => by
    rw [hc]; exact Finset.subset_union_left)
  let b (n : ℕ) := next (c n)
  have hlt (m n : ℕ) (hmn : m < n) : Disjoint (b m) (b n) := by
    apply (hn (c n)).1.mono_left
    exact (show b m ⊆ c (m + 1) by rw [hc]; exact Finset.subset_union_right).trans
      (hm (Nat.succ_le_iff.mpr hmn))
  refine ⟨b, ?_, fun n => (hn (c n)).2⟩
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · exact (hlt n m h).symm

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma orthogonal_projection_finset_sum_le {I : Type v} (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0)
    {P : M} (hP : IsStarProjection P) (hu : ∀ i, p i ≤ P) (s : Finset I) :
    (∑ i ∈ s, p i) ≤ P := by
  classical
  apply ((orthogonal_projection_finset_sum p hp ho s).le_iff_mul_eq_left hP).mpr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => ((hp i).le_iff_mul_eq_left hP).mp (hu i))

omit [StarOrderedRing M] in

theorem uniform_orthogonal_sum_remainder
    (K : Set (StrongDual ℂ M))
    (hadd : ∀ F ∈ K, CompletelyAdditive F)
    (hdecay : ∀ q : ℕ → M, (∀ n, IsStarProjection (q n)) →
      (∀ m n, m ≠ n → q m * q n = 0) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ F ∈ K, ‖F (q n)‖ < ε)
    (I : Type u) (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (P : M) (hP : IsStarProjection P) (hu : ∀ i, p i ≤ P)
    (hl : ∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset I, ∀ F ∈ K, (F (P - ∑ i ∈ s, p i)).re < ε := by
  classical
  by_contra hfail
  push Not at hfail
  have hb : ∀ s : Finset I, ∃ t : Finset I, Disjoint s t ∧
      ∃ F ∈ K, ε / 2 < (F (∑ i ∈ t, p i)).re := by
    intro s
    obtain ⟨F, hFK, hbad⟩ := hfail s
    have ht := Complex.continuous_re.tendsto (F P) |>.comp (hadd F hFK I p hp ho P hP hu hl)
    have hevent : ∀ᶠ t : Finset I in atTop,
        (F P).re - ε / 2 < (∑ i ∈ t, F (p i)).re :=
      (tendsto_order.mp ht).1 _ (by linarith)
    obtain ⟨t, hts, htlarge⟩ := ((eventually_ge_atTop s).and hevent).exists
    refine ⟨t \ s, Finset.disjoint_sdiff, F, hFK, ?_⟩
    have hsum : (∑ i ∈ t \ s, p i) + ∑ i ∈ s, p i = ∑ i ∈ t, p i :=
      Finset.sum_sdiff hts
    have hval := congrArg (fun a : M => (F a).re) hsum
    simp only [map_add, Complex.add_re, map_sum] at hval
    simp only [map_sub, Complex.sub_re, map_sum] at hbad
    rw [map_sum]
    linarith
  obtain ⟨b, hdis, hb⟩ := disjoint_finset_sequence
    (fun t : Finset I => ∃ F ∈ K, ε / 2 < (F (∑ i ∈ t, p i)).re) hb
  let q (n : ℕ) : M := ∑ i ∈ b n, p i
  have hq (n) : IsStarProjection (q n) := orthogonal_projection_finset_sum p hp ho (b n)
  have hqo (m n : ℕ) (hmn : m ≠ n) : q m * q n = 0 := by
    dsimp [q]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact ho i j (fun hij => Finset.disjoint_left.mp (hdis m n hmn) hi (hij ▸ hj))
  obtain ⟨n, hn⟩ := (hdecay q hq hqo (ε / 2) (half_pos hε)).exists
  obtain ⟨F, hFK, hlarge⟩ := hb n
  have hsmall := hn F hFK
  have hre := Complex.re_le_norm (F (q n))
  exact (not_lt_of_ge (le_trans hlarge.le hre)) hsmall
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

theorem weakFunctionalClosure_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (K : Set (StrongDual ℂ M))
    (hpos : ∀ F ∈ K, ∀ a : M, 0 ≤ a → 0 ≤ F a)
    (hnormal : ∀ F ∈ K, F ∈ normalDual e)
    (hdecay : ∀ q : ℕ → M, (∀ n, IsStarProjection (q n)) →
      (∀ m n, m ≠ n → q m * q n = 0) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ F ∈ K, ‖F (q n)‖ < ε)
    {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    WeakDual.toStrongDual F ∈ normalDual e := by
  classical
  have hFpos := weakFunctionalClosure_positive K hpos hF
  let ψ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (WeakDual.toStrongDual F).toLinearMap
      monotone' := (monotone_iff_map_nonneg _).mpr hFpos }
  apply (mem_normalDual e (positiveFunctionalCLM ψ)).mpr
  apply positive_normal_of_completelyAdditive e ψ
  intro I p hp ho P hP hu hl
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := uniform_orthogonal_sum_remainder K
    (fun G hG => normal_completelyAdditive e (hnormal G hG))
    hdecay I p hp ho P hP hu hl (ε / 2) (half_pos hε)
  have hsmall : (F (P - ∑ i ∈ s, p i)).re ≤ ε / 2 := by
    apply closure_minimal
      (t := {G : WeakDual ℂ M | (G (P - ∑ i ∈ s, p i)).re ≤ ε / 2}) _
      (isClosed_le (Complex.continuous_re.comp (WeakDual.eval_continuous _))
        continuous_const) hF
    rintro _ ⟨G, hGK, rfl⟩
    exact (hs G hGK).le
  refine ⟨s, fun t hst => ?_⟩
  have hsum : (∑ i ∈ s, p i) ≤ ∑ i ∈ t, p i :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (hp i).nonneg)
  have htail : 0 ≤ P - ∑ i ∈ t, p i :=
    sub_nonneg.mpr (orthogonal_projection_finset_sum_le p hp ho hP hu t)
  have horder : 0 ≤ F (P - ∑ i ∈ s, p i) - F (P - ∑ i ∈ t, p i) := by
    rw [← map_sub]
    apply hFpos
    exact sub_nonneg.mpr (sub_le_sub_left hsum P)
  have hposval := hFpos _ htail
  have hnorm : ‖F (P - ∑ i ∈ t, p i)‖ ≤ ε / 2 := by
    have hle : F (P - ∑ i ∈ t, p i) ≤ (ε / 2 : ℝ) := by
      apply Complex.le_def.mpr
      constructor
      · exact ((Complex.nonneg_iff.mp horder).1 |> fun h => by
          rw [Complex.sub_re] at h
          simpa only [Complex.ofReal_re] using (by linarith : (F (P - ∑ i ∈ t, p i)).re ≤ ε / 2))
      · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hposval).2.symm
    calc
      ‖F (P - ∑ i ∈ t, p i)‖ ≤ ‖((ε / 2 : ℝ) : ℂ)‖ :=
        Compat.norm_le_norm_of_le_of_nonneg hle hposval
      _ = ε / 2 := Complex.norm_of_nonneg (half_pos hε).le
  rw [dist_eq_norm, ← map_sum]
  change ‖F (∑ i ∈ t, p i) - F P‖ < ε
  simpa only [map_sub, norm_sub_rev] using hnorm.trans_lt (half_lt_self hε)

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryPullback_norm_le (F : StrongDual ℂ M) (u : unitary M) :
    ‖unitaryPullback F u‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have hn : ‖(u : M) * a * star (u : M)‖ = ‖a‖ := by
    rw [show star (u : M) = (star u : unitary M) from rfl,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simpa only [unitaryPullback_apply, hn] using F.le_opNorm ((u : M) * a * star (u : M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_norm_le (F : StrongDual ℂ M) {G : StrongDual ℂ M}
    (hG : G ∈ unitaryOrbitHull F) : ‖G‖ ≤ ‖F‖ := by
  have hsubset : unitaryOrbitHull F ⊆ Metric.closedBall 0 ‖F‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    apply convexHull_min _ (convex_closedBall (0 : StrongDual ℂ M) ‖F‖)
    rintro _ ⟨u, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using unitaryPullback_norm_le F u
  simpa only [Metric.mem_closedBall, dist_zero_right] using hsubset hG

theorem normal_positive_orbit_compact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    IsCompact (weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))) ∧
      ∀ F ∈ weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ)),
        WeakDual.toStrongDual F ∈ normalDual e := by
  constructor
  · apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ M)
      ‖positiveFunctionalCLM ψ‖).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (WeakDual.isClosed_closedBall 0 _)
    rintro _ ⟨G, hG, rfl⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual] using
      unitaryOrbitHull_norm_le (positiveFunctionalCLM ψ) hG
  · intro F hF
    apply weakFunctionalClosure_normal e _ (unitaryOrbitHull_positive ψ)
      (fun _ hG => unitaryOrbitHull_normal e
        ((mem_normalDual e (positiveFunctionalCLM ψ)).mpr hψ) hG) _ hF
    exact fun q hq ho ε hε => normal_positive_uniform_orbit_hull e hfinite ψ hψ q hq ho ε hε
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
  [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma weakPredualMap_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Continuous (weakPredualMap e) := by
  apply WeakDual.continuous_of_continuous_eval
  intro a
  exact (WeakBilin.eval_continuous (topDualPairing ℂ X).flip (e.symm a)).star

theorem weakPredualMap_isEmbedding (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Topology.IsEmbedding (weakPredualMap e) := by
  let g (F : WeakDual ℂ M) (f : StrongDual ℂ X) : ℂ := star (F (e f))
  have hg : Continuous g := continuous_pi (fun f => (WeakDual.eval_continuous (e f)).star)
  have heq : g ∘ weakPredualMap e = fun x : WeakSpace ℂ X =>
      fun f : StrongDual ℂ X => f ((toWeakSpace ℂ X).symm x) := by
    funext x f
    simp only [Function.comp_apply, g, weakPredualMap_apply, e.symm_apply_apply, star_star]
  apply Topology.IsEmbedding.of_comp (weakPredualMap_continuous e) hg
  rw [heq]
  exact WeakBilin.isEmbedding (B := (topDualPairing ℂ X).flip) (fun x y h => by
    apply (toWeakSpace ℂ X).symm.injective
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro f
    exact congrArg (fun L : StrongDual ℂ X →ₗ[ℂ] ℂ => L f) h)

lemma range_weakPredualMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Set.range (weakPredualMap e) =
      {F : WeakDual ℂ M | WeakDual.toStrongDual F ∈ normalDual e} := by
  ext F
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(toWeakSpace ℂ X).symm x, rfl⟩
  · intro hF
    obtain ⟨x, hx⟩ := hF
    refine ⟨toWeakSpace ℂ X x, ?_⟩
    exact congrArg StrongDual.toWeakDual hx

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

theorem normal_positive_predual_orbit_compact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    IsCompact ((weakPredualMap e) ⁻¹'
      weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))) := by
  obtain ⟨hc, hn⟩ := normal_positive_orbit_compact e hfinite ψ hψ
  apply (weakPredualMap_isEmbedding e).isInducing.isCompact_preimage' hc
  intro F hF
  rw [range_weakPredualMap]
  exact hn F hF
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.normal_positive_predual_orbit_compact.{u} := @OAI.BoundedHochschild.KadisonRingrose.normal_positive_predual_orbit_compact.{u}
