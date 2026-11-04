-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.WeightedFock.scalar_hasCornerScaling_weighted
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:57:03.928338+00:00
-- url     : https://prove2.me/submissions/4198dfb3-81f2-487b-90ee-7bdbba0489b9

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_weighted_generated_eq_ambient
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_pRightEdge_mem_weightedCommutant
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_weightedFull_left
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_weightedFull_right
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_weightedFull_initial
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_ambientScalarIso_trace

set_option linter.all false

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45

namespace Amplification

section

variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

 theorem map_projection (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    IsStarProjection (Φ p) := hp.map Φ

def cornerCongr (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    Corner p hp ≃⋆ₐ[ℂ] Corner (Φ p) (map_projection Φ p hp) where
  toFun x := ⟨Φ x,by
    constructor
    · rw [← map_mul,x.property.1]
    · rw [← map_mul,x.property.2]⟩
  invFun y := ⟨Φ.symm y,by
    constructor
    · have hy := congrArg Φ.symm y.property.1
      simpa only [map_mul,Φ.symm_apply_apply] using hy
    · have hy := congrArg Φ.symm y.property.2
      simpa only [map_mul,Φ.symm_apply_apply] using hy⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul Φ (x : A) (y : A))
  map_add' x y := Subtype.ext (map_add Φ (x : A) (y : A))
  map_smul' z x := Subtype.ext (map_smul Φ z (x : A))
  map_star' x := Subtype.ext (map_star Φ (x : A))

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

 theorem cornerCongr_normal (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (hΦ : @Continuous _ _ 𝒯A 𝒯B Φ) :
    @Continuous _ _ (cornerTopology 𝒯A p hp)
      (cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)) (cornerCongr Φ p hp) := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
  let : TopologicalSpace (Corner (Φ p) (map_projection Φ p hp)) :=
    cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)
  exact (hΦ.comp continuous_subtype_val).subtype_mk _

end

open scoped ENNReal

end Amplification

namespace FreeFock
open scoped ENNReal

variable {α : Type u_15} {β : Type u_16} [DecidableEq α] [DecidableEq β]

end FreeFock
open Filter Topology

namespace Amplification

section
variable {A : Type u_17} {B : Type u_18} [CStarAlgebra A] [CStarAlgebra B]

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_19} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ENNReal ComplexConjugate
attribute [local instance] OAI.FreeGroupFactorMain.Amplification.instDecidableEqNestedHilbert

variable {I : Type u_21} {J : Type u_22}

end
section
open scoped ENNReal

variable {I : Type u_35} {J : Type u_36}

variable {G : Type u_37} [Group G]

end

section
open scoped ENNReal
variable {G : Type u_38}

variable [Group G]

end

open scoped ENNReal
variable {G : Type u_45} [Group G]

end Amplification

namespace Interpolation

open Amplification
open scoped ENNReal

end Interpolation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.CornerRerouting

section
variable {A : Type u_1} [Ring A] [StarRing A]

 def Supported (p x : A) : Prop := p*x=x ∧ x*p=x
 def lift (v t : A) : A := t+star v*t*v

 theorem supported_star {p t : A} (hp : IsSelfAdjoint p) (ht : Supported p t) :
    Supported p (star t) := by
  constructor
  · simpa only [star_mul,hp.star_eq] using congrArg star ht.2
  · simpa only [star_mul,hp.star_eq] using congrArg star ht.1

 theorem supported_mul_star_zero {p v t : A} (hvp : v*p=0) (hp : IsSelfAdjoint p)
    (ht : Supported p t) : t*star v=0 := by
  calc
    _ = (t*p)*star v := by rw [ht.2]
    _ = t*(p*star v) := mul_assoc _ _ _
    _ = 0 := by rw [star_left_zero hp hvp,mul_zero]

omit [StarRing A] in
 theorem mul_supported_zero {p v t : A} (hvp : v*p=0) (ht : Supported p t) : v*t=0 := by
  calc
    _ = v*(p*t) := by rw [ht.1]
    _ = (v*p)*t := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hvp,zero_mul]

 theorem lift_mul_supported {p v t y : A} (hvp : v*p=0) (hy : Supported p y) :
    lift v t*y=t*y := by
  unfold lift
  rw [add_mul,mul_assoc (star v*t),mul_supported_zero hvp hy,mul_zero,add_zero]

 theorem supported_mul_lift {p v t y : A} (hp : IsSelfAdjoint p) (hvp : v*p=0)
    (hy : Supported p y) : y*lift v t=y*t := by
  unfold lift
  rw [mul_add,← mul_assoc y,← mul_assoc y,supported_mul_star_zero hvp hp hy,
    zero_mul,zero_mul,add_zero]

 theorem lift_commute_supported {p v t y : A} (hp : IsSelfAdjoint p) (hvp : v*p=0)
    (hy : Supported p y) (h : Commute t y) : Commute (lift v t) y := by
  change lift v t*y=y*lift v t
  rw [lift_mul_supported hvp hy,supported_mul_lift hp hvp hy]
  exact h.eq

omit [StarRing A] in
 theorem square_zero {p v : A} (hpv : p*v=v) (hvp : v*p=0) : v*v=0 := by
  calc
    _ = v*(p*v) := by rw [hpv]
    _ = (v*p)*v := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hvp,zero_mul]

 theorem range_mul {p v : A} (hi : star v*v=1-p) (hr : v*(1-p)=v) :
    (v*star v)*v=v := by rw [mul_assoc,hi,hr]

 theorem lift_commute_edge {p v t : A} (hpv : p*v=v) (hvp : v*p=0)
    (hi : star v*v=1-p) (hr : v*(1-p)=v) (ht : Supported p t)
    (htr : Commute t (v*star v)) : Commute (lift v t) v := by
  change lift v t*v=v*lift v t
  have hleft : lift v t*v=t*v := by
    unfold lift
    rw [add_mul,mul_assoc (star v*t),square_zero hpv hvp,mul_zero,add_zero]
  have hright : v*lift v t=t*v := by
    unfold lift
    rw [mul_add,mul_supported_zero hvp ht,zero_add,← mul_assoc v,← mul_assoc v,
      ← htr.eq,mul_assoc t,range_mul hi hr]
  exact hleft.trans hright.symm

 theorem star_lift (v t : A) : star (lift v t)=lift v (star t) := by
  simp only [lift,star_add,star_mul,star_star,mul_assoc]

 theorem lift_commute_edge_star {p v t : A} (hp : IsSelfAdjoint p)
    (hpv : p*v=v) (hvp : v*p=0) (hi : star v*v=1-p) (hr : v*(1-p)=v)
    (ht : Supported p t) (htr : Commute t (v*star v)) :
    Commute (lift v t) (star v) := by
  have hs : Commute (star t) (v*star v) := by
    simpa only [star_mul,star_star] using htr.star_star
  have hh := (lift_commute_edge hpv hvp hi hr (supported_star hp ht) hs).star_star
  simpa only [star_lift,star_star] using hh

end
section
variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {ι : Type u_3}

end
variable {A : Type u_4} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.CornerRerouting
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification.Polar
variable {ι : Type u_5} [DecidableEq ι]

end
section
open FreeFock
variable {ι : Type u_6} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_8} [DecidableEq ι]

end
open FreeFock
variable {ι : Type u_9} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

section
namespace FreeGroupFactorMain.GramSpatial
variable {I : Type u_1} {E : Type u_2} {F : Type u_3}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem spatial_trace (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j))
    (hx : (Submodule.span ℂ (Set.range x)).topologicalClosure=⊤)
    (hy : (Submodule.span ℂ (Set.range y)).topologicalClosure=⊤)
    (i₀ : I) (T : E →L[ℂ] E) :
    inner ℂ (y i₀) ((spatial x y hg hx hy).conjStarAlgEquiv T (y i₀))=
      inner ℂ (x i₀) (T (x i₀)) := by
  let W := spatial x y hg hx hy
  have he : W (x i₀)=y i₀ := spatial_family x y hg hx hy i₀
  rw [← he,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,W.symm_apply_apply,
    W.inner_map_map]

end FreeGroupFactorMain.GramSpatial
namespace FreeGroupFactorMain.GaussianRecognition
variable (A : Type u_4) (E : Type u_5) (I : Type u_6) [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {A E I} {covariance : I → I → A → A}
variable (X : System A E I covariance)

namespace System

variable {F : Type u_9} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (Y : System A F I covariance)

variable
  (hstate : ∀ a, inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

theorem spatial_trace (T : Operator E) :
    inner ℂ Y.root ((spatial X Y hstate hX hY).conjStarAlgEquiv T Y.root)=
      inner ℂ X.root (T X.root) := by
  have h := GramSpatial.spatial_trace X.family Y.family
    (fun w z => normal_inner_eq X Y hstate w.1 z.1 w.2 z.2) hX hY (1,[]) T
  simpa only [spatial,family,normal,map_one,one_apply_eq_self] using h

end System
end FreeGroupFactorMain.GaussianRecognition

end

namespace FreeGroupFactorMain.GaussianRecognition
open CyclicSpectral

end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition WeightedCornerIndex

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

end

section
open MeasureTheory
variable {α : Type u_2} [DecidableEq α]

end
section
open CyclicSpectral MeasureTheory
variable {α : Type u_3} [DecidableEq α]

end

open CyclicSpectral GaussianRecognition CircularRotation WeightedCornerIndex

theorem scalar_weighted_state (u v : ℝ) (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) :
    inner ℂ scalarSystem.root (scalarSystem.coeff a scalarSystem.root)=
      inner ℂ (WeightedFock.weightedSystem u v hv hvu).root
        ((WeightedFock.weightedSystem u v hv hvu).coeff a (WeightedFock.weightedSystem u v hv hvu).root) := by
  change vacuumTrace (scalarUniform (none : ScalarIndex) a)=
    inner ℂ WeightedFock.pRoot (WeightedFock.weightedUniform u v hv hvu a WeightedFock.pRoot)
  rw [scalarUniform_state,WeightedFock.weightedUniform_state]
end FreeGroupFactorMain.FreeFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.GaussianRecognition
section Algebraic
variable {A : Type u_1} {B : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

end Algebraic

variable {E : Type u_3} {F : Type u_4}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def sequenceMap (W : E ≃ₗᵢ[ℂ] F) (ξ : lp (fun _ : ℕ => E) 2) : lp (fun _ : ℕ => F) 2 :=
  ⟨fun n => W (ξ n),Memℓp.of_norm (by simpa only [W.norm_map] using (lp.memℓp ξ).norm)⟩

theorem spatial_normal (W : E ≃ₗᵢ[ℂ] F) :
    @Continuous _ _ (ultraweak E) (ultraweak F) W.conjStarAlgEquiv := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have heq :
      (fun T : Operator E => ∑' k : ℕ,inner ℂ (η k) (W.conjStarAlgEquiv T (ξ k)))=
      (fun T : Operator E => ∑' k : ℕ,
        inner ℂ (sequenceMap W.symm η k) (T (sequenceMap W.symm ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    change inner ℂ (η k) (W (T (W.symm (ξ k)))) =
      inner ℂ (W.symm (η k)) (T (W.symm (ξ k)))
    rw [← W.inner_map_map]
    simp
  change @Continuous _ _ (ultraweak E) _
    (fun T : Operator E => ∑' k : ℕ,inner ℂ (η k) (W.conjStarAlgEquiv T (ξ k)))
  rw [heq]
  exact continuous_iInf_dom (i := sequenceMap W.symm ξ)
    (continuous_iInf_dom (i := sequenceMap W.symm η) continuous_induced_dom)

namespace System
variable {A : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable {covariance : I → I → A → A}
variable (X : System A E I covariance) (Y : System A F I covariance)
variable
  (hstate : ∀ a,inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

theorem generatedIso_normal (σ : I → I) :
    @Continuous _ _ (X.generatedTopology σ) (Y.generatedTopology σ)
      (X.generatedIso Y hstate hX hY σ) := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (Operator F) := ultraweak F
  let : TopologicalSpace (X.generated σ) := X.generatedTopology σ
  let : TopologicalSpace (Y.generated σ) := Y.generatedTopology σ
  apply continuous_induced_rng.mpr
  have hi : Continuous (fun T : X.generated σ => (T : Operator E)) := continuous_induced_dom
  exact (spatial_normal (X.spatial Y hstate hX hY)).comp hi

theorem generatedIso_trace (σ : I → I) (T : X.generated σ) :
    inner ℂ Y.root ((X.generatedIso Y hstate hX hY σ T : Operator F) Y.root)=
      inner ℂ X.root ((T : Operator E) X.root) :=
  X.spatial_trace Y hstate hX hY (T : Operator E)

end System
end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_8} {E : Type u_9} {I : Type u_10} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

end FreeGroupFactorMain.GaussianRecognition.System

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock MeasureTheory CyclicSpectral
variable {ι : Type u_1} [DecidableEq ι]

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock WeightedCornerIndex GaussianRecognition CyclicSpectral

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock CyclicSpectral GaussianRecognition Filter Topology
open scoped ENNReal
variable {ι : Type u_2} [DecidableEq ι]

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

open FreeFock GaussianRecognition CyclicSpectral
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

theorem ambientGaussianIso_normal :
    @Continuous _ _ ((ambientSystem u v hu hv hunit).generatedTopology scalarFlip)
      (scalarSystem.generatedTopology scalarFlip) (ambientGaussianIso u v hu hv hunit) :=
  (ambientSystem u v hu hv hunit).generatedIso_normal scalarSystem
    (scalar_ambient_state u v hu hv hunit)
    (ambientSystem_total u v hu hv hunit) scalarSystem_total scalarFlip

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.HilbertUltraweak
variable (E : Type u_1) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[instance_reducible] def topology : TopologicalSpace (E →L[ℂ] E) :=
  ⨅ (ξ : lp (fun _ : ℕ => E) 2) (η : lp (fun _ : ℕ => E) 2),
    TopologicalSpace.induced (fun T : E →L[ℂ] E => ∑' k : ℕ, inner ℂ (η k) (T (ξ k))) inferInstance

variable {E} {F : Type u_2} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
def sequenceMap (L : E →L[ℂ] F) (ξ : lp (fun _ : ℕ => E) 2) : lp (fun _ : ℕ => F) 2 :=
  ⟨fun k => L (ξ k),((lp.memℓp ξ).norm.const_mul ‖L‖).mono (fun k => L.le_opNorm (ξ k))⟩

omit [CompleteSpace E] in
theorem functional_continuous (ξ η : lp (fun _ : ℕ => E) 2) :
    @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (T (ξ k))) :=
  continuous_iInf_dom (i := ξ) (continuous_iInf_dom (i := η) continuous_induced_dom)

theorem sandwich_continuous (L : E →L[ℂ] F) (R : F →L[ℂ] E) :
    @Continuous _ _ (topology E) (topology F) (fun T : E →L[ℂ] E => L.comp (T.comp R)) := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he : (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))=
      (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (sequenceMap (ContinuousLinearMap.adjoint L) η k)
        (T (sequenceMap R ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    exact (ContinuousLinearMap.adjoint_inner_left L (T (R (ξ k))) (η k)).symm
  change @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))
  rw [he]
  exact functional_continuous _ _

omit [CompleteSpace E] in
theorem add_continuous {X : Type u_3} [TopologicalSpace X] {f g : X → (E →L[ℂ] E)}
    (hf : @Continuous _ _ _ (topology E) f) (hg : @Continuous _ _ _ (topology E) g) :
    @Continuous _ _ _ (topology E) (fun x => f x+g x) := by
  let : TopologicalSpace (E →L[ℂ] E) := topology E
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he (x : X) :
      (∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))=
        (∑' k : ℕ,inner ℂ (η k) (f x (ξ k)))+(∑' k : ℕ,inner ℂ (η k) (g x (ξ k))) := by
    simp only [add_apply,inner_add_right]
    exact (lp.summable_inner η (sequenceMap (f x) ξ)).tsum_add (lp.summable_inner η (sequenceMap (g x) ξ))
  change Continuous (fun x : X => ∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))
  simp_rw [he]
  exact ((functional_continuous ξ η).comp hf).add ((functional_continuous ξ η).comp hg)
end FreeGroupFactorMain.HilbertUltraweak

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_4} [Ring A] [StarRing A]

theorem lift_commute_four {p v t z : A} (hp : IsStarProjection p)
    (hpv : p*v=v) (hvr : v*(1-p)=v) (hvi : star v*v=1-p)
    (ht : Supported p t) (htr : Commute t (v*star v))
    (ha : Commute t (p*z*p)) (hb : Commute t (p*z*star v))
    (hc : Commute t (v*z*p)) (hd : Commute t (v*z*star v)) : Commute (lift v t) z := by
  have hvp := right_zero hvr
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hsupport (a b : A) (hal : p*a=a) (hbr : b*p=b) : Supported p (a*z*b) := by
    exact ⟨by rw [← mul_assoc,← mul_assoc,hal],by rw [mul_assoc,hbr]⟩
  have ha' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport p p hp.isIdempotentElem.eq hp.isIdempotentElem.eq) ha
  have hb' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport p (star v) hp.isIdempotentElem.eq hvsp) hb
  have hc' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport v p hpv hp.isIdempotentElem.eq) hc
  have hd' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport v (star v) hpv hvsp) hd
  have hv' := lift_commute_edge hpv hvp hvi hvr ht htr
  have hvs' := lift_commute_edge_star hp.isSelfAdjoint hpv hvp hvi hvr ht htr
  have hz : z=p*z*p+(p*z*star v)*v+star v*(v*z*p)+star v*(v*z*star v)*v := by
    calc
      z = (p+star v*v)*z*(p+star v*v) := by rw [hvi]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [hz]
  exact ((ha'.add_right (hb'.mul_right hv')).add_right (hvs'.mul_right hc')).add_right
    ((hvs'.mul_right hd').mul_right hv')
end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.FullReducingCorner
open Amplification CornerRerouting
variable {A : Type u_5} [CStarAlgebra A]

def bicomm (s : Set A) : StarSubalgebra ℂ A :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A)

def compress (p : A) (hp : IsStarProjection p) (a : A) : Corner p hp :=
  ⟨p*a*p,by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],by rw [mul_assoc,hp.isIdempotentElem.eq]⟩

theorem compress_star (p : A) (hp : IsStarProjection p) (a : A) :
    compress p hp (star a)=star (compress p hp a) := by
  apply Subtype.ext
  change p*star a*p=star (p*a*p)
  simp only [star_mul,hp.isSelfAdjoint.star_eq,mul_assoc]

def compressedSet (p : A) (hp : IsStarProjection p) (s : Set A) : Set (Corner p hp) := compress p hp '' s

variable (p : A) (hp : IsStarProjection p) (s : Set A)
variable (hps : p∈StarSubalgebra.centralizer ℂ s)

theorem supported_commutant (x : Corner p hp) (hx : (x:A)∈StarSubalgebra.centralizer ℂ s) :
    x∈StarSubalgebra.centralizer ℂ (compressedSet p hp s) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  rintro _ ⟨y,hy,rfl⟩
  have hpy : Commute p (x:A) := x.property.1.trans x.property.2.symm
  have hyx : Commute y (x:A) := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx y hy).1
  have he : Commute (compress p hp y) x := by
    apply Subtype.ext
    exact ((hpy.mul_left hyx).mul_left hpy).eq
  have hyx' : Commute (star y) (x:A) :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx y hy).2
  have he' : Commute (compress p hp (star y)) x := by
    apply Subtype.ext
    exact ((hpy.mul_left hyx').mul_left hpy).eq
  rw [compress_star] at he'
  exact ⟨he.eq,he'.eq⟩

include hps in
theorem commutant_of_supported (x : Corner p hp)
    (hx : x∈StarSubalgebra.centralizer ℂ (compressedSet p hp s)) :
    (x:A)∈StarSubalgebra.centralizer ℂ s := by
  have htest (y : A) (hyP : Commute y p) (hh : Commute (compress p hp y) x) : Commute y (x:A) := by
    have hh' := congrArg Subtype.val hh.eq
    change (p*y*p)*(x:A)=(x:A)*(p*y*p) at hh'
    change y*(x:A)=(x:A)*y
    calc
      y*(x:A)= (p*y*p)*(x:A) := by
        calc
          y*(x:A) = (y*p)*(x:A) := by rw [mul_assoc,x.property.1]
          _ = (p*y)*(x:A) := by rw [hyP]
          _ = (p*y*p)*(x:A) := by rw [mul_assoc (p*y),x.property.1]
      _ = (x:A)*(p*y*p) := hh'
      _ = (x:A)*y := by
        calc
          (x:A)*(p*y*p) = (x:A)*(y*p) := by rw [← mul_assoc,← mul_assoc,x.property.2,mul_assoc]
          _ = (x:A)*(p*y) := by rw [hyP]
          _ = (x:A)*y := by rw [← mul_assoc,x.property.2]
  rw [StarSubalgebra.mem_centralizer_iff]
  intro y hy
  have hc := (StarSubalgebra.mem_centralizer_iff ℂ).mp hx _ ⟨y,hy,rfl⟩
  have hpY := (StarSubalgebra.mem_centralizer_iff ℂ).mp hps y hy
  refine ⟨(htest y hpY.1 hc.1).eq,?_⟩
  apply htest (star y) hpY.2
  change compress p hp (star y)*x=x*compress p hp (star y)
  rw [compress_star]
  exact hc.2

include hps in
theorem compress_mem (a : bicomm s) : compress p hp (a:A)∈bicomm (compressedSet p hp s) := by
  rw [bicomm,StarSubalgebra.mem_centralizer_iff]
  intro x hx
  have ht (z : Corner p hp) (hz : z∈StarSubalgebra.centralizer ℂ (compressedSet p hp s)) :
      Commute z (compress p hp (a:A)) := by
    have hzA := commutant_of_supported p hp s hps z hz
    have hza := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property (z:A) hzA).1
    have hzp : Commute (z:A) p := z.property.2.trans z.property.1.symm
    apply Subtype.ext
    exact ((hzp.mul_right hza).mul_right hzp).eq
  exact ⟨(ht x hx).eq,(ht (star x) (star_mem hx)).eq⟩

variable (v : A) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : p*v=v) (hvr : v*(1-p)=v) (hvi : star v*v=1-p)

include hps hvs hpv hvr hvi in
theorem lift_mem (x : bicomm (compressedSet p hp s)) : lift v (x.val:A)∈bicomm s := by
  have hsupport (a b : A) (hal : p*a=a) (hbr : b*p=b) : Supported p (a*b) :=
    ⟨by rw [← mul_assoc,hal],by rw [mul_assoc,hbr]⟩
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hx (z : A) (hz : z∈StarSubalgebra.centralizer ℂ s) (hzp : Supported p z) :
      Commute (x.val:A) z := by
    let z' : Corner p hp := ⟨z,hzp⟩
    have hm := supported_commutant p hp s z' hz
    have hh := ((StarSubalgebra.mem_centralizer_iff ℂ).mp x.property z' hm).1
    exact (congrArg Subtype.val hh).symm
  have htest (z : A) (hz : z∈StarSubalgebra.centralizer ℂ s) : Commute (lift v (x.val:A)) z := by
    apply lift_commute_four hp hpv hvr hvi x.val.property
    · exact hx _ (mul_mem hvs (star_mem hvs)) (hsupport v (star v) hpv hvsp)
    · exact hx _ (mul_mem (mul_mem hps hz) hps)
        (hsupport (p*z) p (by rw [← mul_assoc,hp.isIdempotentElem.eq]) hp.isIdempotentElem.eq)
    · exact hx _ (mul_mem (mul_mem hps hz) (star_mem hvs))
        (hsupport (p*z) (star v) (by rw [← mul_assoc,hp.isIdempotentElem.eq]) hvsp)
    · exact hx _ (mul_mem (mul_mem hvs hz) hps)
        (hsupport (v*z) p (by rw [← mul_assoc,hpv]) hp.isIdempotentElem.eq)
    · exact hx _ (mul_mem (mul_mem hvs hz) (star_mem hvs))
        (hsupport (v*z) (star v) (by rw [← mul_assoc,hpv]) hvsp)
  rw [bicomm,StarSubalgebra.mem_centralizer_iff]
  intro z hz
  exact ⟨(htest z hz).symm.eq,(htest (star z) (star_mem hz)).symm.eq⟩

include hps hvs hpv hvi in
theorem lift_compress (a : bicomm s) : lift v (compress p hp (a:A):A)=(a:A) := by
  have hap := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property p hps).1
  have havs := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property v hvs).2
  change p*(a:A)*p+star v*(p*(a:A)*p)*v=(a:A)
  rw [hap,mul_assoc,hp.isIdempotentElem.eq,← mul_assoc (star v),havs,mul_assoc,hpv,mul_assoc,hvi]
  noncomm_ring

include hvr in
theorem compress_lift (x : Corner p hp) : compress p hp (lift v (x:A))=x := by
  have hvp := right_zero hvr
  apply Subtype.ext
  change p*lift v (x:A)*p=(x:A)
  rw [mul_assoc,lift_mul_supported hvp ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩,x.property.2,x.property.1]

def iso : bicomm s ≃⋆ₐ[ℂ] bicomm (compressedSet p hp s) where
  toFun a := ⟨compress p hp a,compress_mem p hp s hps a⟩
  invFun x := ⟨lift v (x.val:A),lift_mem p hp s hps v hvs hpv hvr hvi x⟩
  left_inv a := Subtype.ext (lift_compress p hp s hps v hvs hpv hvi a)
  right_inv x := Subtype.ext (compress_lift p hp v hvr x.val)
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    have hpA := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property p hps).1
    change p*((a:A)*(b:A))*p=(p*(a:A)*p)*(p*(b:A)*p)
    calc
      p*((a:A)*(b:A))*p = (p*(a:A))*((b:A)*p) := by simp only [mul_assoc]
      _ = ((a:A)*p)*((b:A)*p) := by rw [hpA]
      _ = (p*(a:A)*p)*(p*(b:A)*p) := by
        rw [hpA]
        simp only [mul_assoc,← mul_assoc p p,hp.isIdempotentElem.eq]
  map_add' a b := by
    apply Subtype.ext; apply Subtype.ext
    change p*((a:A)+(b:A))*p=p*(a:A)*p+p*(b:A)*p
    simp only [mul_add,add_mul]
  map_smul' c a := by
    apply Subtype.ext; apply Subtype.ext
    change p*(c • (a:A))*p=c • (p*(a:A)*p)
    simp only [mul_smul_comm,smul_mul_assoc]
  map_star' a := Subtype.ext (compress_star p hp (a:A))
end FreeGroupFactorMain.FullReducingCorner

end

namespace FreeGroupFactorMain.ReducingSubspace
variable {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [CompleteSpace K]

def reduce (T : E →L[ℂ] E) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp (T.comp K.subtypeL)

theorem reduce_apply (T : E →L[ℂ] E) (hT : ∀ ξ∈K,T ξ∈K) (ξ : K) :
    (reduce K T ξ:E)=T ξ := K.starProjection_eq_self_iff.mpr (hT ξ ξ.property)

theorem reduce_one : reduce K (1:E →L[ℂ] E)=1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact K.orthogonalProjectionOnto_mem_subspace_eq_self ξ

theorem reduce_add (T U : E →L[ℂ] E) : reduce K (T+U)=reduce K T+reduce K U := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact K.orthogonalProjectionOnto.map_add _ _

theorem reduce_smul (c : ℂ) (T : E →L[ℂ] E) : reduce K (c • T)=c • reduce K T := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact K.orthogonalProjectionOnto.map_smul c _

theorem inner_reduce (T : E →L[ℂ] E) (ξ η : K) :
    inner ℂ ξ (reduce K T η)=inner ℂ (ξ:E) (T η) :=
  K.inner_orthogonalProjectionOnto_eq_of_mem_left ξ (T η)

variable [CompleteSpace E]

theorem reduce_star (T : E →L[ℂ] E) : reduce K (star T)=star (reduce K T) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  rw [inner_reduce,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact (K.inner_orthogonalProjectionOnto_eq_of_mem_right ξ (T η)).symm

omit [CompleteSpace E] in
theorem reduce_mul (T U : E →L[ℂ] E) (hU : ∀ ξ∈K,U ξ∈K) :
    reduce K (T*U)=reduce K T*reduce K U := by
  apply ContinuousLinearMap.ext
  intro ξ
  change K.orthogonalProjectionOnto (T (U ξ))=K.orthogonalProjectionOnto (T (reduce K U ξ:E))
  rw [reduce_apply K U hU]
end FreeGroupFactorMain.ReducingSubspace

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace
variable {A : Type u_7} {E : Type u_8} {I : Type u_9} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

def reducedCoeff : A →⋆ₐ[ℂ] (X.normalHull →L[ℂ] X.normalHull) where
  toFun a := reduce X.normalHull (X.coeff a)
  map_zero' := by simp [reduce]
  map_one' := by rw [map_one,reduce_one]
  map_add' a b := by rw [map_add,reduce_add]
  map_mul' a b := by rw [map_mul,reduce_mul X.normalHull _ _ (fun _ h => X.normalHull_coeff b h)]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,reduce_smul,reduce_one,Algebra.algebraMap_eq_smul_one]
  map_star' a := by rw [map_star,reduce_star]

def reducedSystem : System A X.normalHull I covariance where
  coeff := X.reducedCoeff
  root := ⟨X.root,X.normalHull_root⟩
  create i := reduce X.normalHull (X.create i)
  contract i j a := by
    change star (reduce X.normalHull (X.create i))*reduce X.normalHull (X.coeff a)*
      reduce X.normalHull (X.create j)=reduce X.normalHull (X.coeff (covariance i j a))
    rw [← reduce_star,← reduce_mul X.normalHull _ _ (fun _ h => X.normalHull_coeff a h),
      ← reduce_mul X.normalHull _ _ (fun _ h => X.normalHull_create j h),X.contract]
  annihilate i a := by
    apply Subtype.ext
    rw [← reduce_star,reduce_apply X.normalHull _ (fun _ h => X.normalHull_annihilate i h)]
    change star (X.create i) ((reduce X.normalHull (X.coeff a) ⟨X.root,X.normalHull_root⟩):E)=0
    rw [reduce_apply X.normalHull _ (fun _ h => X.normalHull_coeff a h),X.annihilate]

theorem reducedSystem_normal (a : A) (w : List (I × A)) :
    (X.reducedSystem.normal a w:E)=X.normal a w := by
  induction w generalizing a with
  | nil => exact reduce_apply X.normalHull _ (fun _ h => X.normalHull_coeff a h) _
  | cons q w ih =>
    rcases q with ⟨i,b⟩
    change (reduce X.normalHull (X.coeff a)
      (reduce X.normalHull (X.create i) (X.reducedSystem.normal b w)):E)=_
    rw [reduce_apply X.normalHull _ (fun _ h => X.normalHull_coeff a h),
      reduce_apply X.normalHull _ (fun _ h => X.normalHull_create i h),ih]
    rfl

theorem reducedSystem_family (w : Word A I) : (X.reducedSystem.family w:E)=X.family w :=
  X.reducedSystem_normal _ _

theorem reducedSystem_state (a : A) :
    inner ℂ X.reducedSystem.root (X.reducedSystem.coeff a X.reducedSystem.root)=
      inner ℂ X.root (X.coeff a X.root) := inner_reduce X.normalHull _ _ _

theorem reducedSystem_total :
    (Submodule.span ℂ (Set.range X.reducedSystem.family)).topologicalClosure=⊤ := by
  have hi : (Subtype.val '' (Submodule.span ℂ (Set.range X.reducedSystem.family) : Set X.normalHull))=
      (X.normalSpan:Set E) := by
    change ((Submodule.span ℂ (Set.range X.reducedSystem.family)).map X.normalHull.subtype : Set E)=_
    rw [Submodule.map_span,← Set.range_comp]
    change (Submodule.span ℂ (Set.range (fun w => (X.reducedSystem.family w:E))) : Set E)=_
    simp only [X.reducedSystem_family,normalSpan]
  apply top_unique
  intro ξ _
  change ξ∈closure (Submodule.span ℂ (Set.range X.reducedSystem.family) : Set X.normalHull)
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hi]
  exact ξ.property
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem reduced_weighted_scalar_state (a : UniformAlgebra) :
    inner ℂ (weightedSystem u v hv hvu).reducedSystem.root
      ((weightedSystem u v hv hvu).reducedSystem.coeff a (weightedSystem u v hv hvu).reducedSystem.root)=
      inner ℂ scalarSystem.root (scalarSystem.coeff a scalarSystem.root) := by
  rw [(weightedSystem u v hv hvu).reducedSystem_state]
  exact (scalar_weighted_state u v hv hvu a).symm

def reducedGaussianIso :
    (weightedSystem u v hv hvu).reducedSystem.generated scalarFlip ≃⋆ₐ[ℂ]
      scalarSystem.generated scalarFlip :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip

theorem reducedGaussianIso_normal :
    @Continuous _ _ ((weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip)
      (scalarSystem.generatedTopology scalarFlip) (reducedGaussianIso u v hv hvu) :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso_normal scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip

theorem reducedGaussianIso_trace (T : (weightedSystem u v hv hvu).reducedSystem.generated scalarFlip) :
    inner ℂ scalarSystem.root ((reducedGaussianIso u v hv hvu T : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      inner ℂ (weightedSystem u v hv hvu).reducedSystem.root
        ((T : (weightedSystem u v hv hvu).normalHull →L[ℂ] (weightedSystem u v hv hvu).normalHull)
          (weightedSystem u v hv hvu).reducedSystem.root) :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso_trace scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip T
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

section
namespace FreeGroupFactorMain.FullReducingCorner
open Amplification GaussianRecognition ReducingSubspace
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

def transport (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) (t : Set B) (he : Φ '' s=t) :
    bicomm s ≃⋆ₐ[ℂ] bicomm t where
  toFun T := ⟨Φ T,by
    rw [← he]
    exact (bicommutant_transport Φ s T).mpr T.property⟩
  invFun T := ⟨Φ.symm T,by
    apply (bicommutant_transport Φ s (Φ.symm T)).mp
    rw [StarAlgEquiv.apply_symm_apply,he]
    exact T.property⟩
  left_inv T := Subtype.ext (StarAlgEquiv.symm_apply_apply Φ (T:A))
  right_inv T := Subtype.ext (StarAlgEquiv.apply_symm_apply Φ (T:B))
  map_mul' T U := Subtype.ext (Φ.map_mul (T:A) (U:A))
  map_add' T U := Subtype.ext (Φ.map_add (T:A) (U:A))
  map_smul' c T := Subtype.ext (map_smul Φ c (T:A))
  map_star' T := Subtype.ext (Φ.map_star' (T:A))

variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]

theorem representation_compress (T : E →L[ℂ] E) :
    cornerRepresentation K (compress K.starProjection isStarProjection_starProjection T)=reduce K T := by
  apply ContinuousLinearMap.ext
  intro ξ
  change K.orthogonalProjectionOnto (K.starProjection (T (K.starProjection (ξ:E))))=
    K.orthogonalProjectionOnto (T ξ)
  rw [K.starProjection_mem_subspace_eq_self ξ,K.orthogonalProjectionOnto_starProjection_of_le le_rfl]

def reductionImage (s : Set (E →L[ℂ] E)) : Set (K →L[ℂ] K) := reduce K '' s

theorem representation_compressedSet (s : Set (E →L[ℂ] E)) :
    cornerRepresentation K '' compressedSet K.starProjection isStarProjection_starProjection s=reductionImage K s := by
  rw [compressedSet,Set.image_image]
  simp only [representation_compress,reductionImage]

variable (s : Set (E →L[ℂ] E))
variable (hps : K.starProjection∈StarSubalgebra.centralizer ℂ s)
variable (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : K.starProjection*v=v) (hvr : v*(1-K.starProjection)=v) (hvi : star v*v=1-K.starProjection)

def restrictionIso : bicomm s ≃⋆ₐ[ℂ] bicomm (reductionImage K s) :=
  (iso K.starProjection isStarProjection_starProjection s hps v hvs hpv hvr hvi).trans
    (transport (cornerRepresentation K) _ _ (representation_compressedSet K s))

theorem restrictionIso_apply (T : bicomm s) :
    (restrictionIso K s hps v hvs hpv hvr hvi T : K →L[ℂ] K)=reduce K (T:E →L[ℂ] E) :=
  representation_compress K T

end FreeGroupFactorMain.FullReducingCorner

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace FullReducingCorner
variable {A : Type u_5} {E : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

theorem normalHull_projection_mem (σ : I → I) :
    X.normalHull.starProjection∈StarSubalgebra.centralizer ℂ (X.generators σ) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro U hU
  rcases hU with ⟨a,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨(X.normalHull_projection_coeff a).eq.symm,
      (by simpa only [map_star] using (X.normalHull_projection_coeff (star a)).eq.symm)⟩
  · refine ⟨(X.normalHull_projection_generator σ i).eq.symm,?_⟩
    change star (X.create i+star (X.create (σ i)))*_= _*star (X.create i+star (X.create (σ i)))
    rw [star_add (R := Operator E),star_star]
    exact ((X.normalHull_projection_annihilate i).add_right (X.normalHull_projection_create (σ i))).eq.symm

theorem reduced_generators (σ : I → I) :
    reductionImage X.normalHull (X.generators σ)=X.reducedSystem.generators σ := by
  have hgen (i : I) : reduce X.normalHull (X.generator σ i)=X.reducedSystem.generator σ i := by
    change reduce X.normalHull (X.create i+star (X.create (σ i)))=
      reduce X.normalHull (X.create i)+star (reduce X.normalHull (X.create (σ i)))
    rw [reduce_add,reduce_star]
  change reduce X.normalHull '' (Set.range X.coeff ∪ Set.range (X.generator σ))=
    Set.range X.reducedSystem.coeff ∪ Set.range (X.reducedSystem.generator σ)
  rw [Set.image_union,← Set.range_comp,← Set.range_comp]
  have hg : reduce X.normalHull ∘ X.generator σ=X.reducedSystem.generator σ := funext hgen
  rw [hg]
  rfl

variable (σ : I → I) (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ (X.generators σ))
variable (hpv : X.normalHull.starProjection*v=v) (hvr : v*(1-X.normalHull.starProjection)=v)
variable (hvi : star v*v=1-X.normalHull.starProjection)

def fullReductionIso : X.generated σ ≃⋆ₐ[ℂ] X.reducedSystem.generated σ := by
  have he := X.reduced_generators σ
  exact (restrictionIso X.normalHull (X.generators σ) (X.normalHull_projection_mem σ) v hvs hpv hvr hvi).trans
    (transport (StarAlgEquiv.refl ℂ _) _ _ (by simpa only [StarAlgEquiv.coe_refl,Set.image_id] using he))

theorem fullReductionIso_apply (T : X.generated σ) :
    (X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull)=reduce X.normalHull (T:Operator E) :=
  restrictionIso_apply X.normalHull _ _ v hvs hpv hvr hvi T

theorem fullReductionIso_normal :
    @Continuous _ _ (X.generatedTopology σ) (X.reducedSystem.generatedTopology σ)
      (X.fullReductionIso σ v hvs hpv hvr hvi) := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (X.generated σ) := X.generatedTopology σ
  let : TopologicalSpace (X.normalHull →L[ℂ] X.normalHull) := ultraweak X.normalHull
  apply continuous_induced_rng.mpr
  have he : (fun T : X.generated σ => (X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull))=
      (fun T : X.generated σ => reduce X.normalHull (T:Operator E)) := funext (X.fullReductionIso_apply σ v hvs hpv hvr hvi)
  change @Continuous _ _ (X.generatedTopology σ) (ultraweak X.normalHull)
    (fun T : X.generated σ => (X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull))
  rw [he]
  exact (HilbertUltraweak.sandwich_continuous X.normalHull.orthogonalProjectionOnto X.normalHull.subtypeL).comp
    continuous_subtype_val

theorem fullReductionIso_trace (T : X.generated σ) :
    inner ℂ X.reducedSystem.root ((X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull)
      X.reducedSystem.root)=inner ℂ X.root ((T:Operator E) X.root) := by
  rw [fullReductionIso_apply]
  exact inner_reduce X.normalHull _ _ _
end FreeGroupFactorMain.GaussianRecognition.System

end

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition ReducingSubspace
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

def fullGaussianIso : (weightedSystem u v hv hvu).generated scalarFlip ≃⋆ₐ[ℂ]
    scalarSystem.generated scalarFlip :=
  ((weightedSystem u v hv hvu).fullReductionIso scalarFlip (pRightEdge u v)
    (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
    (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu)).trans
      (reducedGaussianIso u v hv hvu)

theorem fullGaussianIso_normal :
    @Continuous _ _ ((weightedSystem u v hv hvu).generatedTopology scalarFlip)
      (scalarSystem.generatedTopology scalarFlip) (fullGaussianIso u v hv hvu) := by
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace ((weightedSystem u v hv hvu).reducedSystem.generated scalarFlip) :=
    (weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (reducedGaussianIso_normal u v hv hvu).comp
    ((weightedSystem u v hv hvu).fullReductionIso_normal scalarFlip (pRightEdge u v)
      (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
      (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu))

theorem fullGaussianIso_trace (T : (weightedSystem u v hv hvu).generated scalarFlip) :
    inner ℂ scalarSystem.root ((fullGaussianIso u v hv hvu T : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      inner ℂ pRoot ((T:PRange ℕ →L[ℂ] PRange ℕ) pRoot) := by
  rw [fullGaussianIso,StarAlgEquiv.trans_apply,reducedGaussianIso_trace]
  exact (weightedSystem u v hv hvu).fullReductionIso_trace scalarFlip (pRightEdge u v)
    (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
    (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu) T
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

omit [IsClosed (M : Set A)] in
include hp in
theorem subtype_projection : IsStarProjection (p:A) :=
  hp.map M.subtype

def cornerSubtypeEquiv : Corner p hp ≃⋆ₐ[ℂ] subalgebraCorner M (p:A) (subtype_projection M p hp) p.property where
  toFun x := ⟨⟨x.val.val,⟨congrArg Subtype.val x.property.1,congrArg Subtype.val x.property.2⟩⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,⟨Subtype.ext x.val.property.1,Subtype.ext x.val.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem projectionRepresentation_normal (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range] :
    @Continuous _ _ (cornerTopology (HilbertUltraweak.topology E) p hp)
      (HilbertUltraweak.topology p.range) (projectionRepresentation p hp) := by
  let : TopologicalSpace (E →L[ℂ] E) := HilbertUltraweak.topology E
  let : TopologicalSpace (p.range →L[ℂ] p.range) := HilbertUltraweak.topology p.range
  let : TopologicalSpace (Corner p hp) := cornerTopology (HilbertUltraweak.topology E) p hp
  have he : (fun x : Corner p hp => projectionRepresentation p hp x)=
      (fun x : Corner p hp => p.range.orthogonalProjectionOnto.comp ((x:E →L[ℂ] E).comp p.range.subtypeL)) := by
    funext x
    change cornerRestrict p.range (cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
      (projectionRange_starProjection p hp).symm x)=_
    unfold cornerRestrict
    rw [cornerEqualityEquiv_val]
  change Continuous (fun x : Corner p hp => projectionRepresentation p hp x)
  rw [he]
  exact (HilbertUltraweak.sandwich_continuous p.range.orthogonalProjectionOnto p.range.subtypeL).comp continuous_subtype_val

 theorem projectionRepresentation_symm_normal (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range] :
    @Continuous _ _ (HilbertUltraweak.topology p.range)
      (cornerTopology (HilbertUltraweak.topology E) p hp) (projectionRepresentation p hp).symm := by
  let : TopologicalSpace (E →L[ℂ] E) := HilbertUltraweak.topology E
  let : TopologicalSpace (p.range →L[ℂ] p.range) := HilbertUltraweak.topology p.range
  apply continuous_induced_rng.mpr
  have he : (fun x : p.range →L[ℂ] p.range => ((projectionRepresentation p hp).symm x : E →L[ℂ] E))=
      (fun x : p.range →L[ℂ] p.range => p.range.subtypeL.comp (x.comp p.range.orthogonalProjectionOnto)) := by
    funext x
    have h := cornerEqualityEquiv_val p p.range.starProjection hp isStarProjection_starProjection
      (projectionRange_starProjection p hp).symm
      ((cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
        (projectionRange_starProjection p hp).symm).symm ((cornerRepresentation p.range).symm x))
    rw [StarAlgEquiv.apply_symm_apply] at h
    exact h.symm
  change Continuous (fun x : p.range →L[ℂ] p.range => ((projectionRepresentation p hp).symm x : E →L[ℂ] E))
  rw [he]
  exact HilbertUltraweak.sandwich_continuous p.range.subtypeL p.range.orthogonalProjectionOnto
end

variable {A : Type u_6} {B : Type u_7} [CStarAlgebra A] [CStarAlgebra B]
@[instance_reducible] def subalgebraTopology (𝒯 : TopologicalSpace A) (M : StarSubalgebra ℂ A) : TopologicalSpace M :=
  TopologicalSpace.induced (fun x : M => (x:A)) 𝒯

theorem subalgebraEquiv_normal (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a,e a∈N ↔ a∈M)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B) (hn : @Continuous _ _ 𝒯A 𝒯B e) :
    @Continuous _ _ (subalgebraTopology 𝒯A M) (subalgebraTopology 𝒯B N) (subalgebraEquiv M N e he) := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace M := subalgebraTopology 𝒯A M
  exact (hn.comp continuous_subtype_val).subtype_mk _

theorem subalgebraEquiv_symm_normal (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a,e a∈N ↔ a∈M)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B) (hn : @Continuous _ _ 𝒯B 𝒯A e.symm) :
    @Continuous _ _ (subalgebraTopology 𝒯B N) (subalgebraTopology 𝒯A M) (subalgebraEquiv M N e he).symm := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace N := subalgebraTopology 𝒯B N
  exact (hn.comp continuous_subtype_val).subtype_mk _

theorem subalgebraEqualityEquiv_normal (M N : StarSubalgebra ℂ A) (he : M=N) (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology 𝒯 M) (subalgebraTopology 𝒯 N) (subalgebraEqualityEquiv M N he) :=
  subalgebraEquiv_normal M N (StarAlgEquiv.refl ℂ A) _ 𝒯 𝒯 (@continuous_id A 𝒯)

theorem subalgebraEqualityEquiv_symm_normal (M N : StarSubalgebra ℂ A) (he : M=N) (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology 𝒯 N) (subalgebraTopology 𝒯 M) (subalgebraEqualityEquiv M N he).symm :=
  subalgebraEquiv_symm_normal M N (StarAlgEquiv.refl ℂ A) _ 𝒯 𝒯 (@continuous_id A 𝒯)

theorem cornerCongr_symm_normal (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (hΦ : @Continuous _ _ 𝒯B 𝒯A Φ.symm) :
    @Continuous _ _ (cornerTopology 𝒯B (Φ p) (map_projection Φ p hp))
      (cornerTopology 𝒯A p hp) (cornerCongr Φ p hp).symm := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace (Corner (Φ p) (map_projection Φ p hp)) :=
    cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)
  exact (hΦ.comp continuous_subtype_val).subtype_mk _

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)] (p : M) (hp : IsStarProjection p)

theorem cornerSubtypeEquiv_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (cornerTopology (subalgebraTopology 𝒯 M) p hp)
      (subalgebraTopology (cornerTopology 𝒯 (p:A) (subtype_projection M p hp))
        (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property)) (cornerSubtypeEquiv M p hp) := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace M := subalgebraTopology 𝒯 M
  let : TopologicalSpace (Corner p hp) := cornerTopology (subalgebraTopology 𝒯 M) p hp
  let : TopologicalSpace (Corner (p:A) (subtype_projection M p hp)) := cornerTopology 𝒯 (p:A) (subtype_projection M p hp)
  exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem cornerSubtypeEquiv_symm_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology (cornerTopology 𝒯 (p:A) (subtype_projection M p hp))
        (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property))
      (cornerTopology (subalgebraTopology 𝒯 M) p hp) (cornerSubtypeEquiv M p hp).symm := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace M := subalgebraTopology 𝒯 M
  let : TopologicalSpace (Corner (p:A) (subtype_projection M p hp)) := cornerTopology 𝒯 (p:A) (subtype_projection M p hp)
  let : TopologicalSpace (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property) :=
    subalgebraTopology (cornerTopology 𝒯 (p:A) (subtype_projection M p hp))
      (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property)
  exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.FreeFock
open Amplification
variable {α : Type u_8} [DecidableEq α]

end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_9} {B : Type u_10} [CStarAlgebra A] [CStarAlgebra B]
variable (p : A) (hp : IsStarProjection p) (q : Corner p hp) (hq : IsStarProjection q)

variable (τ : A → ℂ) (𝒯 : TopologicalSpace A)

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace FullReducingCorner
variable {A : Type u_1} {E : Type u_2} {F : Type u_3} {I : Type u_4} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {covariance : I → I → A → A} (X : System A E I covariance) (Y : System A F I covariance)
variable (hstate : ∀ a,inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
variable (hX : X.normalHull=⊤) (hY : Y.normalHull=⊤)

theorem generatedIso_symm_normal (σ : I → I) :
    @Continuous _ _ (Y.generatedTopology σ) (X.generatedTopology σ)
      (X.generatedIso Y hstate hX hY σ).symm := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (Operator F) := ultraweak F
  let : TopologicalSpace (Y.generated σ) := Y.generatedTopology σ
  apply continuous_induced_rng.mpr
  exact (spatial_normal (X.spatial Y hstate hX hY).symm).comp continuous_subtype_val
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.FullReducingCorner
open Amplification GaussianRecognition ReducingSubspace
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]
variable (s : Set (E →L[ℂ] E)) (hps : K.starProjection∈StarSubalgebra.centralizer ℂ s)
variable (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : K.starProjection*v=v) (hvr : v*(1-K.starProjection)=v) (hvi : star v*v=1-K.starProjection)

end FreeGroupFactorMain.FullReducingCorner

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace FullReducingCorner
variable {A : Type u_6} {E : Type u_7} {I : Type u_8} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)
variable (σ : I → I) (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ (X.generators σ))
variable (hpv : X.normalHull.starProjection*v=v) (hvr : v*(1-X.normalHull.starProjection)=v)
variable (hvi : star v*v=1-X.normalHull.starProjection)

theorem fullReductionIso_symm_normal :
    @Continuous _ _ (X.reducedSystem.generatedTopology σ) (X.generatedTopology σ)
      (X.fullReductionIso σ v hvs hpv hvr hvi).symm := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (X.normalHull →L[ℂ] X.normalHull) := ultraweak X.normalHull
  let : TopologicalSpace (X.reducedSystem.generated σ) := X.reducedSystem.generatedTopology σ
  apply continuous_induced_rng.mpr
  have he : Continuous (fun T : X.reducedSystem.generated σ =>
      X.normalHull.subtypeL.comp ((T:X.normalHull →L[ℂ] X.normalHull).comp X.normalHull.orthogonalProjectionOnto)) :=
    (HilbertUltraweak.sandwich_continuous X.normalHull.subtypeL X.normalHull.orthogonalProjectionOnto).comp continuous_subtype_val
  have hc := HilbertUltraweak.add_continuous he
    ((HilbertUltraweak.sandwich_continuous (star v) v).comp he)
  convert hc using 1 <;> rfl
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)
theorem reducedGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      ((weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip) (reducedGaussianIso u v hv hvu).symm :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso_symm_normal scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip

theorem fullGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      ((weightedSystem u v hv hvu).generatedTopology scalarFlip) (fullGaussianIso u v hv hvu).symm := by
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace ((weightedSystem u v hv hvu).reducedSystem.generated scalarFlip) :=
    (weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact ((weightedSystem u v hv hvu).fullReductionIso_symm_normal scalarFlip (pRightEdge u v)
      (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
      (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu)).comp
    (reducedGaussianIso_symm_normal u v hv hvu)

variable (hu : u≠0) (hv' : v≠0) (hunit : u^2+v^2=1)
theorem ambientGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      ((ambientSystem u v hu hv' hunit).generatedTopology scalarFlip) (ambientGaussianIso u v hu hv' hunit).symm :=
  (ambientSystem u v hu hv' hunit).generatedIso_symm_normal scalarSystem
    (scalar_ambient_state u v hu hv' hunit)
    (ambientSystem_total u v hu hv' hunit) scalarSystem_total scalarFlip
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section
namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

@[instance_reducible] def ambientTopology : TopologicalSpace (ambientAlgebra (ι := ℕ) u v) :=
  subalgebraTopology (HilbertUltraweak.topology (H ℕ)) (ambientAlgebra u v)
@[instance_reducible] def pAmbientTopology : TopologicalSpace (pAmbient (ι := ℕ) u v) :=
  subalgebraTopology (cornerTopology (HilbertUltraweak.topology (H ℕ)) P projection_P) (pAmbient u v)

theorem pAmbientRepresentation_mem (a : PCorner ℕ) :
    pRepresentation a∈representedAmbient u v ↔ a∈pAmbient u v := by
  change (pRepresentation (ι := ℕ)).symm (pRepresentation a)∈pAmbient u v ↔ a∈pAmbient u v
  rw [StarAlgEquiv.symm_apply_apply]

def pAmbientRepresentation : pAmbient (ι := ℕ) u v ≃⋆ₐ[ℂ] representedAmbient u v where
  toFun a := ⟨pRepresentation a,(pAmbientRepresentation_mem u v a).mpr a.property⟩
  invFun b := ⟨(pRepresentation (ι := ℕ)).symm b,b.property⟩
  left_inv _ := Subtype.ext (StarAlgEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (StarAlgEquiv.apply_symm_apply _ _)
  map_mul' a b := Subtype.ext ((pRepresentation (ι := ℕ)).map_mul (a:PCorner ℕ) (b:PCorner ℕ))
  map_add' a b := Subtype.ext ((pRepresentation (ι := ℕ)).map_add (a:PCorner ℕ) (b:PCorner ℕ))
  map_smul' c a := Subtype.ext ((pRepresentation (ι := ℕ)).map_smul' c (a:PCorner ℕ))
  map_star' a := Subtype.ext ((pRepresentation (ι := ℕ)).map_star' (a:PCorner ℕ))

theorem pAmbientRepresentation_normal :
    @Continuous (pAmbient (ι := ℕ) u v) (representedAmbient u v) (pAmbientTopology u v)
      (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
        (pAmbientRepresentation u v) := by
  let : TopologicalSpace (PCorner ℕ) := cornerTopology (HilbertUltraweak.topology (H ℕ)) P projection_P
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  exact ((projectionRepresentation_normal P projection_P).comp continuous_subtype_val).subtype_mk _

theorem pAmbientRepresentation_symm_normal :
    @Continuous (representedAmbient u v) (pAmbient (ι := ℕ) u v) (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
      (pAmbientTopology u v) (pAmbientRepresentation u v).symm := by
  let : TopologicalSpace (PCorner ℕ) := cornerTopology (HilbertUltraweak.topology (H ℕ)) P projection_P
  let : TopologicalSpace (representedAmbient u v) :=
    subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  exact ((projectionRepresentation_symm_normal P projection_P).comp continuous_subtype_val).subtype_mk _

def representedGeneratedIso : representedAmbient u v ≃⋆ₐ[ℂ]
    (weightedSystem u v hv hvu).generated scalarFlip where
  toFun a := ⟨a.val, by rw [weighted_generated_eq_ambient]; exact a.property⟩
  invFun a := ⟨a.val, by rw [←weighted_generated_eq_ambient u v hv hvu]; exact a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem representedGeneratedIso_normal :
    @Continuous (representedAmbient u v) ((weightedSystem u v hv hvu).generated scalarFlip)
      (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
      ((weightedSystem u v hv hvu).generatedTopology scalarFlip) (representedGeneratedIso u v hv hvu) := by
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  let : TopologicalSpace (representedAmbient u v) :=
    subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  exact continuous_subtype_val.subtype_mk _

theorem representedGeneratedIso_symm_normal :
    @Continuous ((weightedSystem u v hv hvu).generated scalarFlip) (representedAmbient u v)
      ((weightedSystem u v hv hvu).generatedTopology scalarFlip)
      (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
        (representedGeneratedIso u v hv hvu).symm := by
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  exact continuous_subtype_val.subtype_mk _

def pAmbientGeneratedIso : pAmbient (ι := ℕ) u v ≃⋆ₐ[ℂ]
    (weightedSystem u v hv hvu).generated scalarFlip :=
  (pAmbientRepresentation u v).trans (representedGeneratedIso u v hv hvu)

def pAmbientGaussianIso : pAmbient (ι := ℕ) u v ≃⋆ₐ[ℂ] scalarSystem.generated scalarFlip :=
  (pAmbientGeneratedIso u v hv hvu).trans (fullGaussianIso u v hv hvu)

theorem pAmbientGaussianIso_normal :
    @Continuous _ _ (pAmbientTopology u v) (scalarSystem.generatedTopology scalarFlip)
      (pAmbientGaussianIso u v hv hvu) := by
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (representedAmbient u v) := subalgebraTopology
    (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := (fullGaussianIso_normal u v hv hvu).comp
    ((representedGeneratedIso_normal u v hv hvu).comp
        (pAmbientRepresentation_normal u v))
  convert hc using 1 <;> rfl

theorem pAmbientGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip) (pAmbientTopology u v)
      (pAmbientGaussianIso u v hv hvu).symm := by
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (representedAmbient u v) := subalgebraTopology
    (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := (pAmbientRepresentation_symm_normal u v).comp
    ((representedGeneratedIso_symm_normal u v hv hvu).comp (fullGaussianIso_symm_normal u v hv hvu))
  convert hc using 1 <;> rfl

theorem pAmbientGaussianIso_trace (x : pAmbient (ι := ℕ) u v) :
    inner ℂ scalarSystem.root ((pAmbientGaussianIso u v hv hvu x : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      pVacuumTrace u v (x.val:Operator ℕ) := by
  rw [pAmbientGaussianIso,StarAlgEquiv.trans_apply,fullGaussianIso_trace]
  exact (pRepresentation_vacuumTrace u v (ne_of_gt (lt_trans hv hvu)) x.val).symm

def ambientP : ambientAlgebra (ι := ℕ) u v := ⟨P,P_mem_ambient u v⟩
theorem ambientP_projection : IsStarProjection (ambientP u v) :=
  ⟨Subtype.ext projection_P.isIdempotentElem.eq,Subtype.ext projection_P.isSelfAdjoint.star_eq⟩

def ambientCornerGaussianIso : Corner (ambientP u v) (ambientP_projection u v) ≃⋆ₐ[ℂ]
    scalarSystem.generated scalarFlip :=
  (cornerSubtypeEquiv _ (ambientP u v) (ambientP_projection u v)).trans (pAmbientGaussianIso u v hv hvu)

theorem ambientCornerGaussianIso_normal :
    @Continuous _ _ (cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v))
      (scalarSystem.generatedTopology scalarFlip) (ambientCornerGaussianIso u v hv hvu) := by
  let : TopologicalSpace (Corner (ambientP u v) (ambientP_projection u v)) :=
    cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v)
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := (pAmbientGaussianIso_normal u v hv hvu).comp
    (cornerSubtypeEquiv_normal _ (ambientP u v) (ambientP_projection u v) (HilbertUltraweak.topology (H ℕ)))
  convert hc using 1 <;> rfl

theorem ambientCornerGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      (cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v)) (ambientCornerGaussianIso u v hv hvu).symm := by
  let : TopologicalSpace (Corner (ambientP u v) (ambientP_projection u v)) :=
    cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v)
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hr : @Continuous _ _ (pAmbientTopology u v)
      (cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v))
      (cornerSubtypeEquiv _ (ambientP u v) (ambientP_projection u v)).symm := by
    convert cornerSubtypeEquiv_symm_normal _ (ambientP u v) (ambientP_projection u v)
      (HilbertUltraweak.topology (H ℕ)) using 1 ; rfl
  exact hr.comp (pAmbientGaussianIso_symm_normal u v hv hvu)

theorem ambientCornerGaussianIso_trace (x : Corner (ambientP u v) (ambientP_projection u v)) :
    inner ℂ scalarSystem.root ((ambientCornerGaussianIso u v hv hvu x : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      pVacuumTrace u v (x.val:Operator ℕ) :=
  pAmbientGaussianIso_trace u v hv hvu _

variable (hu : u≠0) (hv' : v≠0) (hunit : u^2+v^2=1)

theorem ambientScalarIso_normal :
    @Continuous _ _ (ambientTopology u v) (scalarSystem.generatedTopology scalarFlip)
      (ambientScalarIso u v hu hv' hunit) := by
  let : TopologicalSpace (ambientAlgebra (ι := ℕ) u v) := ambientTopology u v
  let : TopologicalSpace ((ambientSystem u v hu hv' hunit).generated scalarFlip) :=
    (ambientSystem u v hu hv' hunit).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (ambientGaussianIso_normal u v hu hv' hunit).comp
    (subalgebraEqualityEquiv_normal _ _ (ambient_generated_eq u v hu hv' hunit).symm
      (HilbertUltraweak.topology (H ℕ)))

theorem ambientScalarIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip) (ambientTopology u v)
      (ambientScalarIso u v hu hv' hunit).symm := by
  let : TopologicalSpace (ambientAlgebra (ι := ℕ) u v) := ambientTopology u v
  let : TopologicalSpace ((ambientSystem u v hu hv' hunit).generated scalarFlip) :=
    (ambientSystem u v hu hv' hunit).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (subalgebraEqualityEquiv_symm_normal _ _ (ambient_generated_eq u v hu hv' hunit).symm
      (HilbertUltraweak.topology (H ℕ))).comp (ambientGaussianIso_symm_normal u v hu hv' hunit)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

end

variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

 theorem HasCornerScaling.of_recognitions (τA : A → ℂ) (τB : B → ℂ)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (p : A) (hp : IsStarProjection p) (t : ℝ) (ht : t≠0) (hpt : τA p=(t:ℂ))
    (e : A ≃⋆ₐ[ℂ] B) (en : @Continuous _ _ 𝒯A 𝒯B e)
    (ein : @Continuous _ _ 𝒯B 𝒯A e.symm) (et : ∀x,τB (e x)=τA x)
    (f : Corner p hp ≃⋆ₐ[ℂ] B)
    (fn : @Continuous _ _ (cornerTopology 𝒯A p hp) 𝒯B f)
    (fin : @Continuous _ _ 𝒯B (cornerTopology 𝒯A p hp) f.symm)
    (ft : ∀x,τB (f x)=(t:ℂ)⁻¹*τA (x:A)) : HasCornerScaling τB 𝒯B t := by
  let g := f.symm.trans (cornerCongr e p hp)
  refine ⟨e p,map_projection e p hp,g,?_,?_,?_,?_⟩
  · rw [et,hpt]
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    exact (cornerCongr_normal e p hp 𝒯A 𝒯B en).comp fin
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    let : TopologicalSpace (Corner (e p) (map_projection e p hp)) :=
      cornerTopology 𝒯B (e p) (map_projection e p hp)
    exact fn.comp (cornerCongr_symm_normal e p hp 𝒯A 𝒯B ein)
  · intro x
    change τB (e (f.symm x : A))=(t:ℂ)*τB x
    rw [et,←StarAlgEquiv.apply_symm_apply f x,ft]
    rw [StarAlgEquiv.symm_apply_apply,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht),one_mul]
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition

 theorem scalar_hasCornerScaling_weighted (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (hunit : u^2+v^2=1) :
    HasCornerScaling scalarTrace (scalarSystem.generatedTopology scalarFlip) (u^2) := by
  have hu : u≠0 := (lt_trans hv hvu).ne'
  have hv' : v≠0 := hv.ne'
  apply HasCornerScaling.of_recognitions (fun T : ambientAlgebra (ι := ℕ) u v => vacuumTrace u v (T : WeightedFock.Operator ℕ))
    scalarTrace (ambientTopology u v) (scalarSystem.generatedTopology scalarFlip)
    (ambientP u v) (ambientP_projection u v) (u^2) (pow_ne_zero 2 hu)
    (vacuumTrace_P u v) (ambientScalarIso u v hu hv' hunit)
    (ambientScalarIso_normal u v hu hv' hunit) (ambientScalarIso_symm_normal u v hu hv' hunit)
    (ambientScalarIso_trace u v hu hv' hunit) (ambientCornerGaussianIso u v hv hvu)
    (ambientCornerGaussianIso_normal u v hv hvu) (ambientCornerGaussianIso_symm_normal u v hv hvu)
  intro x
  change inner ℂ scalarSystem.root
    ((ambientCornerGaussianIso u v hv hvu x : FreeFock.Operator ScalarIndex) scalarSystem.root)=_
  rw [ambientCornerGaussianIso_trace,pVacuumTrace,Complex.ofReal_pow,←inv_pow]
  ring

end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
open WeightedFock FreeFock

end FreeGroupFactorMain.Amplification

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.WeightedFock.scalar_hasCornerScaling_weighted := @OAI.FreeGroupFactorMain.WeightedFock.scalar_hasCornerScaling_weighted
