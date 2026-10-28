-- Prove2me | solution 1 for OAI.ElasticityAugmented.supported_matrix_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:06:11.209818+00:00
-- url     : https://prove2.me/submissions/ce6ea630-13aa-4962-a8a2-979d7fcf06ab

import Mathlib
import Definitions.Def_OAIQ6El003
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityAugmented_supported_matrix_smooth
import Theorems.Thm_OAI_ElasticityParameter_holomorphic_of_supported_transport

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityParameter
open scoped BigOperators
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E}
lemma delta_apply (v : E) (f : Smooth E) (x : E) :
    (delta v f : E → ℂ) x=fderiv ℝ (f : E → ℂ) x v := rfl
end ElasticityParameter
namespace ElasticityParameter
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

lemma spatial_slice_deriv (f : Smooth (E × ℂ)) (x v : E) (z : ℂ) :
    fderiv ℝ (fun y => (f : E × ℂ → ℂ) (y,z)) x v=
      fderiv ℝ (f : E × ℂ → ℂ) (x,z) (v,0) := by
  have he : HasFDerivAt (fun y : E => (y,z)) (ContinuousLinearMap.inl ℝ E ℂ) x := by
    simpa only [ContinuousLinearMap.inl,id] using (hasFDerivAt_id x).prodMk (hasFDerivAt_const z x)
  exact congrArg (fun L : E →L[ℝ] ℂ => L v)
    (((smooth f).differentiable (by simp) (x,z)).hasFDerivAt.comp x he).fderiv
end ElasticityParameter
namespace ElasticityParameter
open scoped BigOperators InnerProductSpace

lemma real_complex_plane_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ha : a≠0) (hb : b≠0) (hab : inner ℝ a b=0) :
    Function.Injective (Complex.reCLM.smulRight a+Complex.imCLM.smulRight b : ℂ →L[ℝ] E) := by
  let J : ℂ →L[ℝ] E := Complex.reCLM.smulRight a+Complex.imCLM.smulRight b
  suffices hn : ∀ z : ℂ, J z=0 → z=0 by
    intro z w h
    apply sub_eq_zero.mp
    apply hn
    rw [map_sub,h,sub_self]
  intro z hz
  have ha0 : inner ℝ a a≠0 := by
    intro h
    exact ha (inner_self_eq_zero.mp h)
  have hb0 : inner ℝ b b≠0 := by
    intro h
    exact hb (inner_self_eq_zero.mp h)
  have hba : inner ℝ b a=0 := by rwa [real_inner_comm]
  have hr := congrArg (fun v : E => inner ℝ a v) hz
  have hi := congrArg (fun v : E => inner ℝ b v) hz
  change inner ℝ a (z.re • a+z.im • b)=inner ℝ a 0 at hr
  change inner ℝ b (z.re • a+z.im • b)=inner ℝ b 0 at hi
  simp only [inner_add_right,inner_smul_right,hab,hba,mul_zero,zero_add,add_zero,inner_zero_right] at hr hi
  apply Complex.ext
  · exact (mul_eq_zero.mp hr).resolve_right ha0
  · exact (mul_eq_zero.mp hi).resolve_right hb0

lemma basis_sum_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    (∑ r, v r • basis r : X) i=v i := by
  simp [basis,Pi.single_apply]

lemma null_re_im (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) :
    (∑ i, (θ i).re*(θ i).re)=(∑ i, (θ i).im*(θ i).im) ∧
      (∑ i, (θ i).re*(θ i).im)=0 := by
  have hr := congrArg Complex.re hθ
  have hi := congrArg Complex.im hθ
  simp only [Complex.re_sum,Complex.mul_re,Complex.zero_re,Finset.sum_sub_distrib] at hr
  simp only [Complex.im_sum,Complex.mul_im,Complex.zero_im,Finset.sum_add_distrib] at hi
  have he : (∑ i, (θ i).im*(θ i).re)=(∑ i, (θ i).re*(θ i).im) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he] at hi
  constructor
  · exact sub_eq_zero.mp hr
  · linarith

lemma null_plane_injective (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (hne : θ≠0) :
    Function.Injective (characteristicPlane basis θ) := by
  obtain ⟨hre,him⟩ := null_re_im θ hθ
  let a : X := ∑ i, (θ i).re • basis i
  let b : X := ∑ i, (θ i).im • basis i
  have hai (i : Fin 3) : a i=(θ i).re := basis_sum_apply _ i
  have hbi (i : Fin 3) : b i=(θ i).im := basis_sum_apply _ i
  have haa : inner ℝ a a=∑ i, (θ i).re*(θ i).re := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai]
  have hbb : inner ℝ b b=∑ i, (θ i).im*(θ i).im := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hbi]
  have hab : inner ℝ a b=0 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai,hbi]
    simpa only [mul_comm] using him
  have he : inner ℝ a a=inner ℝ b b := by rw [haa,hbb,hre]
  have hboth : ¬ (a=0 ∧ b=0) := by
    rintro ⟨ha,hb⟩
    apply hne
    funext i
    apply Complex.ext
    · simpa only [ha,PiLp.zero_apply,Pi.zero_apply,Complex.zero_re] using (hai i).symm
    · simpa only [hb,PiLp.zero_apply,Pi.zero_apply,Complex.zero_im] using (hbi i).symm
  have ha : a≠0 := by
    intro hz
    apply hboth
    refine ⟨hz,(@inner_self_eq_zero ℝ X _ _ _).mp ?_⟩
    rw [← he,hz,inner_zero_left]
  have hb : b≠0 := by
    intro hz
    apply ha
    apply (@inner_self_eq_zero ℝ X _ _ _).mp
    rw [he,hz,inner_zero_left]
  exact real_complex_plane_injective a b ha hb hab
end ElasticityParameter
namespace ElasticityAugmented
open scoped BigOperators

lemma thetaDerivation_apply (θ : Fin 3 → ℂ) (f : Smooth) :
    thetaDerivation θ f=direction (A := Smooth) coord θ f := by
  simp [thetaDerivation,direction,Fin.sum_univ_three]
end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented
lemma smooth_sum_eval {ι : Type*} [Fintype ι] (f : ι → Smooth) (x : X) :
    ((∑ i,f i : Smooth) : X → ℂ) x=∑ i,(f i : X → ℂ) x := by
  exact map_sum ((Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom) f Finset.univ
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Conic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityParameter
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma commutator_flatten {R : Type*} [CommRing R]
    (M₂ M₁ G : n → n → R) (i j : n) :
    (∑ k, (M₂ i k*G k j-G i k*M₁ k j))=
      ∑ q : n × n, ((if q.2=j then M₂ i q.1 else 0)-
        (if q.1=i then M₁ q.2 j else 0))*G q.1 q.2 := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [mul_comm]

/-- The comparison equation on a holomorphic fiber chart forces holomorphy
in the parameter. Nullity supplies the injective real characteristic planes;
no compact-kernel or holomorphy premise for the unknown is present. -/
theorem matrix_holomorphic_of_supported_comparison
    (θ : Fin 3 → Smooth (X × ℂ))
    (hθx : ∀ r x z, (θ r : X × ℂ → ℂ) (x,z)=(θ r : X × ℂ → ℂ) (0,z))
    (hθ : ∀ r x, Differentiable ℂ (fun z => (θ r : X × ℂ → ℂ) (x,z)))
    (hnull : ∀ z, ∑ r, (θ r : X × ℂ → ℂ) (0,z)*(θ r : X × ℂ → ℂ) (0,z)=0)
    (hne : ∀ z, (fun r => (θ r : X × ℂ → ℂ) (0,z))≠0)
    (M₂ M₁ G : n → n → Smooth (X × ℂ))
    (hM₂ : ∀ i j x, Differentiable ℂ (fun z => (M₂ i j : X × ℂ → ℂ) (x,z)))
    (hM₁ : ∀ i j x, Differentiable ℂ (fun z => (M₁ i j : X × ℂ → ℂ) (x,z)))
    (he : ∀ i j, ∑ r, θ r*delta (basis r,0) (G i j)=
      ∑ k, (M₂ i k*G k j-G i k*M₁ k j))
    {S : Set X} (hS : IsCompact S)
    (hs : ∀ i j x, x∉S → ∀ z, (G i j : X × ℂ → ℂ) (x,z)=if i=j then 1 else 0) :
    ∀ i j x, Differentiable ℂ (fun z => (G i j : X × ℂ → ℂ) (x,z)) := by
  let a : (n × n) → (n × n) → Smooth (X × ℂ) := fun p q =>
    (if q.2=p.2 then M₂ p.1 q.1 else 0)-(if q.1=p.1 then M₁ q.2 p.2 else 0)
  have ha (p q : n × n) (x : X) :
      Differentiable ℂ (fun z => (a p q : X × ℂ → ℂ) (x,z)) := by
    dsimp only [a]
    split_ifs <;> simp only [Subalgebra.coe_sub,Pi.sub_apply,Subalgebra.coe_zero,Pi.zero_apply]
    · exact (hM₂ _ _ x).sub (hM₁ _ _ x)
    · exact (hM₂ _ _ x).sub (differentiable_const 0)
    · exact (differentiable_const 0).sub (hM₁ _ _ x)
    · exact (differentiable_const 0).sub (differentiable_const 0)
  have h := holomorphic_of_supported_transport basis θ hθx hθ
    (fun z => null_plane_injective _ (hnull z) (hne z)) a ha
    (fun p : n × n => G p.1 p.2) (fun p => (he p.1 p.2).trans
      (commutator_flatten M₂ M₁ G p.1 p.2)) hS
    (fun p : n × n => if p.1=p.2 then 1 else 0) (fun p => hs p.1 p.2)
  exact fun i j => h (i,j)
end ElasticityParameter

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma supported_matrix_eq_one {K : Set X} (G : Matrix n n Smooth)
    (hs : ∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K)
    (x : X) (hx : x∉K) : matrixEval x G=1 := by
  ext i j
  have hz := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs i j hh))
  change (G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0 at hz
  have he : ((1 : Matrix n n Smooth) i j : X → ℂ) x=(1 : Matrix n n ℂ) i j := by
    have hh := congrArg (fun A : Matrix n n ℂ => A i j) (map_one (matrixEval (n := n) x))
    exact hh
  rw [he] at hz
  exact sub_eq_zero.mp hz

lemma matrixD_eval (θ : Fin 3 → ℂ) (G : Matrix n n Smooth) (x : X) (i j : n) :
    matrixEval x (matrixD θ G) i j=∑ r,θ r*fderiv ℝ (G i j : X → ℂ) x (ElasticityParameter.basis r) := by
  simp only [matrixEval_apply,matrixD,thetaDerivation_apply,direction,smooth_sum_eval,
    Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul]
  rfl

end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Holomorphy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Both regularity statements are derived for a separately constructed family
from its transport equation and ONE fixed spatial support. -/
theorem supported_matrix_holomorphic_oai (θ : Fin 3 → ℂ → ℂ)
    (hθs : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i)) (hθh : ∀ i,Differentiable ℂ (θ i))
    (hnull : ∀ z,∑ i,θ i z*θ i z=0) (hne : ∀ z,(fun i => θ i z)≠0)
    (M₀ M₁ G : ℂ → Matrix n n Smooth)
    (hM₀ : ∀ i j,ElasticityConic.JointHolomorphic (fun q : X × ℂ => (M₀ q.2 i j : X → ℂ) q.1))
    (hM₁ : ∀ i j,ElasticityConic.JointHolomorphic (fun q : X × ℂ => (M₁ q.2 i j : X → ℂ) q.1))
    {S : Set X} (hS : IsCompact S) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈S,(χ : X → ℂ) x=1)
    (hs : ∀ z i j,tsupport ((G z i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆S)
    (hMe : ∀ z x,x∉S → matrixEval x (M₀ z)=matrixEval x (M₁ z))
    (he : ∀ z,matrixD (fun i => θ i z) (G z)=M₁ z*G z-G z*M₀ z) :
    ∀ i j,ElasticityConic.JointHolomorphic (fun q : X × ℂ => (G q.2 i j : X → ℂ) q.1) := by
  have hgs := supported_matrix_smooth θ hθs hnull hne M₀ M₁ G
    (fun i j => (hM₀ i j).smooth) (fun i j => (hM₁ i j).smooth) hS χ hχ hχ1 hs hMe he
  let Θ : Fin 3 → ElasticityParameter.Smooth (X × ℂ) := fun i => ⟨fun q => θ i q.2,(hθs i).comp contDiff_snd⟩
  let A : n → n → ElasticityParameter.Smooth (X × ℂ) := fun i j => ⟨fun q => (M₁ q.2 i j : X → ℂ) q.1,(hM₁ i j).smooth⟩
  let B : n → n → ElasticityParameter.Smooth (X × ℂ) := fun i j => ⟨fun q => (M₀ q.2 i j : X → ℂ) q.1,(hM₀ i j).smooth⟩
  let F : n → n → ElasticityParameter.Smooth (X × ℂ) := fun i j => ⟨fun q => (G q.2 i j : X → ℂ) q.1,hgs i j⟩
  have hh := ElasticityParameter.matrix_holomorphic_of_supported_comparison Θ
    (fun _ _ _ => rfl) (fun i _ => hθh i) hnull hne A B F
    (fun i j => (hM₁ i j).holo) (fun i j => (hM₀ i j).holo) (fun i j => ?_) hS (fun i j x hx z => ?_)
  · exact fun i j => ⟨hgs i j,hh i j⟩
  · apply Subtype.ext
    funext q
    rcases q with ⟨x,z⟩
    simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,Subalgebra.coe_mul,
      Subalgebra.coe_sub,Pi.sub_apply,Pi.mul_apply,ElasticityParameter.delta_apply]
    change (∑ r, θ r z * fderiv ℝ (F i j : X × ℂ → ℂ) (x,z) (ElasticityParameter.basis r,0))=
      ∑ a, ((M₁ z i a : X → ℂ) x*(G z a j : X → ℂ) x-
        (G z i a : X → ℂ) x*(M₀ z a j : X → ℂ) x)
    simp_rw [← ElasticityParameter.spatial_slice_deriv]
    have hh := congrArg (fun C : Matrix n n Smooth => matrixEval x C i j) (he z)
    rw [matrixD_eval] at hh
    simpa only [F,map_sub,map_mul,Matrix.sub_apply,Matrix.mul_apply,matrixEval_apply,smooth_sum_eval,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.sub_apply,Pi.mul_apply,Finset.sum_sub_distrib] using hh
  · have h := congrArg (fun C : Matrix n n ℂ => C i j) (supported_matrix_eq_one (G z) (hs z) x hx)
    exact h
end ElasticityAugmented

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityAugmented.supported_matrix_holomorphic_oai.{u_1} := @OAI.ElasticityAugmented.supported_matrix_holomorphic_oai.{u_1}
