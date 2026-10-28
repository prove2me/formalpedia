-- Prove2me | solution 1 for OAI.ElasticityBoundaryForceSupport.transferred_force_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:08:29.579395+00:00
-- url     : https://prove2.me/submissions/3daebc42-062d-402d-8b21-e610472fb890

import Mathlib
import Definitions.Def_OAIQ6El004

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal first and second coordinate chain rules. The maps are genuine
Frechet-smooth maps; a tensor pullback will use these identities, rather
than postulating a transformed elasticity operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChainRule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_dd {f : E → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (dd f v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma smooth_jac {ψ : E → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : E) (α : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (jac ψ v α) :=
  (contDiff_apply ℝ ℝ α).comp ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)

lemma fderiv_basis (f : Y → ℂ) (x v : Y) :
    fderiv ℝ f x v=∑ α, (v α:ℂ)*cp f α x := by
  have hv : v=∑ α : Fin 3, v α • Pi.single α (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  calc
    _ = fderiv ℝ f x (∑ α, v α • Pi.single α (1:ℝ)) := congrArg _ hv
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro α _
      rw [map_smul]
      exact Complex.real_smul

lemma dd_comp {f : Y → ℂ} {ψ : E → Y} (hf : Differentiable ℝ f)
    (hψ : Differentiable ℝ ψ) (v x : E) :
    dd (fun x => f (ψ x)) v x=∑ α, (jac ψ v α x:ℂ)*cp f α (ψ x) := by
  change fderiv ℝ (f ∘ ψ) x v=_
  rw [fderiv_comp x (hf _) (hψ x), ContinuousLinearMap.comp_apply, fderiv_basis]
  rfl

lemma dd_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i∈s, Differentiable ℝ (f i)) (v x : E) :
    dd (fun z => ∑ i∈s, f i z) v x=∑ i∈s, dd (f i) v x := by
  rw [dd, fderiv_fun_sum (fun i hi => hf i hi x), sum_apply]
  rfl

lemma dd_mul {f g : E → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v x : E) : dd (fun z => f z*g z) v x=dd f v x*g x+f x*dd g v x := by
  rw [dd, fderiv_fun_mul (hf x) (hg x)]
  simp only [add_apply, smul_apply, smul_eq_mul, dd]
  ring

lemma dd_ofReal {f : E → ℝ} (hf : Differentiable ℝ f) (v x : E) :
    dd (fun z => (f z:ℂ)) v x=(fderiv ℝ f x v:ℂ) := by
  exact congrArg (fun A : E →L[ℝ] ℂ => A v)
    (Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv

/-- The second chain rule with the exact Hessian-of-coordinate lower term. -/
theorem dd_dd_comp {f : Y → ℂ} {ψ : E → Y}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v w x : E) :
    dd (dd (fun z => f (ψ z)) w) v x=
      (∑ β, (hess ψ v w β x:ℂ)*cp f β (ψ x))+
      ∑ β, ∑ α, (jac ψ w β x:ℂ)*(jac ψ v α x:ℂ)*cp (cp f β) α (ψ x) := by
  have heq : dd (fun z => f (ψ z)) w=
      fun z => ∑ β, (jac ψ w β z:ℂ)*cp f β (ψ z) :=
    funext (dd_comp (hf.differentiable (by simp)) (hψ.differentiable (by simp)) w)
  rw [heq, dd_sum]
  · have hc (β : Fin 3) : Differentiable ℝ (cp f β) :=
      (smooth_dd hf _).differentiable (by simp)
    have hJ (β : Fin 3) : Differentiable ℝ (jac ψ w β) :=
      (smooth_jac hψ w β).differentiable (by simp)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro β _
    rw [dd_mul (f := fun z => (jac ψ w β z : ℂ)) (g := fun z => cp f β (ψ z))
      (Complex.ofRealCLM.differentiable.comp (hJ β))
      ((hc β).comp (hψ.differentiable (by simp))), dd_ofReal (hJ β),
      dd_comp (hc β) (hψ.differentiable (by simp)), Finset.mul_sum]
    simp only [hess, mul_assoc]
  · intro β _
    exact (Complex.ofRealCLM.differentiable.comp ((smooth_jac hψ w β).differentiable (by simp))).mul
      (((smooth_dd hf _).differentiable (by simp)).comp (hψ.differentiable (by simp)))

end ElasticityBoundaryChainRule

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! True pullback of a second-order physical system. The coefficient Hessian
term is retained, and no equivalence of augmented and physical DN data is used. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryPullback
open ElasticityBoundaryChainRule ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma shuffle3 {R : Type*} [AddCommMonoid R] (f : I → I → I → R) :
    (∑ i, ∑ j, ∑ k, f i j k)=∑ j, ∑ k, ∑ i, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

lemma shuffle5 {R : Type*} [AddCommMonoid R] (f : I → I → I → I → I → R) :
    (∑ k, ∑ j, ∑ l, ∑ β, ∑ α, f k j l β α)=
      ∑ α, ∑ j, ∑ β, ∑ k, ∑ l, f k j l β α := by
  simp_rw [Finset.sum_comm (f := fun β α => f _ _ _ β α)]
  simp_rw [Finset.sum_comm (f := fun l α => ∑ β, f _ _ l β α)]
  simp_rw [Finset.sum_comm (f := fun j α => ∑ l, ∑ β, f _ j l β α)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [Finset.sum_comm (f := fun l β => f _ j l β α)]
  exact Finset.sum_comm

/-- The actual system under a smooth coordinate map, including all lower
terms from its Hessian. No coordinate Jacobian is silently discarded. -/
theorem directional_comp (e : I → E) (a : Tensor E) (b : Lower E)
    {ψ : E → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (x : E) :
    directional e a b (fun j z => u j (ψ z)) i x =
      (∑ α, ∑ j, ∑ β, principalPull e a ψ i α j β x*cp (cp (u j) β) α (ψ x))+
        ∑ j, ∑ β, lowerPull e a b ψ i j β x*cp (u j) β (ψ x) := by
  simp only [directional, dd_dd_comp (hu _) hψ,
    dd_comp ((hu _).differentiable (by simp)) (hψ.differentiable (by simp)),
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have hp : (∑ k, ∑ j, ∑ l, ∑ β, ∑ α,
      a i k j l x*((jac ψ (e l) β x:ℂ)*(jac ψ (e k) α x:ℂ)*cp (cp (u j) β) α (ψ x))) =
      ∑ α, ∑ j, ∑ β, principalPull e a ψ i α j β x*cp (cp (u j) β) α (ψ x) := by
    rw [shuffle5]
    unfold principalPull
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hp]
  unfold lowerPull
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  have hh : (∑ k, ∑ j, ∑ l, ∑ β,
      a i k j l x*((hess ψ (e k) (e l) β x:ℂ)*cp (u j) β (ψ x))) =
      ∑ j, ∑ β, ∑ k, ∑ l, a i k j l x*(hess ψ (e k) (e l) β x:ℂ)*cp (u j) β (ψ x) := by
    simp_rw [Finset.sum_comm (f := fun l β => a i _ _ l x*(_*cp (u _) β (ψ x)))]
    rw [shuffle3]
    simp only [mul_assoc]
  have hb : (∑ j, ∑ l, ∑ α, b i j l x*((jac ψ (e l) α x:ℂ)*cp (u j) α (ψ x)))=
      ∑ j, ∑ β, ∑ l, b i j l x*(jac ψ (e l) β x:ℂ)*cp (u j) β (ψ x) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [hh,hb]
  abel

end ElasticityBoundaryPullback

end
end
section
/-! Exact constant-frame transformation of the strong differential operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryFrameOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dd_mix (Q : I → I → ℂ) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (v x : E) :
    dd (mix Q u i) v x=∑ j, Q i j*dd (u j) v x := by
  change dd (fun z => ∑ j, Q i j*u j z) v x=_
  rw [dd_sum Finset.univ (fun j z => Q i j*u j z)
    (fun j _ => (contDiff_const.mul (hu j)).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dd_mul (differentiable_const _) ((hu j).differentiable (by simp))]
  have hz : dd (fun _ : E => Q i j) v x=0 := by simp [dd]
  rw [hz,zero_mul,zero_add]

lemma dd_dd_mix (Q : I → I → ℂ) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (v w x : E) :
    dd (dd (mix Q u i) w) v x=∑ j, Q i j*dd (dd (u j) w) v x := by
  have he : dd (mix Q u i) w=mix Q (fun j => dd (u j) w) i := by
    funext z
    exact dd_mix Q u hu i w z
  rw [he]
  exact dd_mix Q _ (fun j => smooth_dd (hu j) w) i v x

lemma shuffle4 {R : Type*} [AddCommMonoid R] (f : I → I → I → I → R) :
    (∑ i, ∑ j, ∑ l, ∑ r, f i j l r)=∑ r, ∑ l, ∑ i, ∑ j, f i j l r := by
  simp_rw [Finset.sum_comm (f := fun l r => f _ _ l r)]
  simp_rw [Finset.sum_comm (f := fun j r => ∑ l, f _ j l r)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [Finset.sum_comm (f := fun j l => f _ j l r)]
  exact Finset.sum_comm

/-- Input displacement and output equation rotation retain every literal term. -/
theorem directional_mix (e : I → E) (R S : I → I → ℂ) (a : Tensor E) (b : Lower E)
    (u : I → E → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (s : I) (x : E) :
    (∑ i, R s i*directional e a b (mix S u) i x)=
      directional e (mixedTensor R S a) (mixedLower R S b) u s x := by
  simp only [directional, dd_dd_mix S u hu, dd_mix S u hu,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  unfold mixedTensor mixedLower
  simp only [Finset.sum_mul]
  congr 1
  · rw [shuffle5, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [shuffle4]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end ElasticityBoundaryFrameOperator

end
end
section
/-! The strong expression is the divergence of the actual isotropic stress,
with every Lamé-gradient term retained. It is not an independently prescribed
system. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryPhysicalStrong
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryLayerOperator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dd_add {f g : E → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v x : E) :
    dd (fun z => f z+g z) v x=dd f v x+dd g v x := by
  rw [dd, fderiv_fun_add (hf x) (hg x), add_apply]
  rfl

lemma dd_ite (P : Prop) [Decidable P] (f g : E → ℂ) (v x : E) :
    dd (fun z => if P then f z else g z) v x=if P then dd f v x else dd g v x := by
  by_cases h : P <;> simp [h]

lemma smooth_divergence (e : I → E) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) : ContDiff ℝ (⊤ : ℕ∞) (divergence e u) := by
  exact ContDiff.sum (fun j _ => smooth_dd (hu j) _)

lemma stress_derivative (e : I → E) {l m : E → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → E → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i k : I) (x : E) :
    dd (stress e l m u i k) (e k) x =
      (if i=k then dd l (e k) x*divergence e u x+l x*(∑ j, dd (dd (u j) (e j)) (e k) x) else 0)+
      dd m (e k) x*(dd (u i) (e k) x+dd (u k) (e i) x)+
      m x*(dd (dd (u i) (e k)) (e k) x+dd (dd (u k) (e i)) (e k) x) := by
  have hd := smooth_divergence e u hu
  have hsum (v : E) : dd (divergence e u) v x=∑ j, dd (dd (u j) (e j)) v x := by
    exact dd_sum Finset.univ (fun j => dd (u j) (e j))
      (fun j _ => (smooth_dd (hu j) _).differentiable (by simp)) v x
  have h0 : Differentiable ℝ (fun z => if i=k then l z*divergence e u z else 0) := by
    by_cases h : i=k
    · simpa [h] using (hl.mul hd).differentiable (by simp)
    · simp only [h,ite_false]
      exact differentiable_const 0
  change dd (fun z => (if i=k then l z*divergence e u z else 0)+
    m z*(dd (u i) (e k) z+dd (u k) (e i) z)) (e k) x=_
  rw [dd_add h0 ((hm.mul ((smooth_dd (hu i) _).add (smooth_dd (hu k) _))).differentiable (by simp)),
    dd_ite, dd_mul (hl.differentiable (by simp)) (hd.differentiable (by simp)), hsum,
    dd_mul (hm.differentiable (by simp))
      (((smooth_dd (hu i) _).add (smooth_dd (hu k) _)).differentiable (by simp)),
    dd_add ((smooth_dd (hu i) _).differentiable (by simp)) ((smooth_dd (hu k) _).differentiable (by simp))]
  have hz : dd (fun _ : E => (0 : ℂ)) (e k) x=0 := by simp [dd]
  rw [hz]
  ring

lemma tensor_contract (l m : ℂ) (d : I → I → I → ℂ) (i : I) :
    (∑ k, ∑ j, ∑ β, elasticityTensor l m i k j β*d j k β)=
      l*(∑ j, d j i j)+m*(∑ k, d i k k)+m*(∑ k, d k k i) := by
  simp only [elasticityTensor, add_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Fintype.sum_ite_eq, Finset.sum_const_zero]
  simp only [← Finset.mul_sum]
  ring

lemma lower_contract (dl dm : I → ℂ) (d : I → I → ℂ) (i : I) :
    (∑ j, ∑ β, (dl i*(if j=β then 1 else 0)+dm β*(if i=j then 1 else 0)+
      dm j*(if i=β then 1 else 0))*d j β)=
      dl i*(∑ j, d j j)+(∑ k, dm k*d i k)+∑ k, dm k*d k i := by
  simp only [add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Fintype.sum_ite_eq, Finset.sum_const_zero]
  rw [← Finset.mul_sum]

/-- Divergence of the physical Lamé stress equals the constructed literal
second-order system, including its exact first-order coefficient terms. -/
theorem stress_divergence (e : I → E) {l m : E → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → E → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (x : E) :
    (∑ k, dd (stress e l m u i k) (e k) x)=directional e (coeff l m) (lower e l m) u i x := by
  simp only [stress_derivative e hl hm u hu, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_add, ← Finset.mul_sum]
  change _ = (∑ k, ∑ j, ∑ β, elasticityTensor (l x) (m x) i k j β*dd (dd (u j) (e β)) (e k) x)+
    ∑ j, ∑ β, (dd l (e i) x*(if j=β then 1 else 0)+dd m (e β) x*(if i=j then 1 else 0)+
      dd m (e j) x*(if i=β then 1 else 0))*dd (u j) (e β) x
  rw [tensor_contract]
  rw [lower_contract (fun k => dd l (e k) x) (fun k => dd m (e k) x) (fun j β => dd (u j) (e β) x) i]
  simp only [divergence]
  ring

end ElasticityBoundaryPhysicalStrong

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCharts
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The boundary-coordinate differential operator is obtained from literal
physical elasticity by the chain rule and a fixed Euclidean rotation. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChartOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
  ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundarySmoothOperator ElasticityBoundaryLayerOperator ElasticityBoundaryStrongLayer

/-- Exact equality with the true physical stress divergence after pullback.
The inverse chart equality is used literally, not replaced by a formal symbol. -/
theorem physical_chart_operator (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) {ψ : X → Y}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (y : Y) (hy : ψ (Φ y)=y) (s : I) :
    (∑ i, frameMatrix Q i s*(∑ k, dd
      (stress basis l m (mix (frameMatrix Q) (fun j x => u j (ψ x))) i k) (basis k) (Φ y)))=
      strong (chartPrincipal Q Φ ψ l m) (chartLower Q Φ ψ l m) u s y := by
  have hS (i : I) := stress_divergence basis hl hm
    (mix (frameMatrix Q) (fun j x => u j (ψ x)))
    (smooth_mix _ _ (fun j => (hu j).comp hψ)) i (Φ y)
  simp_rw [hS]
  refine (directional_mix basis (fun s i => frameMatrix Q i s) (frameMatrix Q)
    (coeff l m) (lower basis l m) (fun j => u j ∘ ψ) (fun j => (hu j).comp hψ) s (Φ y)).trans ?_
  refine (directional_comp basis _ _ hψ u hu s (Φ y)).trans ?_
  rw [hy]
  rfl

end ElasticityBoundaryChartOperator

end
end
section
/-! Transferring a trial supported in an honest chart produces an actual
 globally smooth compact physical field, without imposing artificial boundary
 data. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma chartTransfer_apply (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {y : E} (hy : y∈e.source) :
    chartTransfer e η u (e y)=u y := by
  unfold chartTransfer
  rw [e.left_inv hy]
  by_cases h : u y=0
  · simp [h]
  · rw [hη _ (mem_image_of_mem e (hu h)),one_smul]

end ElasticityBoundary

end
end
section
/-! Locality and true support control for the physical differential operator
and the compact chart transfer. These use germs, not formal coefficients. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryOperatorLocal
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryPhysicalStrong
  ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dd_germ {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    dd f v =ᶠ[𝓝 x] dd g v := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun A : E →L[ℝ] ℂ => A v) hy

lemma dd_germ_eq {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    dd f v x=dd g v x := (dd_germ h v).eq_of_nhds

lemma directional_germ_eq (e : I → E) (a : Tensor E) (b : Lower E)
    {u v : I → E → ℂ} {x : E} (h : ∀ j, u j =ᶠ[𝓝 x] v j) (i : I) :
    directional e a b u i x=directional e a b v i x := by
  unfold directional
  congr 1
  · apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    rw [dd_germ_eq (dd_germ (h j) (e l)) (e k)]
  · apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    rw [dd_germ_eq (h j) (e l)]

lemma directional_zero (e : I → E) (a : Tensor E) (b : Lower E) (i : I) (x : E) :
    directional e a b (fun _ _ => 0) i x=0 := by
  have hz (v : E) : dd (fun _ : E => (0:ℂ)) v=(fun _ => 0) := by
    funext y
    simp [dd]
  simp only [directional,hz,mul_zero,Finset.sum_const_zero,add_zero]

lemma directional_support (e : I → E) (a : Tensor E) (b : Lower E)
    {K : Set E} (hK : IsClosed K) (u : I → E → ℂ)
    (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (directional e a b u i)⊆K := by
  intro x hx
  by_contra hn
  have hg (j : I) : u j =ᶠ[𝓝 x] (fun _ => 0) := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    exact fun h => hn (closure_minimal (hu j) hK h)
  have heq := directional_germ_eq e a b hg i
  rw [directional_zero] at heq
  exact hx heq

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
lemma chartTransfer_germ (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {x : E} (hx : x∈e.target) :
    chartTransfer e η u =ᶠ[𝓝 x] (fun z => u (e.symm z)) := by
  filter_upwards [e.open_target.mem_nhds hx] with z hz
  have h := chartTransfer_apply e hη hu (e.map_target hz)
  simpa only [e.right_inv hz] using h

omit [NormedSpace ℝ E] in
lemma chartTransfer_extension_germ (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {x : E} (hx : x∈e.target)
    {Ψ : E → E} (hΨ : Ψ =ᶠ[𝓝 x] e.symm) :
    chartTransfer e η u =ᶠ[𝓝 x] (fun z => u (Ψ z)) := by
  filter_upwards [chartTransfer_germ e hη hu hx,hΨ] with z hz hΨz
  rw [hz,hΨz]

end ElasticityBoundaryOperatorLocal

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Physical displacements obtained from compact chart fields. Their literal
strong Lamé force is the constructed curved-coordinate operator on the
whole trial support, rather than a formally equated auxiliary DN system. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalTransfer
open ElasticityBoundary ElasticityBoundaryChainRule ElasticityBoundaryPullback
  ElasticityBoundaryPhysicalStrong ElasticityBoundaryRotation ElasticityBoundaryFrameOperator
  ElasticityBoundaryChartOperator ElasticityBoundaryOperatorLocal ElasticityBoundaryStrongLayer

lemma transferred_germ (e : OpenPartialHomeomorph X X) {K : Set X}
    {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) {x : X} (hx : x∈e.target)
    {Ψ : X → X} (hΨ : Ψ =ᶠ[𝓝 x] e.symm) (i : I) :
    transferred e η Q u i =ᶠ[𝓝 x]
      mix (frameMatrix Q) (fun j z => u j (Ψ z).ofLp) i :=
  chartTransfer_extension_germ e hη (support_lifted Q u hu i) hx hΨ

lemma chart_force (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) {ψ : X → Y}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (y : Y) (hy : ψ (Φ y)=y) (s : I) :
    (∑ i, frameMatrix Q i s*force l m (mix (frameMatrix Q) (fun j x => u j (ψ x))) i (Φ y))=
      strong (chartPrincipal Q Φ ψ l m) (chartLower Q Φ ψ l m) u s y := by
  calc
    _ = ∑ i, frameMatrix Q i s*(∑ k, dd
        (stress basis l m (mix (frameMatrix Q) (fun j x => u j (ψ x))) i k) (basis k) (Φ y)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun z => frameMatrix Q i s*z)
      exact (stress_divergence basis hl hm _
        (fun j => smooth_mix (frameMatrix Q) _ (fun k => (hu k).comp hψ) j) i (Φ y)).symm
    _ = _ := physical_chart_operator Q Φ hψ hl hm u hu y hy s

/-- The exact coordinate operator controls the genuine transferred physical
force at every point of the compact trial support. -/
theorem transferred_force (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : K⊆e.source) {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (y : Y) (hy : WithLp.toLp 2 y∈K)
    (hΦy : Φ (WithLp.toLp 2 y)=e (WithLp.toLp 2 y))
    (hΨy : Ψ =ᶠ[𝓝 (e (WithLp.toLp 2 y))] e.symm) (s : I) :
    (∑ i, frameMatrix Q i s*force l m (transferred e η Q u) i (e (WithLp.toLp 2 y)))=
      strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
        (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s y := by
  have hx := e.map_source (hK hy)
  have hg := transferred_germ e hη Q u hus hx hΨy
  have hid : (Ψ (Φ (WithLp.toLp 2 y))).ofLp=y := by
    rw [hΦy,hΨy.eq_of_nhds,e.left_inv (hK hy)]
  calc
    _ = ∑ i, frameMatrix Q i s*force l m
        (mix (frameMatrix Q) (fun j z => u j (Ψ z).ofLp)) i (e (WithLp.toLp 2 y)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => frameMatrix Q i s*z)
        (directional_germ_eq basis (coeff l m) (lower basis l m) hg i)
    _ = _ := by
      rw [← hΦy]
      exact chart_force Q (fun z => Φ (WithLp.toLp 2 z))
        (PiLp.contDiff_ofLp.comp hΨ) hl hm u hu y hid s

end ElasticityBoundaryPhysicalTransfer

end
end
section
/-! Local boundary layers for arbitrary smooth coefficients. Auxiliary compact
coefficient extensions are removed on the actual trial support; thus no
artificial compactness or global geometry assumption is imposed on a chart. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryLocalParametrix
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundarySmoothOperator
  ElasticityBoundaryMVNormal ElasticityBoundaryActualTower ElasticityBoundaryLayerOperator ElasticityBoundaryProfile ElasticityBoundaryOperatorLocal
  ElasticityBoundary ElasticityBoundaryProfileBounds

lemma strong_support (a : SmoothTensor) (b : SmoothLower) {K : Set Y} (hK : IsClosed K)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (strong a b u i)⊆K :=
  directional_support (fun j => Pi.single j 1) a b hK u hu i

end ElasticityBoundaryLocalParametrix

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Support-complete physical force identification. The coordinate expression
is valid on the entire chart source, including all zero regions, and the
physical force is supported in the genuine compact image. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryForceSupport
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryOperatorLocal
  ElasticityBoundaryLocalParametrix ElasticityBoundaryStrongLayer
  ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryFrameInverse ElasticityBoundaryRotation

lemma force_support (l m : X → ℂ) (u : I → X → ℂ) {K : Set X}
    (hK : IsClosed K) (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (force l m u i)⊆K :=
  directional_support basis _ _ hK u hu i

lemma transferred_force_support (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hη : tsupport η⊆e.target)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (l m : X → ℂ) (i : I) :
    Function.support (force l m (transferred e η Q u) i)⊆e '' K :=
  force_support l m _ (compact_image e hK hs).isClosed (support_transferred e hη Q u hu) i

lemma strong_support_lifted (a : ElasticityBoundarySmoothOperator.SmoothTensor)
    (b : ElasticityBoundarySmoothOperator.SmoothLower) {K : Set X} (hK : IsClosed K)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (i : I) :
    Function.support (fun z : X => strong a b u i z.ofLp)⊆K := by
  intro x hx
  have hcl : IsClosed {y : Y | WithLp.toLp 2 y∈K} := hK.preimage (PiLp.continuous_toLp 2 (fun _ : I => ℝ))
  have hh : ∀ j, Function.support (u j)⊆{y : Y | WithLp.toLp 2 y∈K} := by
    intro j y hy
    exact hu j hy
  exact strong_support a b hcl u hh i hx

/-- No operator identity is required outside the actual support: locality
proves both sides vanish there. -/
theorem transferred_force_all_oai (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (x : X) (hx : x∈e.source) (s : I) :
    (∑ i, frameMatrix Q i s*force l m (transferred e η Q u) i (e x))=
      strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
        (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s x.ofLp := by
  by_cases hxK : x∈K
  · exact transferred_force e hs hη Q u hus hu Φ Ψ hΨ hl hm x.ofLp hxK
      (hΦ x hxK) (hΨe _ (mem_image_of_mem e hxK)) s
  · have hn : e x∉e '' K := by
      rintro ⟨y,hy,he⟩
      exact hxK (e.injOn (hs hy) hx he ▸ hy)
    have hz (i : I) : force l m (transferred e η Q u) i (e x)=0 :=
      Function.notMem_support.mp (fun h => hn (transferred_force_support e hK hs hηs Q u hus l m i h))
    have hr : strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
        (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s x.ofLp=0 :=
      Function.notMem_support.mp (fun h => hxK (strong_support_lifted _ _ hK.isClosed u hus s h))
    simp only [hz,mul_zero,Finset.sum_const_zero,hr]

end ElasticityBoundaryForceSupport

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryForceSupport.transferred_force_all_oai := @OAI.ElasticityBoundaryForceSupport.transferred_force_all_oai
