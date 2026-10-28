-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.Setup.trial_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:10:50.301315+00:00
-- url     : https://prove2.me/submissions/5c0fb2c3-7c28-43b6-a305-558cbb8bb642

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_Elasticity_physicalResidual_sq_mass

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

end ElasticityBoundaryOperatorLocal

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

end ElasticityBoundaryForceSupport

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity
/-! Actual smooth physical displacements give the exact H1 trial objects used
 by the physical DN map. This is a constructor, not a trace assumption. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

lemma smoothTrial_stress_ae {l m : X → ℝ} (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) (i j : Fin 3) :
    jetStress hl hm (smoothTrial f hs hf hd).val i j =ᵐ[volume.restrict Ω]
      fun x => (if i=j then l x*(∑ k, (coordDeriv f k x) k) else 0)+
        m x*((coordDeriv f j x) i+(coordDeriv f i x) j) := by
  let u := (smoothTrial f hs hf hd).val
  have hda : ∀ᵐ x ∂(volume.restrict Ω),∀ k, u (some k) x=coordDeriv f k x :=
    Filter.eventually_all.mpr (fun k => (hd k).coeFn_toLp)
  have hzero : (0 : ScalarL2 Ω) =ᵐ[volume.restrict Ω] fun _ => 0 := Lp.coeFn_zero _ _ _
  by_cases hij : i=j
  · filter_upwards [Lp.coeFn_add (hl.mulL (jetDiv Ω u)) ((2:ℝ) • hm.mulL (jetStrain Ω i j u)),
        Lp.coeFn_smul (2:ℝ) (hm.mulL (jetStrain Ω i j u)), hl.mulL_ae (jetDiv Ω u),
        hm.mulL_ae (jetStrain Ω i j u), jetDiv_ae u,jetStrain_ae u i j,hda] with x h0 h1 h2 h3 h4 h5 h6
    change ((if i=j then hl.mulL (jetDiv Ω u) else 0)+(2:ℝ) • hm.mulL (jetStrain Ω i j u)) x=_
    simp only [hij,ite_true] at *
    rw [h0]
    simp only [Pi.add_apply]
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul,h2,h3,h4,h5,h6]
    ring
  · filter_upwards [Lp.coeFn_add (0 : ScalarL2 Ω) ((2:ℝ) • hm.mulL (jetStrain Ω i j u)),
        Lp.coeFn_smul (2:ℝ) (hm.mulL (jetStrain Ω i j u)),hzero,
        hm.mulL_ae (jetStrain Ω i j u),jetStrain_ae u i j,hda] with x h0 h1 hz h3 h5 h6
    change ((if i=j then hl.mulL (jetDiv Ω u) else 0)+(2:ℝ) • hm.mulL (jetStrain Ω i j u)) x=_
    simp only [hij,ite_false]
    rw [h0]
    simp only [Pi.add_apply]
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul,hz,h3,h5,h6]
    ring

end Elasticity
namespace Elasticity
/-! Exact agreement of the variational trial energy with classical smooth
physical fields and their literal derivatives. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

lemma realField_derivative (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) (i j : Fin 3) (x : X) :
    coordDeriv (realField w u) j x i=
      w (ElasticityBoundaryChainRule.dd (u i) (coordVector j) x) := by
  have h1 := (EuclideanSpace.proj i : V →L[ℝ] ℝ).hasFDerivAt.comp x
    (((smooth_realField w u hu).differentiable (by simp)) x).hasFDerivAt
  have h2 := w.hasFDerivAt.comp x (((hu i).differentiable (by simp)) x).hasFDerivAt
  have he : (EuclideanSpace.proj i : V →L[ℝ] ℝ) ∘ realField w u=w ∘ u i := rfl
  rw [he] at h1
  have hh := congrArg (fun A : X →L[ℝ] ℝ => A (coordVector j)) (h1.unique h2)
  exact hh

end Elasticity
namespace ElasticityBoundaryProjectedStress
/-! The complex quasimode's real and imaginary stresses are the literal real
physical stresses used by the DN map. -/
open Set MeasureTheory
open scoped BigOperators
open Elasticity ElasticityBoundaryChainRule ElasticityBoundaryPhysicalStrong
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalTransfer

lemma smooth_stress {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i j : I) :
    ContDiff ℝ (⊤ : ℕ∞) (stress basis l m u i j) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    (if i=j then l x*divergence basis u x else 0)+
      m x*(dd (u i) (basis j) x+dd (u j) (basis i) x))
  by_cases hij : i=j
  · simp only [hij,ite_true]
    exact (hl.mul (smooth_divergence basis u hu)).add
      (hm.mul ((smooth_dd (hu j) _).add (smooth_dd (hu j) _)))
  · simp only [hij,ite_false,zero_add]
    exact hm.mul ((smooth_dd (hu i) _).add (smooth_dd (hu j) _))

lemma compact_stress (l m : X → ℂ) (u : I → X → ℂ)
    (hu : ∀ j, HasCompactSupport (u j)) (i j : I) :
    HasCompactSupport (stress basis l m u i j) := by
  have hd : HasCompactSupport (divergence basis u) := by
    change HasCompactSupport (fun x => ∑ k, dd (u k) (basis k) x)
    simp only [Fin.sum_univ_three]
    exact (((hu 0).fderiv_apply ℝ _).add ((hu 1).fderiv_apply ℝ _)).add ((hu 2).fderiv_apply ℝ _)
  have hs : HasCompactSupport (fun x => m x*(dd (u i) (basis j) x+dd (u j) (basis i) x)) :=
    ((hu i).fderiv_apply ℝ _ |>.add ((hu j).fderiv_apply ℝ _)).mul_left
  change HasCompactSupport (fun x => (if i=j then l x*divergence basis u x else 0)+
    m x*(dd (u i) (basis j) x+dd (u j) (basis i) x))
  by_cases hij : i=j
  · simp only [hij,ite_true]
    have hl : HasCompactSupport (fun x => l x*divergence basis u x) := hd.mul_left
    convert hl.add hs using 1
    all_goals try with_reducible_and_instances rfl
    subst i
    rfl
  · simpa only [hij,ite_false,zero_add] using hs

lemma project_mul (w : ℂ →L[ℝ] ℝ) (c : ℝ) (z : ℂ) : w ((c:ℂ)*z)=c*w z := by
  rw [← Complex.real_smul,map_smul,smul_eq_mul]

lemma realStress_eq (w : ℂ →L[ℝ] ℝ) (l m : X → ℝ) (u : I → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i j : I) (x : X) :
    realStress w l m u i j x=
      (if i=j then l x*(∑ k, coordDeriv (realField w u) k x k) else 0)+
        m x*(coordDeriv (realField w u) j x i+coordDeriv (realField w u) i x j) := by
  simp only [realStress,stress,map_add,project_mul,divergence,
    realField_derivative w u hu]
  by_cases hij : i=j <;> simp only [hij,ite_true,ite_false,map_zero,project_mul,map_sum]
  all_goals rfl

lemma smooth_realStress (w : ℂ →L[ℝ] ℝ) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i j : I) :
    ContDiff ℝ (⊤ : ℕ∞) (realStress w l m u i j) :=
  w.contDiff.comp (smooth_stress (Complex.ofRealCLM.contDiff.comp hl)
    (Complex.ofRealCLM.contDiff.comp hm) u hu i j)

lemma compact_realStress (w : ℂ →L[ℝ] ℝ) (l m : X → ℝ) (u : I → X → ℂ)
    (hu : ∀ j, HasCompactSupport (u j)) (i j : I) :
    HasCompactSupport (realStress w l m u i j) :=
  (compact_stress _ _ u hu i j).comp_left (g := w) (map_zero w)

lemma derivative_project {f : X → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : ℂ →L[ℝ] ℝ) (v x : X) :
    fderiv ℝ (fun z => w (f z)) x v=w (dd f v x) := by
  rw [show (fun z => w (f z))=w ∘ f from rfl,
    (w.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv]
  rfl

lemma realStress_divergence (w : ℂ →L[ℝ] ℝ) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (x : X) :
    (∑ j, fderiv ℝ (realStress w l m u i j) x (coordVector j))=
      w (force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i x) := by
  have hlc := Complex.ofRealCLM.contDiff.comp hl
  have hmc := Complex.ofRealCLM.contDiff.comp hm
  have he (j : I) : fderiv ℝ (realStress w l m u i j) x (coordVector j)=
      w (dd (stress basis (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i j) (basis j) x) :=
    derivative_project (smooth_stress hlc hmc u hu i j) w _ x
  simp only [he]
  rw [← map_sum]
  exact congrArg w (stress_divergence basis hlc hmc u hu i x)

end ElasticityBoundaryProjectedStress
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryResidualMass
open Elasticity ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule

lemma projected_force_mass_le {Ω : Set X} (w : ℂ →L[ℝ] ℝ) {F : X → ℂ}
    (hF : MemLp F 2 (volume.restrict Ω)) :
    (∫ x in Ω, ‖w (F x)‖^2)≤‖w‖^2*(∫ x in Ω, ‖F x‖^2) := by
  have hInt := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hwF : MemLp (fun x => w (F x)) 2 (volume.restrict Ω) := hF.continuousLinearMap_comp w
  rw [← integral_const_mul]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hwF.aestronglyMeasurable).mp hwF)
    (hInt.const_mul _)
  intro x
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (w.le_opNorm (F x)) 2

/-- Each real projection is an actual finite-energy smooth trial and its
physical variational residual is controlled by the literal complex force. -/
theorem projected_trial_residual {Ω : Set X} (w : ℂ →L[ℝ] ℝ) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hbl : BoundedCoefficient Ω l) (hbm : BoundedCoefficient Ω m)
    (hB : Bornology.IsBounded Ω)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hcu : ∀ j, HasCompactSupport (u j))
    (hf : MemLp (realField w u) 2 (volume.restrict Ω))
    (hdf : ∀ j, MemLp (coordDeriv (realField w u) j) 2 (volume.restrict Ω))
    (hF : ∀ i, MemLp (force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i) 2 (volume.restrict Ω)) :
    ‖physicalResidual hbl hbm (smoothTrial (realField w u) (smooth_realField w u hu) hf hdf)‖^2≤
      3*‖w‖^2*∑ i, (∫ x in Ω, ‖force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i x‖^2) := by
  have hs := smooth_realStress w hl hm u hu
  have hc := compact_realStress w l m u hcu
  have hd (i j : I) : MemLp (fun x => fderiv ℝ (realStress w l m u i j) x (coordVector j)) 2
      (volume.restrict Ω) :=
    (((hs i j).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hc i j).fderiv_apply ℝ _) |>.restrict _
  have hes (i j : I) : jetStress hbl hbm
      (smoothTrial (realField w u) (smooth_realField w u hu) hf hdf).val i j =ᵐ[volume.restrict Ω]
      realStress w l m u i j := by
    filter_upwards [smoothTrial_stress_ae hbl hbm (realField w u) (smooth_realField w u hu) hf hdf i j]
      with x hx
    exact hx.trans (realStress_eq w l m u hu i j x).symm
  apply (physicalResidual_sq_mass hbl hbm hB _ (realStress w l m u) hs hes hd).trans
  simp only [realStress_divergence w hl hm u hu]
  calc
    _ ≤ 3*∑ i, (‖w‖^2*(∫ x in Ω, ‖force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i x‖^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => projected_force_mass_le w (hF i))) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum,mul_assoc]

end ElasticityBoundaryResidualMass

end
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
namespace ElasticityBoundaryPacket
/-! Actual smooth compact physical fields selected from the curved boundary
parametrix, on an arbitrary honest smooth domain. -/
open Set MeasureTheory Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryCutoffLayer ElasticityBoundaryCutoffParametrix ElasticityBoundaryPacketMass
  ElasticityBoundaryGradientMass ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryStrongLayer
  ElasticityBoundaryLocalParametrix ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
  ElasticityBoundaryProfileBounds ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

lemma Setup.field_compact (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (i : I) :
    HasCompactSupport (s.field q δ i) :=
  s.image_compact.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (s.field_support q δ i) s.image_compact.isClosed)

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket
/-! The physical quasimodes are genuine elements of the H1/trace construction
used by the real DN map, with uniform norm and arbitrary dual-residual decay. -/
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule
  ElasticityBoundaryResidualMass ElasticityBoundaryTrialMass ElasticityBoundaryActualTower
  ElasticityBoundaryMVNormal ElasticityBoundaryChartOperator

variable {Ω : Set X} {x : X}

lemma smooth_force {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (u : I → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (force l m u i) := by
  have he : force l m u i=(fun z => ∑ j, dd (stress basis l m u i j) (basis j) z) :=
    funext (fun z => (stress_divergence basis hl hm u hu i z).symm)
  rw [he]
  exact ContDiff.sum (fun j _ => smooth_dd (smooth_stress hl hm u hu i j) _)

lemma compact_force (l m : X → ℂ) (u : I → X → ℂ) {K : Set X}
    (hK : IsCompact K) (hus : ∀ j, Function.support (u j)⊆K) (i : I) :
    HasCompactSupport (force l m u i) :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (force_support l m u hK.isClosed hus i) hK.isClosed)

lemma coarse_sq_bound {A t r : ℝ} (hA : 0≤A) (ht : 0≤t) (hr : 0 ≤ r)
    (h : r^2≤A*t^2) : r≤(A+1)*t := by
  apply (sq_le_sq₀ hr (mul_nonneg (by positivity) ht)).mp
  have hC : A≤(A+1)^2 := by nlinarith [sq_nonneg A]
  calc
    _ ≤ A*t^2 := h
    _ ≤ (A+1)^2*t^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg t)
    _ = _ := (mul_pow _ _ _).symm

lemma Setup.trial_residual_oai (s : Setup Ω x) (hB : Bornology.IsBounded Ω)
    {l m : X → ℝ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hbl : BoundedCoefficient Ω l) (hbm : BoundedCoefficient Ω m)
    (q : Polynomial W) (N : ℕ) {C : ℝ} (hC : 0≤C)
    (hforce : ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i,
      (∫ z in Ω, ‖force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) (s.field q δ) i z‖^2)≤C*δ^(2*N)) :
    ∃ A : ℝ, 0≤A ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      complexResidualSize hbl hbm (s.trial q δ)≤A*δ^N := by
  have hb (w : ℂ →L[ℝ] ℝ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
      ‖physicalResidual hbl hbm
        (projectedTrial w (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ))‖≤
        (9*C+1)*(‖w‖*δ^N) := by
    refine coarse_sq_bound (A := 9*C) (t := ‖w‖*δ^N) (mul_nonneg (by norm_num) hC) (mul_nonneg (norm_nonneg _) (pow_nonneg hδ.le _))
      (norm_nonneg (physicalResidual hbl hbm
        (projectedTrial w (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ)))) ?_
    have hu := s.field_smooth q δ
    have hc := s.field_compact q δ
    have hlc := Complex.ofRealCLM.contDiff.comp hl
    have hmc := Complex.ofRealCLM.contDiff.comp hm
    have hf (i) := (smooth_force hlc hmc _ hu i).continuous.memLp_of_hasCompactSupport
      (compact_force _ _ _ s.image_compact (s.field_support q δ) i) (p := (2:ℝ≥0∞)) (μ := volume) |>.restrict Ω
    apply (projected_trial_residual w hl hm hbl hbm hB _ hu hc _ _ hf).trans
    calc
      _ ≤ 3*‖w‖^2*∑ i : I, (C*δ^(2*N)) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => hforce δ hδ hδ1 i)) (by positivity)
      _ = _ := by simp only [Fin.sum_univ_three]; rw [pow_mul]; ring
  refine ⟨(9*C+1)*(‖Complex.reCLM‖+‖Complex.imCLM‖),by positivity,fun δ hδ hδ1 => ?_⟩
  apply (add_le_add (hb Complex.reCLM δ hδ hδ1) (hb Complex.imCLM δ hδ hδ1)).trans_eq
  ring

end ElasticityBoundaryPacket

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.Setup.trial_residual_oai := @OAI.ElasticityBoundaryPacket.Setup.trial_residual_oai
