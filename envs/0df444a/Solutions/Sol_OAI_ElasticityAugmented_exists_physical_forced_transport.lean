-- Prove2me | solution 1 for OAI.ElasticityAugmented.exists_physical_forced_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:02:20.391558+00:00
-- url     : https://prove2.me/submissions/574511b4-b60e-4365-a9ce-0b7b7a51a165

import Mathlib
import Definitions.Def_OAIQ6El004
import Definitions.Def_OAIQ6El005
import Theorems.Thm_OAI_ElasticityAugmented_forced_equations_at
import Theorems.Thm_OAI_ElasticityFrame_exists_constraint_transport

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
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

lemma characteristicPlane_one (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ 1=∑ r, (θ r).re • e r := by simp [characteristicPlane]
lemma characteristicPlane_I (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ Complex.I=∑ r, (θ r).im • e r := by simp [characteristicPlane]
lemma characteristicPlane_principal (e : k → E) (θ : k → ℂ) (L : E →L[ℝ] ℂ) :
    L (characteristicPlane e θ 1)+Complex.I*L (characteristicPlane e θ Complex.I)=
      ∑ r, θ r*L (e r) := by
  rw [characteristicPlane_one,characteristicPlane_I]
  simp only [map_sum,map_smul,Complex.real_smul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ((θ r).re+(θ r).im*Complex.I)*L (e r) := by ring
    _ = θ r*L (e r) := by rw [Complex.re_add_im]

end ElasticityParameter
namespace ElasticityFrame
open Set Complex Module
open scoped BigOperators

lemma connection_vector (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (t : ℂ) (q : Fin 3 → ℂ) (v : Fiber θ) (i : Fin 3) :
    ((connection θ hθ t q v : Fiber θ) : Amp).1 i=θ i*(v : Amp).2 := by
  simp [connection,scalarPr,vectorPr,nullVector,scalarVector,Fin.sum_univ_three,mul_comm]
lemma connection_scalar (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (t : ℂ) (q : Fin 3 → ℂ) (v : Fiber θ) :
    ((connection θ hθ t q v : Fiber θ) : Amp).2=t*(v : Amp).2+∑ i,q i*(v : Amp).1 i := by
  simp [connection,scalarPr,vectorPr,nullVector,scalarVector,Fin.sum_univ_three]

end ElasticityFrame
namespace ElasticityAugmented
open scoped BigOperators

lemma smoothInv_apply (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) (x : X) :
    (smoothInv f hf : X → ℂ) x=((f : X → ℂ) x)⁻¹ := rfl

lemma change_inverseP (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (p : Fin 3 → Smooth) :
    changeP r (inverseP r hr p)=p := by
  funext i
  apply Subtype.ext
  funext x
  change (r : X → ℂ) x*(((r : X → ℂ) x)⁻¹*(p i : X → ℂ) x)=(p i : X → ℂ) x
  rw [← mul_assoc,mul_inv_cancel₀ (hr x),one_mul]
lemma change_inverseS (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (p : Fin 3 → Smooth) (s : Smooth) :
    changeS k r hr (inverseP r hr p) (inverseS k r hr hk p s)=s := by
  simp only [changeS,change_inverseP]
  apply Subtype.ext
  funext x
  simp only [inverseS,Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_neg,Subalgebra.coe_smul,
    Pi.add_apply,Pi.mul_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,smoothInv_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  field_simp [hr x,hk x]
  ring
end ElasticityAugmented
namespace ElasticityFrame
open scoped BigOperators
open ElasticityAugmented

lemma projection_direction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F →L[ℂ] ℂ) (u : X → F) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (θ : Fin 3 → ℂ) (x : X) :
    (direction (A := Smooth) coord θ (smoothProjection L u hu) : X → ℂ) x=
      L (fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)) := by
  have hd (v : X) :
      fderiv ℝ (smoothProjection L u hu : X → ℂ) x v=L (fderiv ℝ u x v) := by
    exact congrArg (fun M : X →L[ℝ] ℂ => M v)
      (((L.restrictScalars ℝ).hasFDerivAt.comp x
        ((hu.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have he := ElasticityParameter.characteristicPlane_principal
    ElasticityParameter.basis θ (fderiv ℝ (smoothProjection L u hu : X → ℂ) x)
  have hb : ElasticityParameter.basis=ElasticityAugmented.e := rfl
  rw [hd,hd] at he
  rw [map_add,map_smul,smul_eq_mul,he]
  simp only [direction,Fin.sum_univ_three,Subalgebra.coe_add,Subalgebra.coe_smul,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,coord_apply,hb]

lemma smooth_normal (θ : Fin 3 → ℂ) (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ElasticityAugmented.normal θ (vectorSmooth θ u hu)=0 := by
  apply Subtype.ext
  funext x
  have h := (u x).property
  change (∑ i,θ i*((u x : Fiber θ) : Amp).1 i)=0 at h
  simp only [ElasticityAugmented.normal,Fin.sum_univ_three,Subalgebra.coe_add,
    Subalgebra.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change θ 0*((u x : Fiber θ) : Amp).1 0+θ 1*((u x : Fiber θ) : Amp).1 1+
    θ 2*((u x : Fiber θ) : Amp).1 2=0
  simpa only [Fin.sum_univ_three] using h

end ElasticityFrame

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_ForcedTransport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
lemma exists_normalizing_vector (θ : Fin 3 → ℂ) (hθ : θ≠0) : ∃ n : Fin 3 → ℂ,∑ i,θ i*n i=1 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hθ
  change θ i≠0 at hi
  refine ⟨Pi.single i (θ i)⁻¹,?_⟩
  simp [Pi.single_apply,hi]

end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityFrame
open ElasticityAugmented

lemma tangentProjection_apply (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1) (v : Amp) :
    ((tangentProjection θ n hn v : Fiber θ) : Amp)=v-normal θ v • (n,0) := rfl
lemma tangentProjection_of_normal (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1)
    (v : Amp) (hv : normal θ v=0) :
    ((tangentProjection θ n hn v : Fiber θ) : Amp)=v := by
  rw [tangentProjection_apply,hv,zero_smul,sub_zero]
lemma tangentProjection_smooth (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1)
    (p : Fin 3 → Smooth) (s : Smooth) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => tangentProjection θ n hn
      ((fun i => (p i : X → ℂ) x),(s : X → ℂ) x)) := by
  exact ((tangentProjection θ n hn).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
    (((contDiff_pi.mpr (fun i => smooth_coe (p i))).prodMk (smooth_coe s)))

lemma smooth_vector_forced (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (t : Smooth) (qq : Fin 3 → Smooth)
    (f : Fiber θ) (x : X)
    (he : fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)=
        connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)+f) :
    ∀ i,(direction (A := Smooth) coord θ (vectorSmooth θ u hu i) : X → ℂ) x=
      θ i*(scalarSmooth θ u hu : X → ℂ) x+(f : Amp).1 i := by
  intro i
  rw [vectorSmooth,projection_direction,he,map_add]
  exact congrArg (fun z : ℂ => z+(f : Amp).1 i)
    (connection_vector θ hθ ((t : X → ℂ) x) (fun j => (qq j : X → ℂ) x) (u x) i)
lemma smooth_scalar_forced (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (t : Smooth) (qq : Fin 3 → Smooth)
    (f : Fiber θ) (x : X)
    (he : fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)=
        connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)+f) :
    (direction (A := Smooth) coord θ (scalarSmooth θ u hu) : X → ℂ) x=
      ((t*scalarSmooth θ u hu+∑ i,qq i*vectorSmooth θ u hu i : Smooth) : X → ℂ) x+(f : Amp).2 := by
  rw [scalarSmooth,projection_direction,he,map_add]
  apply congrArg (fun z : ℂ => z+(f : Amp).2)
  have h := connection_scalar θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)
  simp only [Fin.sum_univ_three,Subalgebra.coe_add,Subalgebra.coe_mul,Pi.add_apply,Pi.mul_apply]
  change ((connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x) : Fiber θ) : Amp).2=
    (t : X → ℂ) x*((u x : Fiber θ) : Amp).2+
      ((qq 0 : X → ℂ) x*((u x : Fiber θ) : Amp).1 0+
      (qq 1 : X → ℂ) x*((u x : Fiber θ) : Amp).1 1+
      (qq 2 : X → ℂ) x*((u x : Fiber θ) : Amp).1 2)
  simpa only [Fin.sum_univ_three] using h
end ElasticityFrame

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma normal_inverseP (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0)
    (p : Fin 3 → Smooth) : normal θ (inverseP r hr p)=smoothInv r hr*normal θ p := by
  simp only [normal,inverseP,Finset.mul_sum,Algebra.smul_def]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma normal_topSource (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0)
    (H : Fin 3 → Smooth) : normal θ (topSource r hr H)=(1/2 : ℂ) • (smoothInv r hr*normal θ H) := by
  simp only [normal,topSource,Algebra.smul_def,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Smooth physical leading equations with arbitrary tangent vector forcing.
Solvability is proved from actual planar transport, not assumed. Forcing need
only be tangent on the compact region on which the equations are requested. -/
theorem exists_physical_forced_transport_oai (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (H : Fin 3 → Smooth) (K : Smooth) {C : Set X} (hC : IsCompact C)
    (hH : ∀ x∈C,((normal θ H : Smooth) : X → ℂ) x=0) :
    ∃ a : Fin 3 → Smooth, ∃ b : Smooth, normal θ a=0 ∧
      ∀ x∈C, (∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x) ∧
        ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=(K : X → ℂ) x := by
  obtain ⟨n,hn⟩ := exists_normalizing_vector θ hne
  let Fp := topSource r hr H
  let Fs := scalarSource k r hr hl H K
  let f : X → ElasticityFrame.Fiber θ := fun x => ElasticityFrame.tangentProjection θ n hn
    ((fun i => (Fp i : X → ℂ) x),(Fs : X → ℂ) x)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := ElasticityFrame.tangentProjection_smooth θ n hn Fp Fs
  let t := transportT θ k r hk hl
  let q := transportQ θ k r hr hk hl
  obtain ⟨u,hu,he⟩ := ElasticityFrame.exists_constraint_transport θ hθ hne
    (t : X → ℂ) (fun i => (q i : X → ℂ)) (smooth_coe t) (fun i => smooth_coe (q i)) f hf hC
  let p := ElasticityFrame.vectorSmooth θ u hu
  let s := ElasticityFrame.scalarSmooth θ u hu
  let a := inverseP r hr p
  let b := inverseS k r hr hk p s
  refine ⟨a,b,?_,?_⟩
  · rw [show a=inverseP r hr p from rfl,normal_inverseP,
      ElasticityFrame.smooth_normal θ u hu,mul_zero]
  · intro x hx
    have hF : ((f x : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (Fp i : X → ℂ) x),(Fs : X → ℂ) x) := by
      apply ElasticityFrame.tangentProjection_of_normal θ n hn
      have h := congrArg (fun v : Smooth => (v : X → ℂ) x) (normal_topSource θ r hr H)
      change ElasticityFrame.normal θ ((fun i => (Fp i : X → ℂ) x),(Fs : X → ℂ) x)=
        (1/2 : ℂ)*(((r : X → ℂ) x)⁻¹*((normal θ H : Smooth) : X → ℂ) x) at h
      rw [h,hH x hx,mul_zero,mul_zero]
    have hp := ElasticityFrame.smooth_vector_forced θ hθ u hu t q (f x) x (he x hx)
    have hs := ElasticityFrame.smooth_scalar_forced θ hθ u hu t q (f x) x (he x hx)
    rw [hF] at hp hs
    apply forced_equations_at θ k r hr hk hl H K a b x
    · change ∀ i,(direction (A := Smooth) coord θ (changeP r (inverseP r hr p) i) : X → ℂ) x=
        θ i*(changeS k r hr (inverseP r hr p) (inverseS k r hr hk p s) : X → ℂ) x+_
      rw [change_inverseP,change_inverseS]
      exact hp
    · change (direction (A := Smooth) coord θ
        (changeS k r hr (inverseP r hr p) (inverseS k r hr hk p s)) : X → ℂ) x=_
      rw [change_inverseS,change_inverseP]
      exact hs
end ElasticityAugmented

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityAugmented.exists_physical_forced_transport_oai := @OAI.ElasticityAugmented.exists_physical_forced_transport_oai
