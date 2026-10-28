-- Prove2me | solution 1 for OAI.ElasticityAugmented.forced_equations_at
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:04:15.27036+00:00
-- url     : https://prove2.me/submissions/37f7c344-6ec7-43b8-ad2e-a5b940cf84ce

import Mathlib
import Definitions.Def_OAIQ6El004

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented
open scoped BigOperators

lemma smoothInv_apply (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) (x : X) :
    (smoothInv f hf : X → ℂ) x=((f : X → ℂ) x)⁻¹ := rfl
lemma smoothInv_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) : smoothInv f hf*f=1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)
lemma thetaDerivation_apply (θ : Fin 3 → ℂ) (f : Smooth) :
    thetaDerivation θ f=direction (A := Smooth) coord θ f := by
  simp [thetaDerivation,direction,Fin.sum_univ_three]
lemma direction_mul (θ : Fin 3 → ℂ) (f g : Smooth) :
    direction (A := Smooth) coord θ (f*g)=direction (A := Smooth) coord θ f*g+f*direction (A := Smooth) coord θ g := by
  simpa only [thetaDerivation_apply,smul_eq_mul,mul_comm,add_comm] using (thetaDerivation θ).leibniz f g
lemma direction_add (θ : Fin 3 → ℂ) (f g : Smooth) :
    direction (A := Smooth) coord θ (f+g)=direction (A := Smooth) coord θ f+direction (A := Smooth) coord θ g := by
  exact (thetaDerivation θ).map_add f g
lemma direction_smul (θ : Fin 3 → ℂ) (c : ℂ) (f : Smooth) :
    direction (A := Smooth) coord θ (c • f)=c • direction (A := Smooth) coord θ f := by
  exact (thetaDerivation θ).map_smul c f

lemma direction_inv (θ : Fin 3 → ℂ) (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) :
    direction (A := Smooth) coord θ (smoothInv f hf)=
      -(smoothInv f hf)^2*direction (A := Smooth) coord θ f := by
  simpa only [thetaDerivation_apply,smul_eq_mul] using
    (thetaDerivation θ).leibniz_of_mul_eq_one (smoothInv_mul f hf)
lemma gradient_square (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) (i : Fin 3) :
    coord i (r*r)=r*r*logarithmicGrad r hr i := by
  apply Subtype.ext
  funext x
  simp only [Derivation.leibniz,smul_eq_mul,logarithmicGrad,Subalgebra.coe_add,Subalgebra.coe_mul,
    Pi.add_apply,Pi.mul_apply,smoothInv_apply]
  change (r : X → ℂ) x*(coord i r : X → ℂ) x+(r : X → ℂ) x*(coord i r : X → ℂ) x=
    (r : X → ℂ) x*(r : X → ℂ) x*(2*((r : X → ℂ) x)⁻¹*(coord i r : X → ℂ) x)
  field_simp [hr x]
  ring
lemma transformed_gradient (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0)
    (a : Fin 3 → Smooth) (i : Fin 3) :
    2*coord i (r*r)*direction (A := Smooth) coord θ (a i)+
      direction (A := Smooth) coord θ (coord i (r*r))*a i =
      r*(2*logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i)+
        direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i) := by
  rw [gradient_square r hr i]
  simp only [direction_mul,changeP]
  ring

lemma thetaGamma_eq (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) :
    thetaGamma θ r hr=2*smoothInv r hr*direction (A := Smooth) coord θ r := by
  simp only [thetaGamma,logarithmicGrad,direction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Algebra.smul_def]
  ring

lemma direction_sum (θ : Fin 3 → ℂ) (f : Fin 3 → Smooth) :
    direction (A := Smooth) coord θ (∑ i,f i)=∑ i,direction (A := Smooth) coord θ (f i) := by
  exact map_sum (thetaDerivation θ).toLinearMap f Finset.univ
lemma transportT_eq (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    transportT θ k r hk hl=r*r*smoothInv (k+r*r) hl*
      (smoothInv k hk*direction (A := Smooth) coord θ k-thetaGamma θ r hr) := by
  apply Subtype.ext
  funext x
  simp only [transportT,thetaGamma_eq,direction_add,direction_mul,
    Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,smoothInv_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  have hh : (k : X → ℂ) x+(r : X → ℂ) x*(r : X → ℂ) x≠0 := hl x
  have hp : (k : X → ℂ) x+(r : X → ℂ) x^2≠0 := by simpa only [pow_two] using hh
  field_simp [hr x,hk x,hh,hp]
  ring
lemma transportQ_contract (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (p : Fin 3 → Smooth) :
    (∑ i,transportQ θ k r hr hk hl i*p i)=
      (1/2 : ℂ) • ((r*r*smoothInv (k+r*r) hl*smoothInv k hk*direction (A := Smooth) coord θ k-
        (1/2 : ℂ) • thetaGamma θ r hr)*(∑ i,logarithmicGrad r hr i*p i)-
        r*r*smoothInv (k+r*r) hl*(∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*p i)) := by
  simp only [transportQ,Fin.sum_univ_three,Algebra.smul_def]
  ring

/-- Exact intertwining of the vector leading equation, including nonzero source. -/
lemma leadingR_change (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    leadingR coord θ (k-r*r) (r*r) a b i=
      2*r*(direction (A := Smooth) coord θ (changeP r a i)-θ i • changeS k r hr a b) := by
  have hg : (∑ j,coord j (r*r)*a j : Smooth)=r*(∑ j,logarithmicGrad r hr j*changeP r a j) := by
    simp_rw [gradient_square r hr]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [changeP]
    ring
  simp only [leadingR,sub_add_cancel,hg,changeP,direction_mul,changeS]
  apply Subtype.ext
  funext x
  simp only [Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_smul,
    Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,smoothInv_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  field_simp [hr x]
  ring

end ElasticityAugmented

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

lemma scalar_residual_algebra (r k R K b db H J s : ℂ) (hr : r≠0) (hk : k≠0)
    (hl : k+r*r≠0) (hB : 2*r*s+k*b+r*H=0) :
    -(1/2 : ℂ)*((K/r-k*R/r^2)*b+k/r*db+J+(2*R/r)*s)-
      ((r*r/(k+r*r))*(K/k-2*R/r)*s+
        (1/2 : ℂ)*(((r*r/(k+r*r))*(K/k)-(2*R/r)/2)*H-(r*r/(k+r*r))*J))=
      (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*(2*R/r)*s+J)) := by
  calc
    _ = (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*(2*R/r)*s+J))+
        (R/(2*r^2)-r*K/(2*k*(k+r*r)))*(2*r*s+k*b+r*H) := by
      have hp : k+r^2≠0 := by simpa only [pow_two] using hl
      field_simp [hr,hk,hl,hp]
      ring
    _ = _ := by rw [hB]; ring

end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma changeS_derivative_raw (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    direction (A := Smooth) coord θ (changeS k r hr a b)=
      -(1/2 : ℂ) • ((direction (A := Smooth) coord θ k*smoothInv r hr-
        k*(smoothInv r hr)^2*direction (A := Smooth) coord θ r)*b+
        k*smoothInv r hr*direction (A := Smooth) coord θ b+
        (∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)+
          ∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i)) := by
  conv_lhs => rw [changeS,direction_smul,direction_add]
  simp only [direction_sum,direction_mul,direction_inv,Finset.sum_add_distrib]
  congr 1
  ring

lemma transformed_scalar_raw (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    leadingS coord θ (k-r*r) (r*r) a b=
      2*((k+r*r)*direction (A := Smooth) coord θ b+direction (A := Smooth) coord θ k*b+
        r*(2*(∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i))+
          ∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)) := by
  have ht : (∑ i, (2*coord i (r*r)*direction (A := Smooth) coord θ (a i)+
      direction (A := Smooth) coord θ (coord i (r*r))*a i) : Smooth)=
      r*(2*(∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i))+
        ∑ i, direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i) := by
    simp_rw [transformed_gradient θ r hr a]
    rw [← Finset.mul_sum,Finset.sum_add_distrib]
    simp only [Finset.mul_sum,mul_assoc]
  rw [← ht]
  simp only [leadingS,sub_add_cancel,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  ring

end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma leadingR_contract (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    (∑ i,logarithmicGrad r hr i*leadingR coord θ (k-r*r) (r*r) a b i)=
      2*r*((∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i))-
        thetaGamma θ r hr*changeS k r hr a b) := by
  simp_rw [leadingR_change θ k r hr a b]
  simp only [thetaGamma,mul_sub,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib,
    Algebra.smul_def]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma scalar_forced_residual (r k R K b db H J G s : ℂ) (hr : r≠0) (hk : k≠0)
    (hl : k+r*r≠0) (hB : 2*r*s+k*b+r*H=0) :
    -(1/2 : ℂ)*((K/r-k*R/r^2)*b+k/r*db+J+G)-
      ((r*r/(k+r*r))*(K/k-2*R/r)*s+
        (1/2 : ℂ)*(((r*r/(k+r*r))*(K/k)-(2*R/r)/2)*H-(r*r/(k+r*r))*J))=
      (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*G+J))+
        ((k-r*r)/(2*(k+r*r)))*(G-(2*R/r)*s) := by
  have ha := scalar_residual_algebra r k R K b db H J s hr hk hl hB
  calc
    _ = (-(1/2 : ℂ)*((K/r-k*R/r^2)*b+k/r*db+J+(2*R/r)*s)-
      ((r*r/(k+r*r))*(K/k-2*R/r)*s+
        (1/2 : ℂ)*(((r*r/(k+r*r))*(K/k)-(2*R/r)/2)*H-(r*r/(k+r*r))*J)))-
        (1/2 : ℂ)*(G-(2*R/r)*s) := by ring
    _ = (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*(2*R/r)*s+J))-
        (1/2 : ℂ)*(G-(2*R/r)*s) := by rw [ha]
    _ = _ := by
      have hp : k+r^2≠0 := by simpa only [pow_two] using hl
      field_simp [hr,hl,hp]
      ring

/-- Exact forced transport intertwining, with no homogeneous leading-equation
premise. This is the source term needed for the physical compatible recursion. -/
lemma normal_form_forced_residual (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    direction (A := Smooth) coord θ (changeS k r hr a b)-
      (transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i)=
      -(1/4 : ℂ) • (k*smoothInv r hr*smoothInv (k+r*r) hl*leadingS coord θ (k-r*r) (r*r) a b)+
      (1/4 : ℂ) • ((k-r*r)*smoothInv r hr*smoothInv (k+r*r) hl*
        ∑ i,logarithmicGrad r hr i*leadingR coord θ (k-r*r) (r*r) a b i) := by
  rw [changeS_derivative_raw θ k r hr a b,transportT_eq θ k r hr hk hl,
    transportQ_contract,transformed_scalar_raw θ k r hr a b,leadingR_contract]
  apply Subtype.ext
  funext x
  let R := (r : X → ℂ) x
  let K := (k : X → ℂ) x
  let DR := (direction (A := Smooth) coord θ r : X → ℂ) x
  let DK := (direction (A := Smooth) coord θ k : X → ℂ) x
  let B := (b : X → ℂ) x
  let DB := (direction (A := Smooth) coord θ b : X → ℂ) x
  let H := ((∑ i,logarithmicGrad r hr i*changeP r a i : Smooth) : X → ℂ) x
  let J := ((∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i : Smooth) : X → ℂ) x
  let G := ((∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i) : Smooth) : X → ℂ) x
  let S := (changeS k r hr a b : X → ℂ) x
  have he : S=-(1/2 : ℂ)*(K*R⁻¹*B+H) := rfl
  have hB : 2*R*S+K*B+R*H=0 := by
    rw [he]
    have hn : R≠0 := hr x
    field_simp [hn]
    ring
  have hgamma : (thetaGamma θ r hr : X → ℂ) x=2*DR/R := by
    rw [thetaGamma_eq]
    change 2*R⁻¹*DR=2*DR/R
    ring
  have ha := scalar_forced_residual R K DR DK B DB H J G S (hr x) (hk x)
    (show K+R*R≠0 from hl x) hB
  simp only [Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_pow,
    Subalgebra.coe_smul,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Pi.smul_apply,
    smul_eq_mul,smoothInv_apply,hgamma]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  change -(1/2 : ℂ)*((DK*R⁻¹-K*(R⁻¹)^2*DR)*B+K*R⁻¹*DB+J+G)-
    (R*R*(K+R*R)⁻¹*(K⁻¹*DK-2*DR/R)*S+
      (1/2 : ℂ)*((R*R*(K+R*R)⁻¹*K⁻¹*DK-(1/2 : ℂ)*(2*DR/R))*H-R*R*(K+R*R)⁻¹*J))=
    -(1/4 : ℂ)*(K*R⁻¹*(K+R*R)⁻¹*(2*((K+R*R)*DB+DK*B+R*(2*G+J))))+
    (1/4 : ℂ)*((K-R*R)*R⁻¹*(K+R*R)⁻¹*(2*R*(G-(2*DR/R)*S)))
  have hR : R≠0 := hr x
  have hL : K+R^2≠0 := by
    simpa only [pow_two] using (show K+R*R≠0 from hl x)
  convert ha using 1 <;> simp only [div_eq_mul_inv,inv_pow,mul_inv_rev] <;>
    field_simp [hR,hL]
  all_goals norm_num
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma forced_equations_at_oai (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (H : Fin 3 → Smooth) (K : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (x : X)
    (hp : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x+(topSource r hr H i : X → ℂ) x)
    (hs : (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
      ((transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x+
          (scalarSource k r hr hl H K : X → ℂ) x) :
    (∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x) ∧
      ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=(K : X → ℂ) x := by
  have hR (i) : ((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x := by
    have h := congrArg (fun f : Smooth => (f : X → ℂ) x) (leadingR_change θ k r hr a b i)
    change ((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=
      2*(r : X → ℂ) x*((direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x-
        θ i*(changeS k r hr a b : X → ℂ) x) at h
    rw [h,hp i]
    change 2*(r : X → ℂ) x*(θ i*(changeS k r hr a b : X → ℂ) x+
      (1/2 : ℂ)*(((r : X → ℂ) x)⁻¹*(H i : X → ℂ) x)-θ i*(changeS k r hr a b : X → ℂ) x)=_
    field_simp [hr x]
    ring
  refine ⟨hR,?_⟩
  have h := congrArg (fun f : Smooth => (f : X → ℂ) x)
    (normal_form_forced_residual θ k r hr hk hl a b)
  change (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x-
    ((transportT θ k r hk hl*changeS k r hr a b+
      ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x=_ at h
  rw [hs,add_sub_cancel_left] at h
  simp only [scalarSource,Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_sub,
    Subalgebra.coe_smul,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,smoothInv_apply,Fin.sum_univ_three,hR] at h
  have hc : -(1/4 : ℂ)*(k : X → ℂ) x*((r : X → ℂ) x)⁻¹*
      (((k : X → ℂ) x+(r : X → ℂ) x*(r : X → ℂ) x)⁻¹)≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hk x)) (inv_ne_zero (hr x)))
      (inv_ne_zero (hl x))
  apply (mul_left_cancel₀ hc)
  linear_combination -h
end ElasticityAugmented

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityAugmented.forced_equations_at_oai := @OAI.ElasticityAugmented.forced_equations_at_oai
