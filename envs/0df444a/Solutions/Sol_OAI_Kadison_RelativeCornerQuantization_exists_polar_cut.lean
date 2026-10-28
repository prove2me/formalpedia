-- Prove2me | solution 1 for OAI.Kadison.RelativeCornerQuantization.exists_polar_cut
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:31:37.313479+00:00
-- url     : https://prove2.me/submissions/ffeb3d16-491f-4379-927b-ad62ce8d3dd0

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C035
import Theorems.Thm_OAI_Kadison_CornerPolarTransfer_compressed_scalar_polar
import Theorems.Thm_OAI_Kadison_CornerPolarTransfer_defect_bound

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPolarAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.CornerPolarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma kernel_defect_le {q r a : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (ha : 0≤a) (hra : r*a=a) (haq : a*q=a) :
    q-r ≤ star (q-a*a)*(q-a*a) := by
  have has := (IsSelfAdjoint.of_nonneg ha).star_eq
  have har : a*r=a := by
    simpa only [star_mul,has,hr.isSelfAdjoint.star_eq] using congrArg star hra
  have hqa : q*a=a := by
    simpa only [star_mul,has,hq.isSelfAdjoint.star_eq] using congrArg star haq
  have he : star (q-a*a)*(q-a*a)-(q-r)=star (r-a*a)*(r-a*a) := by
    simp only [star_sub,star_mul,has,hq.isSelfAdjoint.star_eq,hr.isSelfAdjoint.star_eq]
    have hqaa : q*(a*a)=a*a := by rw [←mul_assoc,hqa]
    have hraa : r*(a*a)=a*a := by rw [←mul_assoc,hra]
    noncomm_ring [hq.isIdempotentElem.eq,hr.isIdempotentElem.eq,hqa,haq,hra,har,hqaa,hraa]
  exact sub_nonneg.mp (he.symm ▸ star_mul_self_nonneg (r-a*a))

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_partial_isometry_le {r v : A} (hr : IsStarProjection r)
    (hv : star v*v=r) : ‖v‖≤1 := by
  have hnorm : ‖star v*v‖=‖v‖*‖v‖ := CStarRing.norm_star_mul_self
  rw [hv] at hnorm
  have hrnorm := hr.norm_le r
  nlinarith [norm_nonneg v]

end Kadison.CornerPolarAlgebra

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma norm_nonneg (a : A) : 0≤norm τ a := _root_.norm_nonneg _

lemma norm_sq (a : A) : norm τ a^2=(τ (star a*a)).re := by
  rw [norm,InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
  rfl

lemma norm_smul (c : ℂ) (a : A) : norm τ (c • a)=‖c‖*norm τ a := by
  simp only [norm,map_smul,_root_.norm_smul]

lemma norm_real_smul (c : ℝ) (a : A) : norm τ (c • a)=|c| *norm τ a := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),norm_smul]
  congr 1
  exact RCLike.norm_ofReal _

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPolarTransfer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.CornerPolarTransfer

open TracialL2

section Estimates

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

lemma trace_kernel_bound {q r a : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (ha : 0≤a) (hra : r*a=a) (haq : a*q=a) :
    (τ q).re-(τ r).re≤norm τ (q-a*a)^2 := by
  have h := (τ.monotone (CornerPolarAlgebra.kernel_defect_le hq hr ha hra haq)).1
  change (τ (q-r)).re≤(τ (star (q-a*a)*(q-a*a))).re at h
  simpa only [map_sub,Complex.sub_re,←norm_sq] using h

omit [PartialOrder A] [StarOrderedRing A] in
lemma scaled_projection_defect {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) {c t : ℝ} (hct : c*c*t=1) :
    q-star (c • (p*q))*(c • (p*q))=(-c*c) • (q*(p-t • (1:A))*q) := by
  have hpc : star (p*q)*(p*q)=q*p*q := by
    simp only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq]
    rw [mul_assoc q p,←mul_assoc p p q,hp.isIdempotentElem.eq,←mul_assoc]
  have hcen : q*(p-t • (1:A))*q=q*p*q-t • q := by
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,
      hq.isIdempotentElem.eq]
  have hct' : (-c*c)*t=-1 := by nlinarith only [hct]
  rw [hcen,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,smul_smul,hpc,
    smul_sub,smul_smul,hct',neg_one_smul,sub_neg_eq_add,neg_mul,neg_smul,add_comm]
  exact sub_eq_add_neg _ _

lemma norm_scaled_projection_defect {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) {c t : ℝ} (hct : c*c*t=1) :
    norm τ (q-star (c • (p*q))*(c • (p*q)))=
      c^2*norm τ (q*(p-t • (1:A))*q) := by
  rw [scaled_projection_defect hp hq hct,norm_real_smul,
    neg_mul,abs_neg,abs_of_nonneg (mul_self_nonneg c),pow_two]

end Estimates

section Represented

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma abs_coe (b : M) : CFC.abs (b : H →L[ℂ] H)=(CFC.abs b : M) := by
  apply CFC.sqrt_unique
  · exact congrArg (fun x : M => (x : H →L[ℂ] H)) (CFC.abs_mul_abs b)
  · exact CFC.abs_nonneg b

lemma projection_of_coe {p : M} (hp : IsStarProjection (p : H →L[ℂ] H)) :
    IsStarProjection p := by
  exact ⟨Subtype.ext hp.isIdempotentElem.eq,Subtype.ext hp.isSelfAdjoint.star_eq⟩

theorem exists_polar_data (b : M) :
    ∃ v : M, v*CFC.abs b=b ∧
      IsStarProjection (star v*v) ∧ IsStarProjection (v*star v) ∧
      (star v*v)*CFC.abs b=CFC.abs b ∧
      ‖v‖≤1 ∧ (∀ (N : VonNeumannAlgebra H), (b : H →L[ℂ] H)∈N → (v : H →L[ℂ] H)∈N) ∧
      (∀ e : M, IsStarProjection e → e*b=b → v*star v≤e) ∧
      (∀ e : M, IsStarProjection e → b*e=b → star v*v≤e) := by
  let v : M := ⟨Polar.partialIsometry (b : H →L[ℂ] H),
    Polar.partialIsometry_mem_vonNeumann M b.property⟩
  have hi : ((star v*v : M) : H →L[ℂ] H)=Polar.rightSupport (b : H →L[ℂ] H) :=
    Polar.partialIsometry_initial _
  have hp : IsStarProjection (star v*v) := projection_of_coe M
    (hi.symm ▸ Polar.isProjection_rightSupport _)
  refine ⟨v,?_,hp,projection_of_coe M (Polar.isProjection_leftSupport _),?_,
    CornerPolarAlgebra.norm_partial_isometry_le hp rfl,?_,?_,?_⟩
  · apply Subtype.ext
    change Polar.partialIsometry _*((CFC.abs b : M) : H →L[ℂ] H)=_
    rw [←abs_coe M,Polar.factorization]
  · apply Subtype.ext
    change ((star v*v : M) : H →L[ℂ] H)*((CFC.abs b : M) : H →L[ℂ] H)=_
    rw [hi,←abs_coe M,Polar.initial_mul_abs]
  · intro N hb
    exact Polar.partialIsometry_mem_vonNeumann N hb
  · intro e he heb
    change Polar.leftSupport (b : H →L[ℂ] H)≤(e : H →L[ℂ] H)
    exact Polar.leftSupport_le _ _ (he.map M.toStarSubalgebra.subtype)
      (congrArg (fun x : M => (x : H →L[ℂ] H)) heb)
  · intro e he hbe
    change ((star v*v : M) : H →L[ℂ] H)≤(e : H →L[ℂ] H)
    rw [hi]
    exact Polar.rightSupport_le _ _ (he.map M.toStarSubalgebra.subtype)
      (congrArg (fun x : M => (x : H →L[ℂ] H)) hbe)

end Represented

end Kadison.CornerPolarTransfer

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeCornerQuantization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.RelativeCornerQuantization

open TracialL2 CornerPolarTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ in
theorem exists_polar_cut_oai (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
    {c t : ℝ} (hc : 0 ≤ c) (hct : c*c*t=1) :
    ∃ f : M, IsStarProjection f ∧ f ≤ p ∧ (τ f).re ≤ (τ q).re ∧
      (τ q).re-(τ f).re ≤ (c^2*norm τ (q*(p-t • (1:M))*q))^2 ∧
      (∀ y : M, p*y=y → y*p=y → norm τ (f*y*f) ≤ 
        c^2*norm τ (q*y*q)+(1+c)*‖y‖*c^2*norm τ (q*(p-t • (1:M))*q)) ∧
      (∀ N : VonNeumannAlgebra H, (p : H →L[ℂ] H)∈N → (q : H →L[ℂ] H)∈N →
        (f : H →L[ℂ] H)∈N) := by
  let b : M := c • (p*q)
  have hpb : p*b=b := by dsimp [b]; rw [mul_smul_comm,←mul_assoc,hp.isIdempotentElem.eq]
  have hbq : b*q=b := by dsimp [b]; rw [smul_mul_assoc,mul_assoc,hq.isIdempotentElem.eq]
  obtain ⟨v,hva,hr,hf,hra,hvn,hvN,hleft,hright⟩ := exists_polar_data M b
  have hrq : star v*v ≤ q := hright q hq hbq
  have haq : CFC.abs b*q=CFC.abs b := by
    apply Subtype.ext
    change ((CFC.abs b : M) : H →L[ℂ] H)*(q : H →L[ℂ] H)=((CFC.abs b : M) : H →L[ℂ] H)
    rw [←abs_coe M]
    exact Polar.abs_mul_of_mul _ _ (congrArg (fun a : M => (a : H →L[ℂ] H)) hbq)
  have hdef : norm τ (v-b) ≤ c^2*norm τ (q*(p-t • (1:M))*q) := by
    have h := defect_bound τ hq hr hrq (CFC.abs_nonneg b) hra haq rfl
    rw [hva,CFC.abs_mul_abs] at h
    exact h.trans_eq (norm_scaled_projection_defect τ hp hq hct)
  have hker : (τ q).re-(τ (star v*v)).re ≤ (c^2*norm τ (q*(p-t • (1:M))*q))^2 := by
    have h := trace_kernel_bound τ hq hr (CFC.abs_nonneg b) hra haq
    rw [CFC.abs_mul_abs,norm_scaled_projection_defect τ hp hq hct] at h
    exact h
  have htr : τ (star v*v)=τ (v*star v) := hτ _ _
  have hbn : ‖b‖ ≤ c := by
    dsimp [b]
    rw [_root_.norm_smul,Real.norm_of_nonneg hc]
    have hpqn : ‖p*q‖ ≤ 1 := (_root_.norm_mul_le _ _).trans
      ((mul_le_mul (hp.norm_le p) (hq.norm_le q) (_root_.norm_nonneg _) (by norm_num)).trans_eq
        (one_mul (1:ℝ)))
    exact mul_le_of_le_one_right hc hpqn
  refine ⟨v*star v,hf,hleft p hp hpb,?_,by simpa only [htr] using hker,?_,?_⟩
  · have h := (τ.monotone hrq).1
    change (τ (star v*v)).re ≤ (τ q).re at h
    simpa only [htr] using h
  · intro y hpy hyp
    calc
      _ ≤ c^2*norm τ (q*y*q)+(1+‖b‖)*‖y‖*norm τ (v-b) :=
        compressed_scalar_polar τ hτ hp hq hpy hyp rfl hvn
      _ ≤ c^2*norm τ (q*y*q)+(1+c)*‖y‖*(c^2*norm τ (q*(p-t • (1:M))*q)) := by
        apply add_le_add le_rfl
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (add_le_add le_rfl hbn) (_root_.norm_nonneg y))
          hdef (norm_nonneg τ _) (mul_nonneg (by positivity) (_root_.norm_nonneg y))
      _=_ := by rw [mul_assoc ((1+c)*‖y‖)]
  · intro N hpN hqN
    have hbN : (b : H →L[ℂ] H)∈N := by
      change ((c:ℂ) • ((p : H →L[ℂ] H)*(q : H →L[ℂ] H)))∈N
      exact N.toStarSubalgebra.smul_mem (N.mul_mem hpN hqN) _
    exact N.mul_mem (hvN N hbN) (N.star_mem' (hvN N hbN))

end Kadison.RelativeCornerQuantization

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.RelativeCornerQuantization.exists_polar_cut_oai.{u_1} := @OAI.Kadison.RelativeCornerQuantization.exists_polar_cut_oai.{u_1}
