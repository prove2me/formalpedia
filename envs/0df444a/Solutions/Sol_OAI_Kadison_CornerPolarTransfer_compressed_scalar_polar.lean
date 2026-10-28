-- Prove2me | solution 1 for OAI.Kadison.CornerPolarTransfer.compressed_scalar_polar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:12:04.125531+00:00
-- url     : https://prove2.me/submissions/d9810e18-9762-4bd1-a87b-59eec1b74654

import Mathlib
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

lemma norm_add (a b : A) : norm τ (a+b)≤norm τ a+norm τ b := by
  simpa only [norm,map_add] using norm_add_le (τ.toPreGNS a) (τ.toPreGNS b)

lemma norm_smul (c : ℂ) (a : A) : norm τ (c • a)=‖c‖*norm τ a := by
  simp only [norm,map_smul,_root_.norm_smul]

lemma norm_real_smul (c : ℝ) (a : A) : norm τ (c • a)=|c| *norm τ a := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),norm_smul]
  congr 1
  exact RCLike.norm_ofReal _

lemma norm_mul_left (a b : A) : norm τ (a*b)≤‖a‖*norm τ b := by
  change ‖τ.leftMulMapPreGNS a (τ.toPreGNS b)‖≤‖a‖*‖τ.toPreGNS b‖
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (LinearMap.mkContinuous_norm_le _ (_root_.norm_nonneg _) _) (_root_.norm_nonneg _))

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_star (a : A) : norm τ (star a)=norm τ a := by
  apply (sq_eq_sq₀ (norm_nonneg τ _) (norm_nonneg τ _)).mp
  rw [norm_sq,norm_sq,star_star,hτ]

include hτ in
lemma norm_mul_right (a b : A) : norm τ (a*b)≤norm τ a*‖b‖ := by
  calc
    _=norm τ (star b*star a) := by rw [←star_mul,norm_star τ hτ]
    _≤‖star b‖*norm τ (star a) := norm_mul_left τ _ _
    _=_ := by rw [_root_.norm_star,norm_star τ hτ,mul_comm]

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPolarTransfer
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

include hτ in
lemma conjugation_difference (v b y : A) (hv : ‖v‖≤1) :
    norm τ (star v*y*v) ≤ norm τ (star b*y*b)+
      (1+‖b‖)*‖y‖*norm τ (v-b) := by
  have he : star v*y*v=star b*y*b+star (v-b)*y*v+star b*y*(v-b) := by
    simp only [star_sub,sub_mul,mul_sub]
    abel
  have h1 : norm τ (star (v-b)*y*v)≤‖y‖*norm τ (v-b) := by
    calc
      _≤norm τ (star (v-b)*y)*‖v‖ := norm_mul_right τ hτ _ _
      _≤norm τ (star (v-b)*y) := mul_le_of_le_one_right (norm_nonneg τ _) hv
      _≤norm τ (star (v-b))*‖y‖ := norm_mul_right τ hτ _ _
      _=_ := by rw [norm_star τ hτ,mul_comm]
  have h2 : norm τ (star b*y*(v-b))≤‖b‖*‖y‖*norm τ (v-b) := by
    calc
      _≤‖star b*y‖*norm τ (v-b) := norm_mul_left τ _ _
      _≤(‖star b‖*‖y‖)*norm τ (v-b) :=
        mul_le_mul_of_nonneg_right (_root_.norm_mul_le _ _) (norm_nonneg τ _)
      _=_ := by rw [_root_.norm_star]
  calc
    _=norm τ (star b*y*b+star (v-b)*y*v+star b*y*(v-b)) := congrArg (norm τ) he
    _≤norm τ (star b*y*b)+norm τ (star (v-b)*y*v)+norm τ (star b*y*(v-b)) :=
      (norm_add τ (star b*y*b+star (v-b)*y*v) (star b*y*(v-b))).trans
        (add_le_add (norm_add τ (star b*y*b) (star (v-b)*y*v)) le_rfl)
    _≤norm τ (star b*y*b)+‖y‖*norm τ (v-b)+‖b‖*‖y‖*norm τ (v-b) :=
      add_le_add (add_le_add le_rfl h1) h2
    _=_ := by simp only [add_mul,one_mul,add_assoc]

include hτ in
lemma range_compression (v y : A) (hv : ‖v‖≤1) :
    norm τ ((v*star v)*y*(v*star v))≤norm τ (star v*y*v) := by
  calc
    _=norm τ (v*(star v*y*v)*star v) := by simp only [mul_assoc]
    _≤norm τ (v*(star v*y*v))*‖star v‖ := norm_mul_right τ hτ _ _
    _≤norm τ (v*(star v*y*v)) :=
      mul_le_of_le_one_right (norm_nonneg τ _) (by simpa using hv)
    _≤‖v‖*norm τ (star v*y*v) := norm_mul_left τ _ _
    _≤norm τ (star v*y*v) := mul_le_of_le_one_left (norm_nonneg τ _) hv

include hτ in
lemma compressed_scalar_polar_oai {p q v b y : A} {c : ℝ}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpy : p*y=y) (hyp : y*p=y)
    (hb : b=c • (p*q)) (hv : ‖v‖≤1) :
    norm τ ((v*star v)*y*(v*star v)) ≤ c^2*norm τ (q*y*q)+
      (1+‖b‖)*‖y‖*norm τ (v-b) := by
  have he : star b*y*b=(c*c) • (q*y*q) := by
    rw [hb]
    simp only [star_smul,star_mul,star_trivial,hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq,smul_mul_assoc,mul_smul_comm,smul_smul]
    congr 1
    rw [mul_assoc q p y,hpy,←mul_assoc,mul_assoc q y p,hyp]
  have hn : norm τ (star b*y*b)=c^2*norm τ (q*y*q) := by
    rw [he,norm_real_smul,abs_of_nonneg (mul_self_nonneg c),pow_two]
  exact (range_compression τ hτ v y hv).trans ((conjugation_difference τ hτ v b y hv).trans_eq
    (by rw [hn]))

end Estimates

end Kadison.CornerPolarTransfer

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.CornerPolarTransfer.compressed_scalar_polar_oai.{u_1} := @OAI.Kadison.CornerPolarTransfer.compressed_scalar_polar_oai.{u_1}
