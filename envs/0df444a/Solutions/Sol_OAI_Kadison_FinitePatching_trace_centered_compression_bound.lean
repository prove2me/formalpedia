-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.trace_centered_compression_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:13:34.261236+00:00
-- url     : https://prove2.me/submissions/b9358195-2c6d-498a-a267-d8c62ee4b2a1

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

include hτ in
lemma norm_trace_mul (a b : A) : ‖τ (a*b)‖≤norm τ a*norm τ b := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (τ.toPreGNS (star a)) (τ.toPreGNS b)
  change ‖τ (star (star a)*b)‖≤norm τ (star a)*norm τ b at h
  simpa only [star_star,norm_star τ hτ] using h

lemma norm_projection_sq {p : A} (hp : IsStarProjection p) : norm τ p^2=(τ p).re := by
  rw [norm_sq,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

include hτ in
lemma trace_two_corner_letters {q a b c w z : A} (_hq : IsStarProjection q)
    (hw : w*q=w) (hz : q*z=z)
    (ha : ‖a‖≤1) (hc : ‖c‖≤1) (hwn : ‖w‖≤1) (hzn : ‖z‖≤1) :
    ‖τ (a*w*b*z*c)‖≤norm τ (q*b*q)*norm τ q := by
  have he : τ (a*w*b*z*c)=τ ((q*b*q)*(z*c*a*w)) := by
    calc
      _=τ ((a*w)*(b*(z*c))) := by simp only [mul_assoc]
      _=τ ((b*(z*c))*(a*w)) := hτ _ _
      _=τ (b*(z*c*a*w)) := by simp only [mul_assoc]
      _=τ (q*(b*(z*c*a*w))) := by
        rw [hτ q]
        congr 1
        rw [mul_assoc b, mul_assoc (z*c*a) w q,hw]
      _=_ := by
        congr 1
        have hqR : q*(z*c*a*w)=z*c*a*w := by
          rw [←mul_assoc,←mul_assoc,←mul_assoc,hz]
        rw [mul_assoc (q*b) q,hqR,mul_assoc q b]
  have hnorm : norm τ (z*c*a*w)≤norm τ q := by
    have hzq : z=q*z := hz.symm
    calc
      _≤norm τ (z*c*a)*‖w‖ := norm_mul_right τ hτ _ _
      _≤norm τ (z*c*a) := mul_le_of_le_one_right (norm_nonneg τ _) hwn
      _≤norm τ (z*c)*‖a‖ := norm_mul_right τ hτ _ _
      _≤norm τ (z*c) := mul_le_of_le_one_right (norm_nonneg τ _) ha
      _≤norm τ z*‖c‖ := norm_mul_right τ hτ _ _
      _≤norm τ z := mul_le_of_le_one_right (norm_nonneg τ _) hc
      _=norm τ (q*z) := congrArg (norm τ) hzq
      _≤norm τ q*‖z‖ := norm_mul_right τ hτ _ _
      _≤norm τ q := mul_le_of_le_one_right (norm_nonneg τ _) hzn
  rw [he]
  exact (norm_trace_mul τ hτ _ _).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg τ _))

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCenteredEstimates
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

open TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

lemma compress_center {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) (b : A) :
    q*b*q=q*cornerCenter τ p b*q+cornerScalar τ p b • q := by
  have h1 := (hq.le_iff_mul_eq_left hp).mp hqp
  have h2 := (hq.le_iff_mul_eq_right hp).mp hqp
  simp only [cornerCenter,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  have h3 : q*(p*b*p)*q=q*b*q := by
    calc
      _=(q*p)*b*(p*q) := by noncomm_ring
      _=_ := by rw [h1,h2]
  rw [h3,h1,hq.isIdempotentElem.eq,sub_add_cancel]

lemma compressed_bound {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) (b : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    norm τ (q*b*q)*norm τ q ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re := by
  have hsmall' : norm τ (q*cornerCenter τ p b*q) ≤ δ*norm τ q := by
    apply (sq_le_sq₀ (norm_nonneg τ _) (mul_nonneg hδ (norm_nonneg τ _))).mp
    rw [mul_pow,norm_projection_sq τ hq]
    exact hsmall
  have hh : norm τ (q*b*q) ≤ (δ+‖cornerScalar τ p b‖)*norm τ q := by
    rw [compress_center τ hp hq hqp b]
    calc
      _ ≤ norm τ (q*cornerCenter τ p b*q)+norm τ (cornerScalar τ p b • q) :=
        norm_add τ _ _
      _ ≤ δ*norm τ q+‖cornerScalar τ p b‖*norm τ q := by
        rw [TracialL2.norm_smul]
        exact add_le_add hsmall' le_rfl
      _=_ := by ring
  calc
    _ ≤ ((δ+‖cornerScalar τ p b‖)*norm τ q)*norm τ q :=
      mul_le_mul_of_nonneg_right hh (norm_nonneg τ _)
    _ = (δ+‖cornerScalar τ p b‖)*(norm τ q)^2 := by ring
    _ = _ := by rw [norm_projection_sq τ hq]

include hτ in
lemma trace_centered_compression_bound_oai {p q b a c w z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q ≤ p)
    (hw : w*q=w) (hz : q*z=z)
    (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hwn : ‖w‖ ≤ 1) (hzn : ‖z‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    ‖τ (a*w*b*z*c)‖ ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re :=
  (trace_two_corner_letters τ hτ hq hw hz ha hc hwn hzn).trans
    (compressed_bound τ hp hq hqp b hδ hsmall)

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FinitePatching.trace_centered_compression_bound_oai.{u_1} := @OAI.Kadison.FinitePatching.trace_centered_compression_bound_oai.{u_1}
