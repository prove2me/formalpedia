-- Prove2me | solution 1 for OAI.Kadison.CornerPolarTransfer.defect_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:12:26.623417+00:00
-- url     : https://prove2.me/submissions/d3b63e0b-20b8-4dc2-b83b-6d38c12f0022

import Mathlib
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPolarAlgebra
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

namespace Kadison.CornerPolarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma square_root_defect_le {q a : A} (hq : IsStarProjection q)
    (ha : 0≤a) (haq : a*q=a) :
    star (q-a)*(q-a) ≤ star (q-a*a)*(q-a*a) := by
  have has := (IsSelfAdjoint.of_nonneg ha).star_eq
  have hqa : q*a=a := by
    simpa only [star_mul,has,hq.isSelfAdjoint.star_eq] using congrArg star haq
  have hc : Commute q a := hqa.trans haq.symm
  have hsub : IsSelfAdjoint (q-a) := hq.isSelfAdjoint.sub (IsSelfAdjoint.of_nonneg ha)
  have hs : 0≤(q-a)*(q-a) := by
    simpa only [hsub.star_eq] using star_mul_self_nonneg (q-a)
  have hasc : Commute a ((q-a)*(q-a)) :=
    (hc.symm.sub_right (Commute.refl a)).mul_right (hc.symm.sub_right (Commute.refl a))
  have hqa' : Commute (q-a) q := (Commute.refl q).sub_left hc.symm
  have hscq : Commute ((q-a)*(q-a)) q := hqa'.mul_left hqa'
  have hc' : Commute (a*((q-a)*(q-a))) (a+(q+q)) :=
    ((Commute.refl a).mul_left hasc.symm).add_right
      ((hc.symm.mul_left hscq).add_right (hc.symm.mul_left hscq))
  have hpos : 0≤a*((q-a)*(q-a))*(a+(q+q)) :=
    Commute.mul_nonneg (Commute.mul_nonneg ha hs hasc)
      (add_nonneg ha (add_nonneg hq.nonneg hq.nonneg)) hc'
  have he : star (q-a*a)*(q-a*a)-star (q-a)*(q-a)=
      a*((q-a)*(q-a))*(a+(q+q)) := by
    simp only [star_sub,star_mul,has,hq.isSelfAdjoint.star_eq]
    have hqaa : q*(a*a)=a*a := by rw [←mul_assoc,hqa]
    noncomm_ring [hq.isIdempotentElem.eq,hqa,haq,hqaa]
  exact sub_nonneg.mp (he.symm ▸ hpos)

lemma polar_defect_le {q r a v : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hrq : r≤q) (ha : 0≤a)
    (hra : r*a=a) (haq : a*q=a) (hv : star v*v=r) :
    star (v-v*a)*(v-v*a) ≤ star (q-a*a)*(q-a*a) := by
  have has := (IsSelfAdjoint.of_nonneg ha).star_eq
  have har : a*r=a := by
    simpa only [star_mul,has,hr.isSelfAdjoint.star_eq] using congrArg star hra
  have hqa : q*a=a := by
    simpa only [star_mul,has,hq.isSelfAdjoint.star_eq] using congrArg star haq
  have he : star (v-v*a)*(v-v*a)=star (q-a)*(q-a)-(q-r) := by
    simp only [star_sub,star_mul,has,hq.isSelfAdjoint.star_eq]
    have hva : star v*(v*a)=a := by rw [←mul_assoc,hv,hra]
    noncomm_ring [hq.isIdempotentElem.eq,hra,har,hqa,haq,hv,hva]
  rw [he]
  exact (sub_le_self _ (sub_nonneg.mpr hrq)).trans (square_root_defect_le hq ha haq)

end Kadison.CornerPolarAlgebra

end

end
end

end OAI
end

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

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

lemma norm_mono_square {a b : A} (hab : star a*a ≤ star b*b) : norm τ a≤norm τ b := by
  apply (sq_le_sq₀ (norm_nonneg τ _) (norm_nonneg τ _)).mp
  rw [norm_sq,norm_sq]
  exact (τ.monotone hab).1

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

lemma defect_bound_oai {q r a v : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hrq : r≤q) (ha : 0≤a)
    (hra : r*a=a) (haq : a*q=a) (hv : star v*v=r) :
    norm τ (v-v*a) ≤ norm τ (q-a*a) :=
  norm_mono_square τ (CornerPolarAlgebra.polar_defect_le hq hr hrq ha hra haq hv)

end Estimates

end Kadison.CornerPolarTransfer

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.CornerPolarTransfer.defect_bound_oai.{u_1} := @OAI.Kadison.CornerPolarTransfer.defect_bound_oai.{u_1}
