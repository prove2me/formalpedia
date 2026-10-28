-- Prove2me | solution 1 for OAI.Kadison.CentralAverage.exists_finite_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:12:07.135564+00:00
-- url     : https://prove2.me/submissions/c00a68e5-7a1b-47be-9dff-3c75045b1d33

import Mathlib
import Definitions.Def_OAIQ039C020
import Definitions.Def_OAIQ039C030
import Definitions.Def_OAIQ039C031

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryOrbitHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma hull_self (Y : H →L[ℂ] H) : Y∈hull M Y := by
  apply subset_convexHull
  exact ⟨1,by simp [conjugate]⟩

lemma conjugate_mul (v w : unitary M) (Y : H →L[ℂ] H) :
    conjugate M v (conjugate M w Y)=conjugate M (v*w) Y := by
  change ((v:M):H →L[ℂ] H)*(((w:M):H →L[ℂ] H)*Y*star ((w:M):H →L[ℂ] H))*
    star ((v:M):H →L[ℂ] H)=
    (((v:M):H →L[ℂ] H)*((w:M):H →L[ℂ] H))*Y*
      star (((v:M):H →L[ℂ] H)*((w:M):H →L[ℂ] H))
  simp only [star_mul,mul_assoc]

lemma conjugate_mem_hull (v : unitary M) {T Y : H →L[ℂ] H} (hT : T∈hull M Y) :
    conjugate M v T∈hull M Y := by
  have him : conjugateLinear M v '' (Set.range (fun w : unitary M => conjugate M w Y)) ⊆
      Set.range (fun w : unitary M => conjugate M w Y) := by
    rintro _ ⟨_,⟨w,rfl⟩,rfl⟩
    exact ⟨v*w,(conjugate_mul M v w Y).symm⟩
  have hc := convexHull_mono (𝕜 := ℝ) him
  rw [← LinearMap.image_convexHull] at hc
  exact hc ⟨T,hT,rfl⟩

lemma midpoint_mem {Y T V : H →L[ℂ] H} (hT : T∈hull M Y) (hV : V∈hull M Y) :
    (1/2:ℝ) • T+(1/2:ℝ) • V∈hull M Y :=
  convex_convexHull ℝ _ hT hV (by norm_num) (by norm_num) (by norm_num)

end Kadison.UnitaryOrbit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralPinching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.CentralAverage

open UnitaryOrbit

section Algebra

variable {A : Type*} [Ring A] [StarRing A]

lemma pinch_commutes (p T : A) (hp : IsStarProjection p) :
    (T+(p+p-1)*T*(p+p-1))*p=p*(T+(p+p-1)*T*(p+p-1)) := by
  have hpp (x : A) : p*(p*x)=p*x := by rw [←mul_assoc,hp.isIdempotentElem.eq]
  noncomm_ring [hp.isIdempotentElem.eq,hpp]

end Algebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma pinch_mem {Y T : H →L[ℂ] H} (p : CentralProjection M) (hT : T∈hull M Y) :
    pinch M p T∈hull M Y :=
  midpoint_mem M hT (conjugate_mem_hull M _ hT)

lemma pinch_formula (p : CentralProjection M) (T : H →L[ℂ] H) :
    pinch M p T=(1/2:ℝ) • (T+(p.val+p.val-1)*T*(p.val+p.val-1)) := by
  change (1/2:ℝ) • T+(1/2:ℝ) • ((p.val+p.val-1)*T*star (p.val+p.val-1))=_
  simp only [star_sub,star_add,star_one,p.property.2.1.isSelfAdjoint.star_eq,smul_add]

lemma pinch_commutes_projection (p : CentralProjection M) (T : H →L[ℂ] H) :
    pinch M p T*p.val=p.val*pinch M p T := by
  rw [pinch_formula,smul_mul_assoc,mul_smul_comm,pinch_commutes _ _ p.property.2.1]

lemma pinch_preserves (p q : CentralProjection M) {T : H →L[ℂ] H}
    (hT : T*q.val=q.val*T) : pinch M p T*q.val=q.val*pinch M p T := by
  have hpq : Commute p.val q.val := (p.property.2.2 _ q.property.1).symm
  have hU : Commute (p.val+p.val-1) q.val := (hpq.add_left hpq).sub_left (Commute.one_left _)
  have hr := (show Commute T q.val from hT).add_left
    ((hU.mul_left hT).mul_left hU)
  rw [pinch_formula,smul_mul_assoc,mul_smul_comm,hr.eq]

theorem exists_finite_average_oai (Y : H →L[ℂ] H) (s : Finset (CentralProjection M)) :
    ∃ T : H →L[ℂ] H,T∈hull M Y ∧ ∀ p∈s,T*p.val=p.val*T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Y,hull_self M Y,by simp⟩
  | @insert p s hp ih =>
    obtain ⟨T,hT,hc⟩ := ih
    refine ⟨pinch M p T,pinch_mem M p hT,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqp|hq
    · subst q
      exact pinch_commutes_projection M p T
    · exact pinch_preserves M p q (hc q hq)

end Kadison.CentralAverage

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.CentralAverage.exists_finite_average_oai.{u_1} := @OAI.Kadison.CentralAverage.exists_finite_average_oai.{u_1}
