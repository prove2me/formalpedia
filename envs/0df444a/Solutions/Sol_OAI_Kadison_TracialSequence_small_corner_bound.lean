-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.small_corner_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:16:42.997272+00:00
-- url     : https://prove2.me/submissions/b79bcd00-d90a-4931-b392-d4fd058fed26

import Mathlib
import Definitions.Def_OAIQ039C069
import Theorems.Thm_OAI_Kadison_TracialSequence_bicommutant_norm_lift
import Theorems.Thm_OAI_Kadison_TracialSequence_small_projection_lift

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_compress_le (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    ‖compress V T‖ ≤ ‖T‖ := by
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hv' : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact hv
  calc
    ‖compress V T‖ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖T‖ *
        ‖V.toContinuousLinearMap‖ := (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hv' (norm_nonneg _)) hv (norm_nonneg _)
      (by positivity)
    _ = ‖T‖ := by ring

end Kadison.FreeCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequenceOperator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ)

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma norm_act_apply_le (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Space ω E) :
    ‖act ω T x‖≤‖T‖*‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x => simpa only [act_coe,Completion.norm_coe] using norm_actPreLinear_le ω T x

lemma norm_act_le (T : ℕ →ᵇ (E →L[ℂ] F)) : ‖act ω T‖≤‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (norm_act_apply_le ω T)

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ReducingCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

lemma inclusion_intertwines (a : A) : (σ a).comp K.subtypeL=
    K.subtypeL.comp (restrict σ K hinv a) := rfl

lemma projection_intertwines (a : A) : K.orthogonalProjectionOnto.comp (σ a)=
    (restrict σ K hinv a).comp K.orthogonalProjectionOnto := by
  have h := congrArg (fun T : K →L[ℂ] H => T.adjoint) (inclusion_intertwines σ K hinv (star a))
  simpa only [adjoint_comp,Submodule.adjoint_subtypeL,map_star,star_eq_adjoint,adjoint_adjoint] using h

lemma compression_eq (S : H →L[ℂ] H) : compression K S=FreeCorner.compress K.subtypeₗᵢ S := by
  change K.orthogonalProjectionOnto.comp (S.comp K.subtypeL)=
    (K.subtypeL.adjoint.comp S).comp K.subtypeL
  rw [Submodule.adjoint_subtypeL]
  rfl

lemma norm_compression_le (S : H →L[ℂ] H) : ‖compression K S‖≤‖S‖ := by
  rw [compression_eq]
  exact FreeCorner.norm_compress_le _ S

lemma compression_left (S : H →L[ℂ] H) (a : A) :
    compression K (σ a*S)=restrict σ K hinv a*compression K S := by
  simp only [compression,mul_def,←comp_assoc]
  rw [projection_intertwines σ K hinv]

lemma compression_right (S : H →L[ℂ] H) (a : A) :
    compression K (S*σ a)=compression K S*restrict σ K hinv a := by
  simp only [compression,mul_def,comp_assoc]
  rw [inclusion_intertwines σ K hinv]

omit [CompleteSpace H] in
lemma compression_sub (S T : H →L[ℂ] H) : compression K (S-T)=compression K S-compression K T := by
  simp only [compression,comp_sub,sub_comp]

lemma compression_commutator (S : H →L[ℂ] H) (a : A) :
    compression K (S*σ a-σ a*S)=
      compression K S*restrict σ K hinv a-restrict σ K hinv a*compression K S := by
  rw [compression_sub,compression_left σ K hinv,compression_right σ K hinv]

lemma norm_commutator_compression_le (S : H →L[ℂ] H) (a : A) :
    ‖compression K S*restrict σ K hinv a-restrict σ K hinv a*compression K S‖≤‖S*σ a-σ a*S‖ := by
  rw [←compression_commutator σ K hinv]
  exact norm_compression_le K _

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence ReducingRepresentation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma commutator_bound (S : τ.GNS →L[ℂ] τ.GNS) (a : ℕ →ᵇ A) (c : ℝ)
    (hc : ∀ i, ‖S*τ.gnsStarAlgHom (a i)-τ.gnsStarAlgHom (a i)*S‖ ≤ c) :
    ‖compressed τ ω S*leftRestricted τ ω a-leftRestricted τ ω a*compressed τ ω S‖ ≤ c := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  let T : ℕ →ᵇ (τ.GNS →L[ℂ] τ.GNS) :=
    BoundedContinuousFunction.const ℕ S*leftFamily τ a-leftFamily τ a*BoundedContinuousFunction.const ℕ S
  have hT : ‖T‖ ≤ c := (BoundedContinuousFunction.norm_le hc0).mpr hc
  have hid : act ω T=act ω (BoundedContinuousFunction.const ℕ S)*leftHom τ ω a-
      leftHom τ ω a*act ω (BoundedContinuousFunction.const ℕ S) := by
    change actionHom ω (_*_ - _*_) = _
    rw [map_sub,map_mul,map_mul]
    rfl
  calc
    _ ≤ ‖act ω (BoundedContinuousFunction.const ℕ S)*leftHom τ ω a-
        leftHom τ ω a*act ω (BoundedContinuousFunction.const ℕ S)‖ :=
      norm_commutator_compression_le (leftHom τ ω) (boundedSubspace τ ω)
        (leftHom_preserves τ ω) _ a
    _ = ‖act ω T‖ := congrArg norm hid.symm
    _ ≤ ‖T‖ := norm_act_le ω T
    _ ≤ c := hT

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSmallCorners
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
theorem small_corner_bound_oai {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
    (hω : (ω : Filter ℕ)≤atTop)
    (S : τ.GNS →L[ℂ] τ.GNS) {b c : ℝ} (hb : 0≤b) (hc : 0 ≤ c)
    (hS : ∀ (q : N), IsStarProjection q → (τ (f q)).re≤b →
      ∀ a : A, f q*a*f q=a →
        ‖S*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*S‖ ≤ c*‖a‖)
    {e T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (he : IsStarProjection e)
    (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f)))
    (het : (sequenceTrace τ ω e).re<b)
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (heT : e*T*e=T) :
    ‖compressed τ ω S*T-T*compressed τ ω S‖ ≤ c*‖T‖ := by
  obtain ⟨r,hr,hrt,hre⟩ := small_projection_lift τ ω hτ N f hb he her het
  obtain ⟨a,hna,haT⟩ := bicommutant_norm_lift τ ω hτ hω hT
  let z := mapSequence f r*a*mapSequence f r
  have hzT : leftRestricted τ ω z=T := by
    simp only [z,map_mul,hre,haT,heT]
  rw [←hzT]
  apply commutator_bound τ ω S z
  intro i
  have hfi : IsStarProjection (f (r i)) := (hr i).map f
  have hz : f (r i)*z i*f (r i)=z i := by
    change f (r i)*(f (r i)*a i*f (r i))*f (r i)=f (r i)*a i*f (r i)
    simp only [←mul_assoc,hfi.isIdempotentElem.eq]
    rw [mul_assoc _ (f (r i)) (f (r i)),hfi.isIdempotentElem.eq]
  have hn : ‖z i‖≤‖T‖ := by
    change ‖f (r i)*a i*f (r i)‖≤‖T‖
    calc
      _ ≤ ‖f (r i)‖*‖a i‖*‖f (r i)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖a i‖*1 := by gcongr <;> exact hfi.norm_le _
      _ ≤ ‖T‖ := by simpa only [one_mul,mul_one] using (a.norm_coe_le_norm i).trans hna
  exact (hS (r i) (hr i) (hrt i) (z i) hz).trans
    (by rw [hzT]; exact mul_le_mul_of_nonneg_left hn hc)

end Kadison.TracialSequence

end

end OAI
end

theorem solution.{u_1, u_3} : type_of% @OAI.Kadison.TracialSequence.small_corner_bound_oai.{u_1, u_3} := @OAI.Kadison.TracialSequence.small_corner_bound_oai.{u_1, u_3}
