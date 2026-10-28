-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.compressed_commutes_of_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:49:13.99157+00:00
-- url     : https://prove2.me/submissions/8f83b348-fa7a-46f4-ac03-f5bb3799ff39

import Mathlib
import Definitions.Def_OAIQ039C064

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

lemma commutator_zero (S : τ.GNS →L[ℂ] τ.GNS) (a : ℕ →ᵇ A)
    (ha : ∀ i, S*τ.gnsStarAlgHom (a i)=τ.gnsStarAlgHom (a i)*S) :
    compressed τ ω S*leftRestricted τ ω a=leftRestricted τ ω a*compressed τ ω S := by
  apply sub_eq_zero.mp
  exact (@norm_le_zero_iff (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) _ _).mp
    (commutator_bound τ ω S a 0 (fun i => by rw [ha i,sub_self,norm_zero]))

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialRangeCommutation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.TracialSequence

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)

lemma compressed_commutes_of_range_oai (T : τ.GNS →L[ℂ] τ.GNS)
    (hT : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    (d : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    (hd : d∈Set.range ((leftRestricted τ ω).comp (mapSequence j))) :
    compressed τ ω T*d=d*compressed τ ω T := by
  obtain ⟨a,rfl⟩ := hd
  exact commutator_zero τ ω T (mapSequence j a) (fun i => hT (a i))

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.compressed_commutes_of_range_oai := @OAI.Kadison.TracialSequence.compressed_commutes_of_range_oai
