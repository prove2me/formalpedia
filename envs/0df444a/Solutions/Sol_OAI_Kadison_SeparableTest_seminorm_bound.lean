-- Prove2me | solution 1 for OAI.Kadison.SeparableTest.seminorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:28:22.43938+00:00
-- url     : https://prove2.me/submissions/c3a0eb7b-01ca-47f3-a16a-9961e9937618

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C030
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C056
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

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
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFullRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.Kaplansky

open OperatorAmplification CyclicColumns CyclicSpatial

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions_1
variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (Set.range φ))) (hnT : ‖T‖≤1)

lemma fullNet_spec (j : Finset H × ℕ) :
    ‖fullNet φ T hT hnT j‖≤1 ∧ ∀ x∈j.1,‖φ (fullNet φ T hT hnT j) x-T x‖<(j.2+1:ℝ)⁻¹ :=
  (fullNet_exists φ T hT hnT j).choose_spec

lemma fullNet_tendsto (x : H) :
    Tendsto (fun j => φ (fullNet φ T hT hnT j) x) atTop (𝓝 (T x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (({x}:Finset H),N)] with j hj
  rw [dist_eq_norm]
  apply (fullNet_spec φ T hT hnT j).2 x (hj.1 (Finset.mem_singleton_self x)) |>.trans_le
  have hn : (N+1:ℝ)≤j.2+1 := by exact_mod_cast Nat.succ_le_succ hj.2
  exact (inv_anti₀ (by positivity) hn).trans (by simpa only [one_div] using hN.le)

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DerivationKaplansky
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.DerivationColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

theorem seminorm_bicommutant_le (Y : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hY : ∀ a : A,‖Y*σ a-σ a*Y‖ ≤ c*‖a‖) :
    commutatorSeminorm (NormalGNS.bicommutant σ.range) Y ≤ c := by
  classical
  change sSup {r : ℝ | ∃ T : H →L[ℂ] H,T∈NormalGNS.bicommutant σ.range ∧ ‖T‖≤1 ∧ r=‖Y*T-T*Y‖} ≤ c
  refine csSup_le ⟨0,0,zero_mem _,by simp,by simp⟩ ?_
  rintro r ⟨T,hT,hnT,rfl⟩
  have hTb := (NormalGNS.mem_bicommutant σ.range T).mp hT
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have ht := ((Y.continuous.tendsto (T x)).comp
    (Kaplansky.fullNet_tendsto σ T hTb hnT x)).sub
      (Kaplansky.fullNet_tendsto σ T hTb hnT (Y x))
  change Tendsto (fun j => (Y*σ (Kaplansky.fullNet σ T hTb hnT j)-
    σ (Kaplansky.fullNet σ T hTb hnT j)*Y) x) atTop (𝓝 ((Y*T-T*Y) x)) at ht
  apply le_of_tendsto ht.norm
  apply Filter.Eventually.of_forall
  intro j
  calc
    _≤‖Y*σ (Kaplansky.fullNet σ T hTb hnT j)-σ (Kaplansky.fullNet σ T hTb hnT j)*Y‖*‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _≤(c*‖Kaplansky.fullNet σ T hTb hnT j‖)*‖x‖ :=
      mul_le_mul_of_nonneg_right (hY _) (norm_nonneg x)
    _ ≤ c*‖x‖ := by
      have hn := (Kaplansky.fullNet_spec σ T hTb hnT j).1
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hn hc).trans_eq (mul_one c)) (norm_nonneg x)

end Kadison.DerivationColumns

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
-- module Solutions.OAIQ039_CM.Commutator_ReducingMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H),x∈K → σ a x∈K)

omit [CompleteSpace H] in
lemma compression_eq_restrict (Y : H →L[ℂ] H) (hY : ∀ x∈K,Y x∈K) :
    compression K Y=Y.restrict hY := by
  apply ContinuousLinearMap.ext
  intro x
  change K.orthogonalProjectionOnto (Y (x:H))=(Y.restrict hY) x
  exact K.orthogonalProjectionOnto_mem_subspace_eq_self (Y.restrict hY x)

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableTestGeometry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.SeparableTest

open SeparableReducingHull ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (Y : H →L[ℂ] H)

attribute [local instance] OAI.Kadison.SeparableTest.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra : StarOrderedRing (algebra h X) := CStarAlgebra.spectralOrderedRing _

lemma algebra_le (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) : algebra h X≤P.toStarSubalgebra := by
  apply StarSubalgebra.topologicalClosure_minimal
  · exact StarAlgebra.adjoin_le (by rintro _ ⟨⟨i,j⟩,rfl⟩; exact hX i j)
  · exact VonNeumannCStar.isClosed P

variable (ξ : PiLp 2 (fun _ : Fin h => H))

lemma scalar_bound (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) (a : algebra h X) :
    ‖restrictedY h X Y ξ*representation h X Y ξ a-representation h X Y ξ a*restrictedY h X Y ξ‖≤
      commutatorSeminorm P Y*‖a‖ := by
  have hb := norm_commutator_compression_le (algebra h X).subtype (space h X Y ξ)
    (algebra_invariant h X Y ξ) Y a
  rw [compression_eq_restrict _ Y (Y_invariant h X Y ξ)] at hb
  exact hb.trans (commutator_bound P Y (algebra_le h X P hX a.property))

lemma seminorm_bound_oai (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) :
    commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range) (restrictedY h X Y ξ)≤
      commutatorSeminorm P Y :=
  DerivationColumns.seminorm_bicommutant_le _ _ (commutatorSeminorm_nonneg P Y)
    (scalar_bound h X Y ξ P hX)

end Kadison.SeparableTest

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.SeparableTest.seminorm_bound_oai.{u_1} := @OAI.Kadison.SeparableTest.seminorm_bound_oai.{u_1}
