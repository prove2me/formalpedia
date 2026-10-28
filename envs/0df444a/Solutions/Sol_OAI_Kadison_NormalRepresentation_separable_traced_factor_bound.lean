-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.separable_traced_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:27:02.799875+00:00
-- url     : https://prove2.me/submissions/8b633c5f-66ec-4d10-b0b9-56632d3f54ca

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C062
import Theorems.Thm_OAI_Kadison_BiprodLinkColumn_compression_empty
import Theorems.Thm_OAI_Kadison_NormalGNS_separable_gns
import Theorems.Thm_OAI_Kadison_NormalRepresentation_exists_orthogonal_links
import Theorems.Thm_OAI_Kadison_NormalRepresentation_finite_standard_compression_bound
import Theorems.Thm_OAI_Kadison_NormalRepresentation_link_intertwines
import Theorems.Thm_OAI_Kadison_StrongContractionLimit_commutator_bound_limit
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_BiprodLinkColumn
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G))

omit [CompleteSpace H] [CompleteSpace G] in
lemma inl_norm_le : ‖inlL (H:=H) (G:=G)‖≤1 :=
  (inl (H:=H) (G:=G)).norm_toContinuousLinearMap_le

variable (S : Set (Intertwiner N)) (hS : OrthogonalLinks N right left S)

include hS

lemma compression_norm_le (s : Finset S) : ‖compression N S s‖≤1 := by
  calc
    _≤‖(inlL (H:=H) (G:=G)).adjoint‖*
        (‖finiteProjection N right left S s‖*‖inlL (H:=H) (G:=G)‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _≤1*(1*1) := mul_le_mul (by simpa only [ContinuousLinearMap.adjoint.norm_map] using inl_norm_le (H:=H) (G:=G))
      (mul_le_mul (finiteProjection_norm_le N right left S hS s) (inl_norm_le (H:=H) (G:=G))
        (norm_nonneg (inlL (H:=H) (G:=G))) (by norm_num))
      (mul_nonneg (norm_nonneg (finiteProjection N right left S s)) (norm_nonneg (inlL (H:=H) (G:=G)))) (by norm_num)
    _=1 := by norm_num

lemma column_norm_le (s : Finset S) : ‖finiteColumn N S s‖≤1 := by
  have h := compression_norm_le N S hS s
  rw [←column_square N S s,ContinuousLinearMap.norm_adjoint_comp_self] at h
  nlinarith [norm_nonneg (finiteColumn N S s)]

end Kadison.BiprodLinkColumn

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRepresentationColumns
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

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (S : Set (Intertwiner (diagonalAlgebra M τ hnormal).commutant))

lemma finiteColumn_intertwines (s : Finset S) (a : M) :
    (finiteColumn _ S s).comp (a:H →L[ℂ] H)=
      (diagonal (H:=τ.GNS) s (τ.gnsStarAlgHom a)).comp (finiteColumn _ S s) := by
  classical
  ext x i
  exact congrArg (fun T : H →L[ℂ] τ.GNS => T x) (link_intertwines M τ hnormal i.val.val a)

end Kadison.NormalRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContractionLimit
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContractionLimit

variable {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

variable {l : Filter ι}

lemma apply_tendsto (P : ι → H →L[ℂ] G) (Q : H →L[ℂ] G)
    (hP : ∀ i,‖P i‖≤1) (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Q x)))
    {u : ι → H} {x : H} (hu : Tendsto u l (𝓝 x)) :
    Tendsto (fun i => P i (u i)) l (𝓝 (Q x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun i => ‖u i-x‖+‖P i x-Q x‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_add] using
      ((hu.sub (tendsto_const_nhds (x := x))).norm.add
        (((hstrong x).sub (tendsto_const_nhds (x := Q x))).norm))
  apply squeeze_zero (fun i => norm_nonneg _) _ hlim
  intro i
  calc
    ‖P i (u i)-Q x‖=‖P i (u i-x)+(P i x-Q x)‖ := by rw [map_sub]; congr 1; abel
    _≤‖P i (u i-x)‖+‖P i x-Q x‖ := norm_add_le _ _
    _≤‖u i-x‖+‖P i x-Q x‖ := by
      apply add_le_add _ le_rfl
      exact ((P i).le_opNorm (u i-x)).trans (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hP i) (norm_nonneg (u i-x)))

lemma sandwich_tendsto (P : ι → H →L[ℂ] H) (hP : ∀ i,‖P i‖≤1)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 x)) (Y : H →L[ℂ] H) (x : H) :
    Tendsto (fun i => (P i*Y*P i) x) l (𝓝 (Y x)) := by
  exact apply_tendsto P (ContinuousLinearMap.id ℂ H) hP hstrong
    (Y.continuous.tendsto x |>.comp (hstrong x))

end Kadison.StrongContractionLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalTracedFactorMain
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn IntertwinerCompression

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (τ : M →ₚ[ℂ] ℂ)

theorem traced_factor_bound [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (h : ℕ) (hh : 1≤h) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
  classical
  let N := (diagonalAlgebra M τ hnormal).commutant
  obtain ⟨S,hS,hspan⟩ := exists_orthogonal_links M τ hnormal hfac hone
  let P : Finset S → H →L[ℂ] H := compression N S
  have hP (s : Finset S) : ‖P s‖≤1 := compression_norm_le N S hS s
  have hstrong (x : H) : Tendsto (fun s : Finset S => P s x) atTop (𝓝 x) :=
    compression_tendsto N S hS hspan x
  have hbound (s : Finset S) :
      ‖diagonalAmplification h (P s*Y*P s)*matrixOperator h X-
        matrixOperator h X*diagonalAmplification h (P s*Y*P s)‖≤
          (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
    rcases s.eq_empty_or_nonempty with hs|hs
    · subst s
      have hz : P ∅=0 := compression_empty N S
      rw [hz,zero_mul,mul_zero]
      have hd : diagonalAmplification h (0:H →L[ℂ] H)=0 := by ext x i; rfl
      rw [hd,zero_mul,mul_zero,sub_zero,norm_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M Y)) (norm_nonneg _)
    · let : Nonempty s := ⟨⟨hs.choose,hs.choose_spec⟩⟩
      have hc := column_norm_le N S hS s
      have hi := finiteColumn_intertwines M τ hnormal S s
      have hb := finite_standard_compression_bound M τ s hτ hnormal hfaith hone hfac hdiffuse
        (finiteColumn N S s) hc hi h hh Y X hX
      have hsq : (finiteColumn N S s).adjoint.comp (finiteColumn N S s)=P s :=
        column_square N S s
      exact (congrArg (fun Q : H →L[ℂ] H =>
        ‖diagonalAmplification h (Q*Y*Q)*matrixOperator h X-
          matrixOperator h X*diagonalAmplification h (Q*Y*Q)‖ ≤
            (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖) hsq).mp hb
  exact StrongContractionLimit.commutator_bound_limit
    (fun s : Finset S => P s*Y*P s) Y
    (StrongContractionLimit.sandwich_tendsto P hP hstrong Y) h X
    ((3122*commutatorSeminorm M Y)*‖matrixOperator h X‖)
    (mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M Y)) (norm_nonneg _))
    (Filter.Eventually.of_forall hbound)

end Kadison.NormalRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracedSeparableFactorMain
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.NormalRepresentation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (τ : M →ₚ[ℂ] ℂ)

theorem separable_traced_factor_bound_oai
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (h : ℕ) (hh : 1≤h) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
  let := NormalGNS.separable_gns M τ hnormal
  exact traced_factor_bound M τ hτ hnormal hfaith hone hfac hdiffuse h hh Y X hX

end Kadison.NormalRepresentation

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.NormalRepresentation.separable_traced_factor_bound_oai := @OAI.Kadison.NormalRepresentation.separable_traced_factor_bound_oai
