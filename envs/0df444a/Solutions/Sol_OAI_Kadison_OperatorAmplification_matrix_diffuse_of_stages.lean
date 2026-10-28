-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:31.168692+00:00
-- url     : https://prove2.me/submissions/4cc9e326-05d4-429b-bb3c-f51a546765a7

import Mathlib
import Definitions.Def_OAIQ039C062
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_MatrixTower_small_of_stages
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_diagonal
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_faithful
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_tracial

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVonNeumann
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

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (i₀ : ι)

lemma factor_matrixVonNeumann (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M) :
    FactorCorner.IsFactor (matrixVonNeumann ι i₀ M) := by
  intro Z hZ hc
  have he : Z=diagonal (H:=H) ι (entry ι Z i₀ i₀) :=
    diagonal_of_matrixUnits ι i₀ Z (fun i j => hc _ (matrixUnit_mem ι i₀ M i j))
  have ha := (mem_matrixVonNeumann ι i₀ M Z).mp hZ i₀ i₀
  have hca : entry ι Z i₀ i₀∈Set.centralizer (M:Set (H →L[ℂ] H)) := by
    intro a ha
    exact entry_commutes ι Z a (hc _ (diagonal_mem_matrixVonNeumann ι i₀ M ha)) i₀ i₀
  obtain ⟨c,hc⟩ := hM _ ha hca
  refine ⟨c,?_⟩
  rw [he,hc,map_smul,map_one]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerDiffuse
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hfaith in
lemma projection_trace_positive {p : M} (hp : IsStarProjection p) (hpn : p≠0) :
    0<(τ p).re := by
  have hn := τ.map_nonneg hp.nonneg
  apply lt_of_le_of_ne hn.1
  intro heq
  apply hpn
  apply hfaith
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  exact Complex.ext heq.symm hn.2.symm

include hτ hfaith in
lemma diffuse_of_small (hfac : FactorCorner.IsFactor M)
    (hsmall : ∀ ε : ℝ,0<ε → ∃ q : M,IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε) :
    DiffuseProjection.HasNoMinimalProjections M := by
  intro p hpM hp hpn
  let p' : M := ⟨p,hpM⟩
  have hp' : IsStarProjection p' := ⟨Subtype.ext hp.isIdempotentElem.eq,Subtype.ext hp.isSelfAdjoint.star_eq⟩
  have hpn' : p'≠0 := fun h => hpn (congrArg Subtype.val h)
  obtain ⟨q,hq,hqn,hqt⟩ := hsmall (τ p').re (projection_trace_positive M τ hfaith hp' hpn')
  have hle : τ q≤τ p' := ⟨hqt.le,(τ.map_nonneg hq.nonneg).2.symm.trans (τ.map_nonneg hp'.nonneg).2⟩
  have hq' : IsStarProjection (q : H →L[ℂ] H) := hq.map M.toStarSubalgebra.subtype
  obtain ⟨v,hvi⟩ := PartialIsometryOrder.finite_factor_comparison M hfac τ hτ hfaith
    q.property hpM hq' hp hle
  have htrace : τ ⟨v.final,v.final_mem⟩=τ q := by
    rw [←v.trace_initial_final τ hτ]
    exact congrArg τ (Subtype.ext hvi)
  have hpos : 0<(τ ⟨v.final,v.final_mem⟩).re := by
    rw [htrace]; exact projection_trace_positive M τ hfaith hq hqn
  refine ⟨v.final,v.final_mem,v.final_projection,?_,?_,v.target_le⟩
  · intro hz
    have hz' : (⟨v.final,v.final_mem⟩:M)=0 := Subtype.ext hz
    rw [hz',map_zero] at hpos
    exact lt_irrefl _ hpos
  · intro heq
    have heq' : (⟨v.final,v.final_mem⟩:M)=p' := Subtype.ext heq
    rw [heq'] at htrace
    exact (ne_of_lt hqt) (congrArg Complex.re htrace.symm)

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiffuseTransfer
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

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixDiffuseTransferIndexDecidableEq
lemma entry_diagonal (a : H →L[ℂ] H) (i : ι) :
    entry ι (diagonal (H:=H) ι a) i i=a := by
  ext x
  simp only [entry_apply,diagonal_single,single_apply,ite_true]

lemma diagonalHom_injective : Function.Injective (diagonalHom ι i₀ M) := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun T : matrixVonNeumann ι i₀ M =>
    entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i₀ i₀) h
  simpa only [coe_diagonalHom,entry_diagonal] using he

theorem matrix_diffuse_of_stages_oai (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (F : ℕ → MatrixTower.Stage M) (hsize : ∀ N : ℕ,∃ n,N<Fintype.card (F n).I) :
    DiffuseProjection.HasNoMinimalProjections (matrixVonNeumann ι i₀ M) := by
  apply MatrixTower.diffuse_of_small (matrixVonNeumann ι i₀ M) (matrixTrace ι i₀ M τ)
    (matrixTrace_tracial ι i₀ M τ hτ) (matrixTrace_faithful ι i₀ M τ hfaith)
    (factor_matrixVonNeumann ι i₀ M hM)
  intro ε hε
  obtain ⟨q,hq,hqn,hqt⟩ := MatrixTower.small_of_stages M τ hτ h1 F hsize hε
  refine ⟨diagonalHom ι i₀ M q,hq.map (diagonalHom ι i₀ M),?_,?_⟩
  · intro h
    apply hqn
    apply diagonalHom_injective ι i₀ M
    simpa only [map_zero] using h
  · rwa [matrixTrace_diagonal]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages_oai.{u_1, u_2}
