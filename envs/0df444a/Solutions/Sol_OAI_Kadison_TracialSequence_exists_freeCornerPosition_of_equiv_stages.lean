-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:13:46.036496+00:00
-- url     : https://prove2.me/submissions/f5bf0d18-4169-4b04-bf31-9419e244ecbd

import Mathlib
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_TracialSequence_exists_freeCornerPosition_of_equiv_tower

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerInclusion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable [Nontrivial M] (hF : Monotone (fun n => (F n).hom.range))

lemma stageInclusion_commutes {n m : ℕ} (h : n ≤ m) (a : Matrix (F n).I (F n).I ℂ) :
    (F m).hom (stageInclusion M F hF h a)=(F n).hom a := by
  let e := StarAlgEquiv.ofInjective (F m).hom (stage_injective M F m)
  let b : (F m).hom.range := ⟨(F n).hom a,hF h ⟨a,rfl⟩⟩
  exact congrArg Subtype.val (e.apply_symm_apply b)

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixIndexEquiv
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable [Nontrivial M] (hF : Monotone (fun n => (F n).hom.range))

lemma normalizedInclusion_commutes {n m : ℕ} (h : n ≤ m) (a) :
    normalizedStage M F m (normalizedInclusion M F hF h a)=normalizedStage M F n a := by
  change (F m).hom (matrixIndexEquiv (normalizedIndex M F m)
    ((matrixIndexEquiv (normalizedIndex M F m)).symm
      (stageInclusion M F hF h (matrixIndexEquiv (normalizedIndex M F n) a))))=_
  rw [StarAlgEquiv.apply_symm_apply,stageInclusion_commutes]
  rfl

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalizedTowerFreePosition
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

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open MatrixTower

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (M R : VonNeumannAlgebra H) [Nontrivial M] (hRM : R ≤ M)
  (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
  (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)

variable (τ : A →ₚ[ℂ] ℂ) (σ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (E : ℕ → Stage M) (hE : Monotone (fun n => (E n).hom.range))

include hRM hj hE in
theorem exists_freeCornerPosition_of_equiv_stages_oai [TopologicalSpace.SeparableSpace σ.GNS]
    (htrace : ∀ a,σ (e a)=τ a)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M σ)
    (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n a,(E n).hom a*b=b*(E n).hom a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,((E n).hom a : H →L[ℂ] H)∈R)
    (hgrow : Tendsto (fun n => (Fintype.card (E n).I:ℝ)) atTop atTop)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  apply exists_freeCornerPosition_of_equiv_tower M R hRM e j hj τ σ ω
    (normalizedSize M E) (normalizedStage M E) (normalizedInclusion M E hE)
    htrace hτ hσ hω hnormal hfaith hone _ _
    (fun n m h a => normalizedInclusion_commutes M E hE h a) _ hdiffuse
  · intro b hb
    apply hirr b
    intro n a
    have hh := hb n ((matrixIndexEquiv (normalizedIndex M E n)).symm a)
    change (E n).hom ((matrixIndexEquiv (normalizedIndex M E n))
      ((matrixIndexEquiv (normalizedIndex M E n)).symm a))*b=
      b*(E n).hom ((matrixIndexEquiv (normalizedIndex M E n))
      ((matrixIndexEquiv (normalizedIndex M E n)).symm a)) at hh
    simpa only [StarAlgEquiv.apply_symm_apply] using hh
  · intro n a
    exact hstage n (matrixIndexEquiv (normalizedIndex M E n) a)
  · convert hgrow using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact_mod_cast normalizedSize_succ M E n

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages_oai := @OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages_oai
