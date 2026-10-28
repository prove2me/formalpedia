-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.amplifiedStage_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:59:38.531323+00:00
-- url     : https://prove2.me/submissions/4c85fb38-1cfd-48d6-8a99-0d417de3fb72

import Mathlib
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_OperatorAmplification_amplifiedStage_diagonal

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerStage
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

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerStageDecidableEq
lemma scalarMatrixHom_single (i j : ι) :
    (scalarMatrixHom ι i₀ M (Matrix.single i j 1):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=matrixUnit ι i j := by
  simp [scalarMatrixHom,MatrixUnits.representation,Matrix.single_apply,ite_and]

variable (E : MatrixTower.Stage M)

lemma amplifiedStage_scalar (a : Matrix ι ι ℂ) :
    scalarMatrixHom ι i₀ M a∈(amplifiedStage ι i₀ M E).hom.range := by
  have hh := MatrixTensor.left_mem (A := matrixVonNeumann ι i₀ M)
    (I := ι) (J := E.I) (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp E.hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x (E.hom y)) a
  obtain ⟨b,hb⟩ := hh
  exact ⟨b,hb⟩

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerGeometry
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

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

variable (E : ℕ → MatrixTower.Stage M)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerGeometryIndexDecidableEq
lemma amplifiedStage_irreducible_oai
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ c : ℂ,a=c • (1:M))
    (Z : matrixVonNeumann ι i₀ M)
    (hZ : ∀ n b,(amplifiedStage ι i₀ M (E n)).hom b*Z=Z*(amplifiedStage ι i₀ M (E n)).hom b) :
    ∃ c : ℂ,Z=algebraMap ℂ (matrixVonNeumann ι i₀ M) c := by
  have hs (i j : ι) : matrixUnit (H:=H) ι i j*(Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*matrixUnit ι i j := by
    obtain ⟨b,hb⟩ := amplifiedStage_scalar ι i₀ M (E 0) (Matrix.single i j 1)
    change (amplifiedStage ι i₀ M (E 0)).hom b=scalarMatrixHom ι i₀ M (Matrix.single i j 1) at hb
    have hh := hZ 0 b
    rw [hb] at hh
    have hh' := congrArg (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype hh
    change (scalarMatrixHom ι i₀ M (Matrix.single i j 1):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
      (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
      (scalarMatrixHom ι i₀ M (Matrix.single i j 1):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) at hh'
    rw [scalarMatrixHom_single] at hh'
    exact hh' 
  let a : M := ⟨entry ι (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i₀ i₀,
    (mem_matrixVonNeumann ι i₀ M Z).mp Z.property i₀ i₀⟩
  have ha (n : ℕ) (b : Matrix (E n).I (E n).I ℂ) : (E n).hom b*a=a*(E n).hom b := by
    obtain ⟨c,hc⟩ := amplifiedStage_diagonal ι i₀ M (E n) b
    apply Subtype.ext
    apply entry_commutes ι (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    change (amplifiedStage ι i₀ M (E n)).hom c=diagonalHom ι i₀ M ((E n).hom b) at hc
    have hh := hZ n c
    rw [hc] at hh
    exact congrArg (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype hh
  obtain ⟨c,hc⟩ := hirr a ha
  refine ⟨c,?_⟩
  apply Subtype.ext
  have hdiag := diagonal_of_matrixUnits ι i₀ (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) hs
  change (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=c • 1
  rw [hdiag]
  change diagonal (H:=H) ι (a:H →L[ℂ] H)=_
  rw [hc]
  change diagonal (H:=H) ι (c • 1)=c • 1
  rw [map_smul,map_one]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.amplifiedStage_irreducible_oai := @OAI.Kadison.OperatorAmplification.amplifiedStage_irreducible_oai
