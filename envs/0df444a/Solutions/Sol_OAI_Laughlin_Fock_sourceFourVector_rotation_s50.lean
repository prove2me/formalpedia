-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceFourVector_rotation_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:05:50.600198+00:00
-- url     : https://prove2.me/submissions/2068d342-7e8d-431a-9bdb-fdb9b590b05b

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Rotation_physicalPairInclusion_SU2_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem create_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    create i * create j + create j * create i = 0 := by
  refine LinearMap.ext fun x => ?_
  change ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * (ExteriorAlgebra.ι ℂ (mode i) * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbital_sum_modes (Q : ℕ) (v : Orbital Q) : v = ∑ i, v i • mode i := by
  funext j
  simp [mode,Pi.single_apply]

theorem create_exteriorRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) (x : Space Q) :
    exteriorRotation Q g (create i x) =
      ∑ j, sourceSpinRepresentation Q g j i • create j (exteriorRotation Q g x) := by
  change ExteriorAlgebra.map (orbitalRotation Q g) (ExteriorAlgebra.ι ℂ (mode i)*x) = _
  rw [map_mul,ExteriorAlgebra.map_apply_ι,orbital_sum_modes Q (orbitalRotation Q g (mode i))]
  simp only [map_sum,map_smul,Finset.sum_mul,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  have he : orbitalRotation Q g (mode i) j = sourceSpinRepresentation Q g j i := by
    simp [orbitalRotation,mode,Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [he]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_ExteriorRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix Kronecker

theorem exteriorRotation_pair_basis (Q : ℕ) (g : SourceSU2) (i j : Fin (Q+1)) :
    exteriorRotation Q g (create i (create j (1 : Space Q))) =
      ∑ k : Spin.SpinIndex Q Q, (sourceSpinRepresentation Q g k.1 i * sourceSpinRepresentation Q g k.2 j) •
        create k.1 (create k.2 (1 : Space Q)) := by
  rw [create_exteriorRotation,create_exteriorRotation]
  simp only [map_one,map_sum,map_smul,Finset.smul_sum,smul_smul,Fintype.sum_prod_type]

theorem pairExterior_rotation (Q : ℕ) (g : SourceSU2) (v : Spin.SpinIndex Q Q → ℂ) :
    exteriorRotation Q g (pairExterior Q v) =
      pairExterior Q ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ v) := by
  simp only [pairExterior,map_sum,map_smul,exteriorRotation_pair_basis,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec,dotProduct,Matrix.kroneckerMap,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairExterior_sum {I : Type*} [Fintype I] (Q : ℕ) (v : I → Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (∑ a, v a) = ∑ a, pairExterior Q (v a) := by
  simp only [pairExterior,Finset.sum_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem pairExterior_smul (Q : ℕ) (c : ℂ) (v : Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (c • v) = c • pairExterior Q v := by
  simp only [pairExterior,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]

theorem sourcePairVector_pairExterior (Q p : ℕ) :
    sourcePairVector Q p = (Real.sqrt 2 : ℂ)⁻¹ •
      pairExterior Q (fun i => (pairCoefficient Q p i.1 i.2 : ℂ)) := by
  simp only [sourcePairVector,pairExterior,Fintype.sum_prod_type,Finset.smul_sum,smul_smul,
    div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,mul_comm]

theorem sourcePairVector_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) :
    exteriorRotation Q g (sourcePairVector Q p.val) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p • sourcePairVector Q q.val := by
  have hc : ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ
      (fun i => (pairCoefficient Q p.val i.1 i.2 : ℂ))) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p •
        (fun i : Spin.SpinIndex Q Q => (pairCoefficient Q q.val i.1 i.2 : ℂ)) := by
    funext i
    have h := congrFun (congrFun (physicalPairInclusion_SU2_s50 Q hQ g) i) p
    simpa only [physicalPairInclusion,Spin.pairInclusion,Matrix.map_apply,Matrix.mul_apply,
      Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using h
  rw [sourcePairVector_pairExterior,map_smul,pairExterior_rotation,hc,pairExterior_sum]
  simp only [pairExterior_smul,Finset.smul_sum,sourcePairVector_pairExterior]
  apply Finset.sum_congr rfl
  intro q hq
  exact smul_comm _ _ _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_FockCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix Kronecker

theorem antisymmetric_exterior_sum (Q : ℕ) (f : SpinIndex Q Q → Space Q)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (a : SpinIndex Q Q → ℂ) :
    (∑ i, a i • f i) = ∑ i : WedgePairIndex Q, (a i.val-a i.val.swap) • f i.val := by
  apply (occupationBasis Q).repr.injective
  ext A
  have h := antisymmetric_ordered_sum Q
    (fun i => (occupationBasis Q).repr (f i) A) a (by
      intro i j; rw [hf,map_neg]; rfl)
  simpa only [map_sum,map_smul,Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,mul_comm] using h

theorem wedgePairVector_rotation (Q : ℕ) (g : SourceSU2) (i : WedgePairIndex Q) :
    exteriorRotation Q g (wedgePairVector Q i) =
      ∑ j, wedgePairRepresentation Q g j i • wedgePairVector Q j := by
  have ha (i j : Fin (Q+1)) : create j (create i (1 : Space Q)) = -create i (create j 1) := by
    have h := LinearMap.congr_fun (create_anticommute j i) (1 : Space Q)
    exact eq_neg_of_add_eq_zero_left h
  rw [wedgePairVector,exteriorRotation_pair_basis]
  have h := antisymmetric_exterior_sum Q
    (fun k : SpinIndex Q Q => create k.1 (create k.2 (1 : Space Q))) ha
    (fun j : SpinIndex Q Q => sourceSpinRepresentation Q g j.1 i.val.1 *
      sourceSpinRepresentation Q g j.2 i.val.2)
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  change (_ - _) • wedgePairVector Q j = _ • wedgePairVector Q j
  congr 1
  dsimp [wedgePairRepresentation,wedgePairMatrix]
  ring

theorem sourceFourVector_rotation_s50_oai (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) (i : FourWedgeIndex Q) :
    exteriorRotation Q g (sourceFourVector Q i) =
      ∑ j, fourBodySpinRepresentation Q g j i • sourceFourVector Q j := by
  rw [sourceFourVector,map_mul,sourcePairVector_rotation Q hQ,wedgePairVector_rotation]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Fintype.sum_prod_type,
    fourBodySpinRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,Matrix.kroneckerMap,
    Matrix.of_apply,sourceFourVector]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceFourVector_rotation_s50_oai := @OAI.Laughlin.Fock.sourceFourVector_rotation_s50_oai
