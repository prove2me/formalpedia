-- Prove2me | solution 1 for GlobalTheory.KeyPow.exists_thetaLaw_zero_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:29.381861+00:00
-- url     : https://prove2.me/submissions/ea930c97-6d26-4db7-9d5f-bccf30315404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaLawMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsSymmMulVecAddDiagModTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsThetaLawZeroOfEven
import Theorems.Thm_GlobalTheory_KeyPow_thetaLaw_generators
import Theorems.Thm_GlobalTheory_KeyPow_thetaLaw_mul
import Theorems.Thm_GlobalTheory_exists_isSymm_mulVec_add_diag_mod_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem_sp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KeyPow
open Matrix ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace GlobalTheory.KeyPow
theorem _root_.solution (hInv : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement) (g : ℕ)
    (n n' : Fin g → ℤ) (h : Even (n ⬝ᵥ n')) :
    ∃ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, GlobalTheory.KeyPow.ThetaLaw g sp n n' 0 0 := by
  obtain ⟨S, hS, hd⟩ := GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two g n n' h
  have h1 : ThetaLaw g (spTransl S) n n' n 0 :=
    (thetaLaw_generators hInv g n 0).1 S n' hS fun i => by simpa using hd i
  have h2 : ThetaLaw g (Matrix.J (Fin g) ℤ) n 0 0 n := (thetaLaw_generators hInv g 0 n).2
  have hD : (Matrix.diagonal n).IsSymm := Matrix.isSymm_diagonal _
  have h3 : ThetaLaw g (spTransl (Matrix.diagonal n)) 0 n 0 0 :=
    (thetaLaw_generators hInv g 0 0).1 _ n hD fun i => by simp
  have m1 : spTransl S ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hS
  have m2 : Matrix.J (Fin g) ℤ ∈ Matrix.symplecticGroup (Fin g) ℤ := SymplecticGroup.J_mem _ _
  have m3 : spTransl (Matrix.diagonal n) ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hD
  exact ⟨_, mul_mem m3 (mul_mem m2 m1), thetaLaw_mul g _ _ _ _ _ _ _ _ m3 (mul_mem m2 m1)
    (thetaLaw_mul g _ _ _ _ _ _ _ _ m2 m1 h1 h2) h3⟩
end GlobalTheory.KeyPow
