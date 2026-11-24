-- Prove2me | solution 1 for GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:15.192604+00:00
-- url     : https://prove2.me/submissions/76559a4e-2e5d-4c5d-b70a-b1a44df56001

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoefficientIdealFamilyEqTopOfDisjoint
import Theorems.Thm_GlobalTheory_NormSheafDescent_normIdeal_top
import Theorems.Thm_GlobalTheory_NormSheafDescent_ideal_eq_top_of_forall_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent
namespace GlobalTheory.NormSheafDescent
theorem _root_.solution : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  intro Y Z π _ _ hK hfd I U hU
  unfold famIdeal
  split_ifs with h
  · have hV : I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ = ⊤ :=
      ideal_eq_top_of_forall_not_mem I _ (fun y hy hyV => hU y hy hyV)
    simp only [hV]
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    exact normIdeal_top _ _ _ _
  · rfl
end GlobalTheory.NormSheafDescent
