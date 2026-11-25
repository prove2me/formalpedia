-- Prove2me | solution 1 for GlobalTheory.LevelDict.isLevel_thetaChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:01.074251+00:00
-- url     : https://prove2.me/submissions/615a1e4c-3e70-41c6-bdc9-938f1fb94138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
import Theorems.Thm_GlobalTheory_TorusAlg_ofRealVec_re
import Theorems.Thm_GlobalTheory_TorusAlg_thetaChar_level


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict
namespace GlobalTheory.LevelDict
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    IsLevel τ a b 1 (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := TorusAlg.thetaChar_level hs hp hab.1 hab.2
  have hm : thetaChar τ a b ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [h1]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar, TorusAlg.ofRealVec_re hab.1, TorusAlg.ofRealVec_re hab.2] at hm
  refine ⟨⟨hm.1, fun m n z => ?_⟩, h0⟩
  have h := hm.2 n m z
  rw [add_assoc, add_comm (τ.mulVec _), ReciprocityTheory.PTheta.eC, ReciprocityTheory.PTheta.eC, ← Complex.exp_add] at h
  refine h.trans ?_
  rw [pow_one]
  congr 2
  unfold ReciprocityTheory.PTheta.ofIntVec
  push_cast
  ring
end GlobalTheory.LevelDict
