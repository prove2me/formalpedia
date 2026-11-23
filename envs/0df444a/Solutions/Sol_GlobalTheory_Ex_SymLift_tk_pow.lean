-- Prove2me | solution 1 for GlobalTheory.Ex.SymLift.tk_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:17.833412+00:00
-- url     : https://prove2.me/submissions/93510c00-554b-41f7-96b4-66721ea7474a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.SymLift
theorem _root_.solution {k : ℕ} (p p' : N.QT k) :
    N.tk p p' ^ k = N.τ p.1.1.toAdd p'.1.1.toAdd *
      (cubN N.θ k 1 p.1.2.b (p'.1.2.b ^ k) * cubN N.θ k 1 p'.1.2.b p.1.2.b ^ k) := by
  have a := NumD.Gt.pow_s p.1.2 k p'.1.1.toAdd
  rw [N.mem_QT.1 p.2, NumD.io_s, ← N.QT_pow_b p'] at a
  rw [NumD.tk, mul_pow, ← a, mul_assoc]
end GlobalTheory.Ex.SymLift
