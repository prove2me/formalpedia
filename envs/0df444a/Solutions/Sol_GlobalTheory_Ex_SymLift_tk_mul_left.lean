-- Prove2me | solution 1 for GlobalTheory.Ex.SymLift.tk_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:17.236118+00:00
-- url     : https://prove2.me/submissions/e3a7850c-ee57-4a6f-9433-20ae23be9f4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add


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
theorem _root_.solution {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have a := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b p''] at a
  change p.1.2.s p''.1.1.toAdd * p'.1.2.s p''.1.1.toAdd / N.θ (N.c p''.1.1.toAdd) p.1.2.b p'.1.2.b *
    cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  replace a := congrArg Additive.ofMul a
  apply Additive.ofMul.injective
  simp only [NumD.tk, ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) a
end GlobalTheory.Ex.SymLift
