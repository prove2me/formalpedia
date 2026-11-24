-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.vt_mul_io_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:30:08.548921+00:00
-- url     : https://prove2.me/submissions/c3dfe5a5-84a4-4fa4-ab0c-40d658224397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Theorems.Thm_P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc


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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution (g : N.Gt) (w χ : N.X) :
    ((N.ψ w * g.s w : Oˣ) : O) * N.vt (g * N.io w) χ = N.vt g (χ + w) := by
  have e : N.c χ * (g * N.io w).b = N.c (χ + w) * g.b := by
    rw [Gt.mul_b, io_b, N.c_add, mul_assoc, mul_comm g.b]
  rw [vt, vt, e, ← mul_assoc, ← Units.val_mul]
  congr 2
  have a := congrArg Additive.ofMul (g.mult χ w)
  rw [Gt.mul_s, io_s, io_b, N.ψ_add, N.τ_symm w χ, N.cub.s12 (N.c χ) g.b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) -a
end GlobalTheory.Ex.NumD
