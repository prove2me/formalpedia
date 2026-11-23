-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:24.241744+00:00
-- url     : https://prove2.me/submissions/dafa6053-54c3-4f75-b66c-e9f2f34c6fcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Theorems.Thm_GlobalTheory_SW_UniSp_vecMul_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.UniSp
theorem _root_.solution (M : Ψ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) (p q : QI E N) :
    (Sm Ψ N * blockDiagonal M * (Sm Ψ N)ᵀ) p q = ∑ τ : Ψ,
      (fun i => Sm Ψ N p (i, τ)) ᵥ* M τ ⬝ᵥ fun i => Sm Ψ N q (i, τ) := by
  change ∑ x, (Sm Ψ N p ᵥ* blockDiagonal M) x * Sm Ψ N q x = _
  simp only [vecMul_bd]
  rw [Fintype.sum_prod_type_right]
  rfl
end GlobalTheory.SW.UniSp
