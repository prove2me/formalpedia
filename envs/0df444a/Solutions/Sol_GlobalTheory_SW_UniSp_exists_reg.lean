-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.exists_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:36.592969+00:00
-- url     : https://prove2.me/submissions/76ebc367-5bec-405a-a683-2f504ceb940a

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
theorem _root_.solution (X : Matrix (Fin N) (Fin N) E) : ∃ R : Matrix (QI E N) (QI E N) ℚ,
    qm R * Sm Ψ N = Sm Ψ N * blockDiagonal fun τ : Ψ => dl (X.map τ.1) := by
  refine ⟨Matrix.of fun p q =>
    (Module.finBasis ℚ E).repr (Module.finBasis ℚ E p.2 * X p.1 q.1) q.2, ?_⟩
  ext p ⟨i, τ⟩
  change _ = (Sm Ψ N p ᵥ* _) _
  rw [vecMul_bd]
  have key : ∀ x : E, ∑ j, (((Module.finBasis ℚ E).repr x j : ℚ) : ℂ) *
      τ.1 (Module.finBasis ℚ E j) = τ.1 x := fun x => by
    conv_rhs => rw [← (Module.finBasis ℚ E).sum_repr x]
    simp [Algebra.smul_def]
  have key' : ∀ x : E, ∑ j, (((Module.finBasis ℚ E).repr x j : ℚ) : ℂ) *
      conj (τ.1 (Module.finBasis ℚ E j)) = conj (τ.1 x) := fun x => by
    rw [← key x]
    simp
  rcases i with b | b
  · simp [Matrix.mul_apply, qm, Sm, Fintype.sum_prod_type_right, vecMul, dotProduct, dl, key, -Module.Basis.repr_self]
  · simp [Matrix.mul_apply, qm, Sm, Fintype.sum_prod_type_right, vecMul, dotProduct, dl, key', -Module.Basis.repr_self]
end GlobalTheory.SW.UniSp
