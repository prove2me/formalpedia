-- Prove2me | solution 1 for GlobalTheory.UDense.map_inv_field_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:30.372954+00:00
-- url     : https://prove2.me/submissions/d13740a3-9d83-42b4-af33-943d914c1d1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.UDense
namespace GlobalTheory.UDense
theorem _root_.solution {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]
end GlobalTheory.UDense
