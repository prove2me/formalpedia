-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.unit_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:51.581624+00:00
-- url     : https://prove2.me/submissions/0ce69487-2285-4b60-95c7-5e44309abcd9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution {n l : ℕ} (h : l ≤ n) (W : Matrix (Fin n) (Fin n) E) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0) :
    IsUnit (W.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [Matrix.twoBlockTriangular_det W (fun i => (i : ℕ) < l)
    (fun i hi j hj => hc i j (by omega) hj)] at hW
  have h1 := isUnit_of_mul_isUnit_left hW
  let e : Fin l ≃ {i : Fin n // (i : ℕ) < l} :=
    { toFun := fun a => ⟨Fin.castLE h a, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1
end GlobalTheory.OrbitDenom
