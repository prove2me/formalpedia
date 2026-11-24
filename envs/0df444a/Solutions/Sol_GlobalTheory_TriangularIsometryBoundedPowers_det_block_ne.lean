-- Prove2me | solution 1 for GlobalTheory.TriangularIsometryBoundedPowers.det_block_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:53.331863+00:00
-- url     : https://prove2.me/submissions/2ebb0a35-2e66-4f54-974d-c2c9a1e57230

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TriangularIsometryBoundedPowers
open Matrix
namespace GlobalTheory.TriangularIsometryBoundedPowers
theorem _root_.solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    (B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n)).det ≠ 0 := by
  have h := hB (Fin.castSucc j)
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor at h
  let e : Fin ((Fin.castSucc j : Fin (n + 1)) : ℕ) ≃ {c : Fin n // c < j} :=
    { toFun := fun k => ⟨Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt) k, by
        rw [Fin.lt_def]
        exact k.isLt⟩
      invFun := fun c => ⟨c.1.val, c.2⟩
      left_inv := fun k => Fin.ext rfl
      right_inv := fun c => Subtype.ext (Fin.ext rfl) }
  have e2 : (B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n)).submatrix e e =
      B.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc j).isLt)) := rfl
  rw [← Matrix.det_submatrix_equiv_self e, e2]
  exact h
end GlobalTheory.TriangularIsometryBoundedPowers
