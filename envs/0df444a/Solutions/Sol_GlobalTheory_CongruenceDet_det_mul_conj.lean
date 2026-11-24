-- Prove2me | solution 1 for GlobalTheory.CongruenceDet.det_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:32.578341+00:00
-- url     : https://prove2.me/submissions/eca07a3b-d5b8-4dbe-bb58-246c60396dd4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceDet
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory.CongruenceDet
namespace _root_.GlobalTheory.CongruenceDet
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (G g : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (g *ᵥ x) (g *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) :
    g.det * IsCMField.complexConj E g.det = 1 := by
  classical
  let c : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hherm : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ (c ∘ y)) := by
    intro x y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, c]
  have hmat : gᵀ * G * g.map c = G := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    have hcs : c ∘ (Pi.single j (1 : E)) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j <;> simp [Pi.single_apply, hk]
    have hgs : c ∘ (g *ᵥ Pi.single j 1) = g.map c *ᵥ (c ∘ Pi.single j 1) := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    rw [hherm, hherm, hgs, hcs, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [Matrix.mul_assoc] using this
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at hdet
  have e : c g.det = IsCMField.complexConj E g.det := rfl
  apply mul_right_cancel₀ hG
  rw [← e]
  linear_combination hdet
end _root_.GlobalTheory.CongruenceDet
end GlobalTheory.CongruenceDet
