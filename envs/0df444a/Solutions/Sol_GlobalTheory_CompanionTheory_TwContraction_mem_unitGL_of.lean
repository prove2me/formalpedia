-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.mem_unitGL_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:46.33483+00:00
-- url     : https://prove2.me/submissions/5dc9a407-7594-4624-87bd-a8848eeb83b4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution (g : GL (Fin n) F) (h0 : ∀ i l, valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ 1)
    (hd : valuation F (g : Matrix (Fin n) (Fin n) F).det = 1) : g ∈ unitGL (n := Fin n) F := by
  set O := Valuation.integer (valuation F) with hO
  let M₀ : Matrix (Fin n) (Fin n) O := fun i l => ⟨(g : Matrix (Fin n) (Fin n) F) i l, h0 i l⟩
  have hmap : O.subtype.mapMatrix M₀ = (g : Matrix (Fin n) (Fin n) F) := by
    ext i l; rfl
  have hdet : ((M₀.det : O) : F) = (g : Matrix (Fin n) (Fin n) F).det := by
    have := O.subtype.map_det M₀
    rw [hmap] at this
    exact this
  have hne : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hinv : valuation F ((g : Matrix (Fin n) (Fin n) F).det)⁻¹ ≤ 1 := by
    rw [map_inv₀, hd, inv_one]
  have hu : IsUnit M₀.det := by
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) ?_
    apply Subtype.ext
    show ((M₀.det : O) : F) * ((g : Matrix (Fin n) (Fin n) F).det)⁻¹ = 1
    rw [hdet, mul_inv_cancel₀ hne]
  refine ⟨Matrix.GeneralLinearGroup.mk'' M₀ hu, Units.ext ?_⟩
  ext i l
  rfl
end GlobalTheory.CompanionTheory.TwContraction
