-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.val_det_of_mem_unitGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:48.952701+00:00
-- url     : https://prove2.me/submissions/2b81c835-7539-45b1-94f3-c9df53668e81

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
theorem _root_.solution {g : GL (Fin n) F} (hg : g ∈ unitGL (n := Fin n) F) :
    valuation F (g : Matrix (Fin n) (Fin n) F).det = 1 := by
  obtain ⟨g₀, rfl⟩ := hg
  have hdet : ∀ h : GL (Fin n) (Valuation.integer (valuation F)),
      ((Matrix.GeneralLinearGroup.map (Valuation.integer (valuation F)).subtype h : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F).det =
        (((h : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det :
          Valuation.integer (valuation F)) : F) := fun h =>
    ((Valuation.integer (valuation F)).subtype.map_det _).symm
  rw [hdet]
  have h1 : valuation F (((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) ≤ 1 :=
    ((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det).2
  have h2 : valuation F ((((g₀⁻¹ : GL (Fin n) (Valuation.integer (valuation F))) : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) ≤ 1 :=
    (((g₀⁻¹ : GL (Fin n) (Valuation.integer (valuation F))) : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det).2
  have h3 : (((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) *
      ((((g₀⁻¹ : GL (Fin n) (Valuation.integer (valuation F))) : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) = 1 := by
    rw [← Subring.coe_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
    simp
  have h4 := congrArg (valuation F) h3
  rw [map_mul, map_one] at h4
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero F) = _ := h4.symm
    _ ≤ valuation F (((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) * 1 :=
        mul_le_mul' le_rfl h2
    _ = _ := mul_one _
end GlobalTheory.CompanionTheory.TwContraction
