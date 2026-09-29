-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPic0_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bcbeae95-0d86-50ee-aaf9-d873a7ccd67d

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPic0_apply

p2m_open "ModularCurve ModularCurve.CharPModel AlgebraicCurve"

theorem solution (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hpres : fm.SpDivPreservesPrincipal hred dataAll hsep) :
    ∀ D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ModularCurve.modularFunctionFieldBar N),
    fm.spPic0 hred dataAll hsep (AlgebraicCurve.Pic0.mk D)
      = AlgebraicCurve.Pic0.mk
          ⟨fm.spDiv hred dataAll hsep ↑D, hpres.1 ↑D D.2⟩ := by
  intro D
  simp only [FibreModel.spPic0]
  rw [dif_pos hpres]
  rfl

end S_ModularCurve_CharPModel_FibreModel_spPic0_apply
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPic0_apply (solution)
