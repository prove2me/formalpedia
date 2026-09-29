-- Prove2me | solution 1 for LanglandsTunnell.exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ed69992e-2e80-5324-9b6b-316dad09634b

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Theorems.Thm_LanglandsTunnell_exists_resolventSignChar_sylowH
import Theorems.Thm_LanglandsTunnell_not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH
p2m_attr_erase "instance" "LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldC8H_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldC8H LanglandsTunnell.algebra_fixFldSylowH_fixFldC8H LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (h₆seed : (AutomorphicForm.formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
          (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) Φ)).AgreesAwayFromFinite
        ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map AutomorphicForm.iotaZsqrtdNegTwo)) :
    ∃ (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (χ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → ℂ),
      (∀ v ∉ S₀, χ v * χ v = 1) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S₀ →
        (χ v = 1 ↔ ∀ 𝔓 : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))),
          𝔓.under (NumberField.RingOfIntegers ℚ) = v →
            (𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2)) ∧
      ¬ Φ.AgreesAwayFromFinite (Φ.twist χ) := by

  obtain ⟨S₀, χ, hdet, hχ2, _hsplit, hlink, _hunr⟩ := LanglandsTunnell.exists_resolventSignChar_sylowH e

  exact ⟨S₀, χ, hχ2, hlink,
    LanglandsTunnell.not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH e Φ h₆seed S₀ χ hdet⟩

end S_LanglandsTunnell_exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH
end P2MW
export P2MW.S_LanglandsTunnell_exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH (solution)
