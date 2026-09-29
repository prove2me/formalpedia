-- Prove2me | solution 1 for HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e87933ed-5a53-596b-8dd1-e86c709656aa

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaIota
import Theorems.Thm_HeckeEis_heckeOperatorHom_eq_of_kernelPair
import Theorems.Thm_Ihara_ihara_hom_factor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway"
p2m_attr_erase "simp" "Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply"

theorem solution (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : Type*) [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) = 0)
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ ∧ HeckeEis.heckeOperatorHom N ℓ A ψ = (ℓ + 1) • ψ :=
  HeckeEis.heckeOperatorHom_eq_of_kernelPair @Ihara.ihara_hom_factor N q hq hqN A h2 h3 φ ψ hker hℓ hℓN

end S_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel
end P2MW
export P2MW.S_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel (solution)
