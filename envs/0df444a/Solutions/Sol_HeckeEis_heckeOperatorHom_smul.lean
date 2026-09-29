-- Prove2me | solution 1 for HeckeEis.heckeOperatorHom_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ea0e106c-5370-5874-a1f2-6519951fe9ec

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_heckeOperatorHom_smul

open CongruenceSubgroup Subgroup

theorem solution (N ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    {R : Type*} [Monoid R] [DistribMulAction R A] (r : R)
    (φ : Additive ↥(Gamma0 N) →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (r • φ) =
      r • HeckeEis.heckeOperatorHom N ℓ A φ := by
  ext g
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  show (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, (r • φ) _) =
    r • (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, φ _)
  simp only [AddMonoidHom.smul_apply]
  exact Finset.smul_sum.symm

end S_HeckeEis_heckeOperatorHom_smul
end P2MW
export P2MW.S_HeckeEis_heckeOperatorHom_smul (solution)
