-- Prove2me | solution 1 for HeckeEis.heckeOperatorHom_eq_of_factorsThroughEntry
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/57ba0d94-7175-56e2-a523-a514d015e8c5

import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_heckeOperatorHom_eq_of_factorsThroughEntry

theorem solution (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hfac : ∀ γ δ : CongruenceSubgroup.Gamma0 N,
      CongruenceSubgroup.Gamma0Map N γ = CongruenceSubgroup.Gamma0Map N δ →
        φ (Additive.ofMul γ) = φ (Additive.ofMul δ)) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ := by
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.nsmul_apply, ← ofMul_toMul x]
  exact HeckeEis.heckeOperatorHom_apply_of_factorsThroughEntry N A hℓ hℓN φ hfac x.toMul

end S_HeckeEis_heckeOperatorHom_eq_of_factorsThroughEntry
end P2MW
export P2MW.S_HeckeEis_heckeOperatorHom_eq_of_factorsThroughEntry (solution)
