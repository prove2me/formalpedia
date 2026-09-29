-- Prove2me | solution 1 for HeckeEis.heckeOperatorHom_apply_of_factorsThroughEntry
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4b321126-7b7c-54fe-ab1c-2dc65fad6d56

import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_HeckeEis_heckeOperatorHom_apply_of_conj_invariant
import Theorems.Thm_ModularCurve_index_heckeUpper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry

theorem solution (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hfac : ∀ γ δ : CongruenceSubgroup.Gamma0 N,
      CongruenceSubgroup.Gamma0Map N γ = CongruenceSubgroup.Gamma0Map N δ →
        φ (Additive.ofMul γ) = φ (Additive.ofMul δ))
    (g : CongruenceSubgroup.Gamma0 N) :
    HeckeEis.heckeOperatorHom N ℓ A φ (Additive.ofMul g) = (ℓ + 1) • φ (Additive.ofMul g) := by
  rw [HeckeEis.heckeOperatorHom_apply_of_conj_invariant N ℓ φ (fun γ => hfac _ _ rfl) (Additive.ofMul g),
    ModularCurve.index_heckeUpper hℓ hℓN]

end S_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry
end P2MW
export P2MW.S_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry (solution)
