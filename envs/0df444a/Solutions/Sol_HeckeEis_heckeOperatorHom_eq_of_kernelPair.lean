-- Prove2me | solution 1 for HeckeEis.heckeOperatorHom_eq_of_kernelPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5d1ce489-1965-5480-979a-456f24a1b634

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaIota
import Theorems.Thm_HeckeEis_heckeOperatorHom_comp_gamma0UnitsChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_heckeOperatorHom_eq_of_kernelPair

universe u

theorem solution
    (ihara : ∀ (N q : ℕ) (_ : q.Prime) (_ : ¬ q ∣ N) (A : Type u) [AddCommGroup A]
      (_ : ∀ a : A, a + a = 0 → a = 0) (_ : ∀ a : A, a + a + a = 0 → a = 0)
      (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
      (_ : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) = 0),
      (∃ χ : Additive (ZMod N)ˣ →+ A, φ = χ.comp (Ihara.gamma0UnitsChar N)) ∧
      (∃ χ : Additive (ZMod N)ˣ →+ A, ψ = χ.comp (Ihara.gamma0UnitsChar N)))
    (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : Type u) [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) = 0)
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ ∧ HeckeEis.heckeOperatorHom N ℓ A ψ = (ℓ + 1) • ψ := by
  obtain ⟨⟨χ₁, rfl⟩, ⟨χ₂, rfl⟩⟩ := ihara N q hq hqN A h2 h3 φ ψ hker
  exact ⟨HeckeEis.heckeOperatorHom_comp_gamma0UnitsChar N A hℓ hℓN χ₁,
    HeckeEis.heckeOperatorHom_comp_gamma0UnitsChar N A hℓ hℓN χ₂⟩

end S_HeckeEis_heckeOperatorHom_eq_of_kernelPair
end P2MW
export P2MW.S_HeckeEis_heckeOperatorHom_eq_of_kernelPair (solution)
