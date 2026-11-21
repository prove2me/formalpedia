-- Prove2me | solution 1 for JardenShami.power_lt_of_isInaccessible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:22.866927+00:00
-- url     : https://prove2.me/submissions/b0caaa2a-ddf3-46cc-93d8-a99cfcb74c95

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {κ lam μ : Cardinal.{w}} (hκ : κ.IsInaccessible)
    (hlam : lam < κ) (hμ : μ < κ) : lam ^ μ < κ := by
  calc lam ^ μ ≤ (2 ^ lam) ^ μ := Cardinal.power_le_power_right (Cardinal.cantor lam).le
    _ = 2 ^ (lam * μ) := Cardinal.power_mul.symm
    _ < κ := hκ.isStrongPrelimit (Cardinal.mul_lt_of_lt hκ.aleph0_lt.le hlam hμ)
end JardenShami
