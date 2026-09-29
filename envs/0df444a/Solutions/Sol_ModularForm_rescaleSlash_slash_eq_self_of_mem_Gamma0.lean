-- Prove2me | solution 1 for ModularForm.rescaleSlash_slash_eq_self_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4d914d8c-8437-5e5d-a1ad-da9e9d917a2e

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0

open scoped ModularForm

theorem solution {R M d : ℕ} [NeZero M]
    (hdRM : d * R ∣ M) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (SlashAction.map k (ModularForm.heckeDiagMatrix d) f)
      = SlashAction.map k (ModularForm.heckeDiagMatrix d) f :=
  FreyPackage.ModMCarrier.rescaleSlash_slash hdRM k hf hγ

end S_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0
end P2MW
export P2MW.S_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0 (solution)
