-- Prove2me | solution 1 for GlobalTheory.JetOnly.coeff_iterate_Dof_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:07:07.418378+00:00
-- url     : https://prove2.me/submissions/eab472cb-f63d-4c96-9853-f4f29e890cef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Theorems.Thm_GlobalTheory_JetOnly_coeff_Dof_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.JetOnly
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.JetOnly
theorem _root_.solution (F : Fin d → PS k 2 d) (v : Fin d → k) (r : ℕ) :
    ∀ (n : ℕ) (f g : PS k 1 d),
      (∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n →
        coeff mo ((Dof F v)^[r] f) = coeff mo ((Dof F v)^[r] g) := by
  induction r with
  | zero => intro n f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro n f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih n _ _ (coeff_Dof_congr F v (n + r) f g h) mo hmo
end GlobalTheory.JetOnly
