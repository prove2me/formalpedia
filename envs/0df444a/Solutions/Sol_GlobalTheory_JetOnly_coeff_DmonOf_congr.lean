-- Prove2me | solution 1 for GlobalTheory.JetOnly.coeff_DmonOf_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:16.006976+00:00
-- url     : https://prove2.me/submissions/a564f794-cf47-48b6-b20b-1dab8e034d9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Theorems.Thm_GlobalTheory_JetOnly_coeff_foldr_Dof_congr

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
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (m : ι →₀ ℕ) (f g : PS k 1 d) (n : ℕ)
    (h : ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ n + m.degree → coeff mo f = coeff mo g)
    (mo : Fin 1 × Fin d →₀ ℕ) (hmo : mo.degree ≤ n) :
    coeff mo (DmonOf F u m f) = coeff mo (DmonOf F u m g) := by
  unfold DmonOf
  refine coeff_foldr_Dof_congr F u m f g _ n (fun mo' h' => h mo' ?_) mo hmo
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum] at h'
end GlobalTheory.JetOnly
