-- Prove2me | solution 1 for GlobalTheory.EigenCongruence.pderiv_mem_coeffIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:56.092692+00:00
-- url     : https://prove2.me/submissions/5170dcb2-17a0-4c0e-9d95-e77d6c416d82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.EigenCongruence
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.EigenCongruence
theorem _root_.solution {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R}
    (hg : g ∈ coeffIdeal I) (s : σ) : pderiv R s g ∈ coeffIdeal I := by
  intro mo
  rw [coeff_pderiv]
  exact I.mul_mem_right _ (hg _)
end GlobalTheory.EigenCongruence
