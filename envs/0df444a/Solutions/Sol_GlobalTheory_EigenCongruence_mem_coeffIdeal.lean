-- Prove2me | solution 1 for GlobalTheory.EigenCongruence.mem_coeffIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:42:47.315957+00:00
-- url     : https://prove2.me/submissions/51145f6f-6eaa-4481-a4df-2ae58b1e3c67

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
theorem _root_.solution {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R} :
    g ∈ coeffIdeal I ↔ ∀ mo, coeff mo g ∈ I := Iff.rfl
end GlobalTheory.EigenCongruence
