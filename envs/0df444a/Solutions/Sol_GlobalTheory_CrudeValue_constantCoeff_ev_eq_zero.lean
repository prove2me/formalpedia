-- Prove2me | solution 1 for GlobalTheory.CrudeValue.constantCoeff_ev_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:06:16.125956+00:00
-- url     : https://prove2.me/submissions/1e052c21-0338-4312-9556-e3a59565e369

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors

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
open GlobalTheory GlobalTheory.CrudeValue
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.CrudeValue
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt k n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have ha' : ∀ q : Fin m × Fin d, constantCoeff ((fun q : Fin m × Fin d => a q.1 q.2) q) = 0 :=
    fun q => ha q.1 q.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
    (hasSubst_of_constantCoeff_zero ha') ha' hf
end GlobalTheory.CrudeValue
