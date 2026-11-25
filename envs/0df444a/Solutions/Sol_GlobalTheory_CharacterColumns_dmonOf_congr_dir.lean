-- Prove2me | solution 1 for GlobalTheory.CharacterColumns.dmonOf_congr_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:52.153194+00:00
-- url     : https://prove2.me/submissions/987301b5-5285-4e95-94dd-932817d1d651

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ConstantCoeffDmonOfEigen

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
open GlobalTheory GlobalTheory.CharacterColumns
namespace GlobalTheory.CharacterColumns
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u u' : ι → Fin d → R) (mo : ι →₀ ℕ) (hu : ∀ l, mo l ≠ 0 → u l = u' l)
    (f : PS R 1 d) : DmonOf F u mo f = DmonOf F u' mo f := by
  unfold DmonOf
  congr 1
  funext l g
  by_cases hl : mo l = 0
  · rw [hl]; rfl
  · rw [hu l hl]
end GlobalTheory.CharacterColumns
