-- Prove2me | solution 1 for GlobalTheory.DirScale.dmonOf_smul_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:27.439178+00:00
-- url     : https://prove2.me/submissions/acfa3db5-ce3b-42da-a31f-d00862b257ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DofIterSmulDir
import Theorems.Thm_GlobalTheory_DirScale_foldr_smul_dir

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
open GlobalTheory GlobalTheory.DirScale
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.DirScale
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (ι : Type)
    [Fintype ι] (c : ι → R) (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d),
    DmonOf F (fun l => c l • u l) m f = C (∏ l, c l ^ m l) * DmonOf F u m f := by
  intro R _ d F ι _ c u m f
  unfold DmonOf
  have h : ((Finset.univ : Finset ι).toList.map fun l => c l ^ m l).prod = ∏ l, c l ^ m l :=
    Finset.prod_map_toList _ _
  rw [← h]
  exact foldr_smul_dir F c u (fun l => m l) f _
end GlobalTheory.DirScale
