-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.fib_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:20.50888+00:00
-- url     : https://prove2.me/submissions/a6be006a-b017-4991-ac79-1bac4081eb3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_fib_cond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') {m : ℕ} (hJ : (RingHom.ker q) ^ (m + 1) = ⊥) :
    (RingHom.ker (fibFst q)) ^ (m + 1) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : fibFst q z = 0 := Ideal.pow_le_self (Nat.succ_ne_zero m) hz
  have hle : RingHom.ker (fibFst q) ≤ (RingHom.ker q).comap (fibSnd q) := fun w hw => by
    have hw' : fibFst q w = 0 := hw
    show q (fibSnd q w) = 0
    rw [fib_cond, hw', map_zero]
  have h2 := Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono hle (m + 1) hz)
  rw [hJ] at h2
  exact Subtype.ext (Prod.ext h1 h2)
end GlobalTheory.ChartBaseChange
