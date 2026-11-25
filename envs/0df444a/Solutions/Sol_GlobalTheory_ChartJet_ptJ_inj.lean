-- Prove2me | solution 1 for GlobalTheory.ChartJet.ptJ_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:07:21.319927+00:00
-- url     : https://prove2.me/submissions/ad2ebdb5-1d09-4a36-9062-190bf71a6782

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_pj_ext
import Theorems.Thm_GlobalTheory_ChartJet_jP_zR
import Theorems.Thm_GlobalTheory_ChartJet_aug_jS
import Theorems.Thm_GlobalTheory_ChartJet_ptJ_aug
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
variable {x} (hx : IsUnivChart G d x)
include hx
namespace GlobalTheory.ChartJet
theorem _root_.solution {p q : Q R d n} (h : ∀ m, ptJ x m p = ptJ x m q) : p = q := by
  apply Subtype.ext
  funext j
  apply pj_ext
  intro m
  have hu := hx.2.2 (JetR R (Fin n × Fin d) m) (jetAug R _ m) m (ker_jetAug_pow _ m) (ptJ x m q) (ptJ_aug hx m q)
  have e : jP m p = jP m q := hu.unique ⟨aug_jS hx m p, (h m).symm⟩ ⟨aug_jS hx m q, rfl⟩
  rw [← jP_zR m p j, ← jP_zR m q j, e]
end GlobalTheory.ChartJet
