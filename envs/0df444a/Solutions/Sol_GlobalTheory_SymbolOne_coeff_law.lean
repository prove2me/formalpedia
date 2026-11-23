-- Prove2me | solution 1 for GlobalTheory.SymbolOne.coeff_law
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:04.381808+00:00
-- url     : https://prove2.me/submissions/877bbabc-9004-4bce-911b-b36f4c1e2294

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_left


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
open GlobalTheory GlobalTheory.SymbolOne
namespace GlobalTheory.SymbolOne
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i j : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F j) = if j = i then 1 else 0 := by
  have h := WickVanishing.coeff_ev_zero_left (G.F j) (Finsupp.single ((0 : Fin 1), i) 1)
  rw [G.unit, Finsupp.embDomain_single, coeff_X] at h
  change _ = coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F j) at h
  rw [← h]
  by_cases hij : j = i
  · simp [hij]
  · rw [if_neg hij, if_neg]
    intro h'
    rw [Finsupp.single_left_inj one_ne_zero] at h'
    exact hij (congrArg Prod.snd h').symm
end GlobalTheory.SymbolOne
