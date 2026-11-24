-- Prove2me | solution 1 for GlobalTheory.JetSer.constantCoeff_dof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:27.959119+00:00
-- url     : https://prove2.me/submissions/cccc9f05-9365-4cbc-81f1-3aee37a78ac6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DualNumberValueToJet
import Theorems.Thm_GlobalTheory_SymbolOne_coeff_law
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) :
    constantCoeff (Dof (G.mapF f) e u) =
      ∑ j, e j * coeff (Finsupp.single ((0 : Fin 1), j) 1) u := by
  have h : ∀ i j : Fin d, constantCoeff (ev (n := 1) ![pt O d 0, 0]
      (pderiv O ((1 : Fin 2), i) (G.mapF f j))) = if j = i then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_zero_right,
      Finsupp.embDomain_zero, coeff_pderiv, FGLaw.mapF, coeff_map, zero_add, SymbolOne.coeff_law]
    split_ifs <;> simp
  unfold Dof
  simp only [map_sum, map_mul, h, constantCoeff_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp
end GlobalTheory.JetSer
