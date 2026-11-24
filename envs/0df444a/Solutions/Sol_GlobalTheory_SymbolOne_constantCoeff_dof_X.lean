-- Prove2me | solution 1 for GlobalTheory.SymbolOne.constantCoeff_dof_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:00:07.68731+00:00
-- url     : https://prove2.me/submissions/b73ab789-aff1-4111-af20-06deebb0f3ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
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
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolOne
namespace GlobalTheory.SymbolOne
theorem _root_.solution {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
    (G : FGLaw R d) (v : Fin d → k) (j : Fin d) :
    constantCoeff (Dof (G.mapF φ) v (X ((0 : Fin 1), j))) = v j := by
  have h : ∀ i j : Fin d, constantCoeff (ev (n := 1) ![pt k d 0, 0]
      (pderiv k ((1 : Fin 2), i) (G.mapF φ j))) = if j = i then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply, WickVanishing.coeff_ev_zero_right, Finsupp.embDomain_zero,
      coeff_pderiv, FGLaw.mapF, coeff_map, zero_add, coeff_law]
    split_ifs <;> simp
  unfold Dof
  simp only [map_sum, map_mul, h, constantCoeff_C]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj
    rw [pderiv_X_of_ne, map_zero, mul_zero]
    intro h'
    exact hj (by simpa using h'.symm)
  · simp
end GlobalTheory.SymbolOne
