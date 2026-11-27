-- Prove2me | solution 1 for GlobalTheory.nuLocC_le_nuPlE_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:31.153864+00:00
-- url     : https://prove2.me/submissions/da8b47d1-d9ce-47cb-99cf-0e0b052c2812

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNLowerBoundBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NuLocCLeNuPlEBaseChange
import Theorems.Thm_GlobalTheory_nabValN_lower_bound_baseChange
import Theorems.Thm_GlobalTheory_nval_eq_of_extension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_vanish_first_axis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.DescentSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι k Y hY a n
  obtain ⟨hint, hval⟩ := GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι
  unfold FBChart.nuPlE
  refine le_iInf₂ ?_
  rintro x ⟨P, hP, f, hf, rfl⟩
  have hh : MvPowerSeries.constantCoeff (a3h C3) = 0 := by
    let _ := io.toAlgebra
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ C3.ch.gauge.ax0 0 fun _ => rfl
  unfold FBChart.nab
  rw [hY.h, hY.w0, hY.k]
  refine GlobalTheory.nabValN_lower_bound_baseChange T C V.v ι V.RR (fun x => Iff.rfl) hint _ (𝓞 E) (a3B C3) Y.B hY.F hY.act (a3h C3) hh H.w0 k (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) (nuLocC C3 (eOf T V) k a n) ?_ P hP f hf
  intro Q hQ g hg
  rw [← hval]
  unfold nuLocC
  exact iInf_le_of_le Q (iInf_le_of_le hQ (iInf_le_of_le g (iInf_le_of_le hg le_rfl)))
end GlobalTheory
