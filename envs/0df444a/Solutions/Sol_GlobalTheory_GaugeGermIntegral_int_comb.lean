-- Prove2me | solution 1 for GlobalTheory.GaugeGermIntegral.int_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:29.968681+00:00
-- url     : https://prove2.me/submissions/489586e8-3ed5-4319-ae81-7e6db387b6fb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_intS_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_pderiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_integral_family_pair_zero


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
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.GaugeGermIntegral
variable {K : Type} [Field K]
variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {V : VF K}
omit [CharZero K]
namespace GlobalTheory.GaugeGermIntegral
theorem _root_.solution (v : Fin d → K) (hv : ∀ i, V.Ge 0 (v i)) (f : PS K 3 d) (hf : IntS V f) :
    (∑ i, C (v i) * ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), i) f)) ∈
      Ig (intRing V) K (Fin 2 × Fin d) :=
  sum_mem fun i _ => mul_mem (ig_C (R := intRing V) ⟨v i, hv i⟩)
    (ig_ev czZ integral_family_pair_zero (ig_pderiv ((intS_iff V f).1 hf) _))
end GlobalTheory.GaugeGermIntegral
