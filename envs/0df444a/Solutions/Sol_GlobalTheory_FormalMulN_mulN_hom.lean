-- Prove2me | solution 1 for GlobalTheory.FormalMulN.mulN_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:25:59.012983+00:00
-- url     : https://prove2.me/submissions/614cfd87-7b23-4277-bc79-c37ec5bfbdb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_const_mulN
import Theorems.Thm_GlobalTheory_FormalMulN_formalGroupLaw_comp_mulN_add
import Theorems.Thm_GlobalTheory_FormalMulN_dLin_mulN
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)
namespace GlobalTheory.FormalMulN
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ),
    (∀ i, constantCoeff (mulN G n i) = 0) ∧
    comp1 (mulN G n) (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 (mulN G n) (pt R (n := 2) d 0)) (comp1 (mulN G n) (pt R (n := 2) d 1)) ∧
    dLin (mulN G n) = (n : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  intro R inst d G n
  exact ⟨const_mulN G n, formalGroupLaw_comp_mulN_add G n (const_pt 0) (const_pt 1), dLin_mulN G n⟩
end GlobalTheory.FormalMulN
