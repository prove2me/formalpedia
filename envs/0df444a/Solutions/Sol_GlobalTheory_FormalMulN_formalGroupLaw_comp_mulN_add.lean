-- Prove2me | solution 1 for GlobalTheory.FormalMulN.formalGroupLaw_comp_mulN_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:53:23.420293+00:00
-- url     : https://prove2.me/submissions/76b972d5-85ad-43b7-9003-491a2b7206e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_const_add
import Theorems.Thm_GlobalTheory_FormalMulN_zero_add_pt
import Theorems.Thm_GlobalTheory_FormalMulN_add_add_add_comm_pt
import Theorems.Thm_GlobalTheory_FormalMulN_const_mulN
import Theorems.Thm_GlobalTheory_FormalMulN_formalGroupLaw_comp_mulN_zero
import Theorems.Thm_GlobalTheory_FormalMulN_formalGroupLaw_comp_mulN_succ
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_comp1
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_zero


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
theorem _root_.solution (k : ℕ) {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) :
    comp1 (mulN G k) (G.add x y) = G.add (comp1 (mulN G k) x) (comp1 (mulN G k) y) := by
  induction k with
  | zero =>
    rw [formalGroupLaw_comp_mulN_zero G (const_add G hx hy), formalGroupLaw_comp_mulN_zero G hx, formalGroupLaw_comp_mulN_zero G hy,
      zero_add_pt G const_zero]
  | succ k ih =>
    rw [formalGroupLaw_comp_mulN_succ G k (const_add G hx hy), ih, formalGroupLaw_comp_mulN_succ G k hx,
      formalGroupLaw_comp_mulN_succ G k hy,
      add_add_add_comm_pt G (const_comp1 (const_mulN G k) hx) (const_comp1 (const_mulN G k) hy) hx hy]
end GlobalTheory.FormalMulN
