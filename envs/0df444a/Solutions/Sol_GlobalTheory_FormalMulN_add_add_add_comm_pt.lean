-- Prove2me | solution 1 for GlobalTheory.FormalMulN.add_add_add_comm_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:27.372192+00:00
-- url     : https://prove2.me/submissions/b8f33843-03d0-4a05-8b5b-758eb0fb265f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_const_add
import Theorems.Thm_GlobalTheory_FormalMulN_add_comm_pt
import Theorems.Thm_GlobalTheory_FormalMulN_add_assoc_pt

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
theorem _root_.solution {x y z w : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    G.add (G.add x y) (G.add z w) = G.add (G.add x z) (G.add y w) := by
  rw [add_assoc_pt G hx hy (const_add G hz hw), ← add_assoc_pt G hy hz hw, add_comm_pt G hy hz,
    add_assoc_pt G hz hy hw, ← add_assoc_pt G hx hz (const_add G hy hw)]
end GlobalTheory.FormalMulN
