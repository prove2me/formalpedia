-- Prove2me | solution 1 for GlobalTheory.FormalMulN.add_assoc_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:58.540097+00:00
-- url     : https://prove2.me/submissions/cd1ce2ea-3ebb-4b99-b0ec-36eb6b09f71e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_const_three
import Theorems.Thm_GlobalTheory_FormalMulN_ev_pt_fun
import Theorems.Thm_GlobalTheory_FormalMulN_const_add
import Theorems.Thm_GlobalTheory_FormalMulN_ev_add_pts
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
theorem _root_.solution {x y z : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0) :
    G.add (G.add x y) z = G.add x (G.add y z) := by
  have h3 := const_three hx hy hz
  have hA : G.add (G.add (pt R (n := 3) d 0) (pt R d 1)) (pt R d 2) =
      G.add (pt R (n := 3) d 0) (G.add (pt R d 1) (pt R d 2)) := funext fun i => G.assoc i
  have h : (fun i => ev ![x, y, z] (G.add (G.add (pt R (n := 3) d 0) (pt R d 1)) (pt R d 2) i)) =
      fun i => ev ![x, y, z] (G.add (pt R (n := 3) d 0) (G.add (pt R d 1) (pt R d 2)) i) := by
    rw [hA]
  rw [ev_add_pts G (const_add G (const_pt 0) (const_pt 1)) (const_pt 2) h3,
    ev_add_pts G (const_pt 0) (const_add G (const_pt 1) (const_pt 2)) h3,
    ev_add_pts G (const_pt 0) (const_pt 1) h3, ev_add_pts G (const_pt 1) (const_pt 2) h3,
    ev_pt_fun h3 0, ev_pt_fun h3 1, ev_pt_fun h3 2] at h
  exact h
end GlobalTheory.FormalMulN
