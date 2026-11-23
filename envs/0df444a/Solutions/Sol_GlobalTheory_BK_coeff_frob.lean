-- Prove2me | solution 1 for GlobalTheory.BK.coeff_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:50.198612+00:00
-- url     : https://prove2.me/submissions/dcf3b0fb-f47c-48dc-9481-e4202851cd2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] (f : K⟦X⟧) (n : ℕ) :
    coeff n (frob K l f) = if l ∣ n then coeff (n / l) f else 0 := coeff_expand _ _ f
end GlobalTheory.BK
