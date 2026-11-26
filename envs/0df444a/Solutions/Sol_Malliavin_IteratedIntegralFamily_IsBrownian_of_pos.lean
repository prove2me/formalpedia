-- Prove2me | solution 1 for Malliavin.IteratedIntegralFamily.IsBrownian.of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:57.833361+00:00
-- url     : https://prove2.me/submissions/7579ab1d-f234-4a9d-8451-46f8e101442a

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_IteratedIntegralFamily_box_zero

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
namespace IteratedIntegralFamily.IsBrownian
theorem _root_.solution {J : IteratedIntegralFamily P}
    (h : ∀ (n : ℕ), 0 < n → ∀ (u v : Fin n → ℝ≥0), (∀ i, u i ≤ v i) →
      (∀ i j, i < j → v i ≤ u j) →
      (fun ω ↦ J.integral n (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v) :
    J.IsBrownian B := by
  refine ⟨fun n u v huv hord ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact J.box_zero u v
  · exact h n hn u v huv hord
end IteratedIntegralFamily.IsBrownian
end Malliavin
