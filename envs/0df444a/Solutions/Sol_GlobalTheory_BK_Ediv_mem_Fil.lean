-- Prove2me | solution 1 for GlobalTheory.BK.Ediv_mem_Fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:13.501353+00:00
-- url     : https://prove2.me/submissions/d383b0f5-35d9-4c38-8848-8b9bc8e68e8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_FilPre_le_Fil

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
namespace GlobalTheory.BK
theorem _root_.solution (e : ℕ) [NeZero e] {j i : ℕ} (h : j ≤ i) :
    (⟨Ediv K l e i, Ediv_mem_S l e i⟩ : S O K e) ∈ Fil O K l e j :=
  FilPre_le_Fil l e j (Ideal.subset_span ⟨i, h, rfl⟩)
end GlobalTheory.BK
