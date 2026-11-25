-- Prove2me | solution 1 for GlobalTheory.CoeffRingTest.zeta_pd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:25.655004+00:00
-- url     : https://prove2.me/submissions/1e2dfc4c-7fcd-44dd-8caa-699989b70829

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_FullIffBijective
import Theorems.Thm_GlobalTheory_CoeffRingTest_zeta_mem_of_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffRingTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace GlobalTheory.CoeffRingTest
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (h : d.IsLev) : zeta d.pd ∈ c.F := by
  have hM : d.l₂.M' ≠ 0 := Nat.lcm_ne_zero (by have := d.l₂.three_le; omega) d.l₂.A_pos.ne'
  have hd : d.pd ∣ d.l₂.M' := (h.2.1 ▸ dvd_mul_left d.pd l.M).trans (Nat.dvd_lcm_left _ _)
  exact d.hF ▸ zeta_mem_of_dvd hM hd d.c₂.zeta_mem
end GlobalTheory.CoeffRingTest
