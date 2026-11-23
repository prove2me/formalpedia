-- Prove2me | solution 1 for GlobalTheory.LevelPairing.zetaM_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:00.959838+00:00
-- url     : https://prove2.me/submissions/a6fa5f37-7668-41ad-9e56-78a9ef75515e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos

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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution (c : Coeff l) : ((zetaM c : c.F) : ℂ) = zeta l.M := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hA : l.A ≠ 0 := l.A_pos.ne'
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM hA
  have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hM'
  have hdiv : l.M' / l.M = k := by rw [hk]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hM)
  unfold zetaM
  rw [hdiv]
  change (zeta l.M') ^ k = _
  unfold zeta
  rw [← Complex.exp_nat_mul, hk]
  congr 1
  have : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have : (l.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp
end GlobalTheory.LevelPairing
