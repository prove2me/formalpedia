-- Prove2me | solution 1 for ModularCurve.sharpUnitNecessary_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8f964060-8596-5400-9912-9a6ee686ecb3

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_eisensteinNumerator_eq_one
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_eleven
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_five
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_seven
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sharpUnitNecessary_of_prime

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

section N

open ModularCurve

variable (ℓ : ℕ) [NeZero ℓ]

private theorem _root_.DedekindEtaLog.sharpUnitNecessary_of_mod_twelve_eq_eleven (j : ℕ) : ModularCurve.SharpUnitNecessary (12 * j + 11) := ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_eleven j

p2m_export "DedekindEtaLog" "sharpUnitNecessary_of_mod_twelve_eq_eleven"
private theorem _root_.DedekindEtaLog.sharpUnitNecessary_of_mod_twelve_eq_five (j : ℕ) : ModularCurve.SharpUnitNecessary (12 * j + 5) := ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_five j

p2m_export "DedekindEtaLog" "sharpUnitNecessary_of_mod_twelve_eq_five"
private theorem _root_.DedekindEtaLog.sharpUnitNecessary_of_mod_twelve_eq_seven (j : ℕ) : ModularCurve.SharpUnitNecessary (12 * j + 7) := ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_seven j

p2m_export "DedekindEtaLog" "sharpUnitNecessary_of_mod_twelve_eq_seven"
omit [NeZero ℓ] in
private theorem _root_.DedekindEtaLog.sharpUnitNecessary_of_eisensteinNumerator_eq_one (h : eisensteinNumerator ℓ = 1) : SharpUnitNecessary ℓ := ModularCurve.sharpUnitNecessary_of_eisensteinNumerator_eq_one ℓ h

p2m_export "DedekindEtaLog" "sharpUnitNecessary_of_eisensteinNumerator_eq_one"
omit [NeZero ℓ] in

theorem sharpUnitNecessary_of_prime_of_mod_twelve_ne_one [Fact ℓ.Prime] (h : ℓ % 12 ≠ 1) :
    SharpUnitNecessary ℓ := by
  have hp := (Fact.out : ℓ.Prime)
  have h2 := hp.two_le
  have hdiv := Nat.div_add_mod ℓ 12
  have hr := Nat.mod_lt ℓ (by norm_num : 0 < 12)

  by_cases h23 : ℓ = 2 ∨ ℓ = 3
  · refine sharpUnitNecessary_of_eisensteinNumerator_eq_one ℓ ?_
    rcases h23 with rfl | rfl <;> decide
  push Not at h23
  have hodd : ¬ 2 ∣ ℓ := fun hd => by
    have := (Nat.dvd_prime hp).1 hd; omega
  have h3 : ¬ 3 ∣ ℓ := fun hd => by
    have := (Nat.dvd_prime hp).1 hd; omega
  set r := ℓ % 12 with hrdef
  set q := ℓ / 12 with hqdef
  have hℓ : ℓ = 12 * q + r := by omega
  interval_cases r
  all_goals first
    | exact absurd rfl h
    | (exfalso; apply hodd; omega)
    | (exfalso; apply h3; omega)
    | (rw [hℓ]; first
        | exact sharpUnitNecessary_of_mod_twelve_eq_five q
        | exact sharpUnitNecessary_of_mod_twelve_eq_seven q
        | exact sharpUnitNecessary_of_mod_twelve_eq_eleven q)

end N

end DedekindEtaLog

end

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 12 ≠ 1) : ModularCurve.SharpUnitNecessary ℓ :=
  DedekindEtaLog.sharpUnitNecessary_of_prime_of_mod_twelve_ne_one ℓ h

end S_ModularCurve_sharpUnitNecessary_of_prime
end P2MW
export P2MW.S_ModularCurve_sharpUnitNecessary_of_prime (solution)
