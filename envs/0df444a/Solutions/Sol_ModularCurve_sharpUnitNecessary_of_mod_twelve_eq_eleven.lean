-- Prove2me | solution 1 for ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_eleven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8b354385-d87c-535a-a4ca-4fe6b40c6450

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_witness
import Theorems.Thm_rademacher_phi_level_witness_eleven
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_eleven

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

section N

open ModularCurve

variable (ℓ : ℕ) [NeZero ℓ]

private theorem _root_.DedekindEtaLog.sharpUnitNecessary_of_witness (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c')
    (h1 : a * d ≡ 1 [ZMOD ((ℓ * c' : ℕ) : ℤ)]) (z₀ : ℤ)
    (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ))
        + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀)
    (hcop : Nat.Coprime z₀.natAbs (eisensteinNumerator ℓ)) : SharpUnitNecessary ℓ :=
  ModularCurve.sharpUnitNecessary_of_witness ℓ hℓ a d c' hc' h1 z₀ hδ hcop

p2m_export "DedekindEtaLog" "sharpUnitNecessary_of_witness"
theorem etaPhase_witness_eleven (j : ℕ) : 12 * ((((4 * j + 4 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 11 : ℕ) : ℚ)) / (12 * ((12 * j + 11 : ℕ) : ℚ)) + dedekindSum 3 1 - dedekindSum 3 (12 * j + 11)) = ((Nat.gcd ((12 * j + 11) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 4)) ∧ Nat.Coprime (Int.natAbs (-(4 * (j : ℤ) + 4))) (((12 * j + 11) - 1) / Nat.gcd ((12 * j + 11) - 1) 12) :=
  rademacher_phi_level_witness_eleven j

omit [NeZero ℓ] in
private lemma modEq_helper (ℓ : ℕ) (a d t : ℤ) (h : a * d = 1 + t * ℓ) :
    a * d ≡ 1 [ZMOD ((ℓ * 1 : ℕ) : ℤ)] :=
  Int.modEq_iff_dvd.2 ⟨-t, by push_cast; linear_combination -h⟩

theorem sharpUnitNecessary_of_mod_twelve_eq_eleven (j : ℕ) : SharpUnitNecessary (12 * j + 11) := by
  haveI : NeZero (12 * j + 11) := ⟨by omega⟩
  obtain ⟨hδ, hcop⟩ := etaPhase_witness_eleven j
  refine sharpUnitNecessary_of_witness (12 * j + 11) (by omega) ((4 * j + 4 : ℕ) : ℤ) 3 1 one_pos
    (modEq_helper _ _ _ 1 (by push_cast; ring)) (-(4 * (j : ℤ) + 4)) ?_ ?_
  · simpa only [mul_one, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hδ
  · exact hcop

end N

end DedekindEtaLog

end

theorem solution (j : ℕ) : ModularCurve.SharpUnitNecessary (12 * j + 11) :=
  DedekindEtaLog.sharpUnitNecessary_of_mod_twelve_eq_eleven j

end S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_eleven
end P2MW
export P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_eleven (solution)
