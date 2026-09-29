-- Prove2me | solution 1 for ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4cadcf29-0d1e-511e-a5be-183776fc4b57

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_witness
import Theorems.Thm_rademacher_phi_level_witness_mod_sixty_eq_thirtySeven
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirtySeven

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
theorem etaPhase_witness_mod60_37 (i : ℕ) : 12 * ((((24 * i + 15 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((60 * i + 37 : ℕ) : ℚ)) / (12 * ((60 * i + 37 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (60 * i + 37)) = ((Nat.gcd ((60 * i + 37) - 1) 12 : ℕ) : ℚ) * (-(3 * (i : ℤ) + 2)) ∧ Nat.Coprime (Int.natAbs (-(3 * (i : ℤ) + 2))) (((60 * i + 37) - 1) / Nat.gcd ((60 * i + 37) - 1) 12) :=
  rademacher_phi_level_witness_mod_sixty_eq_thirtySeven i

private lemma modEq_helper (ℓ : ℕ) (a d t : ℤ) (h : a * d = 1 + t * ℓ) :
    a * d ≡ 1 [ZMOD ((ℓ * 1 : ℕ) : ℤ)] :=
  Int.modEq_iff_dvd.2 ⟨-t, by push_cast; linear_combination -h⟩

theorem sharpUnitNecessary_of_mod_sixty_eq_thirtySeven (i : ℕ) : SharpUnitNecessary (60 * i + 37) := by
  haveI : NeZero (60 * i + 37) := ⟨by omega⟩
  obtain ⟨hδ, hcop⟩ := etaPhase_witness_mod60_37 i
  refine sharpUnitNecessary_of_witness (60 * i + 37) (by omega) ((24 * i + 15 : ℕ) : ℤ) 5 1 one_pos
    (modEq_helper _ _ _ 2 (by push_cast; ring)) (-(3 * (i : ℤ) + 2)) ?_ ?_
  · simpa only [mul_one, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_one] using hδ
  · exact hcop

end N

end DedekindEtaLog

end

theorem solution (i : ℕ) : ModularCurve.SharpUnitNecessary (60 * i + 37) :=
  DedekindEtaLog.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven i

end S_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirtySeven
end P2MW
export P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirtySeven (solution)
