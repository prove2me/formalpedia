-- Prove2me | solution 1 for ModularCurve.CuspSpace.card_cuspSpace_eq_cuspCount
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b17bf4a0-4372-5461-84de-9c063fcbef3b

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_CuspSpace_classification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount.ModularCurve ModularCurve.CuspSpace P2MW.S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount.ModularCurve.CuspSpace"

namespace ModularCurve
p2m_export "ModularCurve" "CuspSpace cuspCount CuspSpace.classification"
namespace CuspSpace
p2m_export "ModularCurve.CuspSpace" "Classification classification"
p2m_open "ModularCurve.CuspSpace ModularCurve"

open Finset

variable {N : ℕ}

theorem card_sigma_units :
    Nat.card ((d : N.divisors) × (ZMod (Nat.gcd d (N / (d : ℕ))))ˣ) = cuspCount N := by
  have hgcd : ∀ d : N.divisors, NeZero (Nat.gcd (d : ℕ) (N / (d : ℕ))) := by
    rintro ⟨d, hd⟩
    rw [Nat.mem_divisors] at hd
    exact ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero
      (fun h => hd.2 (Nat.eq_zero_of_zero_dvd (h ▸ hd.1))))).ne'⟩
  rw [Nat.card_sigma]
  simp only [cuspCount]
  rw [← Finset.sum_attach N.divisors fun d => Nat.totient (Nat.gcd d (N / d)),
    ← Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := hgcd d
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem card_eq_cuspCount_of_classification (hcl : Classification N) :
    Nat.card (CuspSpace N) = cuspCount N := by
  obtain ⟨e⟩ := hcl
  rw [Nat.card_congr e, card_sigma_units]

end ModularCurve.CuspSpace

theorem solution {N : ℕ} (hN : N ≠ 0) :
    Nat.card (ModularCurve.CuspSpace N) = ModularCurve.cuspCount N :=
  ModularCurve.CuspSpace.card_eq_cuspCount_of_classification (ModularCurve.CuspSpace.classification hN)

end S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount
end P2MW
export P2MW.S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount (solution)
