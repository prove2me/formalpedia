-- Prove2me | solution 1 for MulAction.card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/23344518-361b-5787-9abb-031c6df7519d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime

set_option autoImplicit false

open MulAction in
theorem solution
    (G : Type*) {X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) :
    p * Nat.card (MulAction.orbitRel.Quotient G X)
      = Nat.card X + (p - 1) * Nat.card (MulAction.fixedPoints G X) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype X := Fintype.ofFinite X
  have hGc : Fintype.card G = p := by rw [← Nat.card_eq_fintype_card]; exact hG

  have hfix : ∀ g : G, g ≠ 1 → fixedBy X g = fixedPoints G X := by
    intro g hg
    have hord : orderOf g = p := by
      have hdvd : orderOf g ∣ p := hG ▸ orderOf_dvd_natCard g
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h
      · exact absurd (orderOf_eq_one_iff.mp h1) hg
      · exact h
    have hgen : Subgroup.zpowers g = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, hG]
    ext x
    simp only [mem_fixedBy, mem_fixedPoints]
    constructor
    · intro hx h
      have hle : Subgroup.zpowers g ≤ stabilizer G x := by
        rw [Subgroup.zpowers_le]; exact hx
      exact hle (by rw [hgen]; exact Subgroup.mem_top h)
    · intro hx; exact hx g

  have c1 : Fintype.card (fixedBy X (1 : G)) = Fintype.card X :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => show x ∈ fixedBy X (1 : G) from one_smul G x))
  have cg : ∀ g : G, g ≠ 1 → Fintype.card (fixedBy X g) = Fintype.card (fixedPoints G X) :=
    fun g hg => Fintype.card_congr (Equiv.setCongr (hfix g hg))

  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)), c1,
    Finset.sum_congr rfl (fun g hg => cg g (Finset.ne_of_mem_erase hg)),
    Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, hGc] at hB

  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

  convert hB.symm using 1
  all_goals (first | exact mul_comm _ _ | rfl | simp [mul_comm])

end S_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
end P2MW
export P2MW.S_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime (solution)
