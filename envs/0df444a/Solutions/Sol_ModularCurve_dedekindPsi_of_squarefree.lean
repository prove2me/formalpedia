-- Prove2me | solution 1 for ModularCurve.dedekindPsi_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a9fedc75-775a-59ea-9cd9-0296dc065c0d

import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dedekindPsi_of_squarefree
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

namespace ModularCurve
p2m_export "ModularCurve" "dedekindPsi dedekindPsi_one dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace W1
p2m_open "ModularCurve"

private theorem psi_prime_pow_aux {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ModularCurve.dedekindPsi (p ^ (k + 1)) = p ^ (k + 1) + p ^ k := by
  unfold ModularCurve.dedekindPsi
  have hfil : Finset.filter (fun d => Squarefree d) (p ^ (k + 1)).divisors = {1, p} := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisors_prime_pow hp, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j, -, rfl⟩, hsq⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl (pow_zero p)
      · have hj1 : j = 1 := ((Nat.squarefree_pow_iff hp.ne_one hj0.ne').mp hsq).2
        subst hj1
        exact Or.inr (pow_one p)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, Nat.zero_le _, (pow_zero p).symm⟩, squarefree_one⟩
      · exact ⟨⟨1, by omega, (pow_one _).symm⟩, hp.prime.squarefree⟩
  rw [hfil, Finset.sum_pair hp.one_lt.ne, Nat.div_one, pow_succ,
    Nat.mul_div_cancel _ hp.pos]

end ModularCurve.W1

namespace ModularCurve p2m_export "ModularCurve" "dedekindPsi dedekindPsi_one dedekindPsi_mul_of_coprime dedekindPsi_prime" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.dedekindPsi_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    dedekindPsi (p ^ (k + 1)) = (p + 1) * p ^ k := by
  rw [ModularCurve.W1.psi_prime_pow_aux hp k, Nat.add_mul, Nat.one_mul, ← pow_succ']

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.dedekindPsi_of_squarefree {N : ℕ} (hN : Squarefree N) :
    dedekindPsi N = ∏ p ∈ N.primeFactors, (p + 1) := by
  revert hN
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro hsq
    have hn1 : n = 1 := ((Nat.squarefree_pow_iff hp.ne_one hn.ne').mp hsq).2
    subst hn1
    rw [pow_one, ModularCurve.dedekindPsi_prime hp, hp.primeFactors, Finset.prod_singleton]
  | zero => exact fun h => absurd h not_squarefree_zero
  | one =>
    intro _
    rw [ModularCurve.dedekindPsi_one, Nat.primeFactors_one, Finset.prod_empty]
  | coprime a b ha hb hab iha ihb =>
    intro hsq
    obtain ⟨-, hsa, hsb⟩ := Nat.squarefree_mul_iff.mp hsq
    rw [ModularCurve.dedekindPsi_mul_of_coprime a b hab,
      Nat.primeFactors_mul (by omega : a ≠ 0) (by omega : b ≠ 0),
      Finset.prod_union hab.disjoint_primeFactors, iha hsa, ihb hsb]

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_dedekindPsi_of_squarefree.ModularCurve in

theorem solution {N : ℕ} (hN : Squarefree N) : dedekindPsi N = ∏ p ∈ N.primeFactors, (p + 1) :=
  ModularCurve.dedekindPsi_of_squarefree hN

#print axioms solution

end S_ModularCurve_dedekindPsi_of_squarefree
end P2MW
export P2MW.S_ModularCurve_dedekindPsi_of_squarefree (solution)
