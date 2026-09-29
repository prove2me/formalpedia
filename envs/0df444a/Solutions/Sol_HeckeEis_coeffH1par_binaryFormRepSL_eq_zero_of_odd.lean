-- Prove2me | solution 1 for HeckeEis.coeffH1par_binaryFormRepSL_eq_zero_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/88f530b4-4d37-5d07-84f7-12b0c3bfd9c5

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep

import Theorems.Thm_HeckeEis_binaryFormRepSL_neg_one_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped MatrixGroups

namespace HeckeEis
p2m_export "HeckeEis" "mem_coeffCocycles_iff mem_coeffCoboundaries_iff coeffH1par coeffH1parMk_surjective coeffH1parMk_eq_zero_iff BinaryForm binaryFormRepSL binaryFormRepSL_neg_one_apply"
namespace OddSol
p2m_open "HeckeEis"

open CongruenceSubgroup

theorem neg_one_mem (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp

def m (N : ℕ) : Gamma0 N := ⟨-1, neg_one_mem N⟩

theorem m_mul (N : ℕ) (g : Gamma0 N) : m N * g = g * m N := by
  apply Subtype.ext
  show (-1 : SL(2, ℤ)) * g = g * (-1)
  rw [neg_one_mul, mul_neg_one]

theorem rho_m {K : Type*} [CommRing K] (N n : ℕ) (hn : Odd n) (P : ↥(BinaryForm K n)) :
    ((binaryFormRepSL K n).comp (Gamma0 N).subtype) (m N) P = -P := by
  show binaryFormRepSL K n ((m N : Gamma0 N) : SL(2, ℤ)) P = -P
  rw [show ((m N : Gamma0 N) : SL(2, ℤ)) = -1 from rfl, binaryFormRepSL_neg_one_apply, hn.neg_one_pow]
  exact neg_one_smul K P

end HeckeEis.OddSol

theorem solution (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (N n : ℕ) (hn : Odd n)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)) : x = 0 := by
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1parMk_surjective _ x
  rw [HeckeEis.coeffH1parMk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff]
  have hz : ∀ g h : CongruenceSubgroup.Gamma0 N, (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (g * h)
      = (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g + ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) g ((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) h) :=
    (HeckeEis.mem_coeffCocycles_iff _ _).mp z.2.1

  have key : ∀ g : CongruenceSubgroup.Gamma0 N,
      (2 : K) • (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g = (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N)
        - ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) g ((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N)) := by
    intro g
    have h1 := hz g (HeckeEis.OddSol.m N)
    have h3 : (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (g * HeckeEis.OddSol.m N) = (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N) - (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g := by
      rw [← HeckeEis.OddSol.m_mul, hz, HeckeEis.OddSol.rho_m N n hn]; abel
    have e := h1.symm.trans h3

    rw [two_smul]
    calc (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g + (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g
        = ((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g + ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) g ((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N)))
            + (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g - ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) g ((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N)) := by abel
      _ = ((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N) - (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g) + (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g
            - ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) g ((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N)) := by rw [e]
      _ = _ := by abel
  refine ⟨-((2 : K)⁻¹ • (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) (HeckeEis.OddSol.m N)), funext fun g => ?_⟩
  apply smul_right_injective ↥(HeckeEis.BinaryForm K n) h2
  dsimp only
  rw [map_neg, LinearMap.map_smul, key g, smul_sub, smul_neg, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ h2, one_smul, one_smul]
  abel

#print axioms solution

end S_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd
end P2MW
export P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd (solution)
