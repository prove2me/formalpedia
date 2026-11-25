-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_modCharacter_eq_of_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:43:59.269917+00:00
-- url     : https://prove2.me/submissions/1c3c6b2c-6e64-42c6-8c01-3096e91b1062

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_of_comap_eq
import Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_of_eqOn
import Theorems.Thm_GroundTheory_Global_Cyclotomic_eq_of_natCast_mem_rootsOfUnityField
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_modCharacter_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] (k : ℕ)
    (a : (ZMod (p ^ (k + 1)))ˣ) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, modCharacter (p ^ (k + 1)) σ = a := by
  obtain ⟨τ, hτ⟩ := exists_modCharacter_eq (p ^ (k + 1)) a
  set L := rootsOfUnityField (p ^ (k + 1))
  have hpP : ((p : ℕ) : 𝓞 ℚ̄) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := by
      rw [← hP.over]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap, map_natCast] at h
    exact h
  have hpP' : ((p : ℕ) : 𝓞 ℚ̄) ∈ τ⁻¹ • P := by
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    change MulSemiringAction.toRingHom _ _ τ (p : 𝓞 ℚ̄) ∈ P
    rw [map_natCast]
    exact hpP
  have h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L) :=
    eq_of_natCast_mem_rootsOfUnityField k (by rw [Ideal.mem_comap, map_natCast]; exact hpP')
      (by rw [Ideal.mem_comap, map_natCast]; exact hpP)
  obtain ⟨σ, hσ, hστ⟩ := exists_mem_stabilizer_of_comap_eq L P τ h
  exact ⟨σ, hσ, (modCharacter_eq_of_eqOn hστ).trans hτ⟩
end GroundTheory.Global.Cyclotomic
