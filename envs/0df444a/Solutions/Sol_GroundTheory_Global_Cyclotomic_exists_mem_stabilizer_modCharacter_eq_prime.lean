-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_modCharacter_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:23:54.716419+00:00
-- url     : https://prove2.me/submissions/a14f0e85-1ec9-4a3e-bde9-409031120f6f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_of_comap_eq
import Theorems.Thm_GroundTheory_Global_Cyclotomic_existsUnique_isArithFrobAt
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isArithFrobAt_restrictNormal_iff


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
theorem _root_.solution {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] {M : ℕ} [NeZero M] (hM : ¬ p ∣ M) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, (modCharacter M σ : ZMod M) = p := by
  set L := rootsOfUnityField M
  let Q : Ideal (𝓞 L) := P.comap (ringOfIntegersIncl L)
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
    rw [Ideal.under, Ideal.comap_comap, show (ringOfIntegersIncl L).comp (algebraMap ℤ (𝓞 L)) =
      algebraMap ℤ (𝓞 ℚ̄) from RingHom.ext_int _ _]
    exact hP.over⟩
  obtain ⟨τ₀, hτ₀, -⟩ := existsUnique_isArithFrobAt p L Q hM
  let τ : Gal(ℚ̄/ℚ) := τ₀.liftNormal ℚ̄
  have hτ : ∀ x : L, τ (x : ℚ̄) = (τ₀ x : ℚ̄) := fun x => τ₀.liftNormal_commutes ℚ̄ x
  have hstab := hτ₀.mem_stabilizer
  have h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    have h1 : τ • ringOfIntegersIncl L x = ringOfIntegersIncl L (τ₀ • x) :=
      RingOfIntegers.ext (hτ x)
    rw [h1, ← Ideal.mem_comap]
    change τ₀ • x ∈ Q ↔ x ∈ Q
    conv_lhs => rw [← MulAction.mem_stabilizer_iff.1 hstab]
    exact Ideal.smul_mem_pointwise_smul_iff
  obtain ⟨σ, hσ, hστ⟩ := exists_mem_stabilizer_of_comap_eq L P τ h
  refine ⟨σ, hσ, ?_⟩
  have hres : σ.restrictNormal L = τ₀ := by
    ext x
    rw [← hτ x, ← hστ _ x.2]
    exact σ.restrictNormal_commutes L x
  rw [← isArithFrobAt_restrictNormal_iff M p Q hM σ, hres]
  exact hτ₀
end GroundTheory.Global.Cyclotomic
