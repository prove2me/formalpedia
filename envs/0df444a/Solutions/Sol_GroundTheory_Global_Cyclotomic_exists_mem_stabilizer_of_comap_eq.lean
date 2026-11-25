-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:56.205827+00:00
-- url     : https://prove2.me/submissions/c17770bc-f517-4372-ac94-4867794a085d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isOpen_stabilizer_ringOfIntegers

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
theorem _root_.solution (L : IntermediateField ℚ ℚ̄) (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] (τ : Gal(ℚ̄/ℚ))
    (h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L)) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, ∀ x ∈ L, σ x = τ x := by
  let G := L.fixingSubgroup
  let _ : Algebra (𝓞 L) (𝓞 ℚ̄) := (ringOfIntegersIncl L).toAlgebra
  let _ : TopologicalSpace (𝓞 ℚ̄) := ⊥
  have : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  have : CompactSpace G :=
    isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  have hfix : ∀ (g : G) (a : 𝓞 L), g • ringOfIntegersIncl L a = ringOfIntegersIncl L a :=
    fun g a => RingOfIntegers.ext ((mem_fixingSubgroup_iff _ _).1 g.2 _ (a : L).2)
  have : SMulCommClass G (𝓞 L) (𝓞 ℚ̄) := ⟨fun g a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', RingHom.algebraMap_toAlgebra, hfix]⟩
  have : ContinuousSMul G (𝓞 ℚ̄) := continuousSMul_iff_stabilizer_isOpen.2 fun b =>
    (isOpen_stabilizer_ringOfIntegers b).preimage continuous_subtype_val
  have : Algebra.IsInvariant (𝓞 L) (𝓞 ℚ̄) G := ⟨fun b hb => by
    have hmem : (b : ℚ̄) ∈ fixedField L.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro f hf
      exact congrArg (fun c : 𝓞 ℚ̄ => (c : ℚ̄)) (hb ⟨f, hf⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    have hint : IsIntegral ℤ (⟨b, hmem⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L ℚ̄) (algebraMap L ℚ̄).injective).1
        b.isIntegral_coe
    exact ⟨⟨⟨b, hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := 𝓞 L) (G := G) P (τ⁻¹ • P) h.symm
  refine ⟨τ * g, ?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul]
    calc τ • ((g : Gal(ℚ̄/ℚ)) • P) = τ • (g • P) := rfl
      _ = τ • (τ⁻¹ • P) := by rw [hg]; rfl
      _ = P := smul_inv_smul τ P
  · change τ ((g : Gal(ℚ̄/ℚ)) x) = τ x
    rw [(mem_fixingSubgroup_iff _ _).1 g.2 x hx]
end GroundTheory.Global.Cyclotomic
