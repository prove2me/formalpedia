-- Prove2me | solution 1 for GlobalTheory.SW.SplitPrime.exists_prim_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:18.113837+00:00
-- url     : https://prove2.me/submissions/d8aaba28-06f6-428d-a229-9768c965db50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SplitPrime
open Polynomial
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
open Polynomial
namespace GlobalTheory.SW.SplitPrime
namespace _root_.GlobalTheory.SW.SplitPrime
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ (θ : 𝓞 E) (d : ℤ), d ≠ 0 ∧ Algebra.adjoin ℚ {(θ : E)} = ⊤ ∧
      ∀ a : 𝓞 E, ∃ g : ℤ[X], (d : 𝓞 E) * a = aeval θ g := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨y, hy0, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
    (Algebra.IsAlgebraic.isAlgebraic α)).exists_integral_multiple
  set θ : E := y • α with hθdef
  clear_value θ
  have hθ : IntermediateField.adjoin ℚ {θ} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have hy : ((y : ℚ) : E) ≠ 0 := by exact_mod_cast hy0
    have : α = ((y : ℚ) : E)⁻¹ * θ := by
      rw [hθdef, zsmul_eq_mul]; push_cast; field_simp
    rw [this]
    exact mul_mem (inv_mem (IntermediateField.algebraMap_mem _ _))
      (IntermediateField.mem_adjoin_simple_self ℚ θ)
  have hθℚ : IsIntegral ℚ θ := hyi.tower_top
  let B : PowerBasis ℚ E := (IntermediateField.adjoin.powerBasis hθℚ).map
    ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv)
  have hBgen : B.gen = θ := by simp [B]
  have hD := Algebra.discr_isIntegral ℚ (R := ℤ) (b := B.basis) (fun i => by
    rw [B.basis_eq_pow, hBgen]; exact hyi.pow _)
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hD
  refine ⟨⟨θ, hyi⟩, d, ?_, ?_, fun a => ?_⟩
  · rintro rfl
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa using hd.symm)
  · show Algebra.adjoin ℚ {θ} = ⊤
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθℚ.isAlgebraic, hθ]; rfl
  · have hm := Algebra.discr_mul_isIntegral_mem_adjoin ℚ (R := ℤ) (B := B)
      (by rw [hBgen]; exact hyi) a.2
    rw [hBgen, ← hd, Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨g, hg⟩ := hm
    refine ⟨g, Subtype.ext ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hg
    have h1 : ((aeval (⟨θ, hyi⟩ : 𝓞 E) g : 𝓞 E) : E) = aeval θ g :=
      (aeval_algebraMap_apply E (⟨θ, hyi⟩ : 𝓞 E) g).symm
    refine Eq.trans ?_ h1.symm
    rw [hg, algebraMap_smul, zsmul_eq_mul]
    push_cast; rfl
end _root_.GlobalTheory.SW.SplitPrime
end GlobalTheory.SW.SplitPrime
