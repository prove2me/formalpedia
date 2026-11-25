-- Prove2me | solution 1 for GlobalTheory.CycAway.exists_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:52.144801+00:00
-- url     : https://prove2.me/submissions/709133bb-79ae-46e6-9ec7-f565b9951c89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsLocalizationOfLeClosure
import Theorems.Thm_GlobalTheory_CycAway_dedekind_closure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.CycAway
open NumberField
namespace GlobalTheory.CycAway
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n a : ℕ), n.Prime → ∃ (o : Subring Ω) (ze : oˣ), IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧ IsUnit (n : o) ∧ IsPrimitiveRoot (Units.map o.subtype.toMonoidHom ze) (n ^ a) ∧ o = Subring.closure {((ze : o) : Ω), (n : Ω)⁻¹} := by
  intro Ω _ _ _ n a hn
  haveI := Fact.mk hn
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  let K := CyclotomicField (n ^ a) ℚ
  haveI : IsCyclotomicExtension {n ^ a} ℚ K := CyclotomicField.isCyclotomicExtension (n ^ a) ℚ
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  let φ : K →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := K) (M := Ω)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec (n ^ a) ℚ K
  set ζ := IsCyclotomicExtension.zeta (n ^ a) ℚ K
  obtain ⟨hD, hF⟩ := dedekind_closure hn φ hζ
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  have hz : IsPrimitiveRoot (φ ζ) (n ^ a) := hζ.map_of_injective φ.injective
  let z : T := ⟨φ ζ, Subring.subset_closure (Or.inl rfl)⟩
  have hz' : IsPrimitiveRoot z (n ^ a) := IsPrimitiveRoot.of_map_of_injective (f := T.subtype) hz T.subtype_injective
  have hu : IsUnit z := hz'.isUnit (NeZero.ne _)
  refine ⟨T, hu.unit, hD, hF, ?_, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ⟨_, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext ?_)
    simp [h0]
  · rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz
  · rfl
end GlobalTheory.CycAway
