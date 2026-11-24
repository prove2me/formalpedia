-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.genOpen_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:40.502715+00:00
-- url     : https://prove2.me/submissions/6d2b501a-01fa-477b-a5cd-c57580281857

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution [IsDomain R] [IsFractionRing R K] {π : R} (hπ : π ≠ 0) (φ : B →ₐ[R] C) (hi : Function.Injective φ)
    (hs : ∀ b' : C, ∃ (n : ℕ) (b : B), algebraMap R C π ^ n * b' = φ b) : GenOpen K φ := by
  unfold GenOpen
  have hb : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) φ) := by
    constructor
    · haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) φ.toLinearMap hi
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy =>
        obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
        exact ⟨x + y, map_add _ _ _⟩
      | tmul k c =>
        obtain ⟨n, b, hb⟩ := hs c
        have h0 : algebraMap R K (π ^ n) ≠ 0 := by
          simpa using fun h => absurd h hπ
        refine ⟨(k * (algebraMap R K (π ^ n))⁻¹) ⊗ₜ b, ?_⟩
        rw [Algebra.TensorProduct.map_tmul, ← hb, ← map_pow, ← Algebra.smul_def, ← TensorProduct.smul_tmul,
          AlgHom.id_apply, Algebra.smul_def, mul_comm, _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.mul_one]
  have : IsIso (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance
end GlobalTheory.SS.Smoothening
