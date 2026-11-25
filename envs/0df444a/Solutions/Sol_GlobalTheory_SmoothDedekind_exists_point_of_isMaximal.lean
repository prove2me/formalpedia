-- Prove2me | solution 1 for GlobalTheory.SmoothDedekind.exists_point_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:47.173107+00:00
-- url     : https://prove2.me/submissions/bdaa7c84-ec11-426f-b8f5-88cffb410abb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
import Theorems.Thm_GlobalTheory_SmoothTangent_finrank_cotangent_le_finrank_derivation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
namespace GlobalTheory.SmoothDedekind
theorem _root_.solution (k : Type) [Field k] [PerfectField k] {B : Type} [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] (x : Ideal B) [x.IsMaximal] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (r : ℕ)
      (g : B →+* TrivSqZeroExt C (Fin r → C)), Module.finrank (B ⧸ x) x.Cotangent ≤ r ∧
      (∀ c : k, (g (algebraMap k B c)).snd = 0) ∧
      ∀ lam : (Fin r → C) →ₗ[C] C, (∀ b, lam (g b).snd = 0) → lam = 0 := by
  let := Ideal.Quotient.field x
  let C := AlgebraicClosure (B ⧸ x)
  have : Module.Finite C (Derivation k B C) := .equiv (derivationEquivDual k B C).symm
  let D := Module.finBasis C (Derivation k B C)
  refine ⟨C, inferInstance, inferInstance, _, pointOfDerivations D,
    finrank_cotangent_le_finrank_derivation k x C, fun c ↦ funext fun i ↦ (D i).map_algebraMap c,
    fun lam h ↦ ?_⟩
  have h₀ : ∑ i, lam (Pi.single i 1) • D i = 0 := by
    ext b
    have h₁ : lam (fun i ↦ D i b) = 0 := h b
    rw [LinearMap.pi_apply_eq_sum_univ] at h₁
    have h₂ : (∑ i, lam (Pi.single i 1) • D i) b = ∑ i, lam (Pi.single i 1) * D i b := by
      have := map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := B) (M := C))
        (fun i ↦ lam (Pi.single i 1) • D i) Finset.univ
      have := congrFun this b
      rw [Finset.sum_apply] at this
      exact this
    rw [h₂, Derivation.zero_apply, ← h₁]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
  simpa using Fintype.linearIndependent_iff.mp D.linearIndependent _ h₀ i
end GlobalTheory.SmoothDedekind
