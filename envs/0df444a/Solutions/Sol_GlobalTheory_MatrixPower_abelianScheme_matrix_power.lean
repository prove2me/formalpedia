-- Prove2me | solution 1 for GlobalTheory.MatrixPower.abelianScheme_matrix_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:33:00.802507+00:00
-- url     : https://prove2.me/submissions/d1a5651f-e22d-47a4-b74c-2a75584431f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeEighthPowerOfMatrixAction
import Theorems.Thm_GlobalTheory_MatrixPower_exists_power
import Theorems.Thm_GlobalTheory_Retract_over_properties


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
open GlobalTheory GlobalTheory.MatrixPower
namespace GlobalTheory.MatrixPower
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  intro S G _ ρ hab hρ hmul hadd hone
  obtain ⟨hcomm, hsmooth, hproper, hgeo⟩ := hab
  obtain ⟨A, gA, hcA, R, pr, hpr, huniv, hact⟩ := exists_power (0 : Fin 8) G ρ hρ hmul hadd hone
  obtain ⟨-, -, -, hsm, -, -, -, -, hpro, -, hgc, -, -⟩ := GlobalTheory.Retract.over_properties R
  refine ⟨A, gA, pr, ⟨hcA, hsm hsmooth, hpro hproper, hgc hgeo⟩, hpr, huniv, fun m u => ?_⟩
  rw [hact, List.prod_ofFn]
end GlobalTheory.MatrixPower
