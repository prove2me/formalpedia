-- Prove2me | solution 1 for GlobalTheory.LieEtale.lieMult_iff_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:56.755838+00:00
-- url     : https://prove2.me/submissions/d23362bb-b20b-4203-910b-f00a027b1ab8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
import Theorems.Thm_GlobalTheory_LieEtale_mult_iff
import Theorems.Thm_GlobalTheory_LieEtale_epsPtZero_epsPtScale
import Theorems.Thm_GlobalTheory_LieEtale_lieMult_iff
import Theorems.Thm_GlobalTheory_LieEtale_existsUnique_tangent_lift

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
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
namespace GlobalTheory.LieEtale
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n := by
  intro O _ S A B _ _ ψ a b _ _ hab k _ x τ n
  rw [lieMult_iff, lieMult_iff]
  exact mult_iff ψ _ _ (epsPtZero_epsPtScale x) a.act b.act a.hom hab τ
    (existsUnique_tangent_lift x ψ) n
end GlobalTheory.LieEtale
