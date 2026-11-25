-- Prove2me | solution 1 for GlobalTheory.TUniq.ext_of_geoGood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:25:31.821171+00:00
-- url     : https://prove2.me/submissions/a1ee4705-a976-4535-82a7-7298518092e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Theorems.Thm_GlobalTheory_TUniq_epi_spMap
import Theorems.Thm_GlobalTheory_dense_fibres_ext


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
noncomputable section
open GlobalTheory GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
namespace GlobalTheory.TUniq
theorem _root_.solution {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X Y : Scheme.{0}}
    [IsReduced X] (p : X ⟶ S) [Flat p] [LocallyOfFinitePresentation p] (q : Y ⟶ S) [IsSeparated q] {f f' : X ⟶ Y}
    (hf : f ≫ q = p) (hf' : f' ≫ q = p)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ y : Sp K ⟶ X, y ≫ p = x → y ≫ f = y ≫ f') : f = f' := by
  refine (GlobalTheory.dense_fibres_ext X S p Sg hd).2.1 Y q f f' hf hf' fun K _ _ y hy => ?_
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := hg K (y ≫ p) hy
  have := epi_spMap i
  rw [← cancel_epi (spMap i), ← Category.assoc, ← Category.assoc]
  exact H Ω su u _ ψ ψ' h₁ h₂ _ (Category.assoc _ _ _)
end GlobalTheory.TUniq
