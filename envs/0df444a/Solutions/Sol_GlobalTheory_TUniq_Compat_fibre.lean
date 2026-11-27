-- Prove2me | solution 1 for GlobalTheory.TUniq.Compat.fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:03.706979+00:00
-- url     : https://prove2.me/submissions/cd059857-0b24-42a3-94e8-47a7afb24d33

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
import Theorems.Thm_GlobalTheory_dense_fibres_ext
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced


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
namespace Compat
theorem _root_.solution {t t' : TObj g k J b s} {φ : t.A.left ⟶ t'.A.left} (h : Compat t t' (𝟙 _) φ)
    {K : Type} [Field K] [IsAlgClosed K] {su : Sp K ⟶ Sp o} {u : TObj g k J b su} {x : Sp K ⟶ S}
    {ψ : u.A.left ⟶ t.A.left} {ψ' : u.A.left ⟶ t'.A.left} (h₁ : MapBy u t x ψ) (h₂ : MapBy u t' x ψ') :
    ψ ≫ φ = ψ' := by
  have := u.ab.proper
  have := u.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced u.A.hom
  have w : (ψ ≫ φ) ≫ t'.A.hom = u.A.hom ≫ x := by rw [Category.assoc, h.1, Category.id_comp, h₁.1.1.w]
  have e : h₂.1.1.lift _ _ w = 𝟙 _ :=
    (GlobalTheory.dense_fibres_ext _ _ u.A.hom Set.univ dense_univ).2.1 _ u.A.hom _ _ (h₂.1.1.lift_snd _ _ _)
      (Category.id_comp _) fun B _ _ z _ => by
        apply h₂.1.1.hom_ext
        · rw [Category.assoc, h₂.1.1.lift_fst, Category.comp_id, ← Category.assoc]
          exact h.2 K su u x ψ ψ' h₁ h₂ B z _ (Category.comp_id _)
        · rw [Category.assoc, h₂.1.1.lift_snd, Category.comp_id]
  rw [← h₂.1.1.lift_fst _ _ w, e, Category.id_comp]
end Compat
end GlobalTheory.TUniq
