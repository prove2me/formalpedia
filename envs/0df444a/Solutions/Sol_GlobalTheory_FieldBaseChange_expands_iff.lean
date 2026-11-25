-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.expands_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:57:33.434723+00:00
-- url     : https://prove2.me/submissions/86ebf0a8-132e-430f-9cd5-431ec2c8b5bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_secScal_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (k : ℕ) (v : SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (s : Fam D.toPre (FractionRing R) k) : U.Expands k v s ↔ ∃ r : R, r ≠ 0 ∧ ∃ x ∈ expansionPairs U k,
      genericSec U k x.1 = algebraMap R (FractionRing R) r • v ∧
      ∀ α, genericTerm D k α (x.2 α) = algebraMap R (FractionRing R) r • famProj D.toPre _ k α s := by
  have e₁ := fun (σ : IntSec U k) (r : R) => secScal_iff (p := pullback.fst G.hom (jK R)) pullback.condition
    (fun _ => (Category.comp_id _).symm) U.LG.isLB v σ _ (algebraMap R (FractionRing R)) rfl r
  have e₂ := fun α (f : IntTerm D k α) (r : R) => secScal_iff (prB_hom D.toPre (FractionRing R))
    (famφ_prB D.toPre (FractionRing R) α) D.toPre.P.isLB (famProj D.toPre _ k α s) f _
    (algebraMap R (FractionRing R)) (bf_hom D.toPre (FractionRing R)) r
  constructor
  · rintro ⟨r, hr, σ, f, h₁, h₂, h₃⟩
    exact ⟨r, hr, (σ, f), h₃, (e₁ σ r).1 h₁, fun α => (e₂ α (f α) r).1 (h₂ α)⟩
  · rintro ⟨r, hr, x, h₃, h₁, h₂⟩
    exact ⟨r, hr, x.1, x.2, (e₁ x.1 r).2 h₁, fun α => (e₂ α (x.2 α) r).2 (h₂ α), h₃⟩
end GlobalTheory.FieldBaseChange
