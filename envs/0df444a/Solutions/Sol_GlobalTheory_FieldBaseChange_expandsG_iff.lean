-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.expandsG_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:03:26.670744+00:00
-- url     : https://prove2.me/submissions/8204e97d-fa6a-4ae0-8547-20ca4b0e72ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_secLin_iff
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver


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
theorem _root_.solution (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) :
    U.ExpandsG F k v s ↔ ∃ (n : ℕ) (c : Fin n → F) (x : Fin n → IntSec U k × ∀ α, IntTerm D k α),
      (∀ i, x i ∈ expansionPairs U k) ∧ v = ∑ i, c i • extendSec U F k (genericSec U k (x i).1) ∧
      ∀ α, famProj D.toPre F k α s =
        ∑ i, c i • termPull D.toPre (FractionRing R) F k α (genericTerm D k α ((x i).2 α)) := by
  have e₁ := fun (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) => secLin_iff U.LG.isLB v σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))
  have e₂ := fun α (n : ℕ) (c : Fin n → F) (f : Fin n → IntTerm D k α) => secLin_iff D.toPre.P.isLB
    (famProj D.toPre F k α s) f (DegPre.prB D.toPre F).left c
    (fun i => termPull D.toPre (FractionRing R) F k α (genericTerm D k α (f i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f i) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F)))))))
  constructor
  · rintro ⟨n, c, σ, f, h₃, h₁, h₂⟩
    exact ⟨n, c, fun i => (σ i, f i), h₃, (e₁ n c σ).1 h₁, fun α => (e₂ α n c fun i => f i α).1 (h₂ α)⟩
  · rintro ⟨n, c, x, h₃, h₁, h₂⟩
    exact ⟨n, c, fun i => (x i).1, fun i => (x i).2, h₃, (e₁ n c _).2 h₁,
      fun α => (e₂ α n c fun i => (x i).2 α).2 (h₂ α)⟩
end GlobalTheory.FieldBaseChange
