-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.kMap_pA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:06.136199+00:00
-- url     : https://prove2.me/submissions/0d5791e4-2c84-4a91-9a2d-b1e1f51d97f6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_appLE_chain
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_algebraMap_epsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}
attribute [local instance] unit_isAffine
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (x : (OSys A.hom S).obj (op a₀)) :
    (kMap ha).α b (pA A S ((tK a₀).obj b) x) = algebraMap R ((OSys A.hom S).obj b) (epsA ha x) := by
  let tU := secA (wOver (toUnit A)) (⟨(S.u b.unop, ⟨⊤, isAffineOpen_top _⟩), le_top⟩ : Pair (toUnit A).left)
  have h1 : algebraMap R ((OSys A.hom S).obj b) (epsA ha x) = tU (secA (wOver η[A]) (ptPair ha) x) := by
    rw [← algebraMap_epsA]
    exact (tU.commutes _).symm
  rw [h1]
  have hE : ∀ W : A.left.Opens, W ≤ (A.hom ≫ η[A].left) ⁻¹ᵁ (S.u a₀).1 := fun W x _ ↦ by
    have h2 : A.hom x ∈ η[A].left ⁻¹ᵁ (S.u a₀).1 := by rw [ha]; trivial
    exact h2
  exact (appLE_chain (iota A).left (fst A A).left (A.hom ≫ η[A].left) (iota_fst A) _ _ (hE _) x).trans
    (appLE_chain A.hom η[A].left (A.hom ≫ η[A].left) rfl _ _ (hE _) x).symm
end GlobalTheory.CompanionTheory.HopfSys
