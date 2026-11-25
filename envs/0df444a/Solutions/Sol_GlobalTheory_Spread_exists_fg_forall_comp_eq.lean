-- Prove2me | solution 1 for GlobalTheory.Spread.exists_fg_forall_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:51:53.936904+00:00
-- url     : https://prove2.me/submissions/e923e762-efd6-4e30-bfb1-88b7baf1d8ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq
import Theorems.Thm_GlobalTheory_Spread_fg_iSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution [QuasiCompact pB] [QuasiSeparated pB]
    [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (φ : ι → (pullback pB (spMap (algebraMap k A)) ⟶ Z))
    (hφ : ∀ i, φ i ≫ pZ = pullback.fst _ _ ≫ pB) (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (ψ : ι → (pullback pB (spMap (algebraMap k R)) ⟶ Z)),
      R.FG ∧ R₀ ≤ R ∧ ∀ i, ψ i ≫ pZ = pullback.fst _ _ ≫ pB ∧ bcMap pB R.val ≫ ψ i = φ i := by
  choose R ψ hR h₁ h₂ using fun i ↦ exists_fg_comp_eq pB pZ (φ i) (hφ i)
  have hle (i) : R i ≤ R₀ ⊔ ⨆ i, R i := le_sup_of_le_right (le_iSup R i)
  refine ⟨R₀ ⊔ ⨆ i, R i, fun i ↦ bcMap pB (Subalgebra.inclusion (hle i)) ≫ ψ i,
    hR₀.sup (fg_iSup hR), le_sup_left, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [Category.assoc, h₁, bcMap_fst_assoc]
  · rw [bcMap_comp_of_eq_assoc pB _ _ (R i).val fun _ ↦ rfl]
    exact h₂ i
end GlobalTheory.Spread
