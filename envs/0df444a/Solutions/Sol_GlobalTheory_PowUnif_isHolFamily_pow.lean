-- Prove2me | solution 1 for GlobalTheory.PowUnif.isHolFamily_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:10:23.135227+00:00
-- url     : https://prove2.me/submissions/a559f3cf-7568-4360-a7ee-8108e1fe42da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_IsHolFamily_comp
import Theorems.Thm_GlobalTheory_PowUnif_isHolFamily_powObj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PowUnif
theorem _root_.solution {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)
    (c : E → (𝟙_ (Over (Sp ℂ)) ⟶ G'))
    (h : ∀ i, IsHolFamily (Z := G.left) (fun z => (c z ≫ p.pr i).left)) :
    IsHolFamily (Z := G'.left) (fun z => (c z).left) := by
  let φ : G' ⟶ Out.powObj G j := (Out.powIsLimit G j).lift (Fan.mk _ p.pr)
  let ψ : Out.powObj G j ⟶ G' := p.lim.lift (Fan.mk _ (Out.powPr G))
  have hφ : ∀ i, φ ≫ Out.powPr G i = p.pr i := fun i => (Out.powIsLimit G j).fac (Fan.mk _ p.pr) ⟨i⟩
  have hψ : ∀ i, ψ ≫ p.pr i = Out.powPr G i := fun i => p.lim.fac (Fan.mk _ (Out.powPr G)) ⟨i⟩
  have hφψ : φ ≫ ψ = 𝟙 _ := p.lim.hom_ext fun ⟨i⟩ => by
    change (φ ≫ ψ) ≫ p.pr i = 𝟙 _ ≫ p.pr i
    rw [Category.assoc, hψ, hφ, Category.id_comp]
  have h1 := (isHolFamily_powObj G j (fun z => c z ≫ φ) (fun i => by
    simpa only [Category.assoc, hφ] using h i)).comp ψ.left
  have h2 : ∀ z, (c z ≫ φ).left ≫ ψ.left = (c z).left := fun z => by
    rw [← Over.comp_left, Category.assoc, hφψ, Category.comp_id]
  have h3 : (fun z => (c z ≫ φ).left ≫ ψ.left) = fun z => (c z).left := funext h2
  exact h3 ▸ h1
end GlobalTheory.PowUnif
