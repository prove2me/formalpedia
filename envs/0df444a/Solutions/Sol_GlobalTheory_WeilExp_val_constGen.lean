-- Prove2me | solution 1 for GlobalTheory.WeilExp.val_constGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:40.402973+00:00
-- url     : https://prove2.me/submissions/e5efc5ab-4e8a-42ee-a54c-f7ec653f5dd3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_WeilIsExpRiemannForm
import Theorems.Thm_GlobalTheory_WeilExp_le_wchart_iff
import Theorems.Thm_GlobalTheory_WeilExp_val_res
import Theorems.Thm_GlobalTheory_WeilExp_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.WeilExp
variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.WeilExp
theorem _root_.solution {A : Over (Sp ℂ)} [GrpObj A] (M : LB A.left) (V : (𝟙_ (Over (Sp ℂ))).left.Opens) (c : ℂˣ)
    (x : 𝟙_ (Over (Sp ℂ)) ⟶ Out.overRes V ⊗ A) (j : PEmpty → M.ι) :
    valAt' x.left _ ((Out.constGen A M (Out.unitRes V (unitOn c))).s j).val = c := by
  have hx : ⊤ ≤ x.left ⁻¹ᵁ LB.wchart M (Y := (Out.overRes V ⊗ A).left) (K := PEmpty) PEmpty.elim j :=
    (le_wchart_iff _ _ _ _).2 fun k => k.elim
  refine (val_res hv x.left _ _ hx).trans ?_
  refine (val_pull hv x.left (fst (Out.overRes V) A).left ⊤ _).trans ?_
  refine (val_pull hv _ V.ι ⊤ (unitOn c)).trans ?_
  have e : (x.left ≫ (fst (Out.overRes V) A).left) ≫ V.ι = 𝟙 (Sp ℂ) := by
    have : (x ≫ fst (Out.overRes V) A) ≫ Out.overResι V = 𝟙 _ := Subsingleton.elim _ _
    exact congrArg (·.left) this
  rw [e]
  have := (hv _ (𝟙 (Sp ℂ))).2.2.2.2.2 (𝟙 _) (Category.id_comp _) ⊤ c le_top
  refine Eq.trans ?_ this
  congr 1
end GlobalTheory.WeilExp
