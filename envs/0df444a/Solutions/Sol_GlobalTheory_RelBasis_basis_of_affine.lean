-- Prove2me | solution 1 for GlobalTheory.RelBasis.basis_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:10.542944+00:00
-- url     : https://prove2.me/submissions/7a3ab72f-4798-4882-a756-9924fcd9b070

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisOfAffineOpens
import Theorems.Thm_GlobalTheory_RelBasis_comb_res
import Theorems.Thm_GlobalTheory_RelBasis_comb_sub
import Theorems.Thm_GlobalTheory_RelBasis_exists_affine_le
import Theorems.Thm_GlobalTheory_RelBasis_indepOn_of_affine

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
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.RelBasis
variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}
namespace GlobalTheory.RelBasis
theorem _root_.solution (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t))
    (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W) (W : T.Opens) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hI := indepOn_of_affine b p₁ p₂ fun W hW => (H W hW).1
  refine ⟨hI W, fun σ hσ => ?_⟩
  let Ix := {V : T.Opens // IsAffineOpen V ∧ V ≤ W}
  have hloc : ∀ V : Ix, ∃ c : Fin N → Γ(T, V.1), ∀ (y : Y) (i : L.ι), p₁ y ∈ V.1 → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ V.1 c y i := by
    intro V
    have hle : ∀ i, p₁ ⁻¹ᵁ V.1 ⊓ p₂ ⁻¹ᵁ L.U i ≤ p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i := fun i y hy => ⟨V.2.2 hy.1, hy.2⟩
    have hr : ∀ (y : Y) i, p₁ y ∈ V.1 → p₂ y ∈ L.U i →
        gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (hle i)).op).hom (σ i)) = gs (𝟙 Y) y _ (σ i) :=
      fun y i h₁ h₂ => gs_res (𝟙 Y) y (hle i) ⟨h₁, h₂⟩ _
    obtain ⟨c, hc⟩ := (H V.1 V.2.1).2 (fun i => (Y.presheaf.map (homOfLE (hle i)).op).hom (σ i))
      (fun y i i' h₁ h₂ h₃ => (hr y i h₁ h₂).trans ((hσ y i i' (V.2.2 h₁) h₂ h₃).trans
        (congrArg _ (hr y i' h₁ h₃).symm)))
    exact ⟨c, fun y i h₁ h₂ => (hr y i h₁ h₂).symm.trans (hc y i h₁ h₂)⟩
  choose c hc using hloc
  have hcomp : ∀ V V' : Ix, (fun k => (T.presheaf.map (homOfLE (inf_le_left : V.1 ⊓ V'.1 ≤ V.1)).op).hom (c V k)) =
      (fun k => (T.presheaf.map (homOfLE (inf_le_right : V.1 ⊓ V'.1 ≤ V'.1)).op).hom (c V' k)) := by
    intro V V'
    refine sub_eq_zero.1 (hI (V.1 ⊓ V'.1) _ fun y i h₁ h₂ => ?_)
    rw [comb_sub b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁,
      ← hc V y i h₁.1 h₂, ← hc V' y i h₁.2 h₂, sub_self]
  have glue : ∀ k, ∃ a : Γ(T, W), ∀ V : Ix, (T.presheaf.map (homOfLE V.2.2).op).hom a = c V k := by
    intro k
    obtain ⟨a, ha, -⟩ := T.sheaf.existsUnique_gluing' (fun V : Ix => V.1) W (fun V => homOfLE V.2.2)
      (fun x hx => by
        obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hxV⟩) (fun V => c V k)
      (fun V V' => congrFun (hcomp V V') k)
    exact ⟨a, ha⟩
  choose a ha using glue
  refine ⟨a, fun y i h₁ h₂ => ?_⟩
  obtain ⟨V, hV, hyV, hle⟩ := exists_affine_le W (p₁ y) h₁
  rw [hc ⟨V, hV, hle⟩ y i hyV h₂, ← comb_res b p₁ p₂ hle a y i hyV]
  exact congrArg (fun c => comb b p₁ p₂ V c y i) (funext fun k => (ha k ⟨V, hV, hle⟩).symm)
end GlobalTheory.RelBasis
