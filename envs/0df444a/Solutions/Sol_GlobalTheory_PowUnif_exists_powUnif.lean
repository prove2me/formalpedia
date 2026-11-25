-- Prove2me | solution 1 for GlobalTheory.PowUnif.exists_powUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:26.764428+00:00
-- url     : https://prove2.me/submissions/8caf7176-8cc0-4125-a119-4144a4f406eb

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
import Theorems.Thm_GlobalTheory_PowUnif_IsHolFamily_precomp
import Theorems.Thm_GlobalTheory_PowUnif_isHolFamily_pow
import Theorems.Thm_GlobalTheory_PowUnif_exists_frame
import Theorems.Thm_GlobalTheory_PowUnif_blockPr_blockIn
import Theorems.Thm_GlobalTheory_PowUnif_blockLat_discrete
import Theorems.Thm_GlobalTheory_PowUnif_blockLat_full
import Theorems.Thm_GlobalTheory_PowUnif_pow_hom_ext
import Theorems.Thm_GlobalTheory_PowUnif_powLift_pr

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
variable {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)
variable {L : LB G.left} {g : ℕ} (u : HolUnif G L g)
namespace GlobalTheory.PowUnif
theorem _root_.solution (hL : L.IsLB) {L' : LB G'.left} (hL' : L'.IsLB) (w : LB.Iso L' (Out.boxLB L p.pr))
    (hw : w.IsGen) {n : ℕ} (e : Fin j × Fin g ≃ Fin n) :
    ∃ u' : HolUnif G' L' n, (∀ z, z ∈ u'.Λ ↔ ∀ i, blockPr e i z ∈ u.Λ) ∧
      (∀ z i, u'.ex z ≫ p.pr i = u.ex (blockPr e i z)) ∧
      ∀ jj b z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (Out.boxLB L p.pr).U jj → ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U b →
        ∏ i, u.fr (jj i) (blockPr e i z) =
          valAt' (u'.ex z).left ((Out.boxLB L p.pr).U jj ⊓ L'.U b) (w.s (jj, b)).val * u'.fr b z := by
  let ex : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ G') := fun z => powLift p fun i => u.ex (blockPr e i z)
  have hex : ∀ z i, ex z ≫ p.pr i = u.ex (blockPr e i z) := fun z i => powLift_pr p _ i
  let c : (Fin n → ℂ) → (Sp ℂ ⟶ G'.left) := fun z => (ex z).left
  let d : (Fin g → ℂ) → (Sp ℂ ⟶ G.left) := fun z => (u.ex z).left
  have hcd : ∀ z i, c z ≫ (p.pr i).left = d (blockPr e i z) := fun z i => congrArg (·.left) (hex z i)
  have hd : IsHolFamily d := u.hol
  have hc : IsHolFamily c := isHolFamily_pow p ex fun i => by
    simp only [hex]
    exact hd.precomp (blockPr e i).differentiable
  obtain ⟨fr', h₁, h₂, h₃, h₄⟩ := exists_frame hc hL hL' (fun i => (p.pr i).left) w hw
    (fun i a z => u.fr a (blockPr e i z))
    (fun i a => by
      simp only [hcd]
      exact (u.fr_hol a).comp (blockPr e i).differentiable.differentiableOn fun _ hz => hz)
    (fun i a z hz => u.fr_ne a _ (by rw [hcd] at hz; exact hz))
    (fun i a a' z hz => by
      rw [hcd] at hz ⊢
      exact u.fr_compat a a' _ hz)
  have := u.discrete
  refine ⟨⟨ex, fun z z' => pow_hom_ext p fun i => ?_, fun a => ?_, blockLat e u.Λ, fun z => ?_,
    blockLat_discrete e u.Λ, blockLat_full e u.Λ u.full, hc, fr', h₁, h₂, h₃⟩, fun z => Iff.rfl, hex, h₄⟩
  · have := p.hom i
    rw [MonObj.mul_comp, hex, hex, hex, map_add, u.ex_add]
  · choose z hz using fun i => u.ex_onto (a ≫ p.pr i)
    refine ⟨∑ i, blockIn e i (z i), pow_hom_ext p fun i => ?_⟩
    rw [hex, ← hz, map_sum]
    simp only [blockPr_blockIn, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · constructor
    · intro h i
      have := p.hom i
      rw [← u.ker, ← hex, h, MonObj.one_comp]
    · intro h
      refine pow_hom_ext p fun i => ?_
      have := p.hom i
      rw [hex, MonObj.one_comp, (u.ker _).2 (h i)]
end GlobalTheory.PowUnif
