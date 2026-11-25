-- Prove2me | solution 1 for GlobalTheory.PullUnifHom.exists_holUnif_pull_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:32.65684+00:00
-- url     : https://prove2.me/submissions/8bbb07b9-72e1-476c-a225-70b381496b2b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHolUnifPullAlongGroupHom
import Theorems.Thm_P2M_GlobalTheory_PullUnifHom_chart_pull_iff__be1866fa7be3
import Theorems.Thm_P2M_GlobalTheory_PullUnifHom_le_left__12395fff6ef7
import Theorems.Thm_P2M_GlobalTheory_PullUnifHom_le_right__76c8cd51ee71
import Theorems.Thm_P2M_GlobalTheory_PullUnifHom_valAt__pull_g__975f6bbd66e3

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.PullUnifHom
open GlobalTheory.PullHermitian
variable {X Y : Scheme.{0}}
namespace GlobalTheory.PullUnifHom
theorem _root_.solution : ∀ (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (φ : A ⟶ B) (L : LB B.left) (g : ℕ) (u' : HolUnif B L g)
    (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ' : u'.Λ → ℂ),
    (∀ z w, ex (z + w) = ex z * ex w) → Function.Surjective ex → (∀ z, ex z = 1 ↔ z ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}) →
    (∀ z, ex z ≫ φ = u'.ex z) → Λ ≤ u'.Λ → u'.IsAH Hm χ' →
    ∃ (u : HolUnif A (L.pull φ.left) g) (χ : u.Λ → ℂ), (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro A B _ _ φ L g u' ex Λ Hm χ' hadd honto hker hdisc hfull hhol hφ hΛ hAH
  have keyl : ∀ z, (ex z).left ≫ φ.left = (u'.ex z).left := fun z => by rw [← Over.comp_left, hφ]
  have hch : ∀ (j : (L.pull φ.left).ι) z, (⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔
      ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  let u : HolUnif A (L.pull φ.left) g :=
    ⟨ex, hadd, honto, Λ, hker, hdisc, hfull, hhol, fun j z => u'.fr (j PUnit.unit) z,
     fun j => (u'.fr_hol (j PUnit.unit)).mono (fun z hz => (hch j z).1 hz),
     fun j z hz => u'.fr_ne _ _ ((hch j z).1 hz),
     fun i j z h => by
        have hi := (hch i z).1 (le_left' h)
        have hj := (hch j z).1 (le_right' h)
        show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
        rw [valAt'_pull_g' _ L _ i j h, keyl z]
        exact u'.fr_compat _ _ _ (inf_of _ hi hj)⟩
  refine ⟨u, fun l => χ' ⟨l.1, hΛ l.2⟩, fun w => Iff.rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hAH
  exact ⟨h1, h2, fun l => h3 _, fun l i z hz => h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((hch i z).1 hz)⟩
end GlobalTheory.PullUnifHom
