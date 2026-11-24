-- Prove2me | solution 1 for GlobalTheory.MulSplit.Descends.weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:57.503969+00:00
-- url     : https://prove2.me/submissions/364225e3-e125-47e3-b2a6-e2dfff7cc556

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_mul_mem_Sg
import Theorems.Thm_GlobalTheory_MulSplit_pl_pl
import Theorems.Thm_GlobalTheory_MulSplit_pl_mem_Sg
import Theorems.Thm_GlobalTheory_MulSplit_Descends_injective
import Theorems.Thm_GlobalTheory_MulSplit_Descends_exists_mem

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B} {G : Type}
namespace GlobalTheory.MulSplit
namespace Descends
theorem _root_.solution (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    (hτ : ∀ g, τ g ≫ p = p) (hτq : ∀ g, τ g ≫ q = q) {D E F : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (hu : IsG E u)
    (χ : G → Γ(B, ⊤)ˣ) (hχ : ∀ g, pl L (τ g) (hτ g) u.val = (χ g).val • u.val)
    (hF : D.mapDomain (q ≫ ·) + E = F) :
    ∃ f : Sg L p D →ₗ[Γ(B, ⊤)] Vals L p, Function.Injective f ∧
      ∀ v, (∃ x, f x = v) ↔ v ∈ Sg L p F ∧ ∀ g, pl L (τ g) (hτ g) v = (χ g).val • v := by
  refine ⟨⟨⟨fun x => pl L q hq x.1 * u.val, fun x y => ?_⟩, fun c x => ?_⟩, ?_, fun v => ⟨?_, ?_⟩⟩
  · rw [Submodule.coe_add, map_add, add_mul]
  · show pl L q hq (c • x.1) * u.val = c • (pl L q hq x.1 * u.val)
    rw [map_smul, smul_mul_assoc]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (H.injective hL hq x.2 (u.mul_left_eq_zero.1 hx))
  · rintro ⟨x, rfl⟩
    refine ⟨mul_mem_Sg hL (pl_mem_Sg hL hq x.2 rfl) hu.1 hF, fun g => ?_⟩
    show pl L (τ g) (hτ g) (pl L q hq x.1 * u.val) = (χ g).val • (pl L q hq x.1 * u.val)
    rw [map_mul, hχ, pl_pl _ _ hq (hτq g), mul_smul_comm]
  · rintro ⟨hv, hv'⟩
    obtain ⟨w, hw, e⟩ := H.exists_mem hL hq hτ hτq (D := D) (v := v * (u⁻¹).val)
      (mul_mem_Sg hL hv hu.2 (by rw [← hF]; abel)) (fun g => by
        have h1 : pl L (τ g) (hτ g) (v * (u⁻¹).val) * pl L (τ g) (hτ g) u.val = pl L (τ g) (hτ g) v := by
          rw [← map_mul, Units.inv_mul_cancel_right]
        rw [hχ, hv', mul_smul_comm] at h1
        have h2 := congrArg (fun t => ((χ g)⁻¹).val • t) h1
        simp only [smul_smul, Units.inv_mul, one_smul] at h2
        exact (Units.eq_mul_inv_iff_mul_eq u).2 h2)
    refine ⟨⟨w, hw⟩, ?_⟩
    show pl L q hq w * u.val = v
    rw [e, Units.inv_mul_cancel_right]
end Descends
end GlobalTheory.MulSplit
