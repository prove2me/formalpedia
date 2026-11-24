-- Prove2me | solution 1 for GlobalTheory.ExpandsLinear.secScal_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:21:26.785064+00:00
-- url     : https://prove2.me/submissions/41967d65-3fec-4940-a0c1-c02e29346595

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap
import Theorems.Thm_GlobalTheory_ExpandsLinear_scalOn_apply
import Theorems.Thm_GlobalTheory_ExpandsLinear_scal_comp_specMap
import Theorems.Thm_GlobalTheory_ExpandsLinear_app_resTop_scal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ExpandsLinear
namespace GlobalTheory.ExpandsLinear
theorem _root_.solution {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {X Y Y' : Scheme.{0}} (L : LB X)
    {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ)
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y) (π : Y' ⟶ Spec (CommRingCat.of C))
    (π' : Y' ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ Spec (CommRingCat.of R))
    (hπ : π' = π ≫ Spec.map (CommRingCat.ofHom φ)) (hp : h ≫ p = π') {n : ℕ}
    (s : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (t : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (r a : Fin n → R) (d : R) (c : Fin n → C) (hc : ∀ i, φ (a i) * φ (r i) = φ d * c i)
    (H : ∀ i, GeneratorPullback.SecScal L φ₁ ε₁ (s i) φ₂ ε₂ (t i) h (scal π' (r i)))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (hs : ∀ j, s₀.f j = ∑ i, resTop _ (scal π (c i)) * (s i).f j) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₀ φ₂ ε₂ (secComb (fun i => scal p (a i)) t) h (scal π' d) := by
  intro j₁ j₂ hco
  erw [hs]
  dsimp only [secComb]
  erw [map_sum, map_sum, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have Hi := H i j₁ j₂ hco
  erw [map_mul, map_mul, map_mul, Hi, app_resTop_scal, SecOps.resTop_res, SecOps.resTop_res]
  rw [hp, hπ, scal_comp_specMap, scal_comp_specMap, scal_comp_specMap, ← _root_.mul_assoc, ← _root_.mul_assoc]
  simp only [scalOn_apply]
  rw [← map_mul, hc, map_mul]
end GlobalTheory.ExpandsLinear
