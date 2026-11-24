-- Prove2me | solution 1 for GlobalTheory.existsUnique_comb_of_independent_special_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:08.935918+00:00
-- url     : https://prove2.me/submissions/aa84ee23-b44e-4d07-a348-3dca9eaafc3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueCombOfIndependentSpecialFibre
import Theorems.Thm_GlobalTheory_SaturatedSections_existsUnique_comb
import Theorems.Thm_GlobalTheory_SaturatedSections_cst_eq
import Theorems.Thm_GlobalTheory_SaturatedSections_eq_zero_of_cst_mul
import Theorems.Thm_GlobalTheory_SaturatedSections_not_mem_basicOpen_cst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SaturatedSections
namespace GlobalTheory
theorem _root_.solution : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (H : Scheme.{0}) (p : H ⟶ Sp W) [Flat p] (M : LB H), M.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec M), (∀ c : Fin r → W, (∀ (j : M.ι) (x : H), x ∈ M.U j → p x = IsLocalRing.closedPoint W → x ∉ H.basicOpen (∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j)) → ∀ i, c i ∈ IsLocalRing.maximalIdeal W) → ∀ t : LB.Sec M, (∃ (a : W) (c : Fin r → W), a ≠ 0 ∧ ∀ j, Out.resTop _ (Out.scal p a) * t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j) → ∃! c : Fin r → W, ∀ j, t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j := by
  intro W _ _ _ H p _ M _ r s ind t ⟨a, c, ha, h⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  simp only [cst_eq] at ind h ⊢
  refine existsUnique_comb (A := fun j => Γ(H, M.U j)) (fun j => cst p (M.U j)) hϖ
    (fun j x hx => eq_zero_of_cst_mul p _ hϖ.ne_zero x hx) (fun i j => (s i).f j)
    (fun c y hy => ind c fun j x _ hx => ?_) t.f a c ha h
  rw [← hy j, Scheme.basicOpen_mul]
  exact fun h => not_mem_basicOpen_cst p _ hϖ.not_isUnit x hx h.1
end GlobalTheory
