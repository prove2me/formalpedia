-- Prove2me | solution 1 for GlobalTheory.eq_of_norm_resultant_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:49.427911+00:00
-- url     : https://prove2.me/submissions/a7434683-fbc1-4a35-a7f6-016b341f4bcc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
import Theorems.Thm_GlobalTheory_ResultantNorm_exists_prod_aeval
import Theorems.Thm_GlobalTheory_ResultantNorm_eq_of_countP
import Theorems.Thm_GlobalTheory_ResultantNorm_countP_le
import Theorems.Thm_GlobalTheory_ResultantNorm_padic_case

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ_[l] Ω] [Algebra.IsAlgebraic ℚ_[l] Ω] (a b : Multiset Ω) (P Q : Polynomial ℚ_[l]), P.map (algebraMap ℚ_[l] Ω) = (a.map fun x => Polynomial.X - Polynomial.C x).prod → Q.map (algebraMap ℚ_[l] Ω) = (b.map fun x => Polynomial.X - Polynomial.C x).prod → (∀ (F : Polynomial ℤ) (u v : ℚ_[l]), algebraMap ℚ_[l] Ω u = (a.map fun x => Polynomial.aeval x F).prod → algebraMap ℚ_[l] Ω v = (b.map fun x => Polynomial.aeval x F).prod → ‖u‖ = ‖v‖) → P = Q := by
  intro l _ Ω _ _ _ a b P Q hP hQ h
  classical
  letI : NormedField Ω := spectralNorm.normedField ℚ_[l] Ω
  letI : NormedAlgebra ℚ_[l] Ω := spectralNorm.normedAlgebra ℚ_[l] Ω
  have h1 : ∀ F : Polynomial ℤ, ‖(a.map fun x => Polynomial.aeval x F).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x F).prod‖ := by
    intro F
    obtain ⟨u, hu⟩ := ResultantNorm.exists_prod_aeval a P hP (F.map (algebraMap ℤ ℚ_[l]))
    obtain ⟨v, hv⟩ := ResultantNorm.exists_prod_aeval b Q hQ (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at hu hv
    rw [← hu, ← hv, norm_algebraMap', norm_algebraMap']
    exact h F u v hu hv
  refine ResultantNorm.eq_of_countP _ a b P Q rfl hP hQ fun G => ?_
  have h2 : ∀ t : ℚ_[l],
      ‖(a.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ := by
    intro t
    simpa only [map_add, Polynomial.aeval_C] using
      ResultantNorm.padic_case (l := l) a b h1 (G + Polynomial.C t)
  exact le_antisymm (ResultantNorm.countP_le b a _ fun t => (h2 t).symm)
    (ResultantNorm.countP_le a b _ h2)
end GlobalTheory
