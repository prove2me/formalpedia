-- Prove2me | solution 1 for GlobalTheory.FamDim.exists_class_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:39.345962+00:00
-- url     : https://prove2.me/submissions/03c13a47-c6d2-42d8-a563-d9826ecd89d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTermBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamDim
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.FamDim
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ)
    (hk : 1 ≤ k) : ∃ ρ : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ q q' mu, ρ q + k • mu = ρ q' → q = q') ∧ (∀ β, ∃ q mu, ρ q + k • mu = β) ∧
      ∀ a b : X, k • a = k • b → a = b := by
  let B := (Module.finBasis ℤ X).equivFun
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun q => B.symm (fun i => ((q i : ℕ) : ℤ)), fun q q' mu h => ?_, fun β => ?_, fun a b h => ?_⟩
  · funext i
    have e := congrFun (congrArg B h) i
    simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply] at e
    rw [nsmul_eq_mul] at e
    have e2 := congrArg (· % (k : ℤ)) e
    simp only [Int.add_mul_emod_self_left] at e2
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q i).2),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q' i).2)] at e2
    exact Fin.ext (by exact_mod_cast e2)
  · refine ⟨fun i => ⟨(B β i % k).toNat, ?_⟩, B.symm (fun i => B β i / k), ?_⟩
    · have := Int.emod_lt_of_pos (B β i) hk'
      have := Int.emod_nonneg (B β i) hk'.ne'
      omega
    · apply B.injective
      funext i
      simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply]
      rw [nsmul_eq_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'.ne')]
      exact Int.emod_add_mul_ediv _ _
  · apply B.injective
    funext i
    have e := congrFun (congrArg B h) i
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul] at e
    exact mul_left_cancel₀ hk'.ne' e
end GlobalTheory.FamDim
