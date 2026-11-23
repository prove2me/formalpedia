-- Prove2me | solution 1 for GlobalTheory.PeriodTate.pre_onto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:42.27542+00:00
-- url     : https://prove2.me/submissions/2331527c-77d5-4333-bde4-9f1aac369921

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoOfPeriods
import Theorems.Thm_GlobalTheory_PeriodTate_pre_injective

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PeriodTate
namespace GlobalTheory.PeriodTate
theorem _root_.solution (hM : Out.MulNSt) {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (Q : Out.PolAV (Sp ℂ))
    {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap β) ⟶ Q.A) (hx : x ^ n = 1) :
    ∃ y : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, y ^ n = 1 ∧ toUnit _ ≫ y = x := by
  have hk : (n : k) ≠ 0 := by
    rw [← map_natCast β]
    exact (map_ne_zero β).2 (by exact_mod_cast hn.ne')
  have c₁ := (hM _ Q n hn).2.2.2.2 k (spMap β) hk
  have c₀ : Nat.card {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} = n ^ (2 * Q.g) :=
    (hM _ Q n hn).2.2.2.2 ℂ (𝟙 _) (by exact_mod_cast hn.ne')
  have : Finite {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₁]; positivity)
  let F : {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} → {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    fun y => ⟨toUnit _ ≫ y.1, by
      have := map_pow (preHom (G := Q.A) (toUnit (Over.mk (spMap β)))) y.1 n
      rw [y.2, map_one] at this
      exact this.symm⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective β Q.A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁])).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩
end GlobalTheory.PeriodTate
