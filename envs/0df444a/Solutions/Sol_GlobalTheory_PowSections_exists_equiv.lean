-- Prove2me | solution 1 for GlobalTheory.PowSections.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:06:01.450998+00:00
-- url     : https://prove2.me/submissions/c96d9de5-a21e-46d6-9f90-f853833fc154

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEquivPow
import Theorems.Thm_GlobalTheory_PowSections_exists_equiv_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PowSections
variable {Y : Scheme.{0}}
namespace GlobalTheory.PowSections
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) :
    ∃ E : H0 (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (N : ℤ))) n ≃
        LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((N * n : ℕ) : ℤ))),
      ∀ a (j : Fin 1 → L.ι) (y : Y), p y ∈ L.U (j 0) →
        gs (𝟙 _) y _ ((E a).f j) = gs (𝟙 _) y _ (a.f (fun _ => j)) := by
  obtain ⟨E, hE⟩ := exists_equiv_pow (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (N : ℤ))) n
    (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((N * n : ℕ) : ℤ))).g (fun i j y hi hj => by
      have e := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) (𝟙 Y) y i j hi hj
      have e' := gm_linComb L (fun _ : Fin 1 => p) (fun _ => ((N * n : ℕ) : ℤ)) (𝟙 Y) y i j hi hj
      rw [Fin.prod_univ_one] at e e'
      refine e'.trans (Eq.trans ?_ (congrArg (· ^ (n : ℤ)) e.symm))
      rw [Nat.cast_mul, zpow_mul])
  refine ⟨E, fun a j y hy => hE a j y (Set.mem_iInter.2 fun k => ?_)⟩
  obtain rfl : k = 0 := Subsingleton.elim _ _
  exact hy
end GlobalTheory.PowSections
