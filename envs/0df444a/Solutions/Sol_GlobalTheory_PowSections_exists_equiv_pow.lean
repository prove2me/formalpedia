-- Prove2me | solution 1 for GlobalTheory.PowSections.exists_equiv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:33.727095+00:00
-- url     : https://prove2.me/submissions/7fd15411-9576-49e5-b947-359097814f73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEquivPow
import Theorems.Thm_GlobalTheory_PowSections_gs_secEquiv

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
theorem _root_.solution (M : LB Y) (n : ℕ) (g : ∀ i j, Γ(Y, M.U i ⊓ M.U j)ˣ)
    (hg : ∀ i j y, y ∈ M.U i → y ∈ M.U j →
      gm (𝟙 Y) y _ (g i j) = gm (𝟙 Y) y _ (M.g i j) ^ (n : ℤ)) :
    ∃ E : H0 M n ≃ LB.Sec (⟨M.ι, M.U, g⟩ : LB Y),
      ∀ a (j : M.ι) (y : Y), y ∈ M.U j →
        gs (𝟙 _) y _ ((E a).f j) = gs (𝟙 _) y _ (a.f (fun _ => j)) := by
  have m₁ : ∀ (j : M.ι) (y : Y), y ∈ M.U j →
      y ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) := fun j y hy => Set.mem_iInter.2 fun _ => hy
  let σ : M.ι ≃ (Fin 1 → M.ι) :=
    ⟨fun j _ => j, fun J => J 0, fun _ => rfl, fun J => funext fun k => by rw [Subsingleton.elim k 0]⟩
  have hU : ∀ j : M.ι, M.U j = LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
    fun j => le_antisymm (fun y hy => m₁ j y hy) (fun y hy => Set.mem_iInter.1 hy 0)
  have hg' : ∀ i j y, y ∈ M.U i → y ∈ M.U j → gm (𝟙 Y) y _ (g i j) = gm (𝟙 Y) y _
      ((LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ))).g (fun _ => i) (fun _ => j)) := by
    intro i j y hi hj
    have e := gm_linComb M (fun _ : Fin 1 => 𝟙 Y) (fun _ => (n : ℤ)) (𝟙 Y) y (fun _ => i) (fun _ => j)
      (m₁ i y hi) (m₁ j y hj)
    rw [Fin.prod_univ_one, Category.id_comp] at e
    rw [hg i j y hi hj]
    exact e.symm
  exact ⟨secEquiv (M := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ)))
    (M' := ⟨M.ι, M.U, g⟩) σ hU hg',
    fun a j y hy => gs_secEquiv (M := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ)))
      (M' := ⟨M.ι, M.U, g⟩) σ hU hg' a j y hy⟩
end GlobalTheory.PowSections
