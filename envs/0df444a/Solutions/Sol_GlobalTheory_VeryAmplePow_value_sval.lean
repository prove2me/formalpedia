-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.value_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:45.813643+00:00
-- url     : https://prove2.me/submissions/2c6f4ff2-f017-4903-b3a0-fb6ab551af22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {a : ℤ} {T : Over S} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (h : IsValueAt A L a s x τ v) (z : T.left) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (ptSecT A x).left z J =
      gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val := by
  have e : (ptSecT A x).left ≫ (snd T A).left = x.left := by rw [← Over.comp_left, ptSecT, lift_snd]
  refine (sval_of _ _ z J (fun _ => J x.left) (fun _ => by rw [e])).trans ?_
  rw [val_of τ _ z J (fun _ => J x.left) (fun _ => by rw [Category.id_comp])]
  have hm : (𝟙 T.left : T.left ⟶ T.left) z ∈ LB.wchart L (fun _ : Fin 1 => x.left) (fun _ => J x.left) :=
    Set.mem_iInter.2 fun _ => hJ x.left
  have := congrArg (gs (𝟙 _) z _) (h fun _ => J x.left)
  rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm] at this
  refine Eq.trans ?_ (this.trans (congrArg _ (gs_unit _ z _ hm _)))
  exact ((gs_pull (𝟙 _) (ptSecT A x).left z _ (val_le A L x _ hm) _).trans (by rw [Category.id_comp])).symm
end GlobalTheory.VeryAmplePow
