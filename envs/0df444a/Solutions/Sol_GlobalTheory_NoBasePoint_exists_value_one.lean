-- Prove2me | solution 1 for GlobalTheory.NoBasePoint.exists_value_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:08:39.219037+00:00
-- url     : https://prove2.me/submissions/95cc8a69-ddf4-4385-a4f3-a6d74fdeea29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSecValueIsUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_isUnit_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.NoBasePoint
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left}
namespace GlobalTheory.NoBasePoint
theorem _root_.solution (hL : L.IsLB) {T : Over S} [Subsingleton T.left] (n : ℤ) (x : T ⟶ A) (p : T.left)
    (h : UnitAt L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => n) ((ptSecT A x).left p)) :
    ∃ (s : LB.Sec (LPow A L n T))
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))),
      τ.IsGen ∧ IsValueAt A L n s x τ 1 := by
  obtain ⟨s, hs⟩ := h
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ ((ptSecT A x).left p))
  have hm := Good.mem hI (fun _ : Fin 1 => (snd T A).left) (𝟙 _)
  have hb : (ptSecT A x).left p ∈ (T ⊗ A).left.basicOpen (s.f (fun _ => I (𝟙 _ ≫ (snd T A).left))) :=
    ((T ⊗ A).left.mem_basicOpen _ _ hm).2 ((congrArg IsUnit (gs_eq (𝟙 _) _ _ hm _)).mp (hs I hI))
  let s' := GlobalTheory.EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A x).left
    (fun _ => x.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd]) (val_le A L x) s
  have hu : ∀ j, IsUnit (s'.f j) := fun j => T.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun q hq => by
    obtain rfl : q = p := Subsingleton.elim _ _
    choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ q)
    have u := isUnit_sval s (ptSecT A x).left q hJ _ hb
    have e := sec_trans s (ptSecT A x).left q (val_le A L x j hq) (Good.mem hJ _ (ptSecT A x).left)
    have e' : gs (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) (s'.f j) =
        gs (𝟙 T.left ≫ (ptSecT A x).left) q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j) :=
      (gs_res (𝟙 T.left) q (val_le A L x j) hq _).trans
        (gs_pull (𝟙 T.left) (ptSecT A x).left q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j)
          (val_le A L x j hq) (s.f j))
    rw [Category.id_comp] at e'
    exact (congrArg IsUnit ((gs_eq (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) hq _).symm.trans
      (e'.trans e))).mpr ((Units.isUnit _).mul u)
  refine ⟨s, ⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun j => ?_⟩
  rw [map_one, _root_.one_mul]
  rfl
end GlobalTheory.NoBasePoint
