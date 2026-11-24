-- Prove2me | solution 1 for GlobalTheory.RankBundle.exists_rank_one_bundle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:28:28.4888+00:00
-- url     : https://prove2.me/submissions/5c1676eb-952a-4276-91e2-c18dc9e876cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsRankOneBundle
import Theorems.Thm_GlobalTheory_RankBundle_gs_one
import Theorems.Thm_GlobalTheory_RankBundle_mem_basicOpen_iff
import Theorems.Thm_GlobalTheory_RankBundle_sec_compat
import Theorems.Thm_GlobalTheory_RankBundle_exists_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RankBundle
variable {X : Scheme.{0}}
namespace GlobalTheory.RankBundle
theorem _root_.solution : ∀ (X : Scheme.{0}) (N : LB X) (n m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → ∃ (H' : LB X) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB ∧ (⨆ i, nonzeroLocus (s' i) = ⊤) ∧ ∀ (x : X) (c : H'.ι), x ∈ H'.U c → ∃ j, ∀ k, x ∈ N.U k → ∃ v : (X.presheaf.stalk x)ˣ, ∀ i, gs (𝟙 X) x (N.U k) ((w i j).f k) = v.val * gs (𝟙 X) x (H'.U c) ((s' i).f c) := by
  intro X N n m w hN hcov hr
  choose S hS using fun (l : Fin (n + 1)) (c : Fin (n + 1) × Fin (m + 1) × N.ι) =>
    exists_ratio ((w l c.2.1).f c.2.2) ((w c.1 c.2.1).f c.2.2)
  let U : Fin (n + 1) × Fin (m + 1) × N.ι → X.Opens := fun c => X.basicOpen ((w c.1 c.2.1).f c.2.2)
  have hle : ∀ c x, x ∈ U c → x ∈ N.U c.2.2 := fun c x hx => X.basicOpen_le _ hx
  have hu : ∀ c x, x ∈ U c → IsUnit (gs (𝟙 X) x (N.U c.2.2) ((w c.1 c.2.1).f c.2.2)) := fun c x hx =>
    (mem_basicOpen_iff x _ (hle c x hx) _).1 hx
  have one : ∀ c x, x ∈ U c → gs (𝟙 X) x (U c) (S c.1 c) = 1 := fun c x hx =>
    (hu c x hx).mul_right_cancel ((hS c.1 c x hx).trans (_root_.one_mul _).symm)
  have key : ∀ l c c' x, x ∈ U c → x ∈ U c' →
      gs (𝟙 X) x (U c) (S l c) = gs (𝟙 X) x (U c) (S c'.1 c) * gs (𝟙 X) x (U c') (S l c') := by
    intro l c c' x hx hx'
    have e₁ := hS l c x hx
    have e₂ := hS c'.1 c x hx
    have e₃ := hS l c' x hx'
    have e₄ := congrArg (gs (𝟙 X) x (N.U c.2.2)) (hr l c'.1 c.2.1 c'.2.1 c.2.2)
    rw [gs_mul (𝟙 X) x _ (hle c x hx), gs_mul (𝟙 X) x _ (hle c x hx),
      sec_compat (w c'.1 c'.2.1) x (hle c x hx) (hle c' x hx'),
      sec_compat (w l c'.2.1) x (hle c x hx) (hle c' x hx')] at e₄
    apply (((hu c x hx).mul (hu c' x hx')).mul
      (gm (𝟙 X) x (N.U c.2.2 ⊓ N.U c'.2.2) (N.g c.2.2 c'.2.2)).isUnit).mul_right_cancel
    rw [← e₁, ← e₂, ← e₃] at e₄
    exact Eq.trans (by ring) (e₄.trans (by ring))
  have hg : ∀ c c', IsUnit (rs X (inf_le_left : U c ⊓ U c' ≤ U c) (S c'.1 c)) := fun c c' =>
    IsUnit.of_mul_eq_one (rs X (inf_le_right : U c ⊓ U c' ≤ U c') (S c.1 c')) (fn_ext fun x hx => by
      rw [gs_mul (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, ← key c.1 c c' x hx.1 hx.2,
        one c x hx.1, gs_one x _ hx])
  have gv : ∀ c c' x, x ∈ U c ⊓ U c' →
      (gm (𝟙 X) x (U c ⊓ U c') (hg c c').unit).val = gs (𝟙 X) x (U c) (S c'.1 c) := fun c c' x hx =>
    (gs_unit (𝟙 X) x _ hx _).symm.trans (gs_res (𝟙 X) x _ hx _)
  have ex : ∀ x : X, ∃ c, x ∈ U c := fun x => by
    have hx : x ∈ ⨆ i, ⨆ j, nonzeroLocus (w i j) := by rw [hcov]; trivial
    obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨k, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨(i, j, k), hx⟩
  let H : LB X := ⟨Fin (n + 1) × Fin (m + 1) × N.ι, U, fun c c' => (hg c c').unit⟩
  let s : Fin (n + 1) → LB.Sec H := fun l => ⟨S l, fun c c' => fn_ext fun x hx =>
    (gs_res (𝟙 X) x _ hx _).trans ((key l c c' x hx.1 hx.2).trans ((gs_mul (𝟙 X) x _ hx _ _).trans
      (congrArg₂ (· * ·) (gs_res (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)⟩
  refine ⟨H, s, ⟨?_, fun c => unit_ext fun x hx => Units.ext ?_, fun a b c => unit_ext fun x hx => Units.ext ?_⟩, ?_, ?_⟩
  · exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 (ex x)
  · rw [gm_res (𝟙 X) x _ hx, map_one, Units.val_one]
    exact (gv c c x ⟨hx, hx⟩).trans (one c x hx)
  · rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, Units.val_mul]
    exact (congrArg₂ (· * ·) (gv a b x hx.1) (gv b c x ⟨hx.1.2, hx.2⟩)).trans
      ((key c.1 a b x hx.1.1 hx.1.2).symm.trans (gv a c x ⟨hx.1.1, hx.2⟩).symm)
  · refine top_unique fun x _ => ?_
    obtain ⟨c, hc⟩ := ex x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨c.1, TopologicalSpace.Opens.mem_iSup.2 ⟨c, ?_⟩⟩
    exact (mem_basicOpen_iff x (U c) hc _).2 ((one c x hc).symm ▸ isUnit_one)
  · intro x c hc
    refine ⟨c.2.1, fun k hk => ⟨gm (𝟙 X) x (N.U k ⊓ N.U c.2.2) (N.g k c.2.2) * (hu c x hc).unit, fun l => ?_⟩⟩
    rw [sec_compat (w l c.2.1) x hk (hle c x hc), ← hS l c x hc, Units.val_mul, IsUnit.unit_spec, _root_.mul_assoc]
    exact congrArg _ (_root_.mul_comm _ _)
end GlobalTheory.RankBundle
