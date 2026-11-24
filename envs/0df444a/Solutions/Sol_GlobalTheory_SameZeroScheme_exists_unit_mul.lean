-- Prove2me | solution 1 for GlobalTheory.SameZeroScheme.exists_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:34.89452+00:00
-- url     : https://prove2.me/submissions/d2444efc-ecd8-4ab0-a261-711ce00a9f2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
import Theorems.Thm_GlobalTheory_SameZeroScheme_res_res
import Theorems.Thm_GlobalTheory_SameZeroScheme_dvd_on_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SameZeroScheme
namespace GlobalTheory.SameZeroScheme
theorem _root_.solution (Y : Scheme.{0}) (V : Y.Opens) (a b : Γ(Y, V))
    (ha : ∀ (V' : Y.Opens) (h : V' ≤ V), resG Y h a ∈ nonZeroDivisors Γ(Y, V'))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 ↔ (t.appLE V ⊤ h).hom b = 0) :
    ∃ c : Γ(Y, V)ˣ, b = (c : Γ(Y, V)) * a := by
  let J := {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}
  let W : J → Y.Opens := fun i => i.1
  have hW : ∀ i, W i ≤ V := fun i => i.2.2
  have hcov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    exact ⟨⟨U, hU, hUV⟩, hyU⟩
  have hc : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 (hcov y hy)
  have hloc : ∀ i, ∃ c : Γ(Y, W i), IsUnit c ∧ resG Y (hW i) b = c * resG Y (hW i) a := fun i => by
    obtain ⟨c, hc⟩ := dvd_on_affine i.2.1 (hW i) a b fun T t h => (H T t h).1
    obtain ⟨d, hd⟩ := dvd_on_affine i.2.1 (hW i) b a fun T t h => (H T t h).2
    refine ⟨c, ?_, hc.trans (mul_comm _ _)⟩
    have e : (c * d) * resG Y (hW i) a = 1 * resG Y (hW i) a := by
      rw [_root_.one_mul]
      conv_rhs => rw [hd, hc]
      ring
    exact IsUnit.of_mul_eq_one d ((mul_cancel_right_mem_nonZeroDivisors (ha _ (hW i))).1 e)
  choose u hu hub using hloc
  have hh : ∀ i j, resG Y (inf_le_left : W i ⊓ W j ≤ W i) (u i) = resG Y inf_le_right (u j) := by
    intro i j
    have e₁ := congrArg (resG Y (inf_le_left : W i ⊓ W j ≤ W i)) (hub i)
    have e₂ := congrArg (resG Y (inf_le_right : W i ⊓ W j ≤ W j)) (hub j)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact (mul_cancel_right_mem_nonZeroDivisors (ha _ (inf_le_left.trans (hW i)))).1
      (e₁.symm.trans e₂)
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc u hh
  have hs' : ∀ i, resG Y (hW i) (show Γ(Y, V) from s) = u i := hs
  have hunit : IsUnit (show Γ(Y, V) from s) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ V _ fun y hy => by
      obtain ⟨i, hi⟩ := hcov y hy
      have h1 := (hu i).map (Y.presheaf.germ (W i) y hi).hom
      rw [← hs' i] at h1
      have h2 := Y.presheaf.germ_res_apply (homOfLE (hW i)) y hi (show Γ(Y, V) from s)
      exact h2 ▸ h1
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  apply Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
  intro i
  change resG Y (hW i) b = resG Y (hW i) ((show Γ(Y, V) from s) * a)
  rw [map_mul, hs', hub]
end GlobalTheory.SameZeroScheme
