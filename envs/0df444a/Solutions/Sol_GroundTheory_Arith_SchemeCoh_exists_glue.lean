-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:28.874944+00:00
-- url     : https://prove2.me/submissions/f93e823a-cb99-4bf6-9a79-3e02415c9ed2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_res_congr
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_le_inter_const
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_zero_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
include hP
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {ι : Type w} (U : ι → Opens X) (V : Opens X) (hUV : ∀ a, U a ≤ V)
    (hV : V ≤ iSup U) (τ : Cochain P U 0) (hτ : d P U 0 τ = 0) :
    ∃ t : P.obj (op V), ∀ i : Fin 1 → ι,
      res P ((inter_le U i 0).trans (hUV (i 0))) t = τ i := by
  let sf : ∀ j, P.obj (op (U j)) := fun j => res P (le_inter_const U j) (τ (fun _ => j))
  have compat : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    have h := congrFun hτ ![i, j]
    rw [d_zero_apply] at h
    have hle : U i ⊓ U j ≤ inter U ![i, j] := by
      intro x hx
      rw [mem_inter_iff]
      intro a
      fin_cases a
      · exact hx.1
      · exact hx.2
    rw [Pi.zero_apply] at h
    have h' := congrArg (res P hle) h
    rw [map_sub, res_res, res_res, map_zero, sub_eq_zero] at h'
    have e0 : (![i, j] ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => j := by
      funext a; fin_cases a; rfl
    have e1 : (![i, j] ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => i := by
      funext a; fin_cases a; rfl
    rw [res_congr P U τ e0 _ ((inf_le_right).trans (le_inter_const U j)),
      res_congr P U τ e1 _ ((inf_le_left).trans (le_inter_const U i))] at h'
    change res P inf_le_left (sf i) = res P inf_le_right (sf j)
    simp only [sf, res_res]
    exact h'.symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨P, hP⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    U V (fun a => homOfLE (hUV a)) hV sf compat
  refine ⟨t, fun i => ?_⟩
  have hi : (fun _ : Fin 1 => i 0) = i := funext fun a => by rw [Subsingleton.elim a 0]
  have ht' : res P (hUV (i 0)) t = sf (i 0) := ht (i 0)
  rw [← res_res P (inter_le U i 0) (hUV (i 0)), ht']
  simp only [sf, res_res]
  exact (res_congr P U τ hi _ le_rfl).trans (res_refl _ _ _)
end GroundTheory.Arith.SchemeCoh
