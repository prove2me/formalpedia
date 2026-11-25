-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.finite_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:07.005808+00:00
-- url     : https://prove2.me/submissions/605e902c-c763-4057-aa2a-ef8f80ce3af5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}
variable (F : X.Modules) [F.IsQuasicoherent]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) [Module.Finite Γ(X, V) Γ(F, V)]
    (g : Γ(X, V)) : Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) := by
  classical
  obtain ⟨r, gen, hgen⟩ := Module.Finite.exists_fin (R := Γ(X, V)) (M := Γ(F, V))
  refine ⟨⟨Finset.univ.image (fun i => resF F (X.basicOpen_le g) (gen i)), ?_⟩⟩
  rw [eq_top_iff]
  rintro t -
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hV g t
  have hm'' : m' ∈ Submodule.span Γ(X, V) (Set.range gen) := hgen ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm''
  have hu : IsUnit (resO (X.basicOpen_le g) g ^ e) :=
    (X.toRingedSpace.isUnit_res_basicOpen g).pow e
  have hres : resF F (X.basicOpen_le g) m' ∈ Submodule.span Γ(X, X.basicOpen g)
      (↑(Finset.univ.image (fun i => resF F (X.basicOpen_le g) (gen i)))) := by
    rw [← hc, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [resF_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rw [hm'] at hres
  exact (Submodule.smul_mem_iff_of_isUnit _ hu).mp hres
end GroundTheory.Arith.SchemeCoh
