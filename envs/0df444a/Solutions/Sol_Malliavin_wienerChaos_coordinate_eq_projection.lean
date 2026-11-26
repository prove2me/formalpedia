-- Prove2me | solution 1 for Malliavin.wienerChaos_coordinate_eq_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:00.174344+00:00
-- url     : https://prove2.me/submissions/2d4abfe6-9f25-42f8-8e0a-b7085f2e8098

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (n : ℕ) (F : RandomL2 P) :
    hsum.linearIsometryEquiv F n =
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).orthogonalProjectionOnto F := by
  apply ext_inner_left ℝ
  intro u
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  calc
    inner ℝ u (hsum.linearIsometryEquiv F n) =
        inner ℝ (lp.single 2 n u) (hsum.linearIsometryEquiv F) :=
      (lp.inner_single_left n u (hsum.linearIsometryEquiv F)).symm
    _ = inner ℝ (hsum.linearIsometryEquiv.symm (lp.single 2 n u))
          (hsum.linearIsometryEquiv.symm (hsum.linearIsometryEquiv F)) := by
      rw [hsum.linearIsometryEquiv.symm.inner_map_map]
    _ = inner ℝ (u : RandomL2 P) F := by
      rw [hsum.linearIsometryEquiv_symm_apply_single,
        hsum.linearIsometryEquiv.symm_apply_apply]
      rfl
end Malliavin
