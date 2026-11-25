-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.DualSec.isBasisOn_dualBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:51.788384+00:00
-- url     : https://prove2.me/submissions/8bc4f8f2-aab2-49a2-97c5-99a9947e048a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_DualSec_dualBasis_app_self
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
open GroundTheory.Arith.SchemeCoh.DualSec
variable {P : PMod X} {U : X.Opens} {s : P.obj (op U)}
namespace GroundTheory.Arith.SchemeCoh.DualSec
theorem _root_.solution (hs : IsBasisOn P U s) : IsBasisOn (dualPre P) U (dualBasis hs) := by
  intro V h
  have hres : resM (dualPre P) h (dualBasis hs) = restr h (dualBasis hs) := rfl
  rw [hres]
  constructor
  · intro c₁ c₂ e
    have := congrArg (fun ξ : DualSec P V => ξ.app V le_rfl (resM P h s)) e
    simp only at this
    change (c₁ • restr h (dualBasis hs)).app V le_rfl (resM P h s) =
      (c₂ • restr h (dualBasis hs)).app V le_rfl (resM P h s) at this
    rw [smul_app', smul_app', LinearMap.smul_apply, LinearMap.smul_apply, restr_app,
      dualBasis_app_self, resR_refl, resR_refl] at this
    simpa using this
  · intro ψ
    refine ⟨ψ.app V le_rfl (resM P h s), ?_⟩
    change _ • restr h (dualBasis hs) = ψ
    refine DualSec.ext (funext fun W => funext fun i => LinearMap.ext fun m => ?_)
    change (resR i (ψ.app V le_rfl (resM P h s)) • (dualBasis hs).app W (i.trans h)) m = ψ.app W i m
    rw [LinearMap.smul_apply, smul_eq_mul]
    have hm : m = (coordEquiv hs W (i.trans h)).symm m • resM P i (resM P h s) := by
      rw [resM_resM, ← coordEquiv_apply hs, LinearEquiv.apply_symm_apply]
    conv_rhs => rw [hm]
    rw [map_smul, ψ.compat V W le_rfl i (resM P h s), smul_eq_mul, mul_comm]
    rfl
end GroundTheory.Arith.SchemeCoh.DualSec
