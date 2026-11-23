-- Prove2me | solution 1 for GlobalTheory.CMVal.TrivOnF.inf_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:40.009496+00:00
-- url     : https://prove2.me/submissions/a35a2621-8ca9-45aa-95c8-4faacacbd0dd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_Formalism_L2_Host_unif_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal
open Neutral.B1 (finiteSingle)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)
open Formalism.L2.Host (atFin atInf unif unif_spec IsUnitAt IsUnifAt upF aboveInf)
variable (E : Type) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable {I : Type} [Fintype I]
namespace GlobalTheory.CMVal
namespace TrivOnF
theorem _root_.solution {χ : HChar E} (h : TrivOnF χ) (k : Eˣ) (hk : (k : E) ∈ maximalRealSubfield E) : χ.inf k = 1 := by
  classical
  let k' : (maximalRealSubfield E)ˣ := Units.mk0 ⟨k, hk⟩ (fun h0 => k.ne_zero (congrArg Subtype.val h0))
  have hkk : k = upF (maximalRealSubfield E) k' := Units.ext rfl
  have h1 : χ.inf k = ∏ w : InfinitePlace E, χ.locInf w (atInf w k) := by
    show χ.1 (infDiag k) = _
    unfold Formalism.L2.Host.infDiag
    rw [MonoidHom.finset_prod_apply, map_prod]
    rfl
  rw [h1, ← Finset.prod_fiberwise Finset.univ (fun w : InfinitePlace E => w.comap (algebraMap (maximalRealSubfield E) E))]
  refine Finset.prod_eq_one fun w _ => ?_
  have h2 := h.2 w k'
  unfold Formalism.L2.Host.HChar.resInf at h2
  rw [MonoidHom.finset_prod_apply] at h2
  rw [hkk]
  convert h2 using 2
  · unfold Formalism.L2.Host.aboveInf
    congr
  · rfl
end TrivOnF
end GlobalTheory.CMVal
