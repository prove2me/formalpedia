-- Prove2me | solution 1 for GlobalTheory.CMVal.infDiag_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:11.199781+00:00
-- url     : https://prove2.me/submissions/66fc24d0-f7d3-44cf-b560-77f1c5c53bcb

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
theorem _root_.solution (k : Eˣ) : infDiag k =
    Units.map (MonoidHom.inl (InfiniteAdeleRing E) (Af E))
      (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) := by
  symm
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finset_prod_apply]
  have : ∀ w, ((infIdele E w).comp (atInf w)) k =
      Units.map (MonoidHom.inl (InfiniteAdeleRing E) (Af E))
        (Units.map (by classical exact MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) w) (atInf w k)) :=
    fun w => rfl
  simp only [this]
  refine Eq.trans ?_ (map_prod (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (Af E))) _ _)
  show Units.map (MonoidHom.inl (InfiniteAdeleRing E) (Af E)) _ = _
  congr 1
  ext : 1
  rw [Units.coe_prod]
  classical
  exact (Finset.univ_prod_mulSingle (fun w : InfinitePlace E => algebraMap E w.Completion (k : E))).symm
end GlobalTheory.CMVal
