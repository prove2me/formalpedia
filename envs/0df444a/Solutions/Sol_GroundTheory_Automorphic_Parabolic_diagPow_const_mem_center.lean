-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagPow_const_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:53.733781+00:00
-- url     : https://prove2.me/submissions/2a77d00e-dda7-413d-851a-415e3dfed687

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (c : ℤ) :
    Cartan.diagPow F n (fun _ => c) ∈ Subgroup.center (GL (Fin n) F) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
    ⟨(uniformizer F : F) ^ c, by rw [Matrix.scalar_apply, Cartan.coe_diagPow]⟩
end GroundTheory.Automorphic.Parabolic
