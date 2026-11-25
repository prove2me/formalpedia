-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_norm_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:36:46.169027+00:00
-- url     : https://prove2.me/submissions/7177f23b-a2b6-4ad1-a899-5e61c76d032e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] {z : Fin n → E} (hz : z ≠ 0) :
    ∃ i, ‖z i‖ = ‖z‖ := by
  have : Nonempty (Fin n) := by
    by_contra h
    exact hz (funext fun i => (h ⟨i⟩).elim)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖) Finset.univ_nonempty
  exact ⟨i, le_antisymm (norm_le_pi_norm z i)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ j))⟩
end GroundTheory.Automorphic.Reduction
