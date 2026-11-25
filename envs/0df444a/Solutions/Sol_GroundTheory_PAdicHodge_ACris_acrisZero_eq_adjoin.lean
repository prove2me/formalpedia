-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.acrisZero_eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:21:38.50374+00:00
-- url     : https://prove2.me/submissions/e4dcade8-8370-4818-bcf5-580d66878cc0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) :
    ACrisZero K p = Algebra.adjoin (AInf K p) (Set.range fun n : ℕ => dpow n ξ) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨n, x, hx, rfl⟩
    rw [hξ] at hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [mul_comm, dpow_mul]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨n, rfl⟩)
      (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ c) n)
  · apply Algebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact dpow_mem (by rw [hξ]; exact Ideal.mem_span_singleton_self ξ) n
end GroundTheory.PAdicHodge.ACris
