-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_untilt_eq_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:20.54196+00:00
-- url     : https://prove2.me/submissions/c58d40d4-9284-42d3-adac-f873d8f834db

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_ofCompatible

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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
variable (K p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution [IsAlgClosed K] : ∃ pflat : 𝒪♭, PreTilt.untilt pflat = p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let root : 𝒪 → 𝒪 := fun z =>
    ⟨Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : K) hp), mem_normInteger.2 (by
      have h := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : K) hp)
      have h2 : ‖Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : K) hp)‖ ^ p ≤ 1 := by
        rw [← norm_pow, h]; exact mem_normInteger.1 z.2
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.ne').1 h2)⟩
  have hroot : ∀ z, root z ^ p = z := fun z => Subtype.ext (by
    simp only [root, SubmonoidClass.coe_pow]
    exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : K) hp))
  let y : ℕ → 𝒪 := fun n => root^[n] p
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => by
    simp only [y, Function.iterate_succ_apply', hroot]
  exact ⟨ofCompatible p y hy, by rw [untilt_ofCompatible]; rfl⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
