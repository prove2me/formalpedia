-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.isUnit_teichmuller_of_untilt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T02:58:00.95083+00:00
-- url     : https://prove2.me/submissions/43a2061e-6c6f-44fe-b5b5-06aea2c8e866

import Mathlib
import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
theorem solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    IsUnit (teichmuller p ε : AInf K p) := by
  have h0 : PreTilt.coeff 0 ε = 1 := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hε, map_one]
  have hn : ∀ n, IsUnit (ε.1 n) := by
    intro n
    induction n with
    | zero =>
      have h00 : ε.1 0 = 1 := h0
      rw [h00]; exact isUnit_one
    | succ n ih =>
      have h := ε.2 n
      rw [← h] at ih
      exact (isUnit_pow_iff hp.out.ne_zero).1 ih
  let g : ℕ → ModP (normInteger K) p := fun n => ↑((hn n).unit⁻¹)
  have hg : ∀ n, g (n + 1) ^ p = g n := by
    intro n
    have e1 : g n * ε.1 n = 1 := (hn n).val_inv_mul
    have e2 : g (n + 1) ^ p * ε.1 n = 1 := by
      rw [← ε.2 n, ← mul_pow, (hn (n+1)).val_inv_mul, one_pow]
    have : g (n+1) ^ p * ε.1 n = g n * ε.1 n := by rw [e1, e2]
    exact (hn n).mul_left_injective this
  let y : 𝒪♭ := ⟨g, hg⟩
  have hy : ε * y = 1 := by
    apply Subtype.ext
    funext n
    show ε.1 n * g n = 1
    exact (hn n).mul_val_inv
  have hu : IsUnit ε := ⟨⟨ε, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  exact hu.map (teichmuller p)
