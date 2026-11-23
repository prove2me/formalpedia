-- Prove2me | solution 1 for GlobalTheory.VolFin.mem_span_of_frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:58.113915+00:00
-- url     : https://prove2.me/submissions/03914a2e-4fcf-47e2-a2fa-91a665497b18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}
variable [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] [Finite ι]
omit [IsScalarTower K F F'] [Module.Finite F F']
namespace GlobalTheory.VolFin
theorem _root_.solution (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    (halg : ∀ b ∈ S, IsAlgebraic F b) (t : F') : t ∈ Submodule.span F (S : Set F') := by
  obtain ⟨a, ha, b, hb, hb0, htb⟩ := hS t
  have hsub : ((Submonoid.closure (S : Set F') : Submonoid F') : Set F') ⊆
      (Submodule.span F (S : Set F') : Set F') := by
    intro x hx
    have hx' : x ∈ S.toSubmonoid :=
      (Submonoid.closure_le (S := S.toSubmonoid)).2 (fun y hy => hy) hx
    exact Submodule.subset_span hx'
  rw [← Algebra.adjoin_eq_span_of_subset F hsub, Subalgebra.mem_toSubmodule]
  have hbinv : b⁻¹ ∈ Algebra.adjoin F (S : Set F') :=
    Algebra.adjoin_mono (Set.singleton_subset_iff.2 hb) (halg b hb).isIntegral.inv_mem_adjoin
  have ht : t = a * b⁻¹ := by rw [← htb, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  rw [ht]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ha) hbinv
end GlobalTheory.VolFin
