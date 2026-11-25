-- Prove2me | solution 1 for GlobalTheory.SymAlg.mapOver_mem_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:13:44.366293+00:00
-- url     : https://prove2.me/submissions/371482f5-b9a3-4d2e-9386-4d7f4e0d4e7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]
namespace GlobalTheory.SymAlg
theorem _root_.solution (j : M →ₗ[R] W) {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : mapOver S j x ∈ homog S W d := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (SymmetricAlgebra S W)]
    exact SetLike.algebraMap_mem_graded (homog S W) _
  | add x y i hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, mapOver_ι, Nat.succ_eq_one_add]
    exact SetLike.mul_mem_graded (ι_mem_homog _) ih
end GlobalTheory.SymAlg
