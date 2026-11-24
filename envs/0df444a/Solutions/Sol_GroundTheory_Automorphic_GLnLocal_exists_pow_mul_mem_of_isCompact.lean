-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.exists_pow_mul_mem_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:49.720559+00:00
-- url     : https://prove2.me/submissions/dd25e26f-ae6e-415a-b47b-6dfd4b915df1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eventually_pow_mul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {S : Set (GL (Fin n) F)} (hS : IsCompact S) :
    ∃ m : ℕ, ∀ g ∈ S, ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F] := by
  let U : ℕ → Set (GL (Fin n) F) := fun m => {g | ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F]}
  have hU : ∀ m, IsOpen (U m) := fun m => by
    have : U m = ⋂ i, ⋂ j,
        (fun g : GL (Fin n) F => (uniformizer F : F) ^ m * g i j) ⁻¹' (𝒪[F] : Set F) := by
      ext g
      simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      Valuation.isOpen_integer.preimage (continuous_const.mul (continuous_entry F n i j))
  have hcover : S ⊆ ⋃ m, U m := fun g _ => by
    have : ∀ᶠ m in atTop, ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F] :=
      eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_pow_mul_mem F (g i j)
    obtain ⟨m, hm⟩ := this.exists
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  have hmono : Monotone U := fun m m' h g hg i j => by
    have : (uniformizer F : F) ^ m' * g i j =
        (uniformizer F : F) ^ (m' - m) * ((uniformizer F : F) ^ m * g i j) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ (uniformizer F).2 _) (hg i j)
  obtain ⟨m, hm⟩ := hS.elim_directed_cover U hU hcover hmono.directed_le
  exact ⟨m, fun g hg => hm hg⟩
end GroundTheory.Automorphic.GLnLocal
