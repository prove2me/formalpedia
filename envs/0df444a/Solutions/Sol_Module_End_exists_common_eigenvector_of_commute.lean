-- Prove2me | solution 1 for Module.End.exists_common_eigenvector_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7fc0cc08-05c8-5d46-b0f3-1d37331e1f8e

import Theorems.Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_common_eigenvector_of_commute

set_option autoImplicit false

open Module Algebra
open scoped IsMulCommutative

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  classical

  let A : Subalgebra K (Module.End K V) := Algebra.adjoin K (Set.range T)

  haveI : IsMulCommutative A := isMulCommutative_adjoin K
    (fun a ⟨i, hi⟩ b ⟨j, hj⟩ => hi ▸ hj ▸ (hcomm i j).eq)
  letI : CommRing A := inferInstance

  haveI : SMulCommClass A K V := Subalgebra.smulCommClass_left A
  haveI : FaithfulSMul A V := inferInstance

  haveI : Nontrivial A :=
    ⟨⟨0, 1, fun h => (zero_ne_one (α := Module.End K V)) (Subtype.ext_iff.mp h)⟩⟩

  obtain ⟨⟨𝔭, h𝔭⟩⟩ := Ideal.nonempty_minimalPrimes (R := A) (I := ⊥) bot_ne_top
  have h𝔭' : 𝔭 ∈ minimalPrimes A := h𝔭

  obtain ⟨χ, -, v, hv0, -, -, heig⟩ :=
    DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
      (K := K) (V := V) (T := A) h𝔭'

  have hTmem : ∀ i, T i ∈ A := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  refine ⟨fun i => χ ⟨T i, hTmem i⟩, v, hv0, fun i => ?_⟩

  have : (⟨T i, hTmem i⟩ : A) • v = χ ⟨T i, hTmem i⟩ • v := heig _
  simp at this ⊢
  exact this

end S_Module_End_exists_common_eigenvector_of_commute
end P2MW
export P2MW.S_Module_End_exists_common_eigenvector_of_commute (solution)
