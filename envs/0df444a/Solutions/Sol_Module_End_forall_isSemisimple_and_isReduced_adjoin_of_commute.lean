-- Prove2me | solution 1 for Module.End.forall_isSemisimple_and_isReduced_adjoin_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4ae70fb8-49ee-5d84-9caa-1b0d45ee52a7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RRedEngine
section Semisimple

variable {K : Type*} [Field K] [PerfectField K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [PerfectField K] [FiniteDimensional K V] in
theorem commute_of_mem_adjoin {s : Set (Module.End K V)} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    {x y : Module.End K V} (hx : x ∈ Algebra.adjoin K s) (hy : y ∈ Algebra.adjoin K s) : Commute x y := by
  have h1 := Algebra.adjoin_le_centralizer_centralizer K s hx
  have h2 : y ∈ Subalgebra.centralizer K s := by
    refine (Algebra.adjoin_le (fun z hz => ?_) : Algebra.adjoin K s ≤ Subalgebra.centralizer K s) hy
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro w hw
    exact hcomm w hw z hz
  rw [Subalgebra.mem_centralizer_iff] at h1
  exact (h1 y h2).symm

theorem isSemisimple_of_mem_adjoin {s : Set (Module.End K V)}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hs : ∀ x ∈ s, Module.End.IsSemisimple x)
    {a : Module.End K V} (ha : a ∈ Algebra.adjoin K s) : a.IsSemisimple := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Module.End.IsSemisimple_smul r Module.End.isSemisimple_id
  | add x y hx hy ihx ihy => exact Module.End.IsSemisimple.add_of_commute (commute_of_mem_adjoin hcomm hx hy) ihx ihy
  | mul x y hx hy ihx ihy => exact Module.End.IsSemisimple.mul_of_commute (commute_of_mem_adjoin hcomm hx hy) ihx ihy

theorem isReduced_adjoin {s : Set (Module.End K V)}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
    IsReduced (Algebra.adjoin K s) := by
  constructor
  rintro ⟨x, hx⟩ ⟨n, hn⟩
  have hxn : x ^ n = 0 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact Subtype.ext
    (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨n, hxn⟩ (isSemisimple_of_mem_adjoin hcomm hs hx))

end Semisimple

end RRedEngine

theorem solution
    {K : Type*} [Field K] [PerfectField K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {s : Set (Module.End K V)} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
    (∀ a ∈ Algebra.adjoin K s, Module.End.IsSemisimple a) ∧ IsReduced ↥(Algebra.adjoin K s) :=
  ⟨fun _ ha => RRedEngine.isSemisimple_of_mem_adjoin hcomm hs ha, RRedEngine.isReduced_adjoin hcomm hs⟩

end S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute
end P2MW
export P2MW.S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute (solution)
