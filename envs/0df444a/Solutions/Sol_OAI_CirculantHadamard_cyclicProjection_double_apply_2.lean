-- Prove2me | solution 2 for OAI.CirculantHadamard.cyclicProjection_double_apply
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:19:28.571935+00:00
-- url     : https://prove2.me/submissions/f30829b5-3e3e-4f8c-93af-0f45fa578ae9

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/ProjectionCoefficients.lean:L65-L82
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.cyclicProjection_double_apply. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Theorems.Thm_OAI_CirculantHadamard_zmod_double_cast_eq_iff

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ProjectionPairFiber ----
namespace OAI

/-!
# The two fibers of reduction modulo half the order

Reduction from `ZMod (2 * m)` to `ZMod m` has exactly the two usual lifts
of each element when `m` is positive.
-/

namespace CirculantHadamard

/-- The two canonical lifts into the group of twice the order are distinct. -/
theorem zmod_double_lifts_ne {m : ℕ} (hm : 0 < m) (j : ZMod m) :
    (j.val : ZMod (2 * m)) ≠ ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  have hjlt : j.val < m := ZMod.val_lt j
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show j.val < 2 * m by omega),
    Nat.mod_eq_of_lt (show j.val + m < 2 * m by omega)] at hv
  omega

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ProjectionCoefficients ----
namespace OAI

universe uA uB uR

/-!
# Coefficients of cyclic quotient maps

The coefficient at an element of the quotient is the sum over its entire
fiber. For the quotient of order `2 * m` onto order `m`, the fiber consists
of the two representatives `j.val` and `j.val + m`.
-/

namespace CirculantHadamard

open scoped BigOperators

section Fiber

variable {A : Type uA} {B : Type uB} {R : Type uR} [Fintype A] [DecidableEq B] [AddCommMonoid R]

/-- Mapping the domain adds precisely the coefficients in a quotient fiber. -/
theorem mapDomain_apply_sum (q : A → B) (f : A →₀ R) (b : B) :
    Finsupp.mapDomain q f b = ∑ a ∈ Finset.univ.filter (fun a => q a = b), f a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.single_apply, Finset.sum_filter]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hzero : f a = 0 := Finsupp.notMem_support_iff.mp ha
  simp [hzero]

end Fiber

section Cyclic

variable {R : Type uR} [Semiring R]

/-- Coefficients of the actual cyclic group-ring quotient as a finite filter sum. -/
theorem cyclicProjection_apply_sum {m n : ℕ} [NeZero n] (h : m ∣ n)
    (f : CyclicRing.Elem R n) (a : ZMod m) :
    (cyclicProjection R h f).coeff a =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod n =>
        ZMod.castHom h (ZMod m) x = a), f.coeff x := by
  change Finsupp.mapDomain (ZMod.castHom h (ZMod m)) f.coeff a = _
  exact mapDomain_apply_sum _ _ _

/-- A quotient by the subgroup of order two adds opposite coefficients. -/
theorem cyclicProjection_double_apply {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (f : CyclicRing.Elem R (2 * m)) (j : ZMod m) :
    (cyclicProjection R h f).coeff j =
      f.coeff (j.val : ZMod (2 * m)) + f.coeff ((j.val + m : ℕ) : ZMod (2 * m)) := by
  classical
  let : NeZero (2 * m) := ⟨(Nat.mul_pos (by decide) hm).ne'⟩
  rw [cyclicProjection_apply_sum]
  refine Finset.sum_eq_add_of_mem _ _ ?_ ?_ (zmod_double_lifts_ne hm j) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (zmod_double_cast_eq_iff hm h _ j).mpr (Or.inl rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (zmod_double_cast_eq_iff hm h _ j).mpr (Or.inr rfl)
  · intro x hx hne
    have hx' := (Finset.mem_filter.mp hx).2
    rcases (zmod_double_cast_eq_iff hm h x j).mp hx' with hxj | hxj
    · exact (hne.1 hxj).elim
    · exact (hne.2 hxj).elim

end Cyclic

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uR} : type_of% @_root_.OAI.CirculantHadamard.cyclicProjection_double_apply.{uR} := @_root_.OAI.CirculantHadamard.cyclicProjection_double_apply.{uR}
