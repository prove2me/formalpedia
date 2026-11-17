-- Prove2me | solution 1 for N25.LocalFive.bijective_of_injective_of_factor_nsmul_of_surjective_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:17.801972+00:00
-- url     : https://prove2.me/submissions/0987990b-fe01-4cd0-9b8e-aed9dac0e348

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_N25_LocalFive_exists_fully_invariant_surjective_nsmul_range

noncomputable section

namespace N25.LocalFive

/-- An injective factor of scalar multiplication is onto under finite-index division. -/
theorem _root_.solution
    {M : Type*} [AddCommGroup M]
    (n : ℕ) (pi rho : M →+ M)
    (hfactor : pi.comp rho = nsmulAddMonoidHom (α := M) n)
    (hpi : Function.Injective pi)
    (hlocal : FiniteQuotientSurj M n) :
    Function.Bijective pi := by
  obtain ⟨U, hfin, hU⟩ := hlocal
  obtain ⟨r, hUD, hDfin, hD, hinv⟩ :=
    exists_fully_invariant_surjective_nsmul_range n U hfin hU
  let D := (nsmulAddMonoidHom (α := M) (n ^ r)).range
  letI : Finite (M ⧸ D) := hDfin
  have honto : ∀ y ∈ D, ∃ x ∈ D, pi x = y := by
    intro y hy
    obtain ⟨z, hz⟩ := hD ⟨y, hy⟩
    refine ⟨rho z, hinv rho z z.property, ?_⟩
    have hf := DFunLike.congr_fun hfactor (z : M)
    exact hf.trans (congrArg Subtype.val hz)
  have hreflect : ∀ x, pi x ∈ D → x ∈ D := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := honto (pi x) hx
    exact hpi hdx ▸ hd
  let q := QuotientAddGroup.mk' D
  let p := QuotientAddGroup.map D D pi (fun x hx => hinv pi x hx)
  have hp : Function.Injective p := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective D x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective D y
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply hreflect
    rw [map_sub]
    exact QuotientAddGroup.eq_iff_sub_mem.mp hxy
  have hps : Function.Surjective p := Finite.surjective_of_injective hp
  refine ⟨hpi, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hps (q y)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective D x
  have herr : y - pi x ∈ D := QuotientAddGroup.eq_iff_sub_mem.mp hx.symm
  obtain ⟨d, hd, hdy⟩ := honto (y - pi x) herr
  refine ⟨x + d, ?_⟩
  rw [map_add, hdy]
  abel

end N25.LocalFive
