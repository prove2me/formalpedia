-- Prove2me | solution 1 for JuschenkoMonod.exists_orbitIndexing_monoidHom_unique_and_injective_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:54:33.08676+00:00
-- url     : https://prove2.me/submissions/0fd75ce4-7f76-4e36-b6c7-5a144e2d4a79

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

open scoped Pointwise
namespace JuschenkoMonod

open Topology

section Common

variable {C : Type*} [TopologicalSpace C]

lemma zpow_apply_add (T : C ≃ₜ C) (a b : ℤ) (x : C) : (T ^ (a + b)) x = (T ^ a) ((T ^ b) x) := by
  rw [zpow_add]; rfl

lemma fullGroup_local {T : C ≃ₜ C} (g : fullGroup T) (x : C) :
    ∃ U ∈ 𝓝 x, ∃ k : ℤ, ∀ y ∈ U, (g : C ≃ₜ C) y = (T ^ k) y := g.2 x

lemma orbit_injective (T : C ≃ₜ C) (p : C) (hp : (Set.range fun k : ℤ => (T ^ k) p).Infinite) :
    Function.Injective fun k : ℤ => (T ^ k) p := by
  intro a b hab
  by_contra hne
  have hab' : (T ^ a) p = (T ^ b) p := hab
  set d : ℤ := a - b with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
  set q := (T ^ b) p with hq
  have hfix : (T ^ d) q = q := by
    have : (T ^ a) p = (T ^ d) ((T ^ b) p) := by
      rw [← zpow_apply_add]; congr 2; simp [hd]
    rw [← this, hab']
  have hfixm : ∀ m : ℤ, (T ^ (d * m)) q = q := by
    intro m
    have hmem : (T ^ d) ∈ {f : C ≃ₜ C | f q = q} := hfix
    let S : Subgroup (C ≃ₜ C) :=
      { carrier := {f | f q = q}
        mul_mem' := fun {f g} hf hg => by
          show (f * g) q = q
          rw [Homeomorph.mul_apply]
          show f (g q) = q
          rw [show g q = q from hg]; exact hf
        one_mem' := rfl
        inv_mem' := fun {f} hf => by
          show (f⁻¹) q = q
          rw [Homeomorph.inv_apply]
          exact (Homeomorph.symm_apply_eq f).mpr hf.symm }
    have : (T ^ d) ^ m ∈ S := zpow_mem hmem m
    rw [zpow_mul]; exact this
  apply hp
  refine Set.Finite.subset ((Set.finite_Ico (0 : ℤ) |d|).image fun n : ℤ => (T ^ n) q) ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨(k - b) % d, ⟨Int.emod_nonneg _ hd0, ?_⟩, ?_⟩
  · have := Int.emod_lt (k - b) hd0; simpa using this
  · show (T ^ ((k - b) % d)) q = (T ^ k) p
    have e1 : (T ^ k) p = (T ^ (k - b)) q := by
      rw [hq, ← zpow_apply_add]; congr 2; ring
    rw [e1]
    calc (T ^ ((k - b) % d)) q = (T ^ ((k - b) % d)) ((T ^ (d * ((k - b) / d))) q) := by
          rw [hfixm]
      _ = (T ^ ((k - b) % d + d * ((k - b) / d))) q := (zpow_apply_add _ _ _ _).symm
      _ = (T ^ (k - b)) q := by rw [Int.emod_add_mul_ediv]

end Common

end JuschenkoMonod

namespace JuschenkoMonod

open Topology

section PiP

variable {C : Type*} [TopologicalSpace C]

open Classical in
noncomputable def ind (T : C ≃ₜ C) (p : C) (g : fullGroup T) (j : ℤ) : ℤ :=
  if h : ∃ k : ℤ, (g : C ≃ₜ C) ((T ^ j) p) = (T ^ k) p then h.choose else 0

lemma ind_spec {T : C ≃ₜ C} {p : C} (hinj : Function.Injective fun k : ℤ => (T ^ k) p)
    (g : fullGroup T) (j : ℤ) : (g : C ≃ₜ C) ((T ^ j) p) = (T ^ ind T p g j) p := by
  have h : ∃ k : ℤ, (g : C ≃ₜ C) ((T ^ j) p) = (T ^ k) p := by
    obtain ⟨U, hU, γ, hγ⟩ := fullGroup_local g ((T ^ j) p)
    exact ⟨γ + j, by rw [hγ _ (mem_of_mem_nhds hU), zpow_apply_add]⟩
  rw [ind, dif_pos h]; exact h.choose_spec

lemma ind_eq {T : C ≃ₜ C} {p : C} (hinj : Function.Injective fun k : ℤ => (T ^ k) p)
    (g : fullGroup T) (j k : ℤ) (h : (g : C ≃ₜ C) ((T ^ j) p) = (T ^ k) p) : ind T p g j = k :=
  hinj (by simpa using (ind_spec hinj g j).symm.trans h)

lemma ind_mul {T : C ≃ₜ C} {p : C} (hinj : Function.Injective fun k : ℤ => (T ^ k) p)
    (g h : fullGroup T) (j : ℤ) : ind T p (g * h) j = ind T p g (ind T p h j) := by
  apply ind_eq hinj
  show (g : C ≃ₜ C) ((h : C ≃ₜ C) ((T ^ j) p)) = _
  rw [ind_spec hinj h j, ind_spec hinj g]

lemma ind_one {T : C ≃ₜ C} {p : C} (hinj : Function.Injective fun k : ℤ => (T ^ k) p) (j : ℤ) :
    ind T p (1 : fullGroup T) j = j := by
  apply ind_eq hinj; rfl

noncomputable def indPerm {T : C ≃ₜ C} {p : C} (hinj : Function.Injective fun k : ℤ => (T ^ k) p)
    (g : fullGroup T) : Equiv.Perm ℤ where
  toFun := ind T p g
  invFun := ind T p g⁻¹
  left_inv j := by rw [← ind_mul hinj, inv_mul_cancel, ind_one hinj]
  right_inv j := by rw [← ind_mul hinj, mul_inv_cancel, ind_one hinj]

lemma indPerm_mem [CompactSpace C] {T : C ≃ₜ C} {p : C}
    (hinj : Function.Injective fun k : ℤ => (T ^ k) p) (g : fullGroup T) :
    indPerm hinj g ∈ IntervalExchange.wobbling ℤ := by
  choose U hU γ hγ using fun x : C => fullGroup_local g x
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU
  refine ⟨∑ x ∈ t, |(γ x : ℝ)|, fun j => ?_⟩
  have hx : (T ^ j) p ∈ ⋃ x ∈ t, U x := by rw [ht]; trivial
  simp only [Set.mem_iUnion] at hx
  obtain ⟨x, hxt, hxU⟩ := hx
  have : ind T p g j = γ x + j := by
    apply ind_eq hinj
    rw [hγ x _ hxU, zpow_apply_add]
  show dist (ind T p g j) j ≤ _
  rw [this, Int.dist_eq]
  push_cast
  rw [add_sub_cancel_right]
  exact Finset.single_le_sum (f := fun x => |(γ x : ℝ)|) (fun _ _ => abs_nonneg _) hxt

end PiP

theorem pi_aux (C : Type*) [TopologicalSpace C]
    (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C)
    (hT : ∀ x : C, (Set.range fun k : ℤ => (T ^ k) x).Infinite) (p : C) :
    ∃ φ : fullGroup T →* IntervalExchange.wobbling ℤ,
      IsOrbitIndexing T p (fun g => (φ g : Equiv.Perm ℤ)) ∧
      (∀ ψ : fullGroup T → Equiv.Perm ℤ, IsOrbitIndexing T p ψ → ψ = fun g => (φ g : Equiv.Perm ℤ)) ∧
      (Dense (Set.range fun k : ℤ => (T ^ k) p) → Function.Injective φ) := by
  haveI : CompactSpace C := hC.2.1
  have hinj := orbit_injective T p (hT p)
  let φ : fullGroup T →* IntervalExchange.wobbling ℤ :=
    { toFun := fun g => ⟨indPerm hinj g, indPerm_mem hinj g⟩
      map_one' := by
        apply Subtype.ext; ext j; exact ind_one hinj j
      map_mul' := fun g h => by
        apply Subtype.ext; ext j; exact ind_mul hinj g h j }
  have hφ : IsOrbitIndexing T p (fun g => (φ g : Equiv.Perm ℤ)) := fun g j => ind_spec hinj g j
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro ψ hψ
    funext g
    ext j
    exact hinj (by simpa using (hψ g j).symm.trans (hφ g j))
  · intro hd
    haveI : TopologicalSpace.MetrizableSpace C := hC.2.2.1
    intro g h hgh
    have hgh' : ∀ j, ind T p g j = ind T p h j := fun j => by
      have := congrArg (fun w : IntervalExchange.wobbling ℤ => (w : Equiv.Perm ℤ) j) hgh
      exact this
    apply Subtype.ext
    apply Homeomorph.ext
    have := Continuous.ext_on hd (g : C ≃ₜ C).continuous (h : C ≃ₜ C).continuous (f := fun x => (g : C ≃ₜ C) x)
      (g := fun x => (h : C ≃ₜ C) x) (by
        rintro _ ⟨j, rfl⟩
        show (g : C ≃ₜ C) ((T ^ j) p) = (h : C ≃ₜ C) ((T ^ j) p)
        rw [ind_spec hinj g j, ind_spec hinj h j, hgh' j])
    exact fun x => congrFun this x

end JuschenkoMonod

theorem solution : type_of% @JuschenkoMonod.pi_aux := @JuschenkoMonod.pi_aux
