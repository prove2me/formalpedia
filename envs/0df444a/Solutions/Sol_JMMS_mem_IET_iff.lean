-- Prove2me | solution 1 for JMMS.mem_IET_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T10:54:16.362488+00:00
-- url     : https://prove2.me/submissions/bff87ad1-36fd-4e21-8648-0373af0a55b7

import Mathlib
import Definitions.Def_IntervalExchange

section
open IntervalExchange
open scoped ENNReal
open Filter Topology

namespace JMMS
namespace IETP1

lemma contMk : Continuous (fun t : ℝ => (t : UnitAddCircle)) := continuous_quotient_mk'

/-- A function continuous within `s` at `a` with values in a finite set is eventually constant. -/
lemma eventually_eq_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {f : α → β} {s : Set α} {a : α} {S : Set β} (hS : S.Finite) (hf : ∀ t, f t ∈ S)
    (hc : ContinuousWithinAt f s a) : ∀ᶠ t in 𝓝[s] a, f t = f a := by
  have hopen : IsOpen (S \ {f a})ᶜ := ((hS.subset Set.sdiff_subset).isClosed).isOpen_compl
  have hmem : f a ∈ (S \ {f a})ᶜ := by simp
  filter_upwards [hc (hopen.mem_nhds hmem)] with t ht
  by_contra hne
  exact ht ⟨hf t, hne⟩

/-- `g` is a translation near every point, from the right. -/
def LocTrans (g : UnitAddCircle → UnitAddCircle) : Prop :=
  ∀ x : UnitAddCircle, ∀ᶠ t : ℝ in 𝓝[Set.Ici (0:ℝ)] (0:ℝ), g (x + (t : UnitAddCircle)) = g x + t

lemma locTrans_of {g : UnitAddCircle → UnitAddCircle} (hr : IsRightContinuous g)
    (ha : (angles g).Finite) : LocTrans g := by
  intro x
  have hc : ContinuousWithinAt
      (fun t : ℝ => g (x + (t : UnitAddCircle)) - (x + (t : UnitAddCircle))) (Set.Ici 0) 0 :=
    (hr x).sub ((continuous_const.add contMk).continuousWithinAt)
  filter_upwards [eventually_eq_of_finite ha (fun t => ⟨x + t, rfl⟩) hc] with t ht
  simp only [QuotientAddGroup.mk_zero, add_zero] at ht
  rw [← sub_add_cancel (g (x + t)) (x + t), ht]
  abel

lemma rc_of_locTrans {g : UnitAddCircle → UnitAddCircle} (h : LocTrans g) :
    IsRightContinuous g := by
  intro x
  have hc : ContinuousWithinAt (fun t : ℝ => g x + (t : UnitAddCircle)) (Set.Ici 0) 0 :=
    (continuous_const.add contMk).continuousWithinAt
  exact hc.congr_of_eventuallyEq (h x) (by simp)

lemma locTrans_comp {g h : UnitAddCircle → UnitAddCircle} (hg : LocTrans g) (hh : LocTrans h) :
    LocTrans (g ∘ h) := by
  intro x
  filter_upwards [hh x, hg (h x)] with t h1 h2
  simp only [Function.comp]
  rw [h1, h2]

lemma eventually_of_continuousAt {g : UnitAddCircle → UnitAddCircle} (ha : (angles g).Finite)
    {x : UnitAddCircle} (hc : ContinuousAt g x) : ∀ᶠ z in 𝓝 x, g z - z = g x - x := by
  have := eventually_eq_of_finite (s := Set.univ) ha (fun t => ⟨t, rfl⟩)
    ((hc.sub continuousAt_id).continuousWithinAt)
  simpa [nhdsWithin_univ] using this

lemma continuousAt_inv (g : Equiv.Perm UnitAddCircle) (ha : (angles g).Finite)
    {x : UnitAddCircle} (hc : ContinuousAt g x) : ContinuousAt (⇑g⁻¹) (g x) := by
  set c := g x - x with hcdef
  have hU := eventually_of_continuousAt ha hc
  have hV : ∀ᶠ w in 𝓝 (g x), g⁻¹ w = w - c := by
    have ht : Tendsto (fun w => w - c) (𝓝 (g x)) (𝓝 x) := by
      have := (continuous_sub_right c).tendsto (g x)
      simpa [c] using this
    filter_upwards [ht hU] with w hw
    have hw' : g (w - c) = w := by
      have hw2 : g (w - c) - (w - c) = c := hw
      rw [← sub_add_cancel (g (w - c)) (w - c), hw2]
      abel
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hw'.symm
  have : ContinuousAt (fun w : UnitAddCircle => w - c) (g x) :=
    (continuous_id.sub continuous_const).continuousAt
  exact this.congr (hV.mono fun w hw => hw.symm)

/-- The interval exchange transformations form a subgroup. -/
def S : Subgroup (Equiv.Perm UnitAddCircle) where
  carrier := {g | IsIntervalExchange g}
  one_mem' := by
    refine ⟨fun x => ?_, ?_, ?_⟩
    · exact (continuous_const.add contMk).continuousWithinAt
    · refine (Set.finite_singleton (0 : UnitAddCircle)).subset ?_
      rintro _ ⟨x, rfl⟩
      simp
    · refine Set.finite_empty.subset ?_
      intro x hx
      exact hx continuous_id.continuousAt
  mul_mem' := by
    rintro g h ⟨hgr, hga, hgd⟩ ⟨hhr, hha, hhd⟩
    refine ⟨?_, ?_, ?_⟩
    · apply rc_of_locTrans
      rw [Equiv.Perm.coe_mul]
      exact locTrans_comp (locTrans_of hgr hga) (locTrans_of hhr hha)
    · refine (hga.image2 (· + ·) hha).subset ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨_, ⟨h x, rfl⟩, _, ⟨x, rfl⟩, by simp [Equiv.Perm.mul_apply]⟩
    · refine (hhd.union (hgd.preimage h.injective.injOn)).subset ?_
      intro x hx
      by_contra hn
      apply hx
      rw [Set.mem_union, not_or] at hn
      have h1 : ContinuousAt h x := by simpa using hn.1
      have h2 : ContinuousAt g (h x) := by simpa using hn.2
      rw [Equiv.Perm.coe_mul]
      exact h2.comp h1
  inv_mem' := by
    rintro g ⟨hgr, hga, hgd⟩
    refine ⟨?_, ?_, ?_⟩
    · apply rc_of_locTrans
      intro y
      filter_upwards [locTrans_of hgr hga (g⁻¹ y)] with t ht
      rw [Equiv.Perm.inv_eq_iff_eq, ht]
      simp
    · refine (hga.image Neg.neg).subset ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨_, ⟨g⁻¹ y, rfl⟩, by simp⟩
    · refine (hgd.image g).subset ?_
      intro y hy
      refine ⟨g⁻¹ y, ?_, by simp⟩
      intro hc
      apply hy
      simpa using continuousAt_inv g hga hc

end IETP1

theorem chk_mem_IET_iff (g : Equiv.Perm UnitAddCircle) : g ∈ IET ↔ IsIntervalExchange g := by
  have : IET = IETP1.S := Subgroup.closure_eq IETP1.S
  rw [this]
  rfl

end JMMS
end

open IntervalExchange
open scoped ENNReal
open JMMS in
theorem solution (g : Equiv.Perm UnitAddCircle) : g ∈ IET ↔ IsIntervalExchange g := by
  apply JMMS.chk_mem_IET_iff <;> assumption
