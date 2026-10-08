-- Prove2me | solution 1 for GottschalkSurjunctivity.isSurjunctive_of_fg_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:01:17.369073+00:00
-- url     : https://prove2.me/submissions/a6f36418-5f9e-4192-a67f-bcce1712cf52

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

set_option autoImplicit false

namespace GSLocal1290

open GottschalkSurjunctivity

/-- Curtis–Hedlund–Lyndon style locality: a continuous map to a discrete finite space
depends only on finitely many coordinates. -/
theorem exists_finset_local {G A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (f : (G → A) → A) (hf : Continuous f) :
    ∃ S : Finset G, ∀ x x' : G → A, (∀ s ∈ S, x s = x' s) → f x = f x' := by
  classical
  have hopen : ∀ x : G → A, IsOpen (f ⁻¹' {f x}) := fun x => (isOpen_discrete _).preimage hf
  have hI : ∀ x : G → A, ∃ (I : Finset G) (u : G → Set A),
      (∀ a, a ∈ I → IsOpen (u a) ∧ x a ∈ u a) ∧ (I : Set G).pi u ⊆ f ⁻¹' {f x} :=
    fun x => isOpen_pi_iff.mp (hopen x) x rfl
  choose I u hu hsub using hI
  have : CompactSpace A := Finite.compactSpace
  let U : (G → A) → Set (G → A) := fun x => (I x : Set G).pi (fun s => {x s})
  have hUopen : ∀ x, IsOpen (U x) := fun x =>
    isOpen_set_pi (I x).finite_toSet (fun _ _ => isOpen_discrete _)
  have hUsub : ∀ x, U x ⊆ f ⁻¹' {f x} := by
    intro x x' hx'
    apply hsub x
    intro s hs
    have : x' s = x s := hx' s hs
    rw [this]
    exact (hu x s hs).2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, fun s _ => rfl⟩)
  refine ⟨t.biUnion I, fun x x' hxx' => ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  have hx'i : x' ∈ U i := by
    intro s hs
    have h1 : x s = i s := hxi s hs
    have h2 : x s = x' s := hxx' s (Finset.mem_biUnion.mpr ⟨i, hi, hs⟩)
    show x' s = i s
    rw [← h2, h1]
  have e1 : f x = f i := hUsub i hxi
  have e2 : f x' = f i := hUsub i hx'i
  rw [e1, e2]

theorem local_of_equivariant {G A : Type} [Group G] (τ : (G → A) → (G → A))
    (hτ : IsShiftEquivariant G τ) (S : Finset G)
    (hS : ∀ x x' : G → A, (∀ s ∈ S, x s = x' s) → τ x 1 = τ x' 1)
    (x x' : G → A) (g : G) (h : ∀ s ∈ S, x (g * s) = x' (g * s)) : τ x g = τ x' g := by
  have key : ∀ y : G → A, τ y g = τ (shift G g⁻¹ y) 1 := by
    intro y
    rw [hτ]
    simp [shift]
  rw [key x, key x']
  apply hS
  intro s hs
  simp only [shift_apply, inv_inv]
  exact h s hs

end GSLocal1290

open GSLocal1290 in
open GottschalkSurjunctivity in
theorem solution (G : Type) [Group G]
    (h : ∀ H : Subgroup G, H.FG → GottschalkSurjunctivity.IsSurjunctive H) :
    GottschalkSurjunctivity.IsSurjunctive G := by
  intro A _ _ _ _ τ hcont hequiv hinj
  classical
  have : Finite A := Finite.of_fintype A
  obtain ⟨S, hS⟩ := exists_finset_local (fun x => τ x 1)
    ((continuous_apply 1).comp hcont)
  have hL := local_of_equivariant τ hequiv S hS
  set H : Subgroup G := Subgroup.closure (S : Set G) with hHdef
  have hSH : ∀ s ∈ S, s ∈ H := fun s hs => Subgroup.subset_closure hs
  have hFG : H.FG := ⟨S, rfl⟩
  have a0 : A := Classical.arbitrary A
  let E : (H → A) → (G → A) := fun z g => if hg : g ∈ H then z ⟨g, hg⟩ else a0
  have hE_mem : ∀ (z : H → A) (k : H), E z k = z k := by
    intro z k
    simp [E]
  have hE_cont : Continuous E := by
    apply continuous_pi
    intro g
    by_cases hg : g ∈ H
    · simp only [E, hg, dif_pos]
      exact continuous_apply _
    · simp only [E, hg, dif_neg, not_false_eq_true]
      exact continuous_const
  let τH : (H → A) → (H → A) := fun z k => τ (E z) k
  have hτH_cont : Continuous τH := by
    apply continuous_pi
    intro k
    exact (continuous_apply (k : G)).comp (hcont.comp hE_cont)
  have hτH_equiv : IsShiftEquivariant H τH := by
    intro k z
    funext m
    show τ (E (shift H k z)) m = τ (E z) ↑(k⁻¹ * m)
    have h1 : τ (E (shift H k z)) m = τ (shift G (k : G) (E z)) m := by
      apply hL
      intro s hs
      have hms : (m : G) * s ∈ H := H.mul_mem m.2 (hSH s hs)
      have hkms : (k : G)⁻¹ * ((m : G) * s) ∈ H := H.mul_mem (H.inv_mem k.2) hms
      simp only [E, hms, hkms, dif_pos, shift_apply]
      congr 1
    rw [h1, hequiv]
    simp [shift_apply]
  have hτH_inj : Function.Injective τH := by
    intro z z' hzz
    have hall : τ (E z) = τ (E z') := by
      funext g
      by_cases hg : g ∈ H
      · have := congrFun hzz ⟨g, hg⟩
        exact this
      · apply hL
        intro s hs
        have hgs : g * s ∉ H := by
          intro hm
          apply hg
          have := H.mul_mem hm (H.inv_mem (hSH s hs))
          simpa using this
        simp [E, hgs]
    have hEE := hinj hall
    funext k
    rw [← hE_mem z k, ← hE_mem z' k, hEE]
  have hτH_surj := h H hFG A τH hτH_cont hτH_equiv hτH_inj
  intro y
  let zc : G → (H → A) := fun c => Classical.choose (hτH_surj (fun k : H => y (c * k)))
  have hzc : ∀ c, τH (zc c) = fun k : H => y (c * k) := fun c =>
    Classical.choose_spec (hτH_surj (fun k : H => y (c * k)))
  let r : G → G := fun g => (QuotientGroup.mk g : G ⧸ H).out
  have hr_mem : ∀ g, (r g)⁻¹ * g ∈ H := by
    intro g
    have : (QuotientGroup.mk (r g) : G ⧸ H) = QuotientGroup.mk g := Quotient.out_eq' _
    exact QuotientGroup.eq.mp this
  have hr_coset : ∀ g (k : G), k ∈ H → r (g * k) = r g := by
    intro g k hk
    have : (QuotientGroup.mk (g * k) : G ⧸ H) = QuotientGroup.mk g := by
      apply QuotientGroup.eq.mpr
      simpa using H.inv_mem hk
    simp only [r, this]
  refine ⟨fun g => E (zc (r g)) ((r g)⁻¹ * g), ?_⟩
  funext g
  set c := r g with hc
  have h1 : τ (fun g => E (zc (r g)) ((r g)⁻¹ * g)) g = τ (shift G c (E (zc c))) g := by
    apply hL
    intro s hs
    simp only [shift_apply]
    rw [hr_coset g s (hSH s hs), ← hc]
  rw [h1, hequiv, shift_apply]
  have h2 := congrFun (hzc c) ⟨c⁻¹ * g, hr_mem g⟩
  simp only [τH] at h2
  rw [h2]
  simp
