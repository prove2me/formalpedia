-- Prove2me | solution 1 for MooreFoelner.isMarginal_union_subset_image
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T05:14:36.477056+00:00
-- url     : https://prove2.me/submissions/a19d264e-ac75-421e-909a-519b8b3af47f

import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §3 (group Sec3B): Remark 3.8, Lemmas 3.10, 3.12, 3.14, 3.15
-/

namespace MooreFoelner.Dev.Sec3B

open Classical MooreFoelner

set_option linter.unusedSectionVars false

variable {G S : Type*} [Group G]

/-! ## Marginal sets -/

theorem marginalizes_mono {act : S → G → Option S} {g : G} {E E' I I' : Set S}
    (h : Marginalizes act g E I) (hE : E' ⊆ E) (hI : I ⊆ I') : Marginalizes act g E' I' := by
  intro x hx k hk ⟨y, hy, hxy⟩
  obtain ⟨i, hi, h'⟩ := h x (hE hx) k hk ⟨y, hE hy, hxy⟩
  refine ⟨i, hi, ?_⟩
  rcases h' with h' | ⟨z, hz, hxz⟩
  · exact Or.inl h'
  · exact Or.inr ⟨z, hI hz, hxz⟩

theorem isKMarginal_empty (act : S → G → Option S) : ∀ k, IsKMarginal act k ∅
  | 0 => IsKMarginal.zero
  | k + 1 => by
    have := IsKMarginal.succ (act := act) (k := k) (l := 0) (fun _ => ∅) (fun _ => ∅) (fun _ => 1)
      (fun i => i.elim0) (fun i => i.elim0)
    simpa using this

theorem isKMarginal_succ_of {act : S → G → Option S} {k : ℕ} {E : Set S}
    (h : IsKMarginal act k E) : IsKMarginal act (k + 1) E := by
  induction h with
  | zero => exact isKMarginal_empty act 1
  | succ E I g hI hg ih => exact IsKMarginal.succ E I g ih hg

theorem isKMarginal_mono {act : S → G → Option S} {k k' : ℕ} {E : Set S}
    (h : IsKMarginal act k E) (hk : k ≤ k') : IsKMarginal act k' E := by
  induction k', hk using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact isKMarginal_succ_of ih

theorem isKMarginal_subset {act : S → G → Option S} {k : ℕ} {E E' : Set S}
    (h : IsKMarginal act k E) (hE : E' ⊆ E) : IsKMarginal act k E' := by
  cases h with
  | zero =>
    rw [Set.subset_empty_iff.mp hE]
    exact IsKMarginal.zero
  | succ E I g hI hg =>
    have heq : (⋃ i, (E i ∩ E')) = E' := by
      rw [← Set.iUnion_inter]
      exact Set.inter_eq_right.mpr hE
    rw [← heq]
    exact IsKMarginal.succ (fun i => E i ∩ E') I g hI
      (fun i => marginalizes_mono (hg i) Set.inter_subset_left le_rfl)

theorem isKMarginal_union {act : S → G → Option S} {k : ℕ} {E E' : Set S}
    (h : IsKMarginal act k E) (h' : IsKMarginal act k E') : IsKMarginal act k (E ∪ E') := by
  cases h with
  | zero =>
    rw [Set.empty_union]; exact h'
  | succ E I g hI hg =>
    rename_i k l
    cases h' with
    | succ E' I' g' hI' hg' =>
      rename_i l'
      have heq : (⋃ i, Fin.append E E' i) = (⋃ i, E i) ∪ ⋃ i, E' i := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, hi⟩
          induction i using Fin.addCases with
          | left i => rw [Fin.append_left] at hi; exact Or.inl ⟨i, hi⟩
          | right i => rw [Fin.append_right] at hi; exact Or.inr ⟨i, hi⟩
        · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
          · exact ⟨Fin.castAdd l' i, by rw [Fin.append_left]; exact hi⟩
          · exact ⟨Fin.natAdd l i, by rw [Fin.append_right]; exact hi⟩
      rw [← heq]
      refine IsKMarginal.succ (Fin.append E E') (Fin.append I I') (Fin.append g g') ?_ ?_
      · intro i
        induction i using Fin.addCases with
        | left i => rw [Fin.append_left]; exact hI i
        | right i => rw [Fin.append_right]; exact hI' i
      · intro i
        induction i using Fin.addCases with
        | left i => rw [Fin.append_left, Fin.append_left, Fin.append_left]; exact hg i
        | right i => rw [Fin.append_right, Fin.append_right, Fin.append_right]; exact hg' i

theorem isMarginal_union {act : S → G → Option S} {E E' : Set S}
    (h : IsMarginal act E) (h' : IsMarginal act E') : IsMarginal act (E ∪ E') := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  exact ⟨max k k', isKMarginal_union (isKMarginal_mono hk (le_max_left _ _))
    (isKMarginal_mono hk' (le_max_right _ _))⟩

theorem marginalizes_image_diff {act : S → G → Option S} (hact : IsPartialAction act)
    (E : Set S) (g : G) : Marginalizes act g⁻¹ (image act E g \ E) E := by
  rintro x ⟨⟨y, hy, hyx⟩, hxE⟩ k hk ⟨z, ⟨_, hzE⟩, hxz⟩
  have hxy : act x g⁻¹ = some y := (hact.inv g y x).mp hyx
  have h1 : actPow act x g⁻¹ 1 = some y := by simp [actPow, hxy]
  have hk1 : 1 < k := by
    by_contra hk1
    have : k = 1 := by omega
    subst this
    rw [h1] at hxz
    cases hxz
    exact hzE hy
  exact ⟨1, hk1, Or.inr ⟨y, hy, h1⟩⟩

/-! ## Mass, restriction and `valAt` -/

/-! ## Weighted Følner sets -/

/-! ## Lemma 3.10 -/

/-! ## Γ-connected sets and components -/

section comp

variable {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ}

end comp

/-! ## The right action of `G` on itself -/

end MooreFoelner.Dev.Sec3B

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Sec3B in
theorem solution {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) :
    (∀ s : Finset (Set S), (∀ E ∈ s, IsMarginal act E) → IsMarginal act (⋃₀ (s : Set (Set S)))) ∧
    (∀ E E' : Set S, E' ⊆ E → IsMarginal act E → IsMarginal act E') ∧
    (∀ (E : Set S) (g : G), Marginalizes act g⁻¹ (E \ image act E g) E) ∧
    (∀ (E : Set S) (g : G), IsMarginal act E → IsMarginal act (image act E g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simpa using IsKMarginal.zero⟩
    | insert a s _ ih =>
      intro hs
      rw [Finset.coe_insert, Set.sUnion_insert]
      exact isMarginal_union (hs a (Finset.mem_insert_self a s))
        (ih fun E hE => hs E (Finset.mem_insert_of_mem hE))
  · rintro E E' hE ⟨k, hk⟩
    exact ⟨k, isKMarginal_subset hk hE⟩
  · rintro E g x ⟨hx, _⟩ k _ _
    refine ⟨0, by omega, Or.inr ⟨x, hx, ?_⟩⟩
    simp [actPow, hact.one]
  · rintro E g ⟨k, hk⟩
    have hD : IsKMarginal act (k + 1) (image act E g \ E) := by
      have := IsKMarginal.succ (act := act) (k := k) (l := 1) (fun _ => image act E g \ E)
        (fun _ => E) (fun _ => g⁻¹) (fun _ => hk) (fun _ => marginalizes_image_diff hact E g)
      rwa [Set.iUnion_const] at this
    have hU : IsMarginal act (E ∪ (image act E g \ E)) :=
      isMarginal_union ⟨k, hk⟩ ⟨k + 1, hD⟩
    obtain ⟨m, hm⟩ := hU
    refine ⟨m, isKMarginal_subset hm ?_⟩
    intro y hy
    by_cases hyE : y ∈ E
    · exact Or.inl hyE
    · exact Or.inr ⟨hy, hyE⟩
