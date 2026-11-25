-- Prove2me | solution 1 for GlobalTheory.Per.Sen.adapted_basis_jumps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:00:53.795882+00:00
-- url     : https://prove2.me/submissions/393b9405-a398-4a2f-b341-de407c31f22c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntitoneFiltrationExistsAdaptedLinearIndepSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankSpanImageEqCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module
namespace GlobalTheory.Per.Sen
private theorem exists_eq_of_antitone_le_of_exhaustive {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (hA : Antitone A)
    (hAD : ∀ a, A a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ A a) : ∃ a, A a = D := by
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional D).mpr inferInstance
  have key : ∀ T : Finset M, (T : Set M) ⊆ D → ∃ a, ∀ x ∈ T, x ∈ A a := by
    intro T
    classical
    refine Finset.induction_on T ?_ ?_
    · intro _; exact ⟨0, by simp⟩
    · intro y T _ ih hT
      obtain ⟨a, ha⟩ := ih (fun z hz => hT (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hz)))
      obtain ⟨b, hb⟩ := hex y (hT (Finset.mem_coe.mpr (Finset.mem_insert_self y T)))
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hA (min_le_right a b) hb
      · exact hA (min_le_left a b) (ha x hx)
  obtain ⟨a, ha⟩ := key S (by rw [← hS]; exact Submodule.subset_span)
  refine ⟨a, le_antisymm (hAD a) ?_⟩
  rw [← hS, Submodule.span_le]
  exact fun x hx => ha x hx
private theorem exists_adapted_basis_of_finrank_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (r : ℕ) : ∀ (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M)
    (U : Multiset ℤ), Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) →
    (∀ x ∈ D, ∃ a, x ∈ A a) → (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  induction r with
  | zero =>
    intro D _ A U hr hA hAD hex hsep hU
    have hD : D = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hA0 : ∀ a, A a = ⊥ := fun a => le_bot_iff.mp (hD ▸ hAD a)
    have hU0 : U = 0 := by
      ext a
      have h := hU a
      rw [hA0 a, hA0 (a + 1), finrank_bot] at h
      rw [Multiset.count_zero]
      push_cast at h
      omega
    refine ⟨Fin.elim0, Fin.elim0, by simp [hU0], linearIndependent_empty_type, fun a => ?_⟩
    rw [hA0 a]; symm
    rw [Submodule.span_eq_bot]
    rintro x ⟨k, -, -⟩
    exact k.elim0
  | succ r ih =>
    intro D _ A U hr hA hAD hex hsep hU
    classical
    obtain ⟨a0, ha0⟩ := exists_eq_of_antitone_le_of_exhaustive D A hA hAD hex
    have hDne : D ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hr; omega
    obtain ⟨w, hwD, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hDne
    obtain ⟨b, hb⟩ : ∃ b, w ∉ A b := by
      by_contra h; push Not at h; exact hw0 (hsep w h)
    have hbd : ∀ a, A a = D → a < b := by
      intro a ha; by_contra h; push Not at h
      exact hb (hA h (by rw [ha]; exact hwD))
    obtain ⟨s, hs, hsmax⟩ :=
      Int.exists_greatest_of_bdd ⟨b, fun z hz => (hbd z hz).le⟩ ⟨a0, ha0⟩
    have hBD : A (s + 1) < D :=
      lt_of_le_of_ne (hAD _) (fun h => by have := hsmax _ h; omega)
    obtain ⟨v, hvD, hvB⟩ := SetLike.exists_of_lt hBD
    have hv0 : v ≠ 0 := fun h => hvB (by rw [h]; exact Submodule.zero_mem _)
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (A (s + 1) ⊔ Submodule.span L {v})
    obtain ⟨D', hD'⟩ : ∃ D' : Submodule L M, D' = A (s + 1) ⊔ (C ⊓ D) := ⟨_, rfl⟩
    have hED : A (s + 1) ⊔ Submodule.span L {v} ≤ D :=
      sup_le (hAD _) ((Submodule.span_singleton_le_iff_mem _ _).mpr hvD)
    have hD'D : D' ≤ D := by rw [hD']; exact sup_le (hAD _) inf_le_right
    have hBD' : A (s + 1) ≤ D' := by rw [hD']; exact le_sup_left
    have hvD' : v ∉ D' := by
      intro hv
      rw [hD'] at hv
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
      have hzE : z ∈ A (s + 1) ⊔ Submodule.span L {v} := by
        have : z = v - y := by rw [← hyz]; abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
          (Submodule.mem_sup_left hy)
      have hz0 : z = 0 := (Submodule.disjoint_def.mp hC.disjoint) z hzE hz.1
      apply hvB; rw [← hyz, hz0, add_zero]; exact hy
    have hsup : D' ⊔ Submodule.span L {v} = D := by
      rw [hD', sup_right_comm, ← sup_inf_assoc_of_le _ hED, hC.sup_eq_top, top_inf_eq]
    have hinf : D' ⊓ Submodule.span L {v} = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd ((Submodule.smul_mem_iff _ hc).mp hx1) hvD'
    have : FiniteDimensional L D' := Submodule.finiteDimensional_of_le hD'D
    have : FiniteDimensional L (Submodule.span L {v}) :=
      FiniteDimensional.span_of_finite L (Set.finite_singleton v)
    have hrD' : Module.finrank L D' = r := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq D' (Submodule.span L {v})
      rw [hsup, hinf, finrank_bot, finrank_span_singleton hv0, hr] at h
      omega
    have hlow : ∀ a, a ≤ s → A a = D := fun a ha =>
      le_antisymm (hAD a) (by rw [← hs]; exact hA ha)
    have hs_mem : 0 < U.count s := by
      have h := hU s
      rw [hs, hr] at h
      have := Submodule.finrank_lt_finrank_of_lt hBD
      rw [hr] at this
      omega
    have hU' : ∀ a : ℤ, (Module.finrank L ↥(A a ⊓ D') : ℤ) -
        Module.finrank L ↥(A (a + 1) ⊓ D') = ((U.erase s).count a : ℤ) := by
      intro a
      rcases lt_trichotomy a s with h | h | h
      · have h0 := hU a
        rw [hlow a h.le, hlow (a + 1) (by omega)] at h0
        rw [hlow a h.le, hlow (a + 1) (by omega), inf_eq_right.mpr hD'D,
          Multiset.count_erase_of_ne h.ne]
        omega
      · rw [h]
        have h0 := hU s
        rw [hs, hr] at h0
        rw [hs, inf_eq_right.mpr hD'D, inf_eq_left.mpr hBD', Multiset.count_erase_self, hrD',
          Nat.cast_sub hs_mem, Nat.cast_one]
        push_cast at h0 ⊢
        omega
      · rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD'),
          inf_eq_left.mpr ((hA (show s + 1 ≤ a + 1 by omega)).trans hBD'),
          Multiset.count_erase_of_ne h.ne']
        exact hU a
    obtain ⟨u', d', hu', hd', hspan'⟩ := ih D' (fun a => A a ⊓ D') (U.erase s) hrD'
      (fun a b h => inf_le_inf_right _ (hA h)) (fun a => inf_le_right)
      (fun x hx => by obtain ⟨a, ha⟩ := hex x (hD'D hx); exact ⟨a, Submodule.mem_inf.mpr ⟨ha, hx⟩⟩)
      (fun x hx => hsep x (fun a => (Submodule.mem_inf.mp (hx a)).1)) hU'
    have hd'D' : ∀ k, d' k ∈ D' := by
      intro k
      have h := hspan' (u' k)
      have hk : d' k ∈ Submodule.span L (d' '' {j | u' k ≤ u' j}) :=
        Submodule.subset_span ⟨k, le_refl (u' k), rfl⟩
      rw [← h] at hk
      exact (Submodule.mem_inf.mp hk).2
    refine ⟨Fin.cons s u', Fin.cons v d', ?_, ?_, ?_⟩
    · rw [Fin.univ_val_map, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu']
      exact Multiset.cons_erase (Multiset.count_pos.mp hs_mem)
    · refine linearIndependent_finCons.mpr ⟨hd', fun hv => hvD' ?_⟩
      exact (Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hd'D' k)) hv
    · intro a
      by_cases has : a ≤ s
      · rw [hlow a has]
        apply le_antisymm
        · rw [← hsup, sup_le_iff]
          constructor
          · have h := hspan' a
            rw [hlow a has, inf_eq_right.mpr hD'D] at h
            rw [h]
            apply Submodule.span_mono
            rintro _ ⟨j, hj, rfl⟩
            exact ⟨j.succ, by simpa using hj, by simp⟩
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            exact Submodule.subset_span ⟨0, by simpa using has, by simp⟩
        · rw [Submodule.span_le]
          rintro _ ⟨k, -, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simpa using hvD
          · simpa using hD'D (hd'D' j)
      · push Not at has
        have h := hspan' a
        rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD')] at h
        rw [h]
        congr 1
        ext x
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.succ, by simpa using hj, by simp⟩
        · rintro ⟨k, hk, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simp at hk; omega
          · exact ⟨j, by simpa using hk, by simp⟩
end GlobalTheory.Per.Sen
end

set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.Per GlobalTheory.Per.Sen
namespace GlobalTheory.Per.Sen
theorem _root_.solution : ∀ {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (U : Multiset ℤ) (r : ℕ),
    Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) → (∀ x ∈ D, ∃ a, x ∈ A a) →
    (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  intro L M _ _ _ D _ A U r hr hA hAD hex hsep hU
  exact exists_adapted_basis_of_finrank_jumps r D A U hr hA hAD hex hsep hU
end GlobalTheory.Per.Sen
