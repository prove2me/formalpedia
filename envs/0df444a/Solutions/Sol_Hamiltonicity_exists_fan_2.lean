-- Prove2me | solution 2 for Hamiltonicity.exists_fan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:55:46.971915+00:00
-- url     : https://prove2.me/submissions/a4a4a77d-c64b-4bea-a5e8-14fd4177f3dd

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Theorems.Thm_Hamiltonicity_exists_trunc
public import Theorems.Thm_Hamiltonicity_exists_path_avoiding
public import Theorems.Thm_Hamiltonicity_CycArr_eq_mod
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Menger_Aux_Sep_symm
public import Theorems.Thm_Menger_Aux_start_eq_of_isolated
public import Theorems.Thm_Menger_exists_separator_and_paths


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {x : V} (hx : ∀ i, f i ≠ x) :
    ∃ r, min k m ≤ r ∧ ∃ (t : Fin r → ℕ) (P : ∀ j, G.Walk x (f (t j))),
      (∀ j, (P j).IsPath) ∧ (∀ j, ∀ y ∈ (P j).support, ∀ i, f i = y → y = f (t j)) ∧
      (∀ i j, i ≠ j → ∀ y ∈ (P i).support, y ∈ (P j).support → y = x) := by
  classical
  have := Fintype.ofFinite V
  set H := G.deleteEdges {e | x ∈ e} with hH
  have hHx : ∀ w, ¬ H.Adj x w := by intro w h; simp [hH] at h
  have hle : H ≤ G := G.deleteEdges_le _
  set A := G.neighborFinset x with hA
  set B := (Finset.range m).image f with hB
  have hfB : ∀ i, f i ∈ B := fun i => by
    rw [hC.eq_mod i]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.mod_lt _ hC.pos))
  have hBf : ∀ y ∈ B, ∃ i, f i = y := by
    intro y hy
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hy
    exact ⟨i, hi⟩
  have hBcard : B.card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hC.inj i j (by simpa using hi) (by simpa using hj) hij
  have hxA : x ∉ A := by simp [A]
  obtain ⟨X, hX, a, b, p, hp, hd⟩ := Menger.exists_separator_and_paths H A B
  refine ⟨X.card, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hXk : X.card < k := lt_of_lt_of_le hlt (min_le_left _ _)
    have hXm : X.card < m := lt_of_lt_of_le hlt (min_le_right _ _)
    obtain ⟨β, hβB, hβX⟩ : ∃ β ∈ B, β ∉ X := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card (show B ⊆ X from hcon)
      omega
    obtain ⟨i0, hi0⟩ := hBf β hβB
    set S : Set V := ↑(X.erase x) with hS
    have hSk : S.ncard < k := by
      rw [hS, Set.ncard_coe_finset]
      exact lt_of_le_of_lt (Finset.card_erase_le) hXk
    have hxS : x ∉ S := by simp [S]
    have hβS : β ∉ S := by simp [S, hβX]
    obtain ⟨w, hw, hwS⟩ := exists_path_avoiding S (hconn S hSk) hxS hβS
    have hxβ : x ≠ β := fun h => hx i0 (hi0.trans h.symm)
    obtain ⟨a', hxa', rest, rfl⟩ := Walk.exists_eq_cons_of_ne hxβ w
    rw [Walk.cons_isPath_iff] at hw
    have hrest : ∀ e ∈ rest.edges, e ∉ {e : Sym2 V | x ∈ e} := by
      intro e he hxe
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hxe
      exact hw.2 (rest.fst_mem_support_of_mem_edges he)
    obtain ⟨z, hzX, hzr⟩ := hX a' (by simpa [A] using hxa') β hβB
      (rest.toDeleteEdges {e | x ∈ e} hrest)
    have hzr' : z ∈ rest.support := by
      simp only [Walk.toDeleteEdges] at hzr
      rwa [Walk.support_transfer] at hzr
    have hzx : z ≠ x := fun h => hw.2 (h ▸ hzr')
    exact hwS z (by simp [hzr']) (by simp [S, hzX, hzx])
  · have htr : ∀ i, ∃ b' ∈ (B : Set V), ∃ p' : H.Walk (a i) b', p'.IsPath ∧
        p'.support ⊆ (p i).support ∧ ∀ y ∈ p'.support, y ∈ (B : Set V) → y = b' :=
      fun i => exists_trunc (B : Set V) (p i) (hp i).2.1 (hp i).2.2
    choose b' hb' p' hp' hsub hlast using htr
    have hpos : ∀ i, ∃ t, f t = b' i := fun i => hBf _ (hb' i)
    choose t ht using hpos
    have hxp : ∀ i, x ∉ (p' i).support := by
      intro i hxi
      have := Menger.Aux.start_eq_of_isolated hHx (p' i) hxi
      exact hxA (this ▸ (hp i).1)
    have hadjx : ∀ i, G.Adj x (a i) := fun i => by simpa [A] using (hp i).1
    let P : ∀ i, G.Walk x (f (t i)) := fun i =>
      (Walk.cons (hadjx i) ((p' i).mapLe hle)).copy rfl (ht i).symm
    refine ⟨t, P, fun i => ?_, fun i y hy j hj => ?_, fun i j hij y hyi hyj => ?_⟩
    · simp only [P, Walk.isPath_copy, Walk.cons_isPath_iff, Walk.support_mapLe_eq_support]
      exact ⟨(hp' i).mapLe hle, hxp i⟩
    · simp only [P, Walk.support_copy, Walk.support_cons, Walk.support_mapLe_eq_support,
        List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact absurd hj (hx j)
      · rw [ht i]
        exact hlast i y hy (by rw [← hj]; exact hfB j)
    · simp only [P, Walk.support_copy, Walk.support_cons, Walk.support_mapLe_eq_support,
        List.mem_cons] at hyi hyj
      rcases hyi with rfl | hyi
      · rfl
      rcases hyj with rfl | hyj
      · rfl
      exact absurd (hsub j hyj) (hd i j hij y (hsub i hyi))
end Hamiltonicity
