-- Prove2me | solution 1 for GlobalTheory.TensHead.le_ker_of_simple_commuting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:40:16.069095+00:00
-- url     : https://prove2.me/submissions/a268b16e-770b-4fc6-9b6e-d11c77ec7378

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple
import Theorems.Thm_GlobalTheory_TensHead_MinStab_map
import Theorems.Thm_GlobalTheory_TensHead_exists_stab_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
namespace GlobalTheory.TensHead
theorem _root_.solution {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W]
    [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W))
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L)
    (hmax : ∀ N : Submodule ℂ M, Rel ≤ N → Stab Op N → N ≠ ⊤ → N ≤ K)
    (hKtop : K ≠ ⊤) (hK : Stab Op K) (hRel : Rel ≤ LinearMap.ker φ)
    (hφ : ∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ)
    (hcomm : ∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g)
    (hsimple : ∀ U : Submodule ℂ W, Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) :
    K ≤ LinearMap.ker φ := by
  classical
  have hint : ∀ g ∈ Op, ∀ x, φ (g x) = act g (φ x) := fun g hg x =>
    LinearMap.congr_fun (hφ g hg) x
  by_cases hφ0 : LinearMap.range φ = ⊥
  · intro x _
    have hx : φ x ∈ LinearMap.range φ := LinearMap.mem_range_self φ x
    rw [hφ0] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have hrange : Stab (act '' Op) (LinearMap.range φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨g x, hint g hg x⟩
  have hcomap : ∀ U : Submodule ℂ W, Stab (act '' Op) U → Stab Op (U.comap φ) := by
    intro U hU g hg x hx
    show φ (g x) ∈ U
    rw [hint g hg x]
    exact hU _ ⟨g, hg, rfl⟩ _ hx
  have hRelc : ∀ U : Submodule ℂ W, Rel ≤ U.comap φ := by
    intro U x hx
    show φ x ∈ U
    rw [LinearMap.mem_ker.mp (hRel hx)]
    exact U.zero_mem
  obtain ⟨L, hL⟩ := hL
  let P : Set (Submodule ℂ W) := {U | U ≤ LinearMap.range φ ∧ Stab (act '' Op) U ∧ U ≠ ⊥}
  have hwf : P.WellFoundedOn (· < ·) := by
    rw [Set.wellFoundedOn_iff_no_descending_seq]
    intro f hf
    have hlt : ∀ m n : ℕ, m < n → f n < f m := fun m n h => f.map_rel_iff.mpr h
    have hmono : StrictMono (fun i : Fin (L + 1) => (f (L - i.val)).comap φ) := by
      intro i j hij
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      have hlt' : f (L - i.val) < f (L - j.val) := hlt _ _ (by omega)
      show (f (L - i.val)).comap φ < (f (L - j.val)).comap φ
      refine lt_of_le_of_ne (Submodule.comap_mono hlt'.le) ?_
      intro heq
      have hmap := congrArg (Submodule.map φ) heq
      rw [Submodule.map_comap_eq_self (hf _).1, Submodule.map_comap_eq_self (hf _).1] at hmap
      exact hlt'.ne hmap
    have hbound := hL (L + 1) _ hmono (fun j => ⟨hRelc _, hcomap _ (hf _).2.1⟩)
    omega
  have hPne : LinearMap.range φ ∈ P := ⟨le_rfl, hrange, hφ0⟩
  obtain ⟨T, hTP, hTmin⟩ := (Set.wellFoundedOn_iff.mp hwf).has_min P ⟨_, hPne⟩
  have hTms : MinStab (act '' Op) T := by
    refine ⟨hTP.2.1, fun U hU hUT => ?_⟩
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      by_contra hne
      have hUP : U ∈ P := ⟨hUT.trans hTP.1, hU, hU0⟩
      exact hTmin U hUP ⟨lt_of_le_of_ne hUT hne, hUP, hTP⟩
  have hbcomm : ∀ b ∈ B, ∀ a ∈ act '' Op, a * b = b * a := by
    rintro b hb _ ⟨g, hg, rfl⟩
    exact hcomm g hg b hb
  have hstop : sSup {T | MinStab (act '' Op) T} = ⊤ := by
    have hst : Stab (act '' Op ∪ B) (sSup {T | MinStab (act '' Op) T}) := by
      intro a ha
      rcases ha with ha | ha
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy => (le_sSup hT' : T' ≤ _) (hT'.1 a ha y hy)
        exact fun x hx => hle hx
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy =>
            (le_sSup (MinStab.map hT' a (hbcomm a ha)) : T'.map a ≤ _) (Submodule.mem_map_of_mem hy)
        exact fun x hx => hle hx
    rcases hsimple _ hst with h | h
    · exact absurd (eq_bot_iff.mpr ((le_sSup (show T ∈ {T | MinStab (act '' Op) T} from hTms)).trans h.le)) hTP.2.2
    · exact h
  have hKs : Stab (act '' Op) (K.map φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hint g hg k]
    exact Submodule.mem_map_of_mem (hK g hg k hk)
  obtain ⟨C, hCs, hCK, hCtop⟩ := exists_stab_compl hstop (K.map φ) hKs
  have hNK : C.comap φ ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hm : φ m ∈ C ⊔ K.map φ := by rw [hCtop]; exact Submodule.mem_top
    obtain ⟨c, hc, y, hy, hcy⟩ := Submodule.mem_sup.mp hm
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    have hmk : m - k ∈ C.comap φ := by
      show φ (m - k) ∈ C
      rw [map_sub, ← hcy, add_sub_cancel_right]
      exact hc
    simpa using Submodule.add_mem_sup hmk hk
  by_cases hN : C.comap φ = ⊤
  · intro k hk
    have h1 : k ∈ C.comap φ := by rw [hN]; exact Submodule.mem_top
    have h2 : φ k ∈ C ⊓ K.map φ := ⟨h1, Submodule.mem_map_of_mem hk⟩
    rw [hCK] at h2
    exact (Submodule.mem_bot ℂ).mp h2
  · exact absurd (top_unique (hNK.symm.le.trans
      (sup_le (hmax _ (hRelc C) (hcomap C hCs) hN) le_rfl))) hKtop
end GlobalTheory.TensHead
