-- Prove2me | solution 1 for GlobalTheory.IwaFlag.exists_flag_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:45.528571+00:00
-- url     : https://prove2.me/submissions/bd304a27-2231-4c79-b4b7-3167d2ac20ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
import Theorems.Thm_GlobalTheory_IwaFlag_smul_mem_of_sd
import Theorems.Thm_GlobalTheory_IwaFlag_exists_triangular
import Theorems.Thm_GlobalTheory_IwaFlag_exists_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
namespace GlobalTheory.IwaFlag
theorem _root_.solution (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) :
    ∃ b : Fin ρ → Fin ρ → R, (∀ i l, i < l → b i l = 0) ∧ (∀ i l, ε * b i l = b i l) ∧ (∀ i, X (b i) ∈ M) ∧
      ∃ y : Fin ρ → V, (∀ j, y j ∈ M) ∧ ∀ i j, h (X (b i)) (y j) = if i = j then ε else 0 := by
  classical
  choose b α' hb₁ hb₂ _ hα hJ using exists_triangular hεc hmul hP hM₁ hM₂ X f hXf N hN he hf
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have key : ∀ n : ℕ, n ≤ ρ → ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i : Fin ρ, i.1 < n → h (X (b i)) y = z i := by
    intro n
    induction n with
    | zero => exact fun _ z _ => ⟨0, M.zero_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn z hz
      let j : Fin ρ := ⟨n, hn⟩
      obtain ⟨w, hw, hw₁, hw₂⟩ := exists_step hcc hεε hεc hεO hOε hmul hcO hP hM₁ hM₂ X f hXf N hN he hf b hb₁ hb₂ j
        (α' j) (hα j) (hJ j) (ih (Nat.le_of_succ_le hn))
      obtain ⟨y, hy, hy'⟩ := ih (Nat.le_of_succ_le hn) z hz
      have ho : z j - h (X (b j)) y ∈ O := O.sub_mem (hz j) (hint j y hy)
      refine ⟨y + c (z j - h (X (b j)) y) • w, M.add_mem hy (smul_mem_of_sd hmul hM₁ hM₂ (hcO _ ho) hw), fun i hi => ?_⟩
      rw [map_add, map_smulₛₗ, hcc, smul_eq_mul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [hw₁ i hi, hy' i hi, mul_zero, add_zero]
      · have : i = j := Fin.ext hi
        rw [this, hw₂, mul_comm, hOε _ ho, add_sub_cancel]
  choose y hy hy' using fun j : Fin ρ => key ρ le_rfl (Pi.single j ε) fun l => by
    by_cases hl : l = j
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  refine ⟨b, hb₁, fun i k => ?_, hb₂, y, hy, fun i j => ?_⟩
  · have := congrArg (fun z => h z (f k)) (hM₁ _ (hb₂ i))
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  · rw [hy' j i i.2, Pi.single_apply]
end GlobalTheory.IwaFlag
