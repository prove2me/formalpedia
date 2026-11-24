-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.index_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:28:03.400502+00:00
-- url     : https://prove2.me/submissions/ac907529-4653-40c1-ba54-8b92460abe8a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_chainT
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_val_zpow_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_conj_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (a : Fin N → ℤ), ϖ ≠ 0 →
    ValuativeRel.valuation k (ϖ) < 1 →
    (∀ x : k, ValuativeRel.valuation k (x) < 1 →
      ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Antitone a →
    ∀ D : GL (Fin N) k, (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)) →
    ∀ H : Subgroup (GL (Fin N) k), (H : Set (GL (Fin N) k)) =
      {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)} →
    (H.map (MulAut.conj D).toMonoidHom).relIndex H =
      Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) ^
        (∑ i : Fin N, ∑ j : Fin N, if i < j then (a i - a j).toNat else 0) := by
  intro k _ _ _ _ N ϖ m a h0 h1 hu hm ha D hD H hH
  classical
  have hH' : (H : Set (GL (Fin N) k)) = Kset ϖ (fun _ _ => m) := hH
  set b : Fin N → Fin N → ℕ := fun i j => (a i - a j).toNat with hbdef
  obtain ⟨T, hT⟩ : ∃ T, ∀ i j, b i j ≤ T :=
    ⟨∑ i, ∑ j, b i j, fun i j =>
      (Finset.single_le_sum (f := fun j => b i j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, b i j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i))⟩
  obtain ⟨G, hG, -, hidx⟩ := chainT h0 h1 hu hm (b := b)
    (fun i j l => by simp only [hbdef]; omega) (fun i => by simp [hbdef]) H hH' T
  have hmin : ∀ i j, min (b i j) T = b i j := fun i j => min_eq_left (hT i j)
  simp only [hmin] at hG hidx
  have hGeq : G = H.map (MulAut.conj D).toMonoidHom ⊓ H := by
    apply SetLike.coe_injective
    rw [hG]
    ext g
    have hmap : g ∈ H.map (MulAut.conj D).toMonoidHom ↔ D⁻¹ * g * D ∈ H := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hmemH : ∀ x, x ∈ H ↔ x ∈ Kset ϖ (fun _ _ => m) := fun x => by
      rw [← hH']; rfl
    rw [SetLike.mem_coe, Subgroup.mem_inf, hmap, hmemH, hmemH]
    simp only [Kset, Set.mem_setOf_eq, conj_entry h0 hD]
    constructor
    · intro h
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have := (val_zpow_iff h0 h1 m (a j - a i) _).2 (by simpa [hbdef] using h i j)
        exact this.2
      · have := (val_zpow_iff h0 h1 m (a j - a i) _).2 (by simpa [hbdef] using h i j)
        exact this.1
    · rintro ⟨h2, h3⟩ i j
      have := (val_zpow_iff h0 h1 m (a j - a i) _).1 ⟨h3 i j, h2 i j⟩
      simpa [hbdef] using this
  rw [← Subgroup.inf_relIndex_right, ← hGeq, hidx]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rfl
  · have : a i ≤ a j := ha (not_lt.1 hij)
    simp only [hbdef]
    omega
end GlobalTheory.CompanionTheory.CongIndex
