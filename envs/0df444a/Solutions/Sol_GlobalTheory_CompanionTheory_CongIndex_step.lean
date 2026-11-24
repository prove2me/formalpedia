-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:47.916972+00:00
-- url     : https://prove2.me/submissions/863b9d58-a9af-427b-9415-a3dd6a556af7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_val_add_le
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_add
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_eq_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_pow_le_of_le
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_Kset_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_entry_le
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_entry_mul

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
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ)
    {c c' : Fin N → Fin N → ℕ} {i j : Fin N} (hij : i ≠ j)
    (hc : ∀ l, c i j + 1 ≤ c i l + c l j)
    (hc1 : c' i j = c i j + 1) (hc2 : ∀ a b, ¬ (a = i ∧ b = j) → c' a b = c a b)
    (G : Subgroup (GL (Fin N) k)) (hG : (G : Set (GL (Fin N) k)) = Kset ϖ c) :
    ∃ G' : Subgroup (GL (Fin N) k), (G' : Set (GL (Fin N) k)) = Kset ϖ c' ∧ G' ≤ G ∧
      G'.relIndex G = Nat.card (IsLocalRing.ResidueField (valuation k).integer) := by
  have hmem : ∀ g : G, (g : GL (Fin N) k) ∈ Kset ϖ c := fun g => by
    rw [← hG]; exact g.2
  let φ : G →* Multiplicative (IsLocalRing.ResidueField (valuation k).integer) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd
      (red ϖ (c i j) (((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j))) (by
      intro g h
      obtain ⟨e, he, hgh⟩ := entry_mul h1 hij hc (hmem g) (hmem h)
      have hg := entry_le (hmem g) hij
      have hh := entry_le (hmem h) hij
      have he' : valuation k e ≤ valuation k (ϖ ^ c i j) := he.trans (pow_le_of_le h1 (by omega))
      rw [← ofAdd_add]
      congr 1
      rw [Subgroup.coe_mul, hgh, red_add h0 (val_add_le hg hh) he', red_add h0 hg hh,
        (red_eq_zero_iff h0 h1 hu he').2 he, add_zero])
  have hφ : ∀ g : G, φ g = 1 ↔ valuation k (((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j)
      ≤ valuation k (ϖ ^ (c i j + 1)) := fun g => by
    rw [← red_eq_zero_iff h0 h1 hu (entry_le (hmem g) hij)]
    exact ofAdd_eq_one
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨x, hx, hr⟩ := red_surj h0 (c i j) (Multiplicative.toAdd r)
    have hdet : (Matrix.transvection i j x).det ≠ 0 := by
      rw [Matrix.det_transvection_of_ne i j hij x]; exact one_ne_zero
    let t : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
    have ht : t ∈ Kset ϖ c := by
      intro a b
      have : (t : Matrix (Fin N) (Fin N) k) a b - (1 : Matrix (Fin N) (Fin N) k) a b
          = Matrix.single i j x a b := by
        show (Matrix.transvection i j x) a b - _ = _
        simp [Matrix.transvection]
      rw [this]
      by_cases hab : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hab
        simpa using hx
      · have : Matrix.single i j x a b = 0 := by
          rw [Matrix.single_apply, if_neg]
          tauto
        simp [this]
    refine ⟨⟨t, by rw [← SetLike.mem_coe, hG]; exact ht⟩, ?_⟩
    have : (t : Matrix (Fin N) (Fin N) k) i j = x := by
      show (Matrix.transvection i j x) i j = x
      simp [Matrix.transvection, Matrix.one_apply_ne hij]
    show Multiplicative.ofAdd (red ϖ (c i j) ((t : Matrix (Fin N) (Fin N) k) i j)) = r
    rw [this, hr]
    rfl
  refine ⟨φ.ker.map G.subtype, ?_, ?_, ?_⟩
  · ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      intro a b
      have hk := (hφ g').1 hg'
      by_cases hab : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hab
        rw [hc1]
        simpa [Matrix.one_apply_ne hij] using hk
      · rw [hc2 a b hab]
        exact hmem g' a b
    · intro hg
      have hgc : g ∈ Kset ϖ c := by
        refine Kset_mono h1 (fun a b => ?_) hg
        by_cases hab : a = i ∧ b = j
        · obtain ⟨rfl, rfl⟩ := hab
          omega
        · rw [hc2 a b hab]
      have hgG : g ∈ G := by rw [← SetLike.mem_coe, hG]; exact hgc
      refine ⟨⟨g, hgG⟩, ?_, rfl⟩
      apply (hφ _).2
      have := hg i j
      rw [hc1] at this
      simpa [Matrix.one_apply_ne hij] using this
  · rintro _ ⟨g', _, rfl⟩
    exact g'.2
  · have hsub : (φ.ker.map G.subtype).subgroupOf G = φ.ker := by
      ext g
      simp [Subgroup.mem_subgroupOf]
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj]
    simp only [Subgroup.card_top]
    exact Nat.card_congr Multiplicative.toAdd
end GlobalTheory.CompanionTheory.CongIndex
