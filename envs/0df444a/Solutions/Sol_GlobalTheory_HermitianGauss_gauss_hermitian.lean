-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.gauss_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:06.936443+00:00
-- url     : https://prove2.me/submissions/7d3933d8-3640-4dd0-896a-caad6c2e3393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
import Theorems.Thm_GlobalTheory_HermitianGauss_gauss_fin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
namespace GlobalTheory.HermitianGauss
theorem _root_.solution : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  intro R X _ _ _ σ w hσ hw lam hlam β hadd hsym hadj B C hCB hrad n t htB huniq
  have hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1 := fun c hc y hy => (hrad c (hCB hc)).mp hc y hy
  let C' : Submodule R B := C.comap B.subtype
  have hC' : ∀ a : B, a ∈ C' ↔ (a : X) ∈ C := fun a => Iff.rfl
  let e : Fin n → B ⧸ C' := fun k => Submodule.Quotient.mk ⟨t k, htB k⟩
  have he : Function.Bijective e := by
    constructor
    · intro k l hkl
      have hkl' : (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk ⟨t l, htB l⟩ := hkl
      have h1 : t k - t l ∈ C := by
        have h2 := (Submodule.Quotient.eq C').mp hkl'
        rw [hC'] at h2
        simpa using h2
      obtain ⟨k', _, hk'⟩ := huniq (t k) (htB k)
      exact (hk' k (by show t k - t k ∈ C; rw [sub_self]; exact C.zero_mem)).trans (hk' l h1).symm
    · intro u
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective C' u
      obtain ⟨k, hk, -⟩ := huniq y y.2
      refine ⟨k, ?_⟩
      show (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk y
      rw [Submodule.Quotient.eq, hC', Submodule.coe_sub]
      have h2 : t k - (y : X) = -((y : X) - t k) := by abel
      show t k - (y : X) ∈ C
      rw [h2]
      exact C.neg_mem hk
  haveI : Finite (B ⧸ C') := Finite.of_surjective e he.2
  letI : Fintype (B ⧸ C') := Fintype.ofFinite _
  have hout : ∀ u : B ⧸ C', Submodule.Quotient.mk (Quotient.out u) = u := fun u => Quotient.out_eq u
  have hdesc : ∀ a ∈ B, ∀ a' ∈ B, a - a' ∈ C → ∀ b ∈ B, β a b = β a' b := by
    intro a _ a' _ h b hb
    calc β a b = β (a' + (a - a')) b := by congr 1; abel
      _ = β a' b := by rw [hadd, hC1 _ h b hb, mul_one]
  let β' : B ⧸ C' → B ⧸ C' → ℂ := fun u v => β (Quotient.out u : B) (Quotient.out v : B)
  have hrep : ∀ a : B, ((Quotient.out (Submodule.Quotient.mk a : B ⧸ C') : B) : X) - a ∈ C := by
    intro a
    have h1 := (Submodule.Quotient.eq C').mp (hout (Submodule.Quotient.mk a))
    rw [hC'] at h1
    simpa using h1
  have hβ' : ∀ a b : B, β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = β a b := by
    intro a b
    calc β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
        = β a (Quotient.out (Submodule.Quotient.mk b : B ⧸ C') : B) :=
          hdesc _ (Quotient.out (Submodule.Quotient.mk a : B ⧸ C')).2 _ a.2 (hrep a) _
            (Quotient.out (Submodule.Quotient.mk b : B ⧸ C')).2
      _ = β (Quotient.out (Submodule.Quotient.mk b : B ⧸ C') : B) a := hsym _ _
      _ = β b a := hdesc _ (Quotient.out (Submodule.Quotient.mk b : B ⧸ C')).2 _ b.2 (hrep b) _ a.2
      _ = β a b := hsym _ _
  have hadd' : ∀ u v z : B ⧸ C', β' (u + v) z = β' u z * β' v z := by
    intro u v z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective C' z
    rw [← Submodule.Quotient.mk_add, hβ', hβ', hβ', Submodule.coe_add, hadd]
  have hsym' : ∀ u v : B ⧸ C', β' u v = β' v u := by
    intro u v
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [hβ', hβ', hsym]
  have hadj' : ∀ (r : R) (u v : B ⧸ C'), β' (r • u) v = β' u (σ r • v) := by
    intro r u v
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hβ', hβ', Submodule.coe_smul,
      Submodule.coe_smul, hadj]
  have h0' : ∀ v : B ⧸ C', β' 0 v = 1 := by
    intro v
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [← Submodule.Quotient.mk_zero C', hβ', Submodule.coe_zero]
    exact hC1 0 C.zero_mem b b.2
  have hrad' : ∀ u ∈ (⊤ : Submodule R (B ⧸ C')), u ∈ (⊥ : Submodule R (B ⧸ C')) ↔
      ∀ v ∈ (⊤ : Submodule R (B ⧸ C')), β' u v = 1 := by
    intro u _
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, hC', hrad a a.2]
    constructor
    · intro h v _
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
      rw [hβ']
      exact h b b.2
    · intro h y hy
      have h1 := h (Submodule.Quotient.mk ⟨y, hy⟩) Submodule.mem_top
      rwa [hβ'] at h1
  have hpt : pts (⊤ : Submodule R (B ⧸ C')) = Finset.univ := by
    ext
    simp [pts]
  have hpb : pts (⊥ : Submodule R (B ⧸ C')) = {0} := by
    ext
    simp [pts]
  have hcard : (pts (⊤ : Submodule R (B ⧸ C'))).card = n * (pts (⊥ : Submodule R (B ⧸ C'))).card := by
    rw [hpt, hpb, Finset.card_singleton, mul_one, Finset.card_univ, ← Fintype.card_of_bijective he,
      Fintype.card_fin]
  obtain ⟨hs, hl⟩ := gauss_fin (w := w) hσ hw hlam hadd' hsym' hadj' h0' n ⊤ ⊥ bot_le hrad' hcard
  refine ⟨?_, hl⟩
  rw [hpt, hpb, Finset.card_singleton] at hs
  have h1 : ∑ k, β (w • t k) (t k) = ∑ u : B ⧸ C', β' (w • u) u := by
    calc ∑ k, β (w • t k) (t k) = ∑ k, β' (w • e k) (e k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          show β (w • t k) (t k) = β' (w • Submodule.Quotient.mk ⟨t k, htB k⟩) (Submodule.Quotient.mk ⟨t k, htB k⟩)
          rw [← Submodule.Quotient.mk_smul, hβ']
          rfl
      _ = ∑ u : B ⧸ C', β' (w • u) u := he.sum_comp (fun u => β' (w • u) u)
  rw [h1, hs]
  simp
end GlobalTheory.HermitianGauss
