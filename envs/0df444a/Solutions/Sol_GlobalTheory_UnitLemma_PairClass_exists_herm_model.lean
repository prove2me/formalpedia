-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PairClass.exists_herm_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:12.511489+00:00
-- url     : https://prove2.me/submissions/5446460c-c6c5-40b5-b5d9-5fa706edc747

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_aeval_eq_of_separable
import Theorems.Thm_GlobalTheory_UnitLemma_PairClass_trace_nondeg
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_PairClass_trace___35abbd75f5d9
import Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_intertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass
namespace GlobalTheory.UnitLemma.PairClass
theorem _root_.solution : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E), (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) → (∀ x y, h y x = K.c (h x y)) → (∀ y, (∀ z, h y z = 0) → y = 0) → ∀ (B : InvAlg K) (g : V →ₗ[K.E] V), B.P.Separable → g.charpoly = B.P → ((B.g * B.σ B.g = 1 ∧ ∀ y z, h (g y) (g z) = h y z) ∨ (B.σ B.g = B.g ∧ ∀ y z, h (g y) z = h y (g z))) → ∃ (x : B.Aˣ) (e : B.A ≃ₗ[K.E] V), B.σ (x : B.A) = x ∧ (∀ y, e (B.g * y) = g (e y)) ∧ ∀ y z, h (e y) (e z) = B.herm x y z := by
  intro K V _ _ _ _ _ h hadd hsm hherm hnd B g hsep hchar hcase
  have hsep' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hsep
  obtain ⟨e, he⟩ := exists_intertwine K.E B.A V (LinearMap.mulLeft K.E B.g) g hsep hchar.symm
  have he' : ∀ y, e (B.g * y) = g (e y) := fun y => he y
  have hadd2 : ∀ x y z, h x (y + z) = h x y + h x z := by
    intro x y z
    rw [hherm (y + z) x, hadd, map_add, ← hherm y x, ← hherm z x]
  have hsm2 : ∀ (c : K.E) x z, h x (c • z) = K.c c * h x z := by
    intro c x z
    rw [hherm (c • z) x, hsm, map_mul, ← hherm z x]
  let S : B.A → Prop := fun a => ∀ y z, h (e (a * y)) (e z) = h (e y) (e (B.σ a * z))
  have Salg : ∀ c : K.E, S (algebraMap K.E B.A c) := by
    intro c y z
    rw [B.σ_alg, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, hsm, hsm2, K.c_c]
  have Sg : S B.g := by
    intro y z
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hz : z = B.g * (B.σ B.g * z) := by rw [← mul_assoc, h1, one_mul]
      conv_lhs => rw [hz]
      rw [he', he', h2]
    · rw [h1, he', he', h2]
  have Sadd : ∀ a b, S a → S b → S (a + b) := by
    intro a b ha hb y z
    rw [add_mul, map_add, hadd, ha, hb, map_add, add_mul, map_add, hadd2]
  have Smul : ∀ a b, S a → S b → S (a * b) := by
    intro a b ha hb y z
    rw [mul_assoc, ha, hb, show B.σ b * (B.σ a * z) = B.σ (a * b) * z by rw [map_mul B.σ]; ring]
  have Spoly : ∀ q : K.E[X], S (aeval B.g q) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => rw [aeval_C]; exact Salg c
    | add p q hp hq => rw [map_add]; exact Sadd _ _ hp hq
    | monomial n c ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]; exact Smul _ _ ih Sg
  have Sall : ∀ a, S a := by
    intro a
    obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable B.g hsep' a
    exact Spoly q

  let φ : Module.Dual K.E B.A :=
    { toFun := fun y => h (e y) (e 1)
      map_add' := fun y z => by rw [map_add, hadd]
      map_smul' := fun c y => by rw [map_smul, hsm]; rfl }
  have hinj : Function.Injective (Algebra.traceForm K.E B.A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact trace_nondeg K.E B.A B.g hsep' x fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this
  have hsurj : Function.Surjective (Algebra.traceForm K.E B.A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨x, hx⟩ := hsurj φ
  have hxy : ∀ y, Algebra.trace K.E B.A (x * y) = h (e y) (e 1) := fun y => by
    rw [← Algebra.traceForm_apply, hx]; rfl
  have hrep : ∀ y z, h (e y) (e z) = Algebra.trace K.E B.A (x * y * B.σ z) := by
    intro y z
    have := Sall (B.σ z) y 1
    rw [B.σ_σ, mul_one] at this
    rw [← this, ← hxy]
    congr 1
    ring
  have hfix : B.σ x = x := by
    have h0 := trace_nondeg K.E B.A B.g hsep' (B.σ x - x) fun y => by
      have h1 : Algebra.trace K.E B.A (B.σ x * y) = K.c (Algebra.trace K.E B.A (x * B.σ y)) := by
        rw [← trace_σ, map_mul B.σ x (B.σ y), B.σ_σ]
      have h2 : Algebra.trace K.E B.A (x * B.σ y) = h (e 1) (e y) := by
        rw [hrep]; ring_nf
      rw [sub_mul, map_sub, h1, h2, hherm (e y) (e 1), K.c_c, hxy, sub_self]
    exact sub_eq_zero.1 h0
  have hunit : IsUnit x := by
    have hi : Function.Injective (LinearMap.mulLeft K.E x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have hy' : x * y = 0 := hy
      apply e.injective
      rw [map_zero]
      apply hnd
      intro v
      rw [← e.apply_symm_apply v, hrep, hy', zero_mul, map_zero]
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hi) 1
    exact IsUnit.of_mul_eq_one y hy
  exact ⟨hunit.unit, e, hfix, he', fun y z => hrep y z⟩
end GlobalTheory.UnitLemma.PairClass
