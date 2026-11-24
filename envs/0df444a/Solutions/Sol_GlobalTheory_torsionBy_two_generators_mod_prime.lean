-- Prove2me | solution 1 for GlobalTheory.torsionBy_two_generators_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:46.179308+00:00
-- url     : https://prove2.me/submissions/b226b3e1-1a16-4976-b38d-24a930d38f2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsModPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open scoped Pointwise
namespace GlobalTheory
theorem _root_.solution :
  ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 →
    ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
      x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) := by
  intro F _ _ M _ _ N hN hfin 𝔭 h𝔭 hN𝔭 hcard
  set T := Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) with hT
  have memT : ∀ x : M, x ∈ T ↔ N • x = 0 := by
    intro x; rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  haveI : Finite T := by
    refine Finite.of_injective (fun y : T => (⟨y.1, (memT y.1).1 y.2⟩ : {x : M // N • x = 0})) ?_
    intro y z h
    have h' := congrArg (fun w : {x : M // N • x = 0} => w.1) h
    exact Subtype.ext h'
  have hNR : (N : 𝓞 F) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hspan0 : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hNR
  have h𝔭0 : 𝔭 ≠ ⊥ := fun h => hNR (by simpa [h] using hN𝔭)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    ((Ideal.span_singleton_le_iff_mem _).2 hN𝔭) hspan0
  let φ : T →ₗ[𝓞 F] T := a • LinearMap.id
  have hNT : ∀ y : T, (N : 𝓞 F) • y = 0 := fun y => Subtype.ext ((Submodule.mem_torsionBy_iff _ _).1 y.2)
  have hsmul : 𝔭 • (⊤ : Submodule (𝓞 F) T) = LinearMap.range φ := by
    rw [← ha, Submodule.sup_smul, Submodule.ideal_span_singleton_smul,
      Submodule.ideal_span_singleton_smul]
    ext y
    simp only [Submodule.mem_sup, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      true_and, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, by simp [φ, hNT]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨0, ⟨0, by simp⟩, _, ⟨w, rfl⟩, by simp [φ]⟩

  let P := {x : M // ∀ b ∈ 𝔭, b • x = 0}
  haveI : Finite P := by
    refine Finite.of_injective (fun y : P => (⟨y.1, by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 F)]; exact y.2 _ hN𝔭⟩ : {x : M // N • x = 0})) ?_
    intro y z h
    have h' := congrArg (fun w : {x : M // N • x = 0} => w.1) h
    exact Subtype.ext h'
  have hker : Nat.card (LinearMap.ker φ) ≤ Nat.card P := by
    refine Nat.card_le_card_of_injective (fun y : LinearMap.ker φ => (⟨y.1.1, by
      intro b hb
      rw [← ha] at hb
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Submodule.mem_sup.1 hb
      obtain ⟨c1, rfl⟩ := Ideal.mem_span_singleton'.1 hb1
      obtain ⟨c2, rfl⟩ := Ideal.mem_span_singleton'.1 hb2
      have e1 : (N : 𝓞 F) • y.1.1 = 0 := congrArg Subtype.val (hNT y.1)
      have e2 : a • y.1.1 = 0 := by
        have := y.2
        rw [LinearMap.mem_ker] at this
        exact congrArg Subtype.val this
      rw [add_smul, mul_smul, mul_smul, e1, e2, smul_zero, smul_zero, add_zero]⟩ : P)) ?_
    intro y z h
    have h' := congrArg (fun w : P => w.1) h
    exact Subtype.ext (Subtype.ext h')
  have hQ : Nat.card (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) = Nat.card (LinearMap.ker φ) := by
    rw [hsmul]
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range φ)
    have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
    have h3 : Nat.card (T ⧸ LinearMap.ker φ) = Nat.card (LinearMap.range φ) :=
      Nat.card_congr φ.quotKerEquivRange.toEquiv
    have h4 : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
    rw [h3] at h2
    rw [h1, mul_comm (Nat.card (LinearMap.range φ))] at h2
    exact Nat.eq_of_mul_eq_mul_right h4 h2

  haveI : Finite (𝓞 F ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 h𝔭0
  letI : Field (𝓞 F ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  haveI : Finite (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI : Module.Finite (𝓞 F ⧸ 𝔭) (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) := Module.Finite.of_finite
  have hk : 1 < Nat.card (𝓞 F ⧸ 𝔭) := Finite.one_lt_card
  have hnorm : Ideal.absNorm 𝔭 = Nat.card (𝓞 F ⧸ 𝔭) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hdim : Module.finrank (𝓞 F ⧸ 𝔭) (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) ≤ 2 := by
    have h5 := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ 𝔭) (V := T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T))
    have h6 : Nat.card (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) ≤ Nat.card (𝓞 F ⧸ 𝔭) ^ 2 := by
      rw [hQ, ← hnorm]; exact hker.trans hcard
    rw [h5] at h6
    exact (Nat.pow_le_pow_iff_right hk).1 h6

  set Q := T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T) with hQdef
  set r := Module.finrank (𝓞 F ⧸ 𝔭) Q with hr
  let bs := Module.finBasis (𝓞 F ⧸ 𝔭) Q
  let u' : Q := if h : 0 < r then bs ⟨0, h⟩ else 0
  let v' : Q := if h : 1 < r then bs ⟨1, h⟩ else 0
  have hspan : ∀ q : Q, ∃ c d : 𝓞 F ⧸ 𝔭, c • u' + d • v' = q := by
    intro q
    have hle : Set.range bs ⊆ ({u', v'} : Set Q) := by
      rintro _ ⟨i, rfl⟩
      have hi : i.val = 0 ∨ i.val = 1 := by have := i.2; omega
      rcases hi with hi | hi
      · left
        have h0 : 0 < r := by have := i.2; omega
        simp only [u', dif_pos h0]
        congr 1; exact Fin.ext hi
      · right
        have h1 : 1 < r := by have := i.2; omega
        simp only [v', dif_pos h1]
        simp only [Set.mem_singleton_iff]
        congr 1; exact Fin.ext hi
    have hq : q ∈ Submodule.span (𝓞 F ⧸ 𝔭) (Set.range bs) := by
      rw [bs.span_eq]; exact Submodule.mem_top
    have hq2 := Submodule.span_mono hle hq
    exact Submodule.mem_span_pair.1 hq2
  obtain ⟨u0, hu0⟩ := Submodule.Quotient.mk_surjective _ u'
  obtain ⟨v0, hv0⟩ := Submodule.Quotient.mk_surjective _ v'
  refine ⟨u0.1, v0.1, (memT _).1 u0.2, (memT _).1 v0.2, ?_⟩
  intro x hx
  let y : T := ⟨x, (memT x).2 hx⟩
  obtain ⟨c, d, hcd⟩ := hspan (Submodule.Quotient.mk y)
  obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨d0, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨c0, d0, ?_⟩
  rw [← hu0, ← hv0, Module.Quotient.mk_smul_mk, Module.Quotient.mk_smul_mk,
    ← Submodule.Quotient.mk_add, eq_comm, Submodule.Quotient.eq] at hcd
  have hmap := Submodule.mem_map_of_mem (f := T.subtype) hcd
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmap
  convert hmap using 1
  simp [y, sub_sub]
end GlobalTheory
