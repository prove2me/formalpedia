-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.card_quot_lev_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:55.741617+00:00
-- url     : https://prove2.me/submissions/bd0cb3b9-8801-4a7d-8ce9-963e9102934c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.UnrDens
private theorem mulPow_apply {R : Type} [CommRing R] (ϖ : R) (k : ℕ) (a : R) :
    mulPow ϖ k a = Ideal.Quotient.mk (lev ϖ (k + 1)) (ϖ ^ k * a) := rfl
private theorem lev_succ_le {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k := by
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ k))
private theorem mulPow_ker {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    (mulPow ϖ k).ker = (lev ϖ 1).toAddSubgroup := by
  ext a
  rw [AddMonoidHom.mem_ker, mulPow_apply, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_toAddSubgroup]
  simp only [lev, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hinj : Function.Injective (fun y : R => ϖ ^ k • y) := hr.pow k
    apply hinj
    show ϖ ^ k • a = ϖ ^ k • (ϖ ^ 1 * c)
    rw [smul_eq_mul, smul_eq_mul, hc]
    ring
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩
end GlobalTheory.CompanionTheory.UnrDens
end

set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    Nat.card (R ⧸ lev ϖ (k + 1)) = Nat.card (R ⧸ lev ϖ 1) * Nat.card (R ⧸ lev ϖ k) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⧸ lev ϖ (k + 1) →+ R ⧸ lev ϖ k,
      ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
    ⟨(Ideal.Quotient.lift (lev ϖ (k + 1)) (Ideal.Quotient.mk (lev ϖ k))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (lev_succ_le ϖ k ha))).toAddMonoidHom,
      fun a => by simp⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, hφ a⟩
  have hker : φ.ker = (mulPow ϖ k).range := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AddMonoidHom.mem_ker, hφ, AddMonoidHom.mem_range, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨c, by rw [mulPow_apply, ← hc]⟩
    · rintro ⟨c, hc⟩
      rw [mulPow_apply, Ideal.Quotient.eq] at hc
      have h1 : ϖ ^ k * c - a ∈ lev ϖ k := lev_succ_le ϖ k hc
      have h2 : ϖ ^ k * c ∈ lev ϖ k := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have := sub_mem h2 h1
      simpa using this
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have e2 : Nat.card ((R ⧸ lev ϖ (k + 1)) ⧸ φ.ker) = Nat.card (R ⧸ lev ϖ k) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have e3 : Nat.card φ.ker = Nat.card (R ⧸ lev ϖ 1) := by
    rw [hker]
    have := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulPow ϖ k)).toEquiv
    rw [← this, mulPow_ker hr]
    rfl
  rw [e1, e2, e3]
  ring
end GlobalTheory.CompanionTheory.UnrDens
