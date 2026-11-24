-- Prove2me | solution 1 for GlobalTheory.LevelExist.exists_stdSymp_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:59:25.518372+00:00
-- url     : https://prove2.me/submissions/854e33de-ad78-4e20-befd-43d595e38db6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsIsSymplecticFamilySpan
import Theorems.Thm_GlobalTheory_LevelExist_exists_isSymplecticFamily_span
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_apply_left_sum
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_apply_sum_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.LevelExist
open ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.LevelExist
theorem _root_.solution {p j g : ℕ} (hp : p.Prime) {V : Type*} [AddCommGroup V] [Module (ZMod (p ^ (j + 1))) V]
    (h₀ : Nat.card V = (p ^ (j + 1)) ^ (2 * g)) (h₁ : Nat.card {x : V // p ^ j • x = 0} = (p ^ j) ^ (2 * g))
    (h₂ : Nat.card {x : V // p • x = 0} = p ^ (2 * g))
    {B : LinearMap.BilinForm (ZMod (p ^ (j + 1))) V} (hB : B.IsAlt) (hN : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ v : Fin (2 * g) → V, (∀ i k, B (v i) (v k) = (stdSymp g i k : ℤ)) ∧
      LinearIndependent (ZMod (p ^ (j + 1))) v := by
  have hp0 := hp.pos
  have : NeZero (p ^ (j + 1)) := ⟨by positivity⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h₀]; positivity)
  have hdiv : ∀ x : V, p • x = 0 → ∃ y, p ^ j • y = x := by
    let φ : V →+ V := nsmulAddMonoidHom (p ^ j)
    let ψ : V →+ V := nsmulAddMonoidHom p
    have hle : φ.range ≤ ψ.ker := by
      rintro _ ⟨y, rfl⟩
      show p • p ^ j • y = 0
      rw [smul_smul, ← pow_succ', ← Nat.cast_smul_eq_nsmul (ZMod (p ^ (j + 1))), ZMod.natCast_self, zero_smul]
    have hc : Nat.card φ.range = Nat.card ψ.ker := by
      have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, h₀,
        show Nat.card φ.ker = _ from h₁, pow_succ', mul_pow] at h
      exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm.trans h₂.symm
    have := AddSubgroup.eq_of_le_of_card_ge hle hc.ge
    intro x hx
    exact (this ▸ hx : x ∈ φ.range)
  obtain ⟨g', e, f, hs, hspan⟩ := exists_isSymplecticFamily_span hB ((p ^ j : ℕ) : ZMod (p ^ (j + 1))) (by
    intro r hr
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective r
    refine (ZMod.isUnit_natCast_iff_not_dvd_pow hp j.succ_pos).2 ?_
    rintro ⟨c, rfl⟩
    apply hr
    rw [← Nat.cast_mul, ← mul_assoc, ← pow_succ, Nat.cast_mul, ZMod.natCast_self, zero_mul]) ⊤
    (fun x _ h => hN x fun y => h y trivial) (by
    intro x _ hx
    have hex : ∃ m, p ^ m • x = 0 := ⟨j + 1, by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ (j + 1))), ZMod.natCast_self, zero_smul]⟩
    classical
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (n := Nat.find hex) (by simpa using hx)
    have a₁ : p ^ (m + 1) • x = 0 := by have := Nat.find_spec hex; rwa [hm] at this
    have a₂ : p ^ m • x ≠ 0 := Nat.find_min hex (by omega)
    obtain ⟨y, hy⟩ := hdiv (p ^ m • x) (by rw [smul_smul, ← pow_succ', a₁])
    exact ⟨(p ^ m : ℕ), y, trivial, by simp only [Nat.cast_smul_eq_nsmul, hy], by
      rwa [Nat.cast_smul_eq_nsmul, hy]⟩)
  have hli : LinearIndependent (ZMod (p ^ (j + 1))) (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc (k | k)
    · simpa [hc] using (hs.apply_sum_right c k).symm
    · simpa [hc] using (hs.apply_left_sum c k).symm
  obtain rfl : g' = g := by
    have h := Nat.card_congr (Module.Basis.mk hli hspan.ge).equivFun.toEquiv
    rw [h₀, Nat.card_fun, Nat.card_zmod] at h
    have := Nat.pow_right_injective (Nat.one_lt_pow j.succ_ne_zero hp.one_lt) h
    simp at this
    omega
  let σ : Fin (2 * g') ≃ Fin g' ⊕ Fin g' := (finCongr (two_mul g')).trans finSumFinEquiv.symm
  refine ⟨Sum.elim e f ∘ σ, fun i k => ?_, hli.comp σ σ.injective⟩
  obtain ⟨a, rfl⟩ := σ.symm.surjective i
  obtain ⟨b, rfl⟩ := σ.symm.surjective k
  simp only [Function.comp, Equiv.apply_symm_apply, stdSymp]
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g' + a := fun _ => rfl
  rcases a with a | a <;> rcases b with b | b <;> have := a.2 <;> have := b.2 <;>
    simp only [l, r, Sum.elim_inl, Sum.elim_inr, hs.left_left, hs.right_right, hs.left_right, hs.right_left hB,
      Fin.ext_iff] <;> split_ifs <;> first | omega | simp
end GlobalTheory.LevelExist
