-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.idealCount_prime_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:28:27.511806+00:00
-- url     : https://prove2.me/submissions/518d44fd-5e7d-44aa-b640-cd803a6dbe04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_ringHom
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis
import Theorems.Thm_GlobalTheory_QuadraticZeta_roots_cases
import Theorems.Thm_GlobalTheory_QuadraticZeta_ncard_dvd
import Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_ker
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_span_of_no_root
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_ker_or

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (idealCount K (p * m) : ℤ) = (1 + kroneckerAt (discr K) p) * idealCount K m
      - kroneckerAt (discr K) p * if p ∣ m then (idealCount K (m / p) : ℤ) else 0 := by
  obtain ⟨b, t, n, h0, hw, hD⟩ := exists_basis h2
  haveI := Fact.mk hp
  have hex : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = p * m →
      ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.under ℤ = .span {(p : ℤ)} ∧ P ∣ I := fun I hI =>
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I (hI ▸ dvd_mul_right _ _)
  have hsq : ∀ J : Ideal (𝓞 K), Ideal.absNorm J = p * p →
      {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ J ∣ I}.ncard
        = if p ∣ m then idealCount K (m / p) else 0 := fun J hJ => by
    rw [ncard_dvd (by rw [Ne, ← Ideal.absNorm_eq_zero_iff, hJ]; simp [hp.ne_zero]), hJ,
      Nat.mul_div_mul_left _ _ hp.pos]
    simp only [Nat.mul_dvd_mul_iff_left hp.pos]
  have hone : ∀ J : Ideal (𝓞 K), Ideal.absNorm J = p →
      {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ J ∣ I}.ncard = idealCount K m := fun J hJ => by
    rw [ncard_dvd (by rw [Ne, ← Ideal.absNorm_eq_zero_iff, hJ]; simp [hp.ne_zero]), hJ,
      Nat.mul_div_cancel_left _ hp.pos, if_pos (dvd_mul_right _ _)]
  rw [hD]
  rcases roots_cases t n hp with ⟨hκ, h⟩ | ⟨β, β', hs, hm, h⟩
  · have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p * p := by
      rw [Ideal.absNorm_span_singleton, show (p : 𝓞 K) = algebraMap ℤ _ p by simp,
        Algebra.norm_algebraMap_of_basis b]
      simp [sq, Int.natAbs_mul]
    have := hsq _ hN
    rw [hκ, idealCount, show {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m}
      = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ Ideal.span {(p : 𝓞 K)} ∣ I} from
      Set.ext fun I => (and_iff_left_of_imp fun hI => by
        obtain ⟨P, h1, h2, h3⟩ := hex I hI
        exact eq_span_of_no_root b h0 hw hp h1 h2 h ▸ h3).symm, this]
    split_ifs <;> simp
  · obtain ⟨φ, hφ⟩ := exists_ringHom b h0 hw (β := β) (by rw [← hs, ← hm]; ring)
    obtain ⟨φ', hφ'⟩ := exists_ringHom b h0 hw (β := β') (by rw [← hs, ← hm]; ring)
    rcases h with ⟨hκ, rfl⟩ | ⟨hκ, hne⟩
    · rw [hκ, idealCount, show {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m}
        = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I} from
        Set.ext fun I => (and_iff_left_of_imp fun hI => by
          obtain ⟨P, h1, h2, h3⟩ := hex I hI
          exact (or_self_iff.1 (eq_ker_or b h0 hw hp h1 h2 φ φ (by rw [hφ, hs])
            (by rw [hφ, hm]))) ▸ h3).symm, hone _ (absNorm_ker φ)]
      simp
    · have hmax := RingHom.ker_isMaximal_of_surjective φ (ZMod.ringHom_surjective φ)
      have hmax' := RingHom.ker_isMaximal_of_surjective φ' (ZMod.ringHom_surjective φ')
      have hk : RingHom.ker φ ≠ RingHom.ker φ' := fun e => by
        obtain ⟨c, hc⟩ := ZMod.intCast_surjective β
        have : b 1 - c ∈ RingHom.ker φ := by simp [RingHom.mem_ker, hφ, hc]
        rw [e] at this
        exact hne (by simpa [RingHom.mem_ker, hφ', hc, sub_eq_zero, eq_comm] using this)
      have hcop : IsCoprime (RingHom.ker φ) (RingHom.ker φ') :=
        Ideal.isCoprime_iff_sup_eq.2 (hmax.coprime_of_ne hmax' hk)
      have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) (p * m)
      have hu := Set.ncard_union_add_ncard_inter
        {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I}
        {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ' ∣ I}
        (hfin.subset fun _ h => h.1) (hfin.subset fun _ h => h.1)
      have e1 : {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I} ∪
          {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ' ∣ I}
          = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m} := by
        ext I
        refine ⟨fun h => h.elim And.left And.left, fun hI => ?_⟩
        obtain ⟨P, h1, h2, h3⟩ := hex I hI
        rcases eq_ker_or b h0 hw hp h1 h2 φ φ' (by rw [hφ, hφ', hs]) (by rw [hφ, hφ', hm])
          with rfl | rfl
        exacts [Or.inl ⟨hI, h3⟩, Or.inr ⟨hI, h3⟩]
      have e2 : {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I} ∩
          {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ' ∣ I}
          = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ * RingHom.ker φ' ∣ I} := by
        ext I
        exact ⟨fun h => ⟨h.1.1, hcop.mul_dvd h.1.2 h.2.2⟩, fun h =>
          ⟨⟨h.1, (dvd_mul_right _ _).trans h.2⟩, h.1, (dvd_mul_left _ _).trans h.2⟩⟩
      rw [e1, e2, hone _ (absNorm_ker φ), hone _ (absNorm_ker φ'),
        hsq _ (by rw [map_mul, absNorm_ker, absNorm_ker])] at hu
      rw [hκ, idealCount]
      have hu' := congrArg (Nat.cast : ℕ → ℤ) hu
      push_cast at hu'
      linarith
end GlobalTheory.QuadraticZeta
