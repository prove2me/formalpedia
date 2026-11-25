-- Prove2me | solution 1 for GlobalTheory.DenseSec.hensel_etChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:39.49363+00:00
-- url     : https://prove2.me/submissions/7fd4c07e-8beb-42b2-a6d4-542e9e6ddfaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionLiftingResidueValues
import Theorems.Thm_P2M_GlobalTheory_DenseSec_factor__comp_factor__7e1aebb4d17b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DenseSec
namespace GlobalTheory.DenseSec
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R →
    ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h →
    ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) →
    ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  intro R _ _ hc A _ _ g t h hE ε hε c hcε
  classical
  haveI := hc
  letI iPB : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI iPR : Algebra (MvPolynomial (Fin g) R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  have hPB : ∀ p, algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p =
      algebraMap A (Localization.Away h) (MvPolynomial.aeval t p) := fun _ => rfl
  have hPR : ∀ p, algebraMap (MvPolynomial (Fin g) R) R p = MvPolynomial.aeval c p := fun _ => rfl
  let m := maximalIdeal R

  let e' : Localization.Away h →+* R := IsLocalization.Away.lift h (g := (ε : A →+* R)) hε
  have he' : ∀ x : A, e' (algebraMap A (Localization.Away h) x) = ε x := fun x =>
    IsLocalization.Away.lift_eq h (g := (ε : A →+* R)) hε x
  have hmod : (Ideal.Quotient.mk m).comp ((ε : A →+* R).comp (MvPolynomial.aeval (R := R) t).toRingHom) =
      (Ideal.Quotient.mk m).comp (MvPolynomial.aeval c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact (Ideal.Quotient.eq.2 (by
        have := hcε i
        rw [← neg_mem_iff, neg_sub] at this
        exact this))
  let f₁ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m :=
    { toRingHom := (Ideal.Quotient.mk m).comp e'
      commutes' := fun p => by
        show Ideal.Quotient.mk m (e' (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p)) =
          algebraMap (MvPolynomial (Fin g) R) (R ⧸ m) p
        rw [hPB, he']
        show Ideal.Quotient.mk m (ε (MvPolynomial.aeval t p)) = Ideal.Quotient.mk m (MvPolynomial.aeval c p)
        exact congrArg (fun φ : MvPolynomial (Fin g) R →+* R ⧸ m => φ p) hmod }

  have hle : ∀ n : ℕ, m ^ (n + 1) ≤ m := fun n => Ideal.pow_le_self n.succ_ne_zero
  let q : ∀ n : ℕ, R ⧸ m ^ (n + 1) →ₐ[MvPolynomial (Fin g) R] R ⧸ m := fun n =>
    Ideal.Quotient.factorₐ _ (hle n)
  have hqs : ∀ n, Function.Surjective (q n) := fun n x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hqn : ∀ n, IsNilpotent (RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m)) := fun n => by
    refine ⟨n + 1, le_bot_iff.1 ?_⟩
    have hk : RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m) = Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m :=
      Ideal.Quotient.factor_ker (hle n)
    rw [hk, ← Ideal.map_pow, Ideal.map_quotient_self]
  let F : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ (n + 1) := fun n =>
    Algebra.FormallySmooth.liftOfSurjective f₁ (q n) (hqs n) (hqn n)
  have hF : ∀ n, (q n).comp (F n) = f₁ := fun n => Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hFc : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn))).comp (F n) = F k := by
    intro k n hkn
    refine Algebra.FormallyUnramified.ext' (q k : R ⧸ m ^ (k + 1) →+* R ⧸ m) (hqn k) _ _ fun x => ?_
    have h1 := congrArg (fun φ => φ x) (hF n)
    have h2 := congrArg (fun φ => φ x) (hF k)
    simp only [AlgHom.comp_apply] at h1 h2
    show (q k) ((Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1))) (F n x)) = q k (F k x)
    rw [h2, ← h1]
    have := congrArg (fun φ => φ (F n x)) (factorₐ_comp_factorₐ (P := MvPolynomial (Fin g) R)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1)) (hle k))
    simpa only [AlgHom.comp_apply] using this
  let f : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ n := fun n =>
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (F n)
  have hf : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right hkn)).comp (f n) = f k := by
    intro k n hkn
    simp only [f]
    rw [← AlgHom.comp_assoc, factorₐ_comp_factorₐ, ← hFc hkn, ← AlgHom.comp_assoc, factorₐ_comp_factorₐ]
  let Φ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R := IsAdicComplete.liftAlgHom m f hf
  let a : A →ₐ[R] R :=
    { toRingHom := (Φ : Localization.Away h →+* R).comp (algebraMap A (Localization.Away h))
      commutes' := fun r => by
        show Φ (algebraMap A (Localization.Away h) (algebraMap R A r)) = algebraMap R R r
        have : algebraMap A (Localization.Away h) (algebraMap R A r) =
            algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.C r) := by
          rw [hPB, MvPolynomial.aeval_C]
        rw [this, Φ.commutes, hPR, MvPolynomial.aeval_C] }
  refine ⟨a, ?_, fun i => ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit h).map Φ
  · show Φ (algebraMap A (Localization.Away h) (t i)) = c i
    have : algebraMap A (Localization.Away h) (t i) =
        algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.X i) := by
      rw [hPB, MvPolynomial.aeval_X]
    rw [this, Φ.commutes, hPR, MvPolynomial.aeval_X]
end GlobalTheory.DenseSec
