-- Prove2me | solution 1 for GlobalTheory.NoetherInt.exists_quasiFiniteAt_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:51:12.24639+00:00
-- url     : https://prove2.me/submissions/00d2b1de-d783-42b5-9ba0-24e8a7d828a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Theorems.Thm_GlobalTheory_NoetherInt_quasiFinite_of_isUnit_coeff
import Theorems.Thm_GlobalTheory_NoetherInt_exists_coeff_map_eq_C
import Theorems.Thm_GlobalTheory_NoetherInt_exists_primitive_of_aeval_eq_zero
import Theorems.Thm_GlobalTheory_NoetherInt_quasiFiniteAt_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
namespace GlobalTheory.NoetherInt
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (q : Ideal S) [q.IsPrime] {n : ℕ} (y : Fin (n + 1) → S)
    (h : (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q)
    (hy : ¬ Function.Injective (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S)) :
    ∃ y' : Fin n → S, (aeval y' : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by

  obtain ⟨g, hg0, hg⟩ : ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ aeval y g = 0 := by
    rw [injective_iff_map_eq_zero] at hy
    push_neg at hy
    obtain ⟨g, h1, h2⟩ := hy
    exact ⟨g, h2, h1⟩
  let L := algebraMap S (Localization.AtPrime q)
  let K := IsLocalRing.ResidueField (Localization.AtPrime q)
  let res : Localization.AtPrime q →+* K := IsLocalRing.residue _
  let ι : ℤ →+* K := Int.castRingHom K
  obtain ⟨g₁, hg₁, v, hv⟩ := exists_primitive_of_aeval_eq_zero y g hg0 hg (RingHom.ker ι)
    (RingHom.ker_ne_top ι)
  have hne : MvPolynomial.map ι g₁ ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (MvPolynomial.coeff v) h0
    rw [MvPolynomial.coeff_map] at this
    simpa [RingHom.mem_ker] using this
  obtain ⟨u, k, a, ha, hc⟩ := exists_coeff_map_eq_C ι g₁ hne

  let σ := shear ℤ n u
  let e := finSuccEquiv ℤ n
  let y₁ : Fin (n + 1) → S := fun i => aeval y (σ.symm (X i))
  have h1 : ∀ p, aeval y₁ p = aeval y (σ.symm p) := by
    intro p
    have : (aeval y₁ : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S) =
        (aeval y).comp (σ.symm : _ →ₐ[ℤ] _) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [y₁]
    exact DFunLike.congr_fun this p
  let y' : Fin n → S := fun i => y₁ i.succ
  let t := L (y₁ 0)
  let φ : MvPolynomial (Fin n) ℤ →+* Localization.AtPrime q :=
    L.comp (aeval y' : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom
  have key : ∀ p, Polynomial.eval₂ φ t (e p) = L (aeval y₁ p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← Polynomial.coe_eval₂RingHom]
      simp only [eq_intCast, map_intCast]
    | add p r hp hr => simp [hp, hr, Polynomial.eval₂_add]
    | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval₂_mul, hp]
      congr 1
      cases i using Fin.cases with
      | zero => simp [e, t, finSuccEquiv_X_zero]
      | succ i => simp [e, φ, y', finSuccEquiv_X_succ]
  let E : Polynomial (MvPolynomial (Fin n) ℤ) ≃+* MvPolynomial (Fin (n + 1)) ℤ :=
    (e.symm.trans σ.symm).toRingEquiv
  have hE : Polynomial.eval₂RingHom φ t =
      (L.comp (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S).toRingHom).comp E.toRingHom := by
    refine RingHom.ext fun p => ?_
    obtain ⟨p, rfl⟩ := e.surjective p
    rw [Polynomial.coe_eval₂RingHom, key, h1]
    simp [E]
  have hq : (Polynomial.eval₂RingHom φ t).QuasiFinite := by
    rw [hE]
    exact ((quasiFiniteAt_iff _ q).mp h).comp (RingHom.QuasiFinite.of_finite E.finite)
  have hG : Polynomial.eval₂ φ t (e (σ g₁)) = 0 := by
    rw [key, h1]; simp [hg₁]
  have hunit : IsUnit (φ ((e (σ g₁)).coeff k)) := by
    have hΦ : res.comp φ =
        (MvPolynomial.eval fun i => res (φ (X i))).comp (MvPolynomial.map ι) := by
      apply MvPolynomial.ringHom_ext
      · intro m; simp [ι]
      · intro i; simp
    have h2 : res (φ ((e (σ g₁)).coeff k)) = a := by
      have : res (φ ((e (σ g₁)).coeff k)) = MvPolynomial.eval (fun i => res (φ (X i)))
          (MvPolynomial.map ι ((e (σ g₁)).coeff k)) := DFunLike.congr_fun hΦ ((e (σ g₁)).coeff k)
      rw [this]
      simp only [e, σ]
      rw [hc]; simp
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (h2 ▸ ha)
  exact ⟨y', (quasiFiniteAt_iff _ q).mpr (quasiFinite_of_isUnit_coeff φ t hq _ hG k hunit)⟩
end GlobalTheory.NoetherInt
