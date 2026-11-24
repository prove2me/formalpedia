-- Prove2me | solution 1 for GlobalTheory.card_ker_int_matrix_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:53.438794+00:00
-- url     : https://prove2.me/submissions/6e25bb75-ff33-458b-bccd-a719abc625df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Theorems.Thm_GlobalTheory_card_hom_vanishing_of_diag_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type) [CommGroup G] (m r : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (hm : 1 ≤ m)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hG : ∀ k : ℕ, k ∣ m → Nat.card {x : G // x ^ k = 1} = k ^ r) :
    Nat.card {ξ : Fin 4 → G // ∀ c, ∏ r', ξ r' ^ al r' c = 1} = m ^ (2 * r) := by
  classical
  have hdet : al.det.natAbs = m ^ 2 := by
    have h1 := congrArg Matrix.det hal
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact Nat.mul_self_inj.mp (by rw [h2]; ring)
  have hdet0 : al.det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have : 0 < m ^ 2 := by positivity
    simp at hdet
    omega
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hreg := Matrix.isRegular_of_isLeftRegular_det (A := al)
      (IsRegular.of_ne_zero hdet0).left
    apply hreg.right
    simp only [Matrix.mul_assoc, hal]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  set f : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' al with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 (by simpa [hf] using hv)
  set N := LinearMap.range f with hN
  have hrank : finrank ℤ N = finrank ℤ (Fin 4 → ℤ) :=
    (LinearEquiv.ofInjective f hinj).finrank_eq.symm
  let b0 := Pi.basisFun ℤ (Fin 4)
  let a := Submodule.smithNormalFormCoeffs b0 hrank
  let b := Submodule.smithNormalFormTopBasis b0 hrank
  let c := Submodule.smithNormalFormBotBasis b0 hrank
  have hc : ∀ i, (c i : Fin 4 → ℤ) = a i • b i := Submodule.smithNormalFormBotBasis_def b0 hrank
  have hprod : ∏ i, (a i).natAbs = m ^ 2 := by
    have h1 := Submodule.natAbs_det_equiv N (LinearEquiv.ofInjective f hinj)
    rw [Nat.card_congr (Submodule.quotientEquivPiZMod N b0 hrank).toEquiv, Nat.card_pi] at h1
    simp_rw [Nat.card_zmod] at h1
    rw [← h1, ← hdet, ← LinearMap.det_toLin']
    congr 2
  have hdvd : ∀ i, (a i).natAbs ∣ m := by
    intro i
    have hmem : (m : ℤ) • b i ∈ N := ⟨al.transpose.mulVec (b i), by
      simp [hf, Matrix.mulVec_mulVec, hal', Matrix.smul_mulVec]⟩
    have h1 := congrArg (fun x : N => b.repr (x : Fin 4 → ℤ) i) (c.sum_repr ⟨_, hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hc, map_sum, map_smul, Basis.repr_self,
      Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact Int.natAbs_dvd_natAbs.mpr (Dvd.intro_left _ h1)
  have key := card_hom_vanishing_of_diag_basis (A := Additive G) N b c a hc
  have h3 : ∀ i, Nat.card {y : Additive G // a i • y = 0} = (a i).natAbs ^ r := by
    intro i
    rw [← hG _ (hdvd i)]
    refine Nat.card_congr (Additive.toMul.subtypeEquiv fun y => ?_)
    rw [pow_natAbs_eq_one, ← toMul_zsmul, toMul_eq_one]
  simp_rw [h3] at key
  rw [Finset.prod_pow, hprod, ← pow_mul] at key
  rw [← key]
  refine Nat.card_congr (Equiv.subtypeEquiv
    ((Equiv.piCongrRight fun _ => Additive.ofMul).trans (b0.constr ℤ).toEquiv) fun ξ => ?_)
  have h4 : ∀ j, (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) (f (b0 j)) =
      Additive.ofMul (∏ r', ξ r' ^ al r' j) := by
    intro j
    rw [Basis.constr_apply_fintype, ofMul_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b0, hf, ofMul_zpow]
  constructor
  · rintro hξ _ ⟨x, rfl⟩
    have : (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) ∘ₗ f = 0 :=
      b0.ext fun j => by
        rw [LinearMap.comp_apply, h4, hξ]; rfl
    exact LinearMap.congr_fun this x
  · intro hξ j
    have := hξ (f (b0 j)) ⟨_, rfl⟩
    exact ofMul_eq_zero.mp ((h4 j).symm.trans this)
end GlobalTheory
