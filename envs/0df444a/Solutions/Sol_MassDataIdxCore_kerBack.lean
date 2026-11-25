-- Prove2me | solution 1 for MassDataIdxCore.kerBack
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:24.56262+00:00
-- url     : https://prove2.me/submissions/56b0bd2d-a1b9-47e4-b5bf-0c05dd236045

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Theorems.Thm_MassDataIdxCore_p_pinv
import Theorems.Thm_MassDataIdxCore_key_I
import Theorems.Thm_MassDataIdxCore_conjP_mul
import Theorems.Thm_MassDataIdxCore_conjP_one
import Theorems.Thm_MassDataIdxCore_ker_fwd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n] {θ : T ≃ₐ[K] K × K} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T)
  (P : GL n K)
include hs
namespace MassDataIdxCore
theorem _root_.solution (hJu : IsUnit J.det) : KerBack O θ s J P := by
  intro c g hg hL hc y hy
  have hsm : ∀ (a : K) (t : T), t1 θ (a • t) = a * t1 θ t := fun a t => by simp [t1]
  have hsm2 : ∀ (a : K) (t : T), t2 θ (a • t) = a * t2 θ t := fun a t => by simp [t2]
  have hint : ∀ W : Matrix n n K, (∀ i j, W i j ∈ O) → ∀ v : n → K, IntV O v →
      IntV O (W *ᵥ v) := by
    intro W hW v hv i
    exact sum_mem (fun j _ => mul_mem (hW i j) (hv j))
  have m1 : ∀ (A : Matrix n n T) (x : n → T),
      (fun j => t1 θ ((A *ᵥ x) j)) = A.map (t1 θ) *ᵥ fun j => t1 θ (x j) := by
    intro A x
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have m2 : ∀ (A : Matrix n n T) (x : n → T),
      (fun j => t2 θ ((A *ᵥ x) j)) = A.map (t2 θ) *ᵥ fun j => t2 θ (x j) := by
    intro A x
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have lat_sub : ∀ x x', x ∈ Lat O θ J P → x' ∈ Lat O θ J P → x - x' ∈ Lat O θ J P := by
    intro x x' hx hx'
    unfold Lat at hx hx' ⊢
    simp only [Set.mem_setOf_eq] at hx hx' ⊢
    constructor
    · have e : (fun j => t1 θ ((x - x') j)) = (fun j => t1 θ (x j)) - fun j => t1 θ (x' j) := by
        funext j
        simp
      rw [e, Matrix.mulVec_sub]
      exact fun i => sub_mem (hx.1 i) (hx'.1 i)
    · have e : (fun j => t2 θ ((x - x') j)) = (fun j => t2 θ (x j)) - fun j => t2 θ (x' j) := by
        funext j
        simp
      rw [e, Matrix.mulVec_sub]
      exact fun i => sub_mem (hx.2 i) (hx'.2 i)
  have hy' := hy
  unfold Lat at hy'
  simp only [Set.mem_setOf_eq] at hy'
  have hginv : ∀ x ∈ Lat O θ J P, ((g⁻¹ : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P := by
    intro x hx
    apply (hL _).mpr
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hx
  have hVint := ker_fwd (O := O) (θ := θ) (J := J) (P := P) 1 g⁻¹ (fun x hx =>
    ⟨((g⁻¹ : GL n T) : Matrix n n T) *ᵥ x - x, lat_sub _ _ (hginv x hx) hx, by
      rw [one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]⟩)
  have hV : ∀ i j, conjPrime₂ θ P g⁻¹ i j ∈ O := by
    intro i j
    obtain ⟨w, hw, e⟩ := hVint i j
    have e2 : conjPrime₂ θ P g⁻¹ i j = (1 : Matrix n n K) i j + w := by
      rw [← one_mul w, ← e]
      simp
    rw [e2]
    refine add_mem ?_ hw
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem O
    · exact zero_mem O
  choose W hWO hW using hc
  have hWm : conjPrime₂ θ P g - 1 = c • Matrix.of W := by
    ext i j
    simp [hW i j]
  have hV1 : conjPrime₂ θ P g⁻¹ * conjPrime₂ θ P g = 1 := by
    rw [← conjP_mul, inv_mul_cancel, conjP_one]
  have hW'm : conjPrime₂ θ P g⁻¹ - 1 = c • (-(conjPrime₂ θ P g⁻¹ * Matrix.of W)) := by
    rw [smul_neg, ← Matrix.mul_smul, ← hWm, Matrix.mul_sub, hV1, Matrix.mul_one]
    abel
  have hW'O : ∀ i j, (-(conjPrime₂ θ P g⁻¹ * Matrix.of W)) i j ∈ O := by
    intro i j
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply]
    exact neg_mem (sum_mem (fun k _ => mul_mem (hV i k) (hWO k j)))
  have E1m : ((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T) - 1).map (t1 θ) = (conjPrime₂ θ P g - 1) * ((P⁻¹ : GL n K) : Matrix n n K) := by
    unfold conjPrime₂
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      p_pinv P]
  have E2m : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) * ((g : Matrix n n T) - 1).map (t2 θ) =
      (conjPrime₂ θ P g⁻¹ - 1)ᵀ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, key_I hs J P g hg,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  have hv1 : ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) =
      (conjPrime₂ θ P g - 1) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun j => t1 θ (y j)) := by
    rw [m1, Matrix.mulVec_mulVec, E1m, ← Matrix.mulVec_mulVec]
  have hv2 : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) =
      (conjPrime₂ θ P g⁻¹ - 1)ᵀ *ᵥ (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ fun j => t2 θ (y j)) := by
    rw [m2, Matrix.mulVec_mulVec, E2m, ← Matrix.mulVec_mulVec]
  by_cases hc0 : c = 0
  · subst hc0
    have hM : IsUnit ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ).det := by
      have hJ1 : (J.map (t1 θ)).det = t1 θ J.det := (RingHom.map_det (t1 θ) J).symm
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, hJ1]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).mul (hJu.map _)
    have a1z : (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
      have h0 : ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
        rw [hv1, hWm, zero_smul, Matrix.zero_mulVec]
      calc _ = ((P : Matrix n n K) * ((P⁻¹ : GL n K) : Matrix n n K)) *ᵥ
            (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) := by
            rw [p_pinv P, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    have a2z : (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
      have h0 : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
        rw [hv2, hW'm, zero_smul, Matrix.transpose_zero, Matrix.zero_mulVec]
      calc _ = (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ)⁻¹ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ)) *ᵥ
            (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) := by
            rw [Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    have hv0 : ((g : Matrix n n T) - 1) *ᵥ y = 0 := by
      funext j
      apply θ.injective
      have e1 := congrFun a1z j
      have e2 := congrFun a2z j
      simp only [t1, t2, Pi.zero_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd,
        AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_coe] at e1 e2
      ext
      · simpa using e1
      · simpa using e2
    exact ⟨0, by simpa using lat_sub y y hy hy, by rw [hv0, smul_zero]⟩
  · refine ⟨c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y), ?_, by
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]⟩
    have s1 : (fun j => t1 θ ((c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y)) j)) =
        c⁻¹ • fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j) := by
      funext j
      simp only [Pi.smul_apply, hsm, smul_eq_mul]
    have s2 : (fun j => t2 θ ((c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y)) j)) =
        c⁻¹ • fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j) := by
      funext j
      simp only [Pi.smul_apply, hsm2, smul_eq_mul]
    unfold Lat
    simp only [Set.mem_setOf_eq]
    constructor
    · rw [s1, Matrix.mulVec_smul, hv1, hWm, Matrix.smul_mulVec, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]
      exact hint _ hWO _ hy'.1
    · rw [s2, Matrix.mulVec_smul, hv2, hW'm, Matrix.transpose_smul, Matrix.smul_mulVec,
        smul_smul, inv_mul_cancel₀ hc0, one_smul]
      exact hint _ (fun i j => hW'O j i) _ hy'.2
end MassDataIdxCore
