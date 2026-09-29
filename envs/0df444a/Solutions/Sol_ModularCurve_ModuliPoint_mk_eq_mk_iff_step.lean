-- Prove2me | solution 1 for ModularCurve.ModuliPoint.mk_eq_mk_iff_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9547c3ae-59ca-556d-82ca-ff97a8b48ba3

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_ModuliPoint
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModuliPoint_mk_eq_mk_iff_step

set_option autoImplicit false
set_option maxHeartbeats 4800000

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MWs13
namespace ModuliFibre

variable {K : Type*} [Field K]

theorem vcX_injective (C : VariableChange K) : Function.Injective (vcX C) := fun a b h => by
  simpa using congrArg (vcXInv C) h

theorem vcY_injective (C : VariableChange K) (x' : K) : Function.Injective (vcY C x') := fun a b h => by
  simpa using congrArg (vcYInv C (vcX C x')) h

theorem vcX_mul (γ₁ γ₂ : VariableChange K) (x : K) :
    vcX (γ₂ * γ₁) x = vcX γ₁ (vcX γ₂ x) := by
  simp only [WeierstrassCurve.Affine.vcX, VariableChange.mul_def, Units.val_mul]
  ring

theorem vcY_mul (γ₁ γ₂ : VariableChange K) (x y : K) :
    vcY (γ₂ * γ₁) x y = vcY γ₁ (vcX γ₂ x) (vcY γ₂ x y) := by
  simp only [WeierstrassCurve.Affine.vcY, WeierstrassCurve.Affine.vcX,
    VariableChange.mul_def, Units.val_mul]
  ring

theorem vcXInv_mul (γ₁ γ₂ : VariableChange K) (x : K) :
    vcXInv (γ₂ * γ₁) x = vcXInv γ₂ (vcXInv γ₁ x) := by
  refine vcX_injective (γ₂ * γ₁) ?_
  rw [vcX_vcXInv, vcX_mul, vcX_vcXInv, vcX_vcXInv]

theorem vcYInv_mul (γ₁ γ₂ : VariableChange K) (x y : K) :
    vcYInv (γ₂ * γ₁) x y = vcYInv γ₂ (vcXInv γ₁ x) (vcYInv γ₁ x y) := by
  refine vcY_injective (γ₂ * γ₁) (vcXInv (γ₂ * γ₁) x) ?_
  rw [vcY_vcYInv, vcXInv_mul, vcY_mul, vcX_vcXInv, vcY_vcYInv, vcY_vcYInv]

theorem vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  simp [WeierstrassCurve.Affine.vcXInv, VariableChange.one_def]

theorem vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  simp [WeierstrassCurve.Affine.vcYInv, VariableChange.one_def]

variable [DecidableEq K]

theorem vcInvFun_some (γ : VariableChange K) (W : WeierstrassCurve.Affine K) {x y : K} (h : W.Nonsingular x y) :
    Point.vcInvFun γ W (Point.some x y h) = Point.some (vcXInv γ x) (vcYInv γ x y)
      ((nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

theorem Point.heq_vcInvFun (γ : VariableChange K) {V V' : WeierstrassCurve.Affine K}
    (hV : V' = V) {S : V'.Point} {T : V.Point} (h : HEq S T) :
    HEq (Point.vcInvFun γ V' S) (Point.vcInvFun γ V T) := by
  subst hV
  rw [eq_of_heq h]

noncomputable def vcInvHom (γ : VariableChange K) (W : WeierstrassCurve.Affine K) : W.Point →+ (γ • W).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun γ W) (WeierstrassCurve.Affine.Point.vcInvFun_add γ W)

theorem vcInvFun_injective (γ : VariableChange K) (W : WeierstrassCurve.Affine K) :
    Function.Injective (Point.vcInvFun γ W) :=
  (Point.vcFun_rightInverse (C := γ) (W := W)).injective

theorem addOrderOf_vcInvFun (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    addOrderOf (Point.vcInvFun γ W P) = addOrderOf P :=
  addOrderOf_injective (vcInvHom γ W) (vcInvFun_injective γ W) P

theorem vcInvFun_nsmul (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (k : ℕ) (P : W.Point) :
    Point.vcInvFun γ W (k • P) = k • Point.vcInvFun γ W P :=
  map_nsmul (vcInvHom γ W) k P

theorem vcInvFun_mul_heq (γ₁ γ₂ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (Point.vcInvFun (γ₂ * γ₁) W P)
      (Point.vcInvFun γ₂ ((γ₁ • W : WeierstrassCurve K).toAffine) (Point.vcInvFun γ₁ W P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero (mul_smul γ₂ γ₁ W)
  · simp only [vcInvFun_some]
    exact ModularCurve.Point.heq_some (mul_smul γ₂ γ₁ W) (vcXInv_mul γ₁ γ₂ x) (vcYInv_mul γ₁ γ₂ x y)

theorem vcInvFun_inv_heq (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (Point.vcInvFun γ⁻¹ ((γ • W : WeierstrassCurve K).toAffine) (Point.vcInvFun γ W P)) P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero (inv_smul_smul γ W)
  · simp only [vcInvFun_some]
    refine ModularCurve.Point.heq_some (inv_smul_smul γ W) ?_ ?_
    · rw [← vcXInv_mul, inv_mul_cancel, vcXInv_one]
    · rw [← vcYInv_mul, inv_mul_cancel, vcYInv_one]

theorem vcInvFun_one_heq (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (Point.vcInvFun (1 : VariableChange K) W P) P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero (one_smul _ W)
  · simp only [vcInvFun_some]
    exact ModularCurve.Point.heq_some (one_smul _ W) (vcXInv_one x) (vcYInv_one x y)

omit [DecidableEq K] in
theorem exists_nsmul_nsmul_eq_self {M : Type*} [AddCommGroup M] {N k : ℕ}
    (hk : k.Coprime N) {x : M} (hx : addOrderOf x = N) :
    ∃ m : ℕ, m.Coprime N ∧ m • k • x = x := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hk1 : k = 1 := Nat.coprime_zero_right k |>.mp hk
    exact ⟨1, Nat.coprime_one_left 0, by rw [hk1, one_nsmul, one_nsmul]⟩
  by_cases hN1 : N = 1
  · have hx0 : x = 0 := by
      have h1 : addOrderOf x = 1 := by rw [hx, hN1]
      exact AddMonoid.addOrderOf_eq_one_iff.mp h1
    exact ⟨1, Nat.coprime_one_left N, by rw [hx0, smul_zero, smul_zero]⟩
  · have h1N : 1 < N := by omega
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk h1N
    have hNx : N • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
    have hdiv : N * (k * m / N) + 1 = k * m := by
      have h := Nat.div_add_mod (k * m) N
      rw [hm] at h
      exact h
    refine ⟨m, ?_, ?_⟩
    · have hdm : Nat.gcd m N ∣ N * (k * m / N) + 1 := by
        rw [hdiv]
        exact Dvd.dvd.mul_left (Nat.gcd_dvd_left m N) k
      have hdN : Nat.gcd m N ∣ N * (k * m / N) :=
        Dvd.dvd.mul_right (Nat.gcd_dvd_right m N) _
      exact Nat.dvd_one.mp ((Nat.dvd_add_right hdN).mp hdm)
    · rw [← mul_nsmul x k m, ← hdiv, add_nsmul, mul_nsmul x N (k * m / N), hNx, smul_zero,
        zero_add, one_nsmul]

open ModularCurve

variable {N : ℕ}

theorem step_refl (P : Gamma0Pair N K) : Gamma0Pair.Step P P :=
  ⟨1, one_smul _ _, 1, Nat.coprime_one_left N,
    ((heq_of_eq (one_nsmul _)).trans (vcInvFun_one_heq P.toCurve.toAffine P.gen)).symm⟩

theorem step_symm {P Q : Gamma0Pair N K} (h : Gamma0Pair.Step P Q) : Gamma0Pair.Step Q P := by
  obtain ⟨γ, hγ, k, hk, hgen⟩ := h
  obtain ⟨QC, Qell, Qgen, Qord⟩ := Q
  subst hγ
  have hg : Qgen = k • Point.vcInvFun γ P.toCurve.toAffine P.gen := eq_of_heq hgen
  obtain ⟨m, hm, hmx⟩ := exists_nsmul_nsmul_eq_self hk P.addOrderOf_gen
  refine ⟨γ⁻¹, inv_smul_smul γ P.toCurve, m, hm, ?_⟩
  show HEq P.gen (m • Point.vcInvFun γ⁻¹ (γ • P.toCurve).toAffine Qgen)
  rw [hg, vcInvFun_nsmul]
  refine (heq_of_eq hmx.symm).trans ?_
  exact ModularCurve.Point.heq_nsmul (inv_smul_smul γ P.toCurve).symm m
    (ModularCurve.Point.heq_nsmul (inv_smul_smul γ P.toCurve).symm k
      (vcInvFun_inv_heq γ P.toCurve.toAffine P.gen).symm)

theorem step_trans {P Q R : Gamma0Pair N K} (hPQ : Gamma0Pair.Step P Q)
    (hQR : Gamma0Pair.Step Q R) : Gamma0Pair.Step P R := by
  obtain ⟨γ₁, hγ₁, k₁, hk₁, hgen₁⟩ := hPQ
  obtain ⟨γ₂, hγ₂, k₂, hk₂, hgen₂⟩ := hQR
  refine ⟨γ₂ * γ₁, by rw [mul_smul, hγ₁, hγ₂], k₂ * k₁,
    Nat.coprime_mul_iff_left.mpr ⟨hk₂, hk₁⟩, ?_⟩
  have hVQ : (γ₂ • Q.toCurve : WeierstrassCurve K) = γ₂ • (γ₁ • P.toCurve) := by rw [hγ₁]
  have hV2 : (γ₂ • (γ₁ • P.toCurve) : WeierstrassCurve K) = (γ₂ * γ₁) • P.toCurve :=
    (mul_smul γ₂ γ₁ P.toCurve).symm
  refine hgen₂.trans ?_
  refine HEq.trans (ModularCurve.Point.heq_nsmul hVQ k₂
    ((Point.heq_vcInvFun γ₂ hγ₁.symm hgen₁).trans
      (heq_of_eq (vcInvFun_nsmul γ₂ _ k₁ _)))) ?_
  exact (heq_of_eq (smul_smul k₂ k₁ _)).trans
    (ModularCurve.Point.heq_nsmul hV2 (k₂ * k₁) (vcInvFun_mul_heq γ₁ γ₂ P.toCurve.toAffine P.gen).symm)

theorem stepEquivalence : Equivalence (Gamma0Pair.Step (N := N) (L := K)) :=
  ⟨step_refl, step_symm, step_trans⟩

theorem mk_eq_mk_iff_step {P Q : Gamma0Pair N K} :
    (Quot.mk _ P : ModuliPoint N K) = Quot.mk _ Q ↔ Gamma0Pair.Step P Q :=
  Quot.eq.trans (stepEquivalence (N := N) (K := K)).eqvGen_iff

end P2MWs13.ModuliFibre

open P2MWs13.ModuliFibre in
theorem solution
    {N : ℕ} {L : Type*} [Field L] [DecidableEq L] (P Q : ModularCurve.Gamma0Pair N L) :
    (Quot.mk _ P : ModularCurve.ModuliPoint N L) = Quot.mk _ Q ↔ ModularCurve.Gamma0Pair.Step P Q :=
  P2MWs13.ModuliFibre.mk_eq_mk_iff_step

end S_ModularCurve_ModuliPoint_mk_eq_mk_iff_step
end P2MW
export P2MW.S_ModularCurve_ModuliPoint_mk_eq_mk_iff_step (solution)
