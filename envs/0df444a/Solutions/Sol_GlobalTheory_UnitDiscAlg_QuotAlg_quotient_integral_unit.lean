-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:08.83364+00:00
-- url     : https://prove2.me/submissions/5d30b01d-5f27-448a-9a49-dc8da59aefac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitAndIntegInvOfNormDetEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnit
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_core
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_eq_one_of_mul_eq_one
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_inv_comm
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
import Theorems.Thm_GlobalTheory_T_ultrametric_norm_det_one_add_smul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_add
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_mul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_one
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_pow
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_smul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_isUnit_and_integ_inv_of_norm_det_eq_one
import Theorems.Thm_GlobalTheory_norm_det_le_one_of_entries_le_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.QuotAlg
namespace GlobalTheory.UnitDiscAlg.QuotAlg
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N c b e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) → (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) → ‖u.det‖ = 1 → e₁ * e₁ = e₁ → e₂ * e₂ = e₂ → e₃ * e₃ = e₃ → e₁ * e₂ = 0 → e₁ * e₃ = 0 → e₂ * e₃ = 0 → e₁ + e₂ + e₃ = 1 → c * e₁ = u * e₁ → c * e₂ = ϖ • (a₂ * e₂) → c⁻¹ * e₃ = ϖ • (a₃ * e₃) → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ n N c b e₁ e₂ e₃ u a₂ a₃ ϖ hϖ0 hϖ1 hcomm hcu hcN hbN hbI hbd hN hI hud h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3
  obtain ⟨he₁N, he₂N, he₃N, huN, ha₂N, ha₃N⟩ := hN
  have hϖne : ϖ ≠ 0 := norm_pos_iff.1 hϖ0
  have hϖle : ‖ϖ‖ ≤ 1 := hϖ1.le
  set S := Subalgebra.centralizer E ({N} : Set (Matrix (Fin n) (Fin n) E)) with hS
  have memN : ∀ x : S, x.1 * N = N * x.1 := fun x =>
    ((Subalgebra.mem_centralizer_iff E).1 x.2 N rfl).symm
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun x y => Subtype.ext (hcomm _ _ (memN x) (memN y)) }
  have mem : ∀ x : Matrix (Fin n) (Fin n) E, x * N = N * x → x ∈ S := fun x hx =>
    (Subalgebra.mem_centralizer_iff E).2
      (fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hx.symm)
  have I_mul : ∀ x y : S, (∀ i j, ‖x.1 i j‖ ≤ 1) → (∀ i j, ‖y.1 i j‖ ≤ 1) →
      ∀ i j, ‖(x * y).1 i j‖ ≤ 1 := fun x y hx hy => integ_mul hx hy
  have I_add : ∀ x y : S, (∀ i j, ‖x.1 i j‖ ≤ 1) → (∀ i j, ‖y.1 i j‖ ≤ 1) →
      ∀ i j, ‖(x + y).1 i j‖ ≤ 1 := fun x y hx hy => integ_add hx hy
  have I_pow : ∀ (x : S) (k : ℕ), (∀ i j, ‖x.1 i j‖ ≤ 1) → ∀ i j, ‖(x ^ k).1 i j‖ ≤ 1 :=
    fun x k hx => integ_pow hx k
  have I_one : ∀ i j, ‖(1 : S).1 i j‖ ≤ 1 := integ_one
  have isU : ∀ x y : S, x * y = 1 → IsUnit x.1 := fun x y h =>
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse
      (congrArg Subtype.val h : x.1 * y.1 = 1))

  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hcu
  obtain ⟨hu, huiI⟩ :=
    isUnit_and_integ_inv_of_norm_det_eq_one E n u (fun i j => (hI i j).2.2.2.1) hud
  obtain ⟨hb, hbiI⟩ := isUnit_and_integ_inv_of_norm_det_eq_one E n b hbI hbd
  obtain ⟨C, hCv⟩ : ∃ X : S, X.1 = c := ⟨⟨c, mem c hcN⟩, rfl⟩
  obtain ⟨Ci, hCiv⟩ : ∃ X : S, X.1 = c⁻¹ := ⟨⟨c⁻¹, mem _ (inv_comm hcN)⟩, rfl⟩
  obtain ⟨U, hUv⟩ : ∃ X : S, X.1 = u := ⟨⟨u, mem u huN⟩, rfl⟩
  obtain ⟨Ui, hUiv⟩ : ∃ X : S, X.1 = u⁻¹ := ⟨⟨u⁻¹, mem _ (inv_comm huN)⟩, rfl⟩
  obtain ⟨B, hBv⟩ : ∃ X : S, X.1 = b := ⟨⟨b, mem b hbN⟩, rfl⟩
  obtain ⟨Bi, hBiv⟩ : ∃ X : S, X.1 = b⁻¹ := ⟨⟨b⁻¹, mem _ (inv_comm hbN)⟩, rfl⟩
  obtain ⟨A2, hA2v⟩ : ∃ X : S, X.1 = a₂ := ⟨⟨a₂, mem _ ha₂N⟩, rfl⟩
  obtain ⟨A3, hA3v⟩ : ∃ X : S, X.1 = a₃ := ⟨⟨a₃, mem _ ha₃N⟩, rfl⟩
  obtain ⟨E1, hE1v⟩ : ∃ X : S, X.1 = e₁ := ⟨⟨e₁, mem _ he₁N⟩, rfl⟩
  obtain ⟨E2, hE2v⟩ : ∃ X : S, X.1 = e₂ := ⟨⟨e₂, mem _ he₂N⟩, rfl⟩
  obtain ⟨E3, hE3v⟩ : ∃ X : S, X.1 = e₃ := ⟨⟨e₃, mem _ he₃N⟩, rfl⟩
  obtain ⟨P, hPv⟩ : ∃ X : S, X.1 = ϖ • 1 :=
    ⟨⟨_, mem _ (by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])⟩, rfl⟩
  obtain ⟨Pi, hPiv⟩ : ∃ X : S, X.1 = ϖ⁻¹ • 1 :=
    ⟨⟨_, mem _ (by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])⟩, rfl⟩
  have IU : ∀ i j, ‖U.1 i j‖ ≤ 1 := by rw [hUv]; exact fun i j => (hI i j).2.2.2.1
  have IUi : ∀ i j, ‖Ui.1 i j‖ ≤ 1 := by rw [hUiv]; exact huiI
  have IB : ∀ i j, ‖B.1 i j‖ ≤ 1 := by rw [hBv]; exact hbI
  have IBi : ∀ i j, ‖Bi.1 i j‖ ≤ 1 := by rw [hBiv]; exact hbiI
  have IA2 : ∀ i j, ‖A2.1 i j‖ ≤ 1 := by rw [hA2v]; exact fun i j => (hI i j).2.2.2.2.1
  have NearKilling : ∀ i j, ‖A3.1 i j‖ ≤ 1 := by rw [hA3v]; exact fun i j => (hI i j).2.2.2.2.2
  have IE1 : ∀ i j, ‖E1.1 i j‖ ≤ 1 := by rw [hE1v]; exact fun i j => (hI i j).1
  have IE2 : ∀ i j, ‖E2.1 i j‖ ≤ 1 := by rw [hE2v]; exact fun i j => (hI i j).2.1
  have IE3 : ∀ i j, ‖E3.1 i j‖ ≤ 1 := by rw [hE3v]; exact fun i j => (hI i j).2.2.1
  have IP : ∀ i j, ‖P.1 i j‖ ≤ 1 := by rw [hPv]; exact integ_smul hϖle integ_one
  have hUd : ‖U.1.det‖ = 1 := by rw [hUv]; exact hud
  have hBd : ‖B.1.det‖ = 1 := by rw [hBv]; exact hbd

  have hp : P * Pi = 1 := Subtype.ext (by
    show P.1 * Pi.1 = 1
    rw [hPv, hPiv, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hϖne, one_smul])
  have hci : C * Ci = 1 := Subtype.ext (by
    show C.1 * Ci.1 = 1
    rw [hCv, hCiv]; exact Matrix.mul_nonsing_inv c hcd)
  have hUi : U * Ui = 1 := Subtype.ext (by
    show U.1 * Ui.1 = 1
    rw [hUv, hUiv]; exact Matrix.mul_nonsing_inv u ((Matrix.isUnit_iff_isUnit_det u).1 hu))
  have hBi : B * Bi = 1 := Subtype.ext (by
    show B.1 * Bi.1 = 1
    rw [hBv, hBiv]; exact Matrix.mul_nonsing_inv b ((Matrix.isUnit_iff_isUnit_det b).1 hb))
  have h11S : E1 * E1 = E1 := Subtype.ext (by show E1.1 * E1.1 = E1.1; rw [hE1v]; exact h11)
  have h22S : E2 * E2 = E2 := Subtype.ext (by show E2.1 * E2.1 = E2.1; rw [hE2v]; exact h22)
  have h33S : E3 * E3 = E3 := Subtype.ext (by show E3.1 * E3.1 = E3.1; rw [hE3v]; exact h33)
  have h12S : E1 * E2 = 0 := Subtype.ext (by show E1.1 * E2.1 = 0; rw [hE1v, hE2v]; exact h12)
  have h13S : E1 * E3 = 0 := Subtype.ext (by show E1.1 * E3.1 = 0; rw [hE1v, hE3v]; exact h13)
  have h23S : E2 * E3 = 0 := Subtype.ext (by show E2.1 * E3.1 = 0; rw [hE2v, hE3v]; exact h23)
  have hsS : E1 + E2 + E3 = 1 := Subtype.ext (by
    show E1.1 + E2.1 + E3.1 = 1; rw [hE1v, hE2v, hE3v]; exact hs)
  have hc1S : C * E1 = U * E1 := Subtype.ext (by
    show C.1 * E1.1 = U.1 * E1.1; rw [hCv, hE1v, hUv]; exact hc1)
  have hc2S : C * E2 = P * (A2 * E2) := Subtype.ext (by
    show C.1 * E2.1 = P.1 * (A2.1 * E2.1)
    rw [hCv, hE2v, hPv, hA2v, Matrix.smul_mul, Matrix.one_mul]; exact hc2)
  have hc3S : Ci * E3 = P * (A3 * E3) := Subtype.ext (by
    show Ci.1 * E3.1 = P.1 * (A3.1 * E3.1)
    rw [hCiv, hE3v, hPv, hA3v, Matrix.smul_mul, Matrix.one_mul]; exact hc3)

  have mk : ∀ g w x : S, g = w * (1 + P * x) → (∀ i j, ‖w.1 i j‖ ≤ 1) → ‖w.1.det‖ = 1 →
      (∀ i j, ‖x.1 i j‖ ≤ 1) → ∃ k : S, g * k = 1 ∧ ∀ i j, ‖k.1 i j‖ ≤ 1 := by
    intro g w x hg hw hwd hx
    have hgv : g.1 = w.1 * (1 + ϖ • x.1) := by
      rw [hg]; show w.1 * (1 + P.1 * x.1) = _; rw [hPv, Matrix.smul_mul, Matrix.one_mul]
    have hgI : ∀ i j, ‖g.1 i j‖ ≤ 1 := by
      rw [hgv]; exact integ_mul hw (integ_add integ_one (integ_smul hϖle hx))
    have hgd : ‖g.1.det‖ = 1 := by
      rw [hgv, Matrix.det_mul, norm_mul, hwd, GlobalTheory.T.ultrametric_norm_det_one_add_smul E n x.1 ϖ hϖ1 hx, one_mul]
    obtain ⟨hgu, hgiI⟩ := isUnit_and_integ_inv_of_norm_det_eq_one E n g.1 hgI hgd
    refine ⟨⟨g.1⁻¹, mem _ (inv_comm (memN g))⟩, Subtype.ext ?_, hgiI⟩
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hgu)
  have wpow : ∀ w : S, (∀ i j, ‖w.1 i j‖ ≤ 1) → ‖w.1.det‖ = 1 → ∀ k : ℕ,
      (∀ i j, ‖(w ^ k).1 i j‖ ≤ 1) ∧ ‖(w ^ k).1.det‖ = 1 := fun w hw hd k =>
    ⟨integ_pow hw k, by show ‖(w.1 ^ k).det‖ = 1; rw [Matrix.det_pow, norm_pow, hd, one_pow]⟩
  have w1 : (∀ i j, ‖(1 : S).1 i j‖ ≤ 1) ∧ ‖(1 : S).1.det‖ = 1 :=
    ⟨integ_one, by show ‖(1 : Matrix (Fin n) (Fin n) E).det‖ = 1; simp⟩
  obtain ⟨k11, hk11, Ik11⟩ := mk (P + U ^ 2) (U ^ 2) (Ui ^ 2)
    (by linear_combination -P * (U * Ui + 1) * hUi) (wpow U IU hUd 2).1 (wpow U IU hUd 2).2
    (I_pow _ _ IUi)
  obtain ⟨k12, hk12, Ik12⟩ := mk (1 + P * A2 ^ 2) 1 (A2 ^ 2) (by ring) w1.1 w1.2 (I_pow _ _ IA2)
  obtain ⟨k13, hk13, Ik13⟩ := mk (1 + P ^ 3 * A3 ^ 2) 1 (P ^ 2 * A3 ^ 2) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling))
  obtain ⟨k21, hk21, Ik21⟩ := mk (P + U ^ 3) (U ^ 3) (Ui ^ 3)
    (by linear_combination -P * ((U * Ui) ^ 2 + U * Ui + 1) * hUi) (wpow U IU hUd 3).1
    (wpow U IU hUd 3).2 (I_pow _ _ IUi)
  obtain ⟨k22, hk22, Ik22⟩ := mk (1 + P ^ 2 * A2 ^ 3) 1 (P * A2 ^ 3) (by ring) w1.1 w1.2
    (I_mul _ _ IP (I_pow _ _ IA2))
  obtain ⟨k23, hk23, Ik23⟩ := mk (1 + P ^ 4 * A3 ^ 3) 1 (P ^ 3 * A3 ^ 3) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling))
  obtain ⟨k31, hk31, Ik31⟩ := mk (P * U ^ 2 + B ^ 2) (B ^ 2) (Bi ^ 2 * U ^ 2)
    (by linear_combination -P * U ^ 2 * (B * Bi + 1) * hBi) (wpow B IB hBd 2).1
    (wpow B IB hBd 2).2 (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IU))
  obtain ⟨k32, hk32, Ik32⟩ := mk (B ^ 2 + P ^ 3 * A2 ^ 2) (B ^ 2) (P ^ 2 * (Bi ^ 2 * A2 ^ 2))
    (by linear_combination -P ^ 3 * A2 ^ 2 * (B * Bi + 1) * hBi) (wpow B IB hBd 2).1
    (wpow B IB hBd 2).2 (I_mul _ _ (I_pow _ _ IP) (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IA2)))
  obtain ⟨k33, hk33, Ik33⟩ := mk (1 + P * B ^ 2 * A3 ^ 2) 1 (B ^ 2 * A3 ^ 2) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IB) (I_pow _ _ NearKilling))
  obtain ⟨k41, hk41, Ik41⟩ := mk (P * U ^ 3 + B ^ 3) (B ^ 3) (Bi ^ 3 * U ^ 3)
    (by linear_combination -P * U ^ 3 * ((B * Bi) ^ 2 + B * Bi + 1) * hBi) (wpow B IB hBd 3).1
    (wpow B IB hBd 3).2 (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IU))
  obtain ⟨k42, hk42, Ik42⟩ := mk (B ^ 3 + P ^ 4 * A2 ^ 3) (B ^ 3) (P ^ 3 * (Bi ^ 3 * A2 ^ 3))
    (by linear_combination -P ^ 4 * A2 ^ 3 * ((B * Bi) ^ 2 + B * Bi + 1) * hBi)
    (wpow B IB hBd 3).1 (wpow B IB hBd 3).2
    (I_mul _ _ (I_pow _ _ IP) (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IA2)))
  obtain ⟨k43, hk43, Ik43⟩ := mk (1 + P ^ 2 * B ^ 3 * A3 ^ 3) 1 (P * (B ^ 3 * A3 ^ 3)) (by ring)
    w1.1 w1.2 (I_mul _ _ IP (I_mul _ _ (I_pow _ _ IB) (I_pow _ _ NearKilling)))
  obtain ⟨hX1, hX2, hX3, hX4, hQ, hYY⟩ := core P Pi C Ci U A2 A3 B E1 E2 E3
    k11 k12 k13 k21 k22 k23 k31 k32 k33 k41 k42 k43 hp hci h11S h22S h33S h12S h13S h23S hsS
    hc1S hc2S hc3S hk11 hk12 hk13 hk21 hk22 hk23 hk31 hk32 hk33 hk41 hk42 hk43
  set Y : S := ((P * U ^ 3 + B ^ 3) * (P + U ^ 2) * k21 * k31) * E1
        + ((B ^ 3 + P ^ 4 * A2 ^ 3) * (1 + P * A2 ^ 2) * k22 * k32) * E2
        + ((1 + P ^ 2 * B ^ 3 * A3 ^ 3) * (1 + P ^ 3 * A3 ^ 2) * k23 * k33) * E3 with hY
  set Y' : S := ((P + U ^ 3) * (P * U ^ 2 + B ^ 2) * k41 * k11) * E1
        + ((1 + P ^ 2 * A2 ^ 3) * (B ^ 2 + P ^ 3 * A2 ^ 2) * k42 * k12) * E2
        + ((1 + P ^ 4 * A3 ^ 3) * (1 + P * B ^ 2 * A3 ^ 2) * k43 * k13) * E3 with hY'
  have IY : ∀ i j, ‖Y.1 i j‖ ≤ 1 := by
    rw [hY]
    exact I_add _ _ (I_add _ _
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ (I_mul _ _ IP (I_pow _ _ IU)) (I_pow _ _ IB))
        (I_add _ _ IP (I_pow _ _ IU))) Ik21) Ik31) IE1)
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ (I_pow _ _ IB) (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))
        (I_add _ _ I_one (I_mul _ _ IP (I_pow _ _ IA2)))) Ik22) Ik32) IE2))
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _
        (I_add _ _ I_one (I_mul _ _ (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IB)) (I_pow _ _ NearKilling)))
        (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling)))) Ik23) Ik33) IE3)
  have IY' : ∀ i j, ‖Y'.1 i j‖ ≤ 1 := by
    rw [hY']
    exact I_add _ _ (I_add _ _
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ IP (I_pow _ _ IU))
        (I_add _ _ (I_mul _ _ IP (I_pow _ _ IU)) (I_pow _ _ IB))) Ik41) Ik11) IE1)
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))
        (I_add _ _ (I_pow _ _ IB) (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))) Ik42) Ik12) IE2))
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling)))
        (I_add _ _ I_one (I_mul _ _ (I_mul _ _ IP (I_pow _ _ IB)) (I_pow _ _ NearKilling)))) Ik43) Ik13) IE3)
  have hX1v : (P + C ^ 2).1 = ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2 := by
    show P.1 + C.1 ^ 2 = _; rw [hPv, hCv]
  have hX2v : (P + C ^ 3).1 = ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3 := by
    show P.1 + C.1 ^ 3 = _; rw [hPv, hCv]
  have hX3v : (P * C ^ 2 + B ^ 2).1 = ϖ • c ^ 2 + b ^ 2 := by
    show P.1 * C.1 ^ 2 + B.1 ^ 2 = _; rw [hPv, hCv, hBv, Matrix.smul_mul, Matrix.one_mul]
  have hX4v : (P * C ^ 3 + B ^ 3).1 = ϖ • c ^ 3 + b ^ 3 := by
    show P.1 * C.1 ^ 3 + B.1 ^ 3 = _; rw [hPv, hCv, hBv, Matrix.smul_mul, Matrix.one_mul]
  have u1 := isU _ _ hX1
  have u2 := isU _ _ hX2
  have u3 := isU _ _ hX3
  have u4 := isU _ _ hX4
  rw [hX1v] at u1; rw [hX2v] at u2; rw [hX3v] at u3; rw [hX4v] at u4
  have hdet23 : IsUnit ((P + C ^ 3).1 * (P * C ^ 2 + B ^ 2).1).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((isU _ _ hX2).mul (isU _ _ hX3))
  have hQv : (P * C ^ 3 + B ^ 3).1 * (P + C ^ 2).1 = Y.1 * ((P + C ^ 3).1 * (P * C ^ 2 + B ^ 2).1) :=
    congrArg Subtype.val hQ
  have Qm : (ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) *
      ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹ = Y.1 := by
    rw [← hX1v, ← hX2v, ← hX3v, ← hX4v, hQv, Matrix.mul_nonsing_inv_cancel_right _ _ hdet23]
  have hYYv : Y.1 * Y'.1 = 1 := congrArg Subtype.val hYY
  have hdY : ‖Y.1.det‖ = 1 := by
    have h1 := GlobalTheory.norm_det_le_one_of_entries_le_one E n Y.1 IY
    have h2 := GlobalTheory.norm_det_le_one_of_entries_le_one E n Y'.1 IY'
    have h3 : ‖Y.1.det‖ * ‖Y'.1.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, hYYv, Matrix.det_one, norm_one]
    exact eq_one_of_mul_eq_one (norm_nonneg _) (norm_nonneg _) h1 h2 h3
  exact ⟨u1, u2, u3, u4, by rw [Qm]; exact IY, by rw [Qm]; exact hdY⟩
end GlobalTheory.UnitDiscAlg.QuotAlg
