-- Prove2me | solution 1 for GlobalTheory.DiagBlock.blockJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:06:17.14624+00:00
-- url     : https://prove2.me/submissions/e9271663-4cc7-4153-9618-19cb111ec2e5

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_coeff_kill
import Theorems.Thm_GlobalTheory_DiagBlock_kill_det_pow
import Theorems.Thm_GlobalTheory_DiagBlock_coeff_mul_split
import Theorems.Thm_GlobalTheory_DiagBlock_rowDeg_of_mem
import Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inl
import Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inr
import Theorems.Thm_GlobalTheory_DiagBlock_diagMon_row
import Theorems.Thm_GlobalTheory_DiagBlock_mfact_diagMon
import Theorems.Thm_GlobalTheory_DiagBlock_rowDeg_filter_le
import Theorems.Thm_GlobalTheory_UnitCase_jetAt0_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
namespace GlobalTheory.DiagBlock
section Kill
variable {R : Type} [CommRing R] {σ : Type}
end Kill
private lemma kill_detL_pow_mul_detR_pow {C : Type} [Field C] {n0 n : ℕ} (hn : n0 ≤ n) (L y : ℕ)
    (S : PVar n → Prop) [DecidablePred S]
    (hS1 : ∀ ρ c : Fin n, S (Sum.inl (ρ, c)) ↔ n0 ≤ ρ.val ∧ c ≠ ρ)
    (hS2 : ∀ ρ c : Fin n, S (Sum.inr (ρ, c)) ↔ n0 ≤ ρ.val ∧ c ≠ ρ) :
    kill S (detL C n ^ (L * y) * detR C n ^ y) =
      MvPolynomial.rename (embV hn) (detL C n0 ^ (L * y) * detR C n0 ^ y) *
        MvPolynomial.monomial (diagMon n0 n L y) 1 := by
  rw [show detL C n = (Matrix.of fun b c : Fin n =>
      (MvPolynomial.X (Sum.inl (b, c)) : MvPolynomial (PVar n) C)).det from rfl,
    show detR C n = (Matrix.of fun b c : Fin n =>
      (MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial (PVar n) C)).det from rfl,
    show detL C n0 = (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inl (b, c)) : MvPolynomial (PVar n0) C)).det from rfl,
    show detR C n0 = (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial (PVar n0) C)).det from rfl]
  rw [map_mul, kill_det_pow S hn (fun b c => Sum.inl (b, c)) hS1,
    kill_det_pow S hn (fun b c => Sum.inr (b, c)) hS2, map_mul, map_pow, map_pow,
    AlgHom.map_det, AlgHom.map_det]
  have e1 : (MvPolynomial.rename (R := C) (embV hn)).mapMatrix (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inl (b, c)) : MvPolynomial (PVar n0) C)) =
      Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (Fin.castLE hn b, Fin.castLE hn c)) := by
    ext b c
    simp [AlgHom.mapMatrix_apply, embV]
  have e2 : (MvPolynomial.rename (R := C) (embV hn)).mapMatrix (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial (PVar n0) C)) =
      Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inr (Fin.castLE hn b, Fin.castLE hn c)) := by
    ext b c
    simp [AlgHom.mapMatrix_apply, embV]
  have hmon : ∀ a b : PVar n →₀ ℕ, MvPolynomial.monomial (a + b) (1 : C) =
      MvPolynomial.monomial a 1 * MvPolynomial.monomial b 1 := fun a b => by
    rw [MvPolynomial.monomial_mul, one_mul]
  rw [e1, e2, diagMon, Finset.sum_add_distrib, hmon]
  ring
private lemma filter_nondiag_eq_diagMon_of_coeff_ne_zero {C : Type} [Field C] {n0 n : ℕ} (L y : ℕ) (G1 H : MvPowerSeries (PVar n) C)
    (hG1 : ∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m G1 ≠ 0 → ∀ x ∈ m.support, (rowOf x).val < n0)
    (hH : ∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m H ≠ 0 → ∀ x ∈ m.support, n0 ≤ (rowOf x).val)
    (hHd : ∀ m : PVar n →₀ ℕ, (∀ x ∈ m.support, n0 ≤ (rowOf x).val) →
      (∀ ρ : Fin n, n0 ≤ ρ.val → rowDegZ m ρ ≤ L * y ∧ rowDegZ' m ρ ≤ y) →
      MvPowerSeries.coeff m H = if m = diagMon n0 n L y then 1 else 0)
    (m : PVar n →₀ ℕ) (hm : MvPolynomial.coeff m (detL C n ^ (L * y) * detR C n ^ y) ≠ 0)
    (hmG : MvPowerSeries.coeff m (G1 * H) ≠ 0) :
    m.filter (fun x => ¬ (rowOf x).val < n0) = diagMon n0 n L y := by
  classical
  have hab := Finsupp.filter_add_filter_not m (fun x => (rowOf x).val < n0)
  have hsplit := coeff_mul_split (fun x => (rowOf x).val < n0) G1 H hG1
    (fun m' hm' x hx => not_lt.2 (hH m' hm' x hx))
    (m.filter fun x => (rowOf x).val < n0) (m.filter fun x => ¬ (rowOf x).val < n0)
    (fun x hx => by
      rw [Finsupp.support_filter, Finset.mem_filter] at hx
      exact hx.2)
    (fun x hx => by
      rw [Finsupp.support_filter, Finset.mem_filter] at hx
      exact hx.2)
  rw [hab] at hsplit
  rw [hsplit] at hmG
  have hb := right_ne_zero_of_mul hmG
  have hrow := rowDeg_of_mem (L * y) y m hm
  rw [hHd _ (fun x hx => by
      rw [Finsupp.support_filter, Finset.mem_filter] at hx
      exact not_lt.1 hx.2)
    (fun ρ _ => ⟨(rowDeg_filter_le _ m ρ).1.trans (hrow ρ).1.le,
      (rowDeg_filter_le _ m ρ).2.trans (hrow ρ).2.le⟩)] at hb
  split_ifs at hb with hbeq
  · exact hbeq
  · exact absurd rfl hb
end GlobalTheory.DiagBlock
end
end

set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution : BlockJet := by
  intro C _ _ n0 n hn L y G1 H hG1 hH hHd
  classical
  have hkill := kill_detL_pow_mul_detR_pow (C := C) hn L y
    (fun x : PVar n => n0 ≤ (rowOf x).val ∧ Sum.elim Prod.snd Prod.snd x ≠ rowOf x)
    (fun ρ c => Iff.rfl) (fun ρ c => Iff.rfl)
  have havoid : ∀ m : PVar n →₀ ℕ, MvPolynomial.coeff m (detL C n ^ (L * y) * detR C n ^ y) ≠ 0 →
      MvPowerSeries.coeff m (G1 * H) ≠ 0 →
      ∀ x, (n0 ≤ (rowOf x).val ∧ Sum.elim Prod.snd Prod.snd x ≠ rowOf x) → m x = 0 := by
    intro m hm hmG x hx
    have hb := filter_nondiag_eq_diagMon_of_coeff_ne_zero L y G1 H hG1 hH hHd m hm hmG
    have hmx : m x = (m.filter fun x => ¬ (rowOf x).val < n0) x := by
      rw [Finsupp.filter_apply, if_pos (not_lt.2 hx.1)]
    rw [hmx, hb]
    rcases x with ⟨ρ, c⟩ | ⟨ρ, c⟩
    · rw [diagMon_inl, if_neg]
      rintro ⟨-, rfl⟩
      exact hx.2 rfl
    · rw [diagMon_inr, if_neg]
      rintro ⟨-, rfl⟩
      exact hx.2 rfl
  have h3 : jetAt0 (detL C n ^ (L * y) * detR C n ^ y) (G1 * H) =
      jetAt0 (kill (fun x : PVar n => n0 ≤ (rowOf x).val ∧ Sum.elim Prod.snd Prod.snd x ≠ rowOf x)
        (detL C n ^ (L * y) * detR C n ^ y)) (G1 * H) := by
    rw [GlobalTheory.UnitCase.jetAt0_eq_sum (kill (fun x : PVar n => n0 ≤ (rowOf x).val ∧
      Sum.elim Prod.snd Prod.snd x ≠ rowOf x) (detL C n ^ (L * y) * detR C n ^ y)) (G1 * H)
      (detL C n ^ (L * y) * detR C n ^ y).support ?_, jetAt0]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_kill]
      split_ifs with h
      · rfl
      · by_cases h0 : MvPowerSeries.coeff m (G1 * H) = 0
        · simp [h0]
        · by_cases h1 : MvPolynomial.coeff m (detL C n ^ (L * y) * detR C n ^ y) = 0
          · simp [h1]
          · exact absurd (havoid m h1 h0) h
    · intro m hm
      rw [MvPolynomial.mem_support_iff, coeff_kill] at hm
      rw [MvPolynomial.mem_support_iff]
      split_ifs at hm
      · exact hm
      · exact absurd rfl hm
  rw [h3, hkill]
  have hsupp : (MvPolynomial.rename (embV hn) (detL C n0 ^ (L * y) * detR C n0 ^ y) *
      MvPolynomial.monomial (diagMon n0 n L y) (1 : C)).support ⊆
      (detL C n0 ^ (L * y) * detR C n0 ^ y).support.image
        (fun u => u.mapDomain (embV hn) + diagMon n0 n L y) := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul_monomial'] at hm
    split_ifs at hm with hle
    · rw [mul_one] at hm
      have hm' : m - diagMon n0 n L y ∈
          (MvPolynomial.rename (embV hn) (detL C n0 ^ (L * y) * detR C n0 ^ y)).support :=
        MvPolynomial.mem_support_iff.2 hm
      rw [MvPolynomial.support_rename_of_injective (embV_inj hn), Finset.mem_image] at hm'
      obtain ⟨u, hu, hue⟩ := hm'
      exact Finset.mem_image.2 ⟨u, hu, by rw [hue, tsub_add_cancel_of_le hle]⟩
    · exact absurd rfl hm
  rw [GlobalTheory.UnitCase.jetAt0_eq_sum _ _ _ hsupp,
    Finset.sum_image (fun u _ v _ h => Finsupp.mapDomain_injective (embV_inj hn) (add_right_cancel h)),
    jetAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MvPolynomial.coeff_mul_monomial, mul_one, MvPolynomial.coeff_rename_mapDomain _ (embV_inj hn)]
  have hU : ∀ x ∈ (u.mapDomain (embV hn)).support, (rowOf x).val < n0 := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    rcases v with ⟨b, c⟩ | ⟨b, c⟩
    · exact b.isLt
    · exact b.isLt
  have hDrow : ∀ x ∈ (diagMon n0 n L y).support, ¬ (rowOf x).val < n0 :=
    fun x hx => not_lt.2 (diagMon_row x hx)
  rw [coeff_mul_split (fun x => (rowOf x).val < n0) G1 H hG1
    (fun m hm x hx => not_lt.2 (hH m hm x hx)) _ _ hU hDrow]
  have hHD : MvPowerSeries.coeff (diagMon n0 n L y) H = 1 := by
    rw [hHd _ (fun x hx => diagMon_row x hx) (fun ρ hρ => ⟨by simp [rowDegZ, diagMon_inl, hρ],
      by simp [rowDegZ', diagMon_inr, hρ]⟩), if_pos rfl]
  have hdisj : Disjoint (u.mapDomain (embV hn)).support (diagMon n0 n L y).support :=
    Finset.disjoint_left.2 fun x hx1 hx2 => hDrow x hx2 (hU x hx1)
  have hmf : mfact (u.mapDomain (embV hn) + diagMon n0 n L y) =
      mfact u * ((L * y).factorial * y.factorial) ^ (n - n0) := by
    rw [← mfact_diagMon, mfact, mfact, mfact, Finsupp.prod_add_index_of_disjoint hdisj,
      Finsupp.prod_mapDomain_index_inj (embV_inj hn)]
  have hr : MvPowerSeries.coeff u (restr hn G1) = MvPowerSeries.coeff (u.mapDomain (embV hn)) G1 := rfl
  rw [hHD, mul_one, hmf, hr]
  push_cast
  ring
end GlobalTheory.DiagBlock
