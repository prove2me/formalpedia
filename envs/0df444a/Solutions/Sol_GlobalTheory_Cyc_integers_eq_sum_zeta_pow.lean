-- Prove2me | solution 1 for GlobalTheory.Cyc.integers_eq_sum_zeta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:53.5888+00:00
-- url     : https://prove2.me/submissions/b97f2829-7a65-4aa9-b209-7eecb77a27b1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
import Theorems.Thm_GlobalTheory_Cyc_IntBasis_term_le
import Theorems.Thm_GlobalTheory_Cyc_IntBasis_coeff_le
import Theorems.Thm_GlobalTheory_Cyc_IntBasis_exists_poly
import Theorems.Thm_P2M_GlobalTheory_Cyc_IntBasis_aeval_taylor__c8bfdf8dc923
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
namespace GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]
end GlobalTheory.Cyc.IntBasis
private lemma norm_coeff_taylor_le_one {l : ℕ} [Fact l.Prime] {F : IntermediateField ℚ_[l] (Om l)}
    (g : (↥F)[X]) (r : F) (hr : ‖(r : Om l)‖ ≤ 1) (hg : ∀ b, ‖(g.coeff b : Om l)‖ ≤ 1) (n : ℕ) :
    ‖((taylor r g).coeff n : Om l)‖ ≤ 1 := by
  rw [taylor_coeff, eval_eq_sum_range]
  push_cast
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro m _
  rw [hasseDeriv_coeff]
  push_cast
  rw [norm_mul, norm_mul, norm_pow]
  have h1 := IsUltrametricDist.norm_natCast_le_one (Om l) ((m + n).choose n)
  exact mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) (hg _)) (by positivity)
    (pow_le_one₀ (norm_nonneg _) hr)
private lemma aeval_eq_sum_range_of_natDegree_lt {l : ℕ} [Fact l.Prime] {F : IntermediateField ℚ_[l] (Om l)}
    (q : (↥F)[X]) {n : ℕ} (hq : q.natDegree < n) (w : Om l) :
    aeval w q = ∑ b ∈ Finset.range n, (q.coeff b : Om l) * w ^ b := by
  rw [aeval_eq_sum_range' hq]
  simp [Algebra.smul_def]
end

set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory.Cyc.IntBasis
namespace GlobalTheory.Cyc
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (i : ℕ), 2 ≤ i → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ i) → (∀ x : Om l, x ∈ Ks K i → ‖x‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1) ∧ ‖y a‖ ≤ 1) ∧ x = ∑ a : Fin l, ζ ^ (a : ℕ) * y a) ∧ ∀ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1)) → ∑ a : Fin l, ζ ^ (a : ℕ) * y a = 0 → ∀ a, y a = 0 := by
  intro l _ K i hi ζ hζ
  have hlp : l.Prime := Fact.out
  have hζ1 : ζ ≠ 1 := hζ.ne_one (Nat.one_lt_pow (by omega) hlp.one_lt)
  constructor
  · intro x hx hx1
    obtain ⟨p, hpdeg, hpx⟩ := exists_poly K i hi ζ hζ x hx
    set Q := taylor (1 : ↥(Ks K (i - 1))) p with hQ
    have hQdeg : Q.natDegree < l := by rw [hQ, natDegree_taylor]; exact hpdeg
    have hQx : x = ∑ b ∈ Finset.range l, (Q.coeff b : Om l) * (ζ - 1) ^ b := by
      rw [← aeval_eq_sum_range_of_natDegree_lt Q hQdeg, hQ, aeval_taylor', ← hpx]
      simp
    have hQc : ∀ b, ‖(Q.coeff b : Om l)‖ ≤ 1 := by
      intro b
      by_cases hb : b < l
      · apply coeff_le K i hi ζ hζ _ (Q.coeff b).2 b hb
        calc _ ≤ ‖∑ c ∈ Finset.range l, (Q.coeff c : Om l) * (ζ - 1) ^ c‖ :=
              term_le K i hi ζ hζ (fun c => (Q.coeff c : Om l)) (fun c => (Q.coeff c).2) b hb
          _ = ‖x‖ := by rw [← hQx]
          _ ≤ 1 := hx1
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    have hpQ : p = taylor (-1 : ↥(Ks K (i - 1))) Q := by
      rw [hQ, taylor_taylor]
      simp
    refine ⟨fun a => (p.coeff a : Om l), fun a => ⟨(p.coeff a).2, ?_⟩, ?_⟩
    · rw [hpQ]
      exact norm_coeff_taylor_le_one Q (-1) (by simp) hQc a
    · rw [← hpx, aeval_eq_sum_range_of_natDegree_lt p hpdeg,
        ← Fin.sum_univ_eq_sum_range (fun a => (p.coeff a : Om l) * ζ ^ a)]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  · intro y hy hsum
    set c : Fin l → ↥(Ks K (i - 1)) := fun a => ⟨y a, hy a⟩ with hc
    set P : (↥(Ks K (i - 1)))[X] := ∑ a : Fin l, C (c a) * X ^ (a : ℕ) with hP
    have hPdeg : P.natDegree < l := by
      by_cases hP0 : P = 0
      · rw [hP0, natDegree_zero]
        exact hlp.pos
      · exact (natDegree_lt_iff_degree_lt hP0).2 (degree_sum_fin_lt c)
    have hPcoeff : ∀ a : Fin l, (P.coeff a : Om l) = y a := by
      intro a
      simp [hP, Fin.val_inj, hc]
    have hPζ : aeval ζ P = 0 := by
      rw [aeval_eq_sum_range_of_natDegree_lt P hPdeg,
        ← Fin.sum_univ_eq_sum_range (fun a => (P.coeff a : Om l) * ζ ^ a), ← hsum]
      exact Finset.sum_congr rfl (fun a _ => by rw [hPcoeff a, mul_comm])
    set Q := taylor (1 : ↥(Ks K (i - 1))) P with hQ
    have hQdeg : Q.natDegree < l := by rw [hQ, natDegree_taylor]; exact hPdeg
    have hQ0 : ∑ b ∈ Finset.range l, (Q.coeff b : Om l) * (ζ - 1) ^ b = 0 := by
      rw [← aeval_eq_sum_range_of_natDegree_lt Q hQdeg, hQ, aeval_taylor']
      simpa using hPζ
    have hQz : Q = 0 := by
      refine Polynomial.ext fun b => ?_
      rw [coeff_zero]
      by_cases hb : b < l
      · have h1 := term_le K i hi ζ hζ (fun c => (Q.coeff c : Om l)) (fun c => (Q.coeff c).2) b hb
        rw [hQ0, norm_zero] at h1
        have h2 : (Q.coeff b : Om l) * (ζ - 1) ^ b = 0 := norm_le_zero_iff.1 h1
        have h3 : (ζ - 1) ^ b ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hζ1)
        have h4 : (Q.coeff b : Om l) = 0 := (mul_eq_zero.1 h2).resolve_right h3
        exact_mod_cast h4
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hP0 : P = 0 := taylor_injective (1 : ↥(Ks K (i - 1))) (by rw [← hQ, hQz, map_zero])
    intro a
    rw [← hPcoeff a, hP0, coeff_zero]
    rfl
end GlobalTheory.Cyc
