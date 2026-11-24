-- Prove2me | solution 1 for GlobalTheory.NoetherInt.exists_primitive_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:24.897495+00:00
-- url     : https://prove2.me/submissions/a3be0361-f97d-44ab-b9c5-95790c33cfa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap

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
    {n : ℕ} (y : Fin n → S) (g : MvPolynomial (Fin n) ℤ) (hg0 : g ≠ 0)
    (hg : aeval y g = 0) (I : Ideal ℤ) (hI : I ≠ ⊤) :
    ∃ g₀ : MvPolynomial (Fin n) ℤ, aeval y g₀ = 0 ∧ ∃ v, g₀.coeff v ∉ I := by
  classical
  have hs : g.support.Nonempty := support_nonempty.mpr hg0
  obtain ⟨b, hb, hgcd⟩ := Finset.extract_gcd (fun v => g.coeff v) hs
  set d := g.support.gcd (fun v => g.coeff v) with hd
  have hd0 : d ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := hs
    have := (Finset.gcd_eq_zero_iff.mp h) v hv
    exact (mem_support_iff.mp hv) this
  let g₀ : MvPolynomial (Fin n) ℤ := ∑ v ∈ g.support, monomial v (b v)
  have hc : ∀ v, v ∈ g.support → g₀.coeff v = b v := by
    intro v hv
    simp [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hv]
  have hc' : ∀ v, v ∉ g.support → g₀.coeff v = 0 := by
    intro v hv
    simp only [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    exact Finset.sum_eq_zero fun w hw => if_neg (fun h : w = v => hv (h ▸ hw))
  have hgd : g = MvPolynomial.C d * g₀ := by
    ext v
    rw [MvPolynomial.coeff_C_mul]
    by_cases hv : v ∈ g.support
    · rw [hc v hv]; exact hb v hv
    · rw [hc' v hv, mul_zero]; exact notMem_support_iff.mp hv
  refine ⟨g₀, ?_, ?_⟩
  · have h1 : ((d : ℤ) : S) * aeval y g₀ = 0 := by
      rw [hgd, map_mul] at hg
      simpa using hg
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hd0)
  · by_contra hall
    push_neg at hall
    obtain ⟨l, hl⟩ := (IsPrincipalIdealRing.principal I).principal
    have hdvd : l ∣ g.support.gcd b := Finset.dvd_gcd fun v hv => by
      have := hall v
      rw [hc v hv, hl] at this
      exact Ideal.mem_span_singleton.mp this
    rw [hgcd] at hdvd
    exact hI (by rw [hl]; exact Ideal.span_singleton_eq_top.mpr (isUnit_of_dvd_one hdvd))
end GlobalTheory.NoetherInt
