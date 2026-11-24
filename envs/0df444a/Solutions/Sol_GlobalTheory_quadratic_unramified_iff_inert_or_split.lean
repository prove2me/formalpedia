-- Prove2me | solution 1 for GlobalTheory.quadratic_unramified_iff_inert_or_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:39.113826+00:00
-- url     : https://prove2.me/submissions/62fb8212-d84e-482d-b79e-662479eb4fa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuadraticUnramifiedIffInertOrSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
open GlobalTheory
open scoped TensorProduct
open NumberField IsDedekindDomain
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔
      ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨
        (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by
  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) with hIdef
  set M := UniqueFactorizationMonoid.normalizedFactors I with hMdef
  set s := IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) with hsdef
  have hv : v.asIdeal ≠ ⊥ := v.ne_bot
  have hI : I ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.mpr hv
  have hs : ∀ P, P ∈ s ↔ P ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P => IsDedekindDomain.mem_primesOverFinset_iff hv (𝓞 E)
  have hM : ∀ P, P ∈ v.asIdeal.primesOver (𝓞 E) ↔ P ∈ M :=
    fun P => Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 E) hv
  have hcount : ∀ P ∈ v.asIdeal.primesOver (𝓞 E), P.ramificationIdx (𝓞 F) = M.count P := by
    intro P hP
    haveI : P.LiesOver v.asIdeal := hP.2
    exact Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count v.asIdeal P hI
  have hsum : ∑ P ∈ s, P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P = 2 := by
    rw [← h2, ← Ideal.sum_ramification_inertia (𝓞 E) F E hv]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP' := (hs P).1 hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver v.asIdeal := hP'.2
    rw [Ideal.ramificationIdx_eq_ramificationIdx' v.asIdeal P hv]
  have hterm : ∀ P ∈ s, 1 ≤ P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P := by
    intro P hP
    have hP' := (hs P).1 hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver v.asIdeal := hP'.2
    have h1 : 0 < P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos P (𝓞 F)
    have h2 : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1.ne' h2.ne')
  have hncard : (v.asIdeal.primesOver (𝓞 E)).ncard = s.card := by
    rw [← Set.ncard_coe_finset, hsdef, IsDedekindDomain.coe_primesOverFinset hv]
  have hcard_le : s.card ≤ 2 := by
    have := Finset.card_nsmul_le_sum s _ 1 hterm
    simpa [hsum] using this
  have hcard_pos : 0 < s.card := by
    rw [← hncard]
    exact Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
  have hU : (∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ∀ P ∈ s, P.ramificationIdx (𝓞 F) = 1 := by
    constructor
    · intro h P hP
      have hP' := (hs P).1 hP
      haveI : P.IsPrime := hP'.1
      haveI : P.LiesOver v.asIdeal := hP'.2
      have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv P
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (h ⟨P, hP'.1, hPb⟩ hP'.2)
    · intro h w hw
      have hmem : w.asIdeal ∈ s := (hs _).2 ⟨w.isPrime, hw⟩
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.2 (h _ hmem)
  rw [hU, hncard]
  have hI0 : I ≠ 0 := hI
  constructor
  · intro he
    by_cases h2c : s.card = 2
    · exact Or.inr h2c
    left
    have h1 : s.card = 1 := by omega
    obtain ⟨P, hsP⟩ := Finset.card_eq_one.1 h1
    have hPs : P ∈ s := by simp [hsP]
    have hallM : ∀ Q ∈ M, Q = P := by
      intro Q hQ
      have : Q ∈ s := (hs Q).2 ((hM Q).2 hQ)
      simpa [hsP] using this
    have hcP : M.count P = 1 := by
      rw [← hcount P ((hs P).1 hPs)]
      exact he P hPs
    have hcardM : M.card = 1 := by
      rw [← hcP]
      exact (Multiset.count_eq_card.2 fun x hx => (hallM x hx).symm).symm
    have hMP : M = {P} := by
      rw [Multiset.eq_replicate_of_mem hallM, hcardM, Multiset.replicate_one]
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hI0
    rw [← hMdef, hMP, Multiset.prod_singleton] at hassoc
    rw [← associated_iff_eq.1 hassoc]
    exact ((hs P).1 hPs).1
  · rintro (hp | h2c)
    · intro P hP
      have hirr : Irreducible I := (Ideal.prime_of_isPrime hI hp).irreducible
      have hMI : M = {I} := by
        rw [hMdef, UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, normalize_eq]
      have hPI : P = I := by
        have := (hM P).1 ((hs P).1 hP)
        rw [hMI] at this
        simpa using this
      rw [hcount P ((hs P).1 hP), hMI, hPI, Multiset.count_singleton_self]
    · intro P hP
      by_contra hne
      have hP' := (hs P).1 hP
      haveI : P.IsPrime := hP'.1
      haveI : P.LiesOver v.asIdeal := hP'.2
      have he : 0 < P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos P (𝓞 F)
      have hf : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
      have hge : 2 * 1 ≤ P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P :=
        Nat.mul_le_mul (by omega) hf
      have hrest := Finset.card_nsmul_le_sum (s.erase P) _ 1
        (fun Q hQ => hterm Q (Finset.mem_of_mem_erase hQ))
      rw [← Finset.add_sum_erase s _ hP] at hsum
      rw [Finset.card_erase_of_mem hP, h2c] at hrest
      simp only [smul_eq_mul, mul_one] at hrest
      omega
end _root_.GlobalTheory
end GlobalTheory
