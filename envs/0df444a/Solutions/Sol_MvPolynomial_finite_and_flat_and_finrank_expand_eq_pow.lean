-- Prove2me | solution 1 for MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/458bec41-bd5d-5f5d-abae-4f324d0bf781

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow

set_option autoImplicit false

open MvPolynomial

namespace FrobRankC2

theorem finite_flat_finrank_of_unique_decomposition
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type*} [Fintype ι] (b : ι → S)
    (hex : ∀ s : S, ∃ c : ι → R, ∑ i, f (c i) * b i = s)
    (huniq : ∀ c : ι → R, ∑ i, f (c i) * b i = 0 → ∀ i, c i = 0) :
    f.Finite ∧ f.Flat ∧ ∀ q, f.finrank q = Fintype.card ι := by
  letI : Algebra R S := f.toAlgebra
  have hsmul : ∀ (r : R) (s : S), r • s = f r * s := fun r s => Algebra.smul_def r s
  have hli : LinearIndependent R b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    apply huniq
    simpa [hsmul] using hg
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := by
    rintro s -
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨c, hc⟩ := hex s
    exact ⟨c, by simpa [hsmul] using hc⟩
  let B : Module.Basis ι R S := Module.Basis.mk hli hsp
  haveI : Module.Free R S := Module.Free.of_basis B
  haveI : Module.Finite R S := Module.Finite.of_basis B
  refine ⟨‹Module.Finite R S›, (inferInstance : Module.Flat R S), fun q => ?_⟩
  haveI : Nontrivial R := q.nontrivial
  change Module.rankAtStalk S q = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Module.finrank_eq_card_basis B,
    Nat.cast_id]

section

variable {σ : Type*} (p : ℕ)

noncomputable def divP (e : σ →₀ ℕ) : σ →₀ ℕ := e.mapRange (· / p) (by simp)

@[scoped simp] lemma divP_apply (e : σ →₀ ℕ) (i : σ) : divP p e i = e i / p := by
  simp [divP]

variable [Finite σ]

noncomputable def ofRes (r : σ → Fin p) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (r i : ℕ))

@[scoped simp] lemma ofRes_apply (r : σ → Fin p) (i : σ) : ofRes p r i = (r i : ℕ) := by
  simp [ofRes]

variable {p} (hp : 0 < p)
include hp

def modP (e : σ →₀ ℕ) : σ → Fin p := fun i => ⟨e i % p, Nat.mod_lt _ hp⟩

omit [Finite σ] in
@[scoped simp] lemma modP_apply (e : σ →₀ ℕ) (i : σ) : (modP hp e i : ℕ) = e i % p := rfl

lemma decomp (e : σ →₀ ℕ) : p • divP p e + ofRes p (modP hp e) = e := by
  ext i
  simp [Nat.div_add_mod]

lemma divP_add (d : σ →₀ ℕ) (r : σ → Fin p) : divP p (p • d + ofRes p r) = d := by
  ext i
  simp only [divP_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ofRes_apply]
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (r i).isLt, Nat.zero_add]

lemma modP_add (d : σ →₀ ℕ) (r : σ → Fin p) : modP hp (p • d + ofRes p r) = r := by
  funext i
  apply Fin.ext
  simp only [modP_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ofRes_apply]
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r i).isLt]

lemma le_and_dvd_iff (e : σ →₀ ℕ) (r : σ → Fin p) :
    (ofRes p r ≤ e ∧ ∀ i, p ∣ (e - ofRes p r) i) ↔ modP hp e = r := by
  constructor
  · rintro ⟨hle, hdvd⟩
    funext i
    apply Fin.ext
    simp only [modP_apply]
    have h1 : (r i : ℕ) ≤ e i := by simpa using hle i
    have h2 : p ∣ e i - r i := by simpa using hdvd i
    obtain ⟨k, hk⟩ := h2
    have : e i = r i + p * k := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r i).isLt]
  · rintro rfl
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simpa using Nat.mod_le (e i) p
    · refine ⟨e i / p, ?_⟩
      simp only [Finsupp.coe_tsub, Pi.sub_apply, ofRes_apply, modP_apply]
      have := Nat.div_add_mod (e i) p
      omega

lemma sub_ofRes_modP (e : σ →₀ ℕ) : e - ofRes p (modP hp e) = p • divP p e := by
  ext i
  simp only [Finsupp.coe_tsub, Pi.sub_apply, ofRes_apply, modP_apply, Finsupp.coe_smul,
    Pi.smul_apply, divP_apply, smul_eq_mul]
  have := Nat.div_add_mod (e i) p
  omega

end

section

variable {R : Type*} [CommRing R] {σ : Type*} [Finite σ] {p : ℕ} (hp : 0 < p)
include hp

noncomputable def bvec (r : σ → Fin p) : MvPolynomial σ R := monomial (ofRes p r) 1

omit hp in
lemma bvec_def (r : σ → Fin p) : (bvec r : MvPolynomial σ R) = monomial (ofRes p r) 1 := rfl

lemma coeff_expand_mul_bvec [DecidableEq (σ → Fin p)]
    (c : MvPolynomial σ R) (r : σ → Fin p) (e : σ →₀ ℕ) :
    coeff e (expand p c * bvec r) = if modP hp e = r then coeff (divP p e) c else 0 := by
  classical
  rw [bvec_def, coeff_mul_monomial', mul_one]
  by_cases hr : modP hp e = r
  · rw [if_pos hr]
    have hle : ofRes p r ≤ e := ((le_and_dvd_iff hp e r).mpr hr).1
    rw [if_pos hle]
    subst hr
    rw [sub_ofRes_modP hp e, coeff_expand_smul _ hp.ne']
  · rw [if_neg hr]
    split_ifs with hle
    · have : ¬ ∀ i, p ∣ (e - ofRes p r) i := fun h => hr ((le_and_dvd_iff hp e r).mp ⟨hle, h⟩)
      push Not at this
      obtain ⟨i, hi⟩ := this
      exact coeff_expand_of_not_dvd _ hi
    · rfl

end

section

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {p : ℕ} (hp : 0 < p)
include hp

noncomputable def Ψ (c : (σ → Fin p) → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ r, expand p (c r) * bvec r

omit hp in
lemma Ψ_def (c : (σ → Fin p) → MvPolynomial σ R) :
    Ψ c = ∑ r, expand p (c r) * bvec r := rfl

lemma coeff_Ψ (c : (σ → Fin p) → MvPolynomial σ R) (e : σ →₀ ℕ) :
    coeff e (Ψ c) = coeff (divP p e) (c (modP hp e)) := by
  classical
  rw [Ψ_def, coeff_sum]
  simp_rw [coeff_expand_mul_bvec hp]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

lemma Ψ_eq_zero (c : (σ → Fin p) → MvPolynomial σ R) (h : Ψ c = 0) : ∀ r, c r = 0 := by
  intro r
  ext d
  have := coeff_Ψ hp c (p • d + ofRes p r)
  rw [h, coeff_zero, divP_add hp, modP_add hp] at this
  simpa using this.symm

lemma Ψ_surjective (s : MvPolynomial σ R) : ∃ c : (σ → Fin p) → MvPolynomial σ R, Ψ c = s := by
  classical
  refine ⟨fun r => ∑ e ∈ s.support,
    if modP hp e = r then monomial (divP p e) (coeff e s) else 0, ?_⟩
  ext e
  rw [coeff_Ψ hp]
  rw [coeff_sum]
  simp_rw [apply_ite (coeff (R := R) (divP p e)), coeff_monomial, coeff_zero]

  have key : ∀ e' : σ →₀ ℕ,
      (if modP hp e' = modP hp e then (if divP p e' = divP p e then coeff e' s else 0) else 0) =
        if e' = e then coeff e' s else 0 := by
    intro e'
    by_cases h : e' = e
    · subst h
      simp
    · rw [if_neg h]
      by_cases h1 : modP hp e' = modP hp e
      · rw [if_pos h1, if_neg]
        intro h2
        apply h
        rw [← decomp hp e', ← decomp hp e, h1, h2]
      · rw [if_neg h1]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · exact (notMem_support_iff.mp hmem).symm

end

theorem main (R : Type*) [CommRing R] (σ : Type*) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (expand p (σ := σ) (R := R)).toRingHom.Finite ∧
    (expand p (σ := σ) (R := R)).toRingHom.Flat ∧
    ∀ q, (expand p (σ := σ) (R := R)).toRingHom.finrank q = p ^ Nat.card σ := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  have h := finite_flat_finrank_of_unique_decomposition
    (expand p (σ := σ) (R := R)).toRingHom (ι := σ → Fin p) (bvec (R := R))
    (fun s => by
      obtain ⟨c, hc⟩ := Ψ_surjective hp s
      exact ⟨c, hc⟩)
    (fun c hc => Ψ_eq_zero hp c hc)
  refine ⟨h.1, h.2.1, fun q => ?_⟩
  rw [h.2.2 q, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]

end FrobRankC2
p2m_reactivate "P2MW.S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow.FrobRankC2"

universe u v

theorem solution
    (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Finite ∧
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Flat ∧
    ∀ q : PrimeSpectrum (MvPolynomial σ R),
      (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.finrank q = p ^ Nat.card σ :=
  FrobRankC2.main R σ p hp

end S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow
end P2MW
export P2MW.S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow (solution)
