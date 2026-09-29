-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_seq_not_mem_injective_under_forall_exists_under_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9ba75efd-1930-5821-bdc4-e4d79bf41da3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_seq_not_mem_injective_under_forall_exists_under_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace RecAux

theorem infinite_heightOneSpectrum (L : Type) [Field L] [NumberField L] : Infinite (HeightOneSpectrum (𝓞 L)) := by
  classical
  have key : ∀ p : {p : ℕ // p.Prime}, ∃ v : HeightOneSpectrum (𝓞 L),
      v.asIdeal.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p.1 : ℤ)} := by
    intro p
    have hp : Prime (p.1 : ℤ) := Nat.prime_iff_prime_int.mp p.2
    haveI hmax : (Ideal.span {(p.1 : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hinj : Function.Injective (algebraMap ℤ (𝓞 L)) := (algebraMap ℤ (𝓞 L)).injective_int
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p.1 : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
    refine ⟨⟨Q, hQmax.isPrime, ?_⟩, hQ⟩
    intro hQbot
    rw [hQbot, Ideal.comap_bot_of_injective _ hinj] at hQ
    exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp hQ.symm)
  choose f hf using key
  haveI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
  refine Infinite.of_injective f fun p q hpq => ?_
  apply Subtype.ext
  have h : Ideal.span {(p.1 : ℤ)} = Ideal.span {(q.1 : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have hmem : (p.1 : ℤ) ∈ Ideal.span {(q.1 : ℤ)} := by rw [← h]; exact Ideal.mem_span_singleton_self _
  have hd : q.1 ∣ p.1 := Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hmem)
  exact ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hd).symm

theorem countable_heightOneSpectrum (K : Type) [Field K] [NumberField K] : Countable (HeightOneSpectrum (𝓞 K)) := by
  have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
    have hsub : (Set.univ : Set (Ideal (𝓞 K))) ⊆ ⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ n} := by
      intro I _
      exact Set.mem_iUnion.mpr ⟨Ideal.absNorm I, show Ideal.absNorm I ≤ Ideal.absNorm I from le_rfl⟩
    exact (Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_le n).countable).mono hsub
  haveI : Countable (Ideal (𝓞 K)) := Set.countable_univ_iff.mp hc
  exact Function.Injective.countable fun v w (h : v.asIdeal = w.asIdeal) => HeightOneSpectrum.ext h

theorem finite_fibre_under (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w = v}.Finite := by
  haveI := v.isMaximal
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)
  refine (hfin.preimage (f := HeightOneSpectrum.asIdeal) fun x _ y _ h => HeightOneSpectrum.ext h).subset ?_
  intro w hw
  refine ⟨w.isPrime, ⟨?_⟩⟩
  rw [← hw]
  rfl

theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ rec : ℕ → HeightOneSpectrum (𝓞 L), (∀ k, rec k ∉ SL) ∧
      (Function.Injective fun k => HeightOneSpectrum.under (𝓞 K) (rec k)) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        ∃ k, HeightOneSpectrum.under (𝓞 K) (rec k) = HeightOneSpectrum.under (𝓞 K) w := by
  classical
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ w : HeightOneSpectrum (𝓞 L), w ∉ SL ∧ HeightOneSpectrum.under (𝓞 K) w = v}
  have hmemT : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → HeightOneSpectrum.under (𝓞 K) w ∈ T :=
    fun w hw => ⟨w, hw, rfl⟩
  have hTinf : T.Infinite := by
    intro hTfin
    haveI := infinite_heightOneSpectrum L
    have hcov : ((↑SL : Set (HeightOneSpectrum (𝓞 L)))ᶜ) ⊆
        ⋃ v ∈ T, {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w = v} := by
      intro w hw
      exact Set.mem_biUnion (hmemT w hw) rfl
    have hfin : ((↑SL : Set (HeightOneSpectrum (𝓞 L)))ᶜ).Finite :=
      (hTfin.biUnion fun v _ => finite_fibre_under K L v).subset hcov
    have huniv : (Set.univ : Set (HeightOneSpectrum (𝓞 L))).Finite := by
      rw [← Set.union_compl_self (↑SL : Set (HeightOneSpectrum (𝓞 L)))]
      exact SL.finite_toSet.union hfin
    exact Set.infinite_univ huniv
  haveI : Infinite T := hTinf.to_subtype
  haveI : Countable (HeightOneSpectrum (𝓞 K)) := countable_heightOneSpectrum K
  haveI : Encodable T := Encodable.ofCountable T
  haveI : Denumerable T := Denumerable.ofEncodableOfInfinite T
  let e : ℕ ≃ T := (Denumerable.eqv T).symm
  have hmem : ∀ k : ℕ, ∃ w : HeightOneSpectrum (𝓞 L), w ∉ SL ∧
      HeightOneSpectrum.under (𝓞 K) w = ((e k : T) : HeightOneSpectrum (𝓞 K)) := fun k => (e k).2
  choose rec hrec1 hrec2 using hmem
  refine ⟨rec, hrec1, ?_, ?_⟩
  · intro k₁ k₂ h
    have h' : HeightOneSpectrum.under (𝓞 K) (rec k₁) = HeightOneSpectrum.under (𝓞 K) (rec k₂) := h
    rw [hrec2 k₁, hrec2 k₂] at h'
    exact e.injective (Subtype.ext h')
  · intro w hw
    refine ⟨e.symm ⟨HeightOneSpectrum.under (𝓞 K) w, hmemT w hw⟩, ?_⟩
    rw [hrec2, Equiv.apply_symm_apply]

end RecAux

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ rec : ℕ → HeightOneSpectrum (𝓞 L), (∀ k, rec k ∉ SL) ∧
      (Function.Injective fun k => HeightOneSpectrum.under (𝓞 K) (rec k)) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        ∃ k, HeightOneSpectrum.under (𝓞 K) (rec k) = HeightOneSpectrum.under (𝓞 K) w :=
  RecAux.main K L SL

end S_IsDedekindDomain_HeightOneSpectrum_exists_seq_not_mem_injective_under_forall_exists_under_eq
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_seq_not_mem_injective_under_forall_exists_under_eq (solution)
