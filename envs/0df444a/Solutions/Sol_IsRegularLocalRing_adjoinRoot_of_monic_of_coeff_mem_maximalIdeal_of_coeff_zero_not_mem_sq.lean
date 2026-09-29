-- Prove2me | solution 1 for IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cb495fc1-88e0-5c27-9338-23f44c13de8e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq

set_option autoImplicit false

open IsLocalRing Polynomial

namespace EisRegAux

open Order

section KrullDim

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]

def contr (Q : PrimeSpectrum B) : PrimeSpectrum A :=
  ⟨Q.asIdeal.comap (algebraMap A B), inferInstance⟩

lemma contr_asIdeal (Q : PrimeSpectrum B) : (contr (A := A) Q).asIdeal = Q.asIdeal.comap (algebraMap A B) := rfl

lemma contr_strictMono : StrictMono (contr (A := A) (B := B)) := by
  intro P Q hPQ
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hPQ ⊢
  rw [contr_asIdeal, contr_asIdeal]
  exact Ideal.IsIntegral.comap_lt_comap hPQ

lemma ringKrullDim_le_of_isIntegral : ringKrullDim B ≤ ringKrullDim A :=
  Order.krullDim_le_of_strictMono _ contr_strictMono

lemma exists_ltSeries_contr (hinj : Function.Injective (algebraMap A B)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum A)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum B), q.length = n ∧ contr q.last = p.last := by
  intro n
  induction n with
  | zero =>
      intro p hp
      haveI := p.last.isPrime
      obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal (⊥ : Ideal B)
        (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
      refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, ?_⟩
      exact PrimeSpectrum.ext hQc
  | succ n ih =>
      intro p hp
      have hne : p.length ≠ 0 := by omega
      obtain ⟨q', hq'len, hq'last⟩ := ih p.eraseLast (by simp [hp])
      have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last hne
      haveI := p.last.isPrime
      haveI := q'.last.isPrime
      obtain ⟨Q, hQge, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p.last.asIdeal q'.last.asIdeal
        (by rw [← contr_asIdeal, hq'last]; exact le_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt))
      have hlt' : q'.last < ⟨Q, hQ⟩ := by
        rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
        refine lt_of_le_of_ne hQge ?_
        intro heq
        have : contr (A := A) q'.last = p.last := PrimeSpectrum.ext (by rw [contr_asIdeal, heq, hQc])
        rw [hq'last] at this
        exact (ne_of_lt hlt) this
      refine ⟨q'.snoc ⟨Q, hQ⟩ hlt', by simp [hq'len], ?_⟩
      rw [RelSeries.last_snoc]
      exact PrimeSpectrum.ext hQc

lemma ringKrullDim_ge_of_isIntegral_of_injective (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hq, -⟩ := exists_ltSeries_contr hinj p.length p rfl
  rw [← hq]
  exact le_iSup (fun q : LTSeries (PrimeSpectrum B) => (q.length : WithBot ℕ∞)) q

lemma ringKrullDim_eq_of_isIntegral_of_injective (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A :=
  le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_ge_of_isIntegral_of_injective hinj)

end KrullDim

end EisRegAux

namespace EisRegAux

section AdjoinRootLemmas

variable {S : Type*} [CommRing S]

lemma exists_sub_algebraMap_mem_span_root (g : S[X]) (t : AdjoinRoot g) :
    ∃ c : S, t - algebraMap S (AdjoinRoot g) c ∈ Ideal.span {AdjoinRoot.root g} := by
  induction t using AdjoinRoot.induction_on with
  | ih p =>
    refine ⟨p.coeff 0, ?_⟩
    have e : p = X * p.divX + C (p.coeff 0) := by rw [mul_comm]; exact (Polynomial.divX_mul_X_add p).symm
    have : AdjoinRoot.mk g p = AdjoinRoot.root g * AdjoinRoot.mk g p.divX + algebraMap S (AdjoinRoot g) (p.coeff 0) := by
      conv_lhs => rw [e]
      rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    rw [this, add_sub_cancel_right]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

lemma algebraMap_coeff_zero_mem_span_root (g : S[X]) :
    algebraMap S (AdjoinRoot g) (g.coeff 0) ∈ Ideal.span {AdjoinRoot.root g} := by
  have h : AdjoinRoot.mk g g = 0 := AdjoinRoot.mk_self
  have e : g = X * g.divX + C (g.coeff 0) := by rw [mul_comm]; exact (Polynomial.divX_mul_X_add g).symm
  have h' : AdjoinRoot.root g * AdjoinRoot.mk g g.divX + algebraMap S (AdjoinRoot g) (g.coeff 0) = 0 := by
    have : AdjoinRoot.mk g (X * g.divX + C (g.coeff 0)) = 0 := by rw [← e]; exact AdjoinRoot.mk_self
    rw [AdjoinRoot.algebraMap_eq]
    rwa [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at this
  have : algebraMap S (AdjoinRoot g) (g.coeff 0) = -(AdjoinRoot.root g * AdjoinRoot.mk g g.divX) := by
    linear_combination h'
  rw [this]
  exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

lemma root_pow_natDegree_mem_map (g : S[X]) (hg : g.Monic) (I : Ideal S)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ I) :
    AdjoinRoot.root g ^ g.natDegree ∈ I.map (algebraMap S (AdjoinRoot g)) := by
  have h : AdjoinRoot.mk g g = 0 := AdjoinRoot.mk_self
  have h' : AdjoinRoot.root g ^ g.natDegree +
      ∑ i ∈ Finset.range g.natDegree, AdjoinRoot.mk g (C (g.coeff i) * X ^ i) = 0 := by
    have : AdjoinRoot.mk g (X ^ g.natDegree + ∑ i ∈ Finset.range g.natDegree, C (g.coeff i) * X ^ i) = 0 := by
      rw [← hg.as_sum]; exact AdjoinRoot.mk_self
    rwa [map_add, map_pow, AdjoinRoot.mk_X, map_sum] at this
  have : AdjoinRoot.root g ^ g.natDegree = -∑ i ∈ Finset.range g.natDegree, AdjoinRoot.mk g (C (g.coeff i) * X ^ i) := by
    linear_combination h'
  rw [this]
  refine Submodule.neg_mem _ (Ideal.sum_mem _ fun i hi => ?_)
  rw [map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoeff i (Finset.mem_range.mp hi)))

lemma algebraMap_injective_of_monic (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree) :
    Function.Injective (algebraMap S (AdjoinRoot g)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at ha
  by_contra hne
  exact hg.not_dvd_of_natDegree_lt (Polynomial.C_ne_zero.mpr hne) (by rw [natDegree_C]; omega) ha

end AdjoinRootLemmas

end EisRegAux

open EisRegAux in
theorem solution
    (S : Type*) [CommRing S] [IsRegularLocalRing S]
    (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ maximalIdeal S)
    (h0 : g.coeff 0 ∉ maximalIdeal S ^ 2) :
    IsRegularLocalRing (AdjoinRoot g) ∧ ringKrullDim (AdjoinRoot g) = ringKrullDim S := by
  classical
  haveI : Module.Finite S (AdjoinRoot g) := hg.finite_adjoinRoot
  haveI : Algebra.IsIntegral S (AdjoinRoot g) := Algebra.IsIntegral.of_finite S (AdjoinRoot g)
  have hinj : Function.Injective (algebraMap S (AdjoinRoot g)) := algebraMap_injective_of_monic g hg hn
  haveI : Nontrivial (AdjoinRoot g) := hinj.nontrivial

  set x : AdjoinRoot g := AdjoinRoot.root g with hx
  set φ : S →+* AdjoinRoot g := algebraMap S (AdjoinRoot g) with hφ
  set M : Ideal (AdjoinRoot g) := Ideal.span {x} ⊔ (maximalIdeal S).map φ with hM
  have hMle : ∀ Q : Ideal (AdjoinRoot g), Q.IsMaximal → M ≤ Q := by
    intro Q hQ
    have hQc : Q.comap φ = maximalIdeal S :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S) Q)
    have hmap : (maximalIdeal S).map φ ≤ Q := by rw [Ideal.map_le_iff_le_comap, hQc]
    refine sup_le ?_ hmap
    rw [Ideal.span_singleton_le_iff_mem]
    exact hQ.isPrime.mem_of_pow_mem _ (hmap (root_pow_natDegree_mem_map g hg _ hcoeff))
  have hM1 : M ≠ ⊤ := by
    obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (AdjoinRoot g)
    intro h
    exact hQ.ne_top (top_le_iff.mp (h ▸ hMle Q hQ))
  have hMmax : M.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => hM1 ((Ideal.eq_top_iff_one _).mpr h1), ?_⟩
    intro J t hMJ htM htJ
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_span_root g t
    have hcM : t - φ c ∈ M := Ideal.mem_sup_left hc
    have hcunit : IsUnit c := by
      by_contra hcu
      have hcm : c ∈ maximalIdeal S := hcu
      have : φ c ∈ M := Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hcm)
      have : t ∈ M := by simpa using Ideal.add_mem _ hcM this
      exact htM this
    have hcJ : φ c ∈ J := by
      have := J.sub_mem htJ (hMJ hcM)
      simpa using this
    rw [J.eq_top_of_isUnit_mem hcJ (hcunit.map φ)]
    trivial
  haveI hloc : IsLocalRing (AdjoinRoot g) :=
    IsLocalRing.of_unique_max_ideal ⟨M, hMmax, fun Q hQ => (hMmax.eq_of_le hQ.ne_top (hMle Q hQ)).symm⟩
  have hmaxT : maximalIdeal (AdjoinRoot g) = M := (IsLocalRing.eq_maximalIdeal hMmax).symm

  have hdim : ringKrullDim (AdjoinRoot g) = ringKrullDim S := ringKrullDim_eq_of_isIntegral_of_injective hinj

  obtain ⟨s, hscard, hsspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal S))
  have hsspan' : Ideal.span (s : Set S) = maximalIdeal S := hsspan
  have ha0 : g.coeff 0 ∈ Submodule.span S (s : Set S) := by rw [hsspan]; exact hcoeff 0 (by omega)
  obtain ⟨c, -, hcsum⟩ := Submodule.mem_span_finset.mp ha0
  have hex : ∃ j ∈ s, c j ∉ maximalIdeal S := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← hcsum, pow_two]
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [smul_eq_mul]
    exact Ideal.mul_mem_mul (hall i hi) (hsspan' ▸ Ideal.subset_span hi)
  obtain ⟨j, hj, hcj⟩ := hex
  have hcju : IsUnit (c j) := by
    by_contra h; exact hcj h
  set G : Finset (AdjoinRoot g) := insert x ((s.erase j).image φ) with hG
  have hxG : Ideal.span {x} ≤ Ideal.span (G : Set (AdjoinRoot g)) :=
    Ideal.span_mono (Set.singleton_subset_iff.mpr (by rw [hG, Finset.coe_insert]; exact Set.mem_insert _ _))
  have hiG : ∀ i ∈ s.erase j, φ i ∈ Ideal.span (G : Set (AdjoinRoot g)) := fun i hi =>
    Ideal.subset_span (by
      rw [hG, Finset.coe_insert, Finset.coe_image]
      exact Set.mem_insert_of_mem _ ⟨i, Finset.mem_coe.mpr hi, rfl⟩)
  have hMG : M = Ideal.span (G : Set (AdjoinRoot g)) := by
    apply le_antisymm
    · refine sup_le hxG ?_
      rw [← hsspan', Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      by_cases hij : i = j
      · subst hij
        have hrel : φ (c i) * φ i = φ (g.coeff 0) - ∑ k ∈ s.erase i, φ (c k) * φ k := by
          rw [← hcsum, map_sum, ← Finset.sum_erase_add _ _ hj]
          simp only [smul_eq_mul, map_mul, map_sum]
          ring
        obtain ⟨u, hu⟩ := hcju.map φ
        have : φ i = (↑u⁻¹ : AdjoinRoot g) * (φ (g.coeff 0) - ∑ k ∈ s.erase i, φ (c k) * φ k) := by
          rw [← hrel, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
        rw [this]
        refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (hxG (algebraMap_coeff_zero_mem_span_root g))
          (Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ (hiG k hk)))
      · exact hiG i (Finset.mem_erase.mpr ⟨hij, hi⟩)
    · rw [Ideal.span_le, hG, Finset.coe_insert, Finset.coe_image]
      refine Set.insert_subset_iff.mpr ⟨Ideal.mem_sup_left (Ideal.subset_span rfl), ?_⟩
      rintro _ ⟨i, hi, rfl⟩
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _
        (hsspan' ▸ Ideal.subset_span (Finset.mem_of_mem_erase (Finset.mem_coe.mp hi))))
  have hcardG : G.card ≤ s.card := by
    have h1 : G.card ≤ ((s.erase j).image φ).card + 1 := Finset.card_insert_le _ _
    have h2 : ((s.erase j).image φ).card ≤ (s.erase j).card := Finset.card_image_le
    have h3 : (s.erase j).card + 1 = s.card := Finset.card_erase_add_one hj
    omega
  have hfin : (maximalIdeal (AdjoinRoot g)).spanFinrank ≤ s.card := by
    rw [hmaxT, hMG, ← Ideal.submodule_span_eq]
    calc (Submodule.span (AdjoinRoot g) (G : Set (AdjoinRoot g))).spanFinrank ≤ (G : Set (AdjoinRoot g)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet G)
      _ = G.card := Set.ncard_coe_finset G
      _ ≤ s.card := hcardG
  have hreg : IsRegularLocalRing (AdjoinRoot g) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [hdim, ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := S), ← hscard]
    exact_mod_cast hfin
  exact ⟨hreg, hdim⟩

end S_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
end P2MW
export P2MW.S_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq (solution)
