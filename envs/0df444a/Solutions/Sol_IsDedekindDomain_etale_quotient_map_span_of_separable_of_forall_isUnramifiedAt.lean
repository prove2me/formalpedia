-- Prove2me | solution 1 for IsDedekindDomain.etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/efa94537-bda2-5441-8bb1-134d8f25b11f

import Mathlib
import Theorems.Thm_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt

set_option autoImplicit false

open Polynomial TensorProduct UniqueFactorizationMonoid

universe u

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "etale_quotient_map_span_of_forall_isUnramifiedAt"
p2m_open "IsDedekindDomain"

section CRT

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

noncomputable def quotientInfAlgEquivPiQuotient {ι : Type*} [Finite ι] (f : ι → Ideal B)
    (hf : Pairwise (Function.onFun IsCoprime f)) : (B ⧸ ⨅ i, f i) ≃ₐ[k] ∀ i, B ⧸ f i :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient f hf) (fun x => by
    funext i
    rfl)

end CRT

variable {k : Type u} [Field k] (B : Type u) [CommRing B] [IsDedekindDomain B]
  [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]

theorem etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
    (h : k[X]) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ → Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) := by
  classical
  have h0 : h ≠ 0 := hsep.ne_zero

  set S : Finset k[X] := (normalizedFactors h).toFinset with hS
  have hnodup : (normalizedFactors h).Nodup := (squarefree_iff_nodup_normalizedFactors h0).mp hsep.squarefree
  have hmemS : ∀ {q : k[X]}, q ∈ S → q ∈ normalizedFactors h := fun hq => Multiset.mem_toFinset.mp hq
  have hirr : ∀ {q : k[X]}, q ∈ S → Irreducible q := fun hq => irreducible_of_normalized_factor _ (hmemS hq)
  have hdvd : ∀ {q : k[X]}, q ∈ S → q ∣ h := fun hq => dvd_of_mem_normalizedFactors (hmemS hq)
  have hcop : ∀ {q₁ q₂ : k[X]}, q₁ ∈ S → q₂ ∈ S → q₁ ≠ q₂ → IsCoprime q₁ q₂ := by
    intro q₁ q₂ h₁ h₂ hne
    refine (hirr h₁).coprime_iff_not_dvd.mpr fun hd => hne ?_
    have hass : Associated q₁ q₂ := (hirr h₁).associated_of_dvd (hirr h₂) hd
    rw [← normalize_normalized_factor q₁ (hmemS h₁), ← normalize_normalized_factor q₂ (hmemS h₂)]
    exact normalize_eq_normalize hd hass.symm.dvd

  have hprod : Associated (∏ q ∈ S, q) h := by
    have : ∏ q ∈ S, q = (normalizedFactors h).prod := by
      rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnodup.dedup, Multiset.map_id']
    rw [this]
    exact prod_normalizedFactors h0

  set a : k[X] →+* B := algebraMap k[X] B with ha
  have hmap : Ideal.map a (Ideal.span {h}) = ⨅ q : S, Ideal.span {a q} := by
    rw [Ideal.iInf_span_singleton (fun q₁ q₂ hne => (hcop q₁.2 q₂.2 (fun e => hne (Subtype.ext e))).map a),
      Ideal.map_span, Set.image_singleton, Finset.prod_coe_sort S (fun q => a q), ← map_prod]
    obtain ⟨v, hv⟩ := hprod
    rw [← hv, map_mul, mul_comm, Ideal.span_singleton_mul_left_unit (v.isUnit.map a)]

  haveI : ∀ q : S, Algebra.Etale k (B ⧸ Ideal.span {a (q : k[X])}) := by
    intro q
    have hq : Ideal.span {a (q : k[X])} = Ideal.map a (Ideal.span {(q : k[X])}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hq]
    exact IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt B (q : k[X]) (hirr q.2)
      (hsep.of_dvd (hdvd q.2)) (fun P _ hP hle => hunr P hP
        ((Ideal.span_singleton_le_span_singleton.mpr (hdvd q.2)).trans hle))

  have hpair : Pairwise (Function.onFun IsCoprime fun q : S => Ideal.span {a (q : k[X])}) := by
    intro q₁ q₂ hne
    exact Ideal.isCoprime_span_singleton_iff _ _ |>.mpr ((hcop q₁.2 q₂.2 (fun e => hne (Subtype.ext e))).map a)
  exact Algebra.Etale.of_equiv
    ((Ideal.quotientEquivAlgOfEq k hmap).trans (quotientInfAlgEquivPiQuotient _ hpair)).symm

end IsDedekindDomain

theorem solution
    {k : Type u} [Field k] (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ → Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) :=
  IsDedekindDomain.etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt B h hsep hunr

end S_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
end P2MW
export P2MW.S_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt (solution)
