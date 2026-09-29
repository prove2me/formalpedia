-- Prove2me | solution 1 for ModularCurve.qExpand_jq_mem_adjoin_of_primes_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/08b73408-56d4-59b2-a9fd-20c0e2f5c3e4

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open ModularCurve Polynomial

namespace Key1

private scoped instance (a b : ℕ) [NeZero a] [NeZero b] : NeZero (a * b) :=
  ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩

variable {K : Type*} [Field K] [Algebra ℚ K]

def slotMultiset (ζ : Kˣ) (p q d : ℕ) [NeZero p] [NeZero d] : Multiset (LaurentSeries K) :=
  qExpand K (d * p * p) (coeffEmb K jq) ::ₘ
    ((Finset.range p).val.map fun b => qExpand K d (qTwist (ζ ^ (b * q)) (coeffEmb K jq)))

theorem map_eval₂_eq_slotMultiset_prod (p q d : ℕ) [hp : Fact p.Prime] [NeZero q] [NeZero d]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (p * q)) (data : ModularPolynomialData p) :
    data.Φ.map (eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (coeffEmb K (qExpand ℚ (d * p) jq)))
      = ((slotMultiset ζ p q d).map fun r => X - C r).prod := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hdiv : p * q / p = q := Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne p))
  have h := ModularCurve.PhiGen.splits_prime_at_slot (p * q) ζ hζ p (dvd_mul_right p q)
    data d (1 : Kˣ)
  simp only [hdiv, one_pow, one_mul, qTwist_one_apply] at h
  rw [show coeffEmb K (qExpand ℚ (d * p) jq) = qExpand K (p * d) (coeffEmb K jq) from by
        rw [coeffEmb_qExpand]; exact qExpand_congr (mul_comm d p) _,
      h]
  simp only [slotMultiset, Multiset.map_cons, Multiset.prod_cons]
  congr 1
  · rw [qExpand_congr (show p * (p * d) = d * p * p by ring)]
  · rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl

theorem coeffEmb_qExpand_mem_slotMultiset (ζ : Kˣ) (p q d : ℕ) [NeZero p] [NeZero d] :
    coeffEmb K (qExpand ℚ d jq) ∈ slotMultiset ζ p q d := by
  simp only [slotMultiset]
  refine Multiset.mem_cons_of_mem (Multiset.mem_map.mpr ⟨0, ?_, ?_⟩)
  · exact Finset.mem_val.mpr (Finset.mem_range.mpr (Nat.pos_of_ne_zero (NeZero.ne p)))
  · rw [zero_mul, pow_zero, qTwist_one_apply]
    exact (coeffEmb_qExpand K d jq).symm

theorem exists_primitiveRoot_unit (n : ℕ) (hn : n ≠ 0) :
    ∃ ζ : (CyclotomicField n ℚ)ˣ, IsPrimitiveRoot (ζ : CyclotomicField n ℚ) n := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨μ, hμ⟩ := (CyclotomicField.isCyclotomicExtension n ℚ).exists_isPrimitiveRoot
    (Set.mem_singleton n) hn
  exact ⟨Units.mk0 μ (hμ.ne_zero hn), hμ⟩

theorem data_exists (p : ℕ) [NeZero p] : Nonempty (ModularPolynomialData p) :=
  ModularCurve.nonempty_modularPolynomialData p

section Helpers

private theorem coeffJ_neg_one : (coeffEmb K jq).coeff (-1) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

private theorem coeffJ_of_lt {m : ℤ} (hm : m < -1) : (coeffEmb K jq).coeff m = 0 := by
  rw [coeffEmb_coeff, coeff_jq_of_lt hm, map_zero]

private theorem coeff_stretch_self (n : ℕ) [NeZero n] :
    (qExpand K n (coeffEmb K jq)).coeff (-(n : ℤ)) = 1 := by
  rw [show (-(n : ℤ)) = (n : ℤ) * (-1) by ring, qExpand_coeff_mul, coeffJ_neg_one]

private theorem coeff_twistStretch_neg_d (d : ℕ) [NeZero d] (u : Kˣ) :
    (qExpand K d (qTwist u (coeffEmb K jq))).coeff (-(d : ℤ))
      = ((u ^ (-1 : ℤ) : Kˣ) : K) := by
  rw [show (-(d : ℤ)) = (d : ℤ) * (-1) by ring, qExpand_coeff_mul, qTwist_coeff,
    coeffJ_neg_one, mul_one]

private theorem coeff_twistStretch_deep (d : ℕ) [NeZero d] (u : Kˣ) {m : ℕ}
    (hm : 1 < m) :
    (qExpand K d (qTwist u (coeffEmb K jq))).coeff (-((d * m : ℕ) : ℤ)) = 0 := by
  have hlt : (-(m : ℤ)) < -1 := by
    have : (1 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    omega
  rw [show (-((d * m : ℕ) : ℤ)) = (d : ℤ) * (-(m : ℤ)) by push_cast; ring,
    qExpand_coeff_mul, qTwist_coeff, coeffJ_of_lt hlt, mul_zero]

private theorem not_dvd_cross (d p q : ℕ) (hd : d ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ¬ ((d * q * q : ℕ) : ℤ) ∣ (-((d * p * p : ℕ) : ℤ)) := by
  rw [Int.dvd_neg, Int.natCast_dvd_natCast]
  intro ⟨k, hk⟩
  have heq : d * (p * p) = d * (q * q * k) := by
    have h1 : d * p * p = d * (p * p) := mul_assoc d p p
    have h2 : d * q * q * k = d * (q * q * k) := by rw [mul_assoc d q q, mul_assoc]
    rw [← h1, hk, h2]
  have hpp : p * p = q * q * k :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) heq
  have hqpp : q ∣ p * p := ⟨q * k, by rw [hpp]; ring⟩
  have hqp : q ∣ p := by
    rcases (Nat.Prime.dvd_mul hq).mp hqpp with h | h <;> exact h
  exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).symm

omit [Algebra ℚ K] in

private theorem exp_eq_of_coeff_eq {n : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) n)
    {i j : ℕ} (hi : i < n) (hj : j < n)
    (heq : (((ζ ^ i) ^ (-1 : ℤ) : Kˣ) : K) = (((ζ ^ j) ^ (-1 : ℤ) : Kˣ) : K)) :
    i = j := by
  have hun : (ζ ^ i : Kˣ) = (ζ ^ j : Kˣ) := by
    have := Units.ext heq
    rwa [zpow_neg_one, zpow_neg_one, inv_inj] at this
  have hK : (ζ : K) ^ i = (ζ : K) ^ j := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hun]
  exact hζ.pow_inj hi hj hK

private theorem one_lt_sq_of_prime {p : ℕ} (hp : p.Prime) : 1 < p * p := by
  have h2 : 2 ≤ p := hp.two_le
  calc (1 : ℕ) < 2 * 2 := by omega
    _ ≤ p * p := Nat.mul_le_mul h2 h2

end Helpers

theorem slotMultiset_nodup (p q d : ℕ) [hp : Fact p.Prime] [NeZero q] [NeZero d]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (p * q)) :
    (slotMultiset (K := K) ζ p q d).Nodup := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp2 : 1 < p * p := one_lt_sq_of_prime hp.out
  refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
  ·
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_range, not_exists, not_and]
    intro b _ heq
    apply_fun (·.coeff (-((d * (p * p) : ℕ) : ℤ))) at heq
    rw [coeff_twistStretch_deep d _ hp2] at heq
    rw [show (-((d * (p * p) : ℕ) : ℤ)) = (-((d * p * p : ℕ) : ℤ)) by push_cast; ring,
      coeff_stretch_self] at heq
    exact one_ne_zero heq.symm
  ·
    refine Multiset.Nodup.map_on ?_ (Finset.range p).nodup
    intro b hb b' hb' heq
    apply_fun (·.coeff (-(d : ℤ))) at heq
    rw [coeff_twistStretch_neg_d, coeff_twistStretch_neg_d] at heq
    have hlt : b * q < p * q :=
      (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (NeZero.ne q))).mpr (Finset.mem_range.mp hb)
    have hlt' : b' * q < p * q :=
      (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (NeZero.ne q))).mpr (Finset.mem_range.mp hb')
    have := exp_eq_of_coeff_eq hζ hlt hlt' heq
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne q)) this

theorem slotMultiset_meet (p q d : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] [NeZero d]
    (hne : p ≠ q) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (p * q)) :
    ∀ y ∈ slotMultiset (K := K) ζ p q d, y ∈ slotMultiset (K := K) ζ q p d →
      y = coeffEmb K (qExpand ℚ d jq) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hp2 : 1 < p * p := one_lt_sq_of_prime hp.out
  have hq2 : 1 < q * q := one_lt_sq_of_prime hq.out
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.out hq.out).mpr hne
  intro y hy hy'
  simp only [slotMultiset, Multiset.mem_cons, Multiset.mem_map, Finset.mem_val,
    Finset.mem_range] at hy hy'
  rcases hy with rfl | ⟨b, hb, rfl⟩
  ·
    exfalso
    have h1 : (qExpand K (d * p * p) (coeffEmb K jq)).coeff (-((d * p * p : ℕ) : ℤ)) = 1 := by
      rw [show (-((d * p * p : ℕ) : ℤ)) = (-((d * p * p) : ℤ)) by push_cast; ring]
      exact coeff_stretch_self (d * p * p)
    rcases hy' with heq | ⟨b', _, heq⟩
    ·
      apply_fun (·.coeff (-((d * p * p : ℕ) : ℤ))) at heq
      rw [h1, qExpand_coeff_of_not_dvd (d * q * q) _
        (not_dvd_cross d p q (NeZero.ne d) hp.out hq.out hne)] at heq
      exact one_ne_zero heq
    ·
      apply_fun (·.coeff (-((d * (p * p) : ℕ) : ℤ))) at heq
      rw [coeff_twistStretch_deep d _ hp2,
        show (-((d * (p * p) : ℕ) : ℤ)) = (-((d * p * p : ℕ) : ℤ)) by push_cast; ring,
        h1] at heq
      exact one_ne_zero heq.symm
  · rcases hy' with heq | ⟨b', hb', heq⟩
    ·
      exfalso
      apply_fun (·.coeff (-((d * (q * q) : ℕ) : ℤ))) at heq
      rw [coeff_twistStretch_deep d _ hq2,
        show (-((d * (q * q) : ℕ) : ℤ)) = (-((d * q * q : ℕ) : ℤ)) by push_cast; ring,
        coeff_stretch_self] at heq
      exact one_ne_zero heq.symm
    ·
      apply_fun (·.coeff (-(d : ℤ))) at heq
      rw [coeff_twistStretch_neg_d, coeff_twistStretch_neg_d] at heq
      have hlt : b * q < p * q :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (NeZero.ne q))).mpr hb
      have hlt' : b' * p < p * q := mul_comm q p ▸
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (NeZero.ne p))).mpr hb'
      have hbq : b * q = b' * p := exp_eq_of_coeff_eq hζ hlt hlt' heq.symm
      have hpb : p ∣ b := hcop.dvd_of_dvd_mul_right ⟨b', by rw [hbq]; ring⟩
      have hb0 : b = 0 := Nat.eq_zero_of_dvd_of_lt hpb hb
      subst hb0
      simp only [zero_mul, pow_zero, qTwist_one_apply]
      exact (coeffEmb_qExpand K d jq).symm

theorem mem_of_common_simple_root {F L E : Type*} [Field F] [Field L] [Field E] [Algebra F L]
    (S : IntermediateField F L) (ι : L →+* E) (f' g' : Polynomial S) (x : L) (s t : Multiset E)
    (hf : (f'.map (algebraMap S L)).map ι = (s.map fun r => X - C r).prod)
    (hg : (g'.map (algebraMap S L)).map ι = (t.map fun r => X - C r).prod)
    (hs : s.Nodup) (hxs : ι x ∈ s) (hxt : ι x ∈ t)
    (hmeet : ∀ y ∈ s, y ∈ t → y = ι x) : x ∈ S := by
  classical
  set f : L[X] := f'.map (algebraMap S L) with hf_def
  set g : L[X] := g'.map (algebraMap S L) with hg_def

  have hmonic : ∀ u : Multiset E, (u.map fun r => (X - C r : E[X])).prod.Monic := fun u =>
    monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have hfE0 : f.map ι ≠ 0 := by rw [hf]; exact (hmonic s).ne_zero
  have hgE0 : g.map ι ≠ 0 := by rw [hg]; exact (hmonic t).ne_zero
  have hf0 : f ≠ 0 := fun e => hfE0 (by rw [e, Polynomial.map_zero])
  have hg0 : g ≠ 0 := fun e => hgE0 (by rw [e, Polynomial.map_zero])

  have hfroots : (f.map ι).roots = s := by rw [hf, roots_multiset_prod_X_sub_C]
  have hgroots : (g.map ι).roots = t := by rw [hg, roots_multiset_prod_X_sub_C]

  have hsplit : (f.map ι).Splits := by
    rw [hf]
    exact Splits.multisetProd fun q hq => by
      obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hq
      exact Splits.X_sub_C r
  have hsepE : (f.map ι).Separable :=
    (nodup_roots_iff_of_splits hfE0 hsplit).mp (by rw [hfroots]; exact hs)
  have hsep : f.Separable := (separable_map ι).mp hsepE

  have hxf : ι x ∈ (f.map ι).roots := by rw [hfroots]; exact hxs
  have hxg : ι x ∈ (g.map ι).roots := by rw [hgroots]; exact hxt
  have hfx : f.eval x = 0 := by
    apply ι.injective
    rw [map_zero, ← eval₂_hom, ← eval_map]
    exact (isRoot_of_mem_roots hxf).eq_zero
  have hgx : g.eval x = 0 := by
    apply ι.injective
    rw [map_zero, ← eval₂_hom, ← eval_map]
    exact (isRoot_of_mem_roots hxg).eq_zero

  set p : S[X] := EuclideanDomain.gcd f' g' with hp_def
  set h : L[X] := EuclideanDomain.gcd f g with hh_def
  have hph : p.map (algebraMap S L) = h := by
    rw [hp_def, hh_def, hf_def, hg_def, Polynomial.gcd_map]
  have h0 : h ≠ 0 := fun e => hf0 (EuclideanDomain.gcd_eq_zero_iff.mp e).1
  have hhsep : h.Separable := separable_gcd_left hsep g
  have hhx : h.eval x = 0 := eval_gcd_eq_zero hfx hgx
  have hhsplit : (h.map ι).Splits :=
    hsplit.of_dvd hfE0 (Polynomial.map_dvd ι (EuclideanDomain.gcd_dvd_left f g))
  have hhroots : ∀ y ∈ (h.map ι).roots, y = ι x := by
    intro y hy
    rw [mem_roots_map h0] at hy
    have hyf : y ∈ s := by
      rw [← hfroots, mem_roots_map hf0]
      exact root_left_of_root_gcd hy
    have hyg : y ∈ t := by
      rw [← hgroots, mem_roots_map hg0]
      exact root_right_of_root_gcd hy
    exact hmeet y hyf hyg
  have hlin : h = C h.leadingCoeff * (X - C x) :=
    eq_X_sub_C_of_separable_of_root_eq hhsep hhx hhsplit hhroots

  obtain ⟨c, hc0, hpc⟩ : ∃ c : L, c ≠ 0 ∧ p.map (algebraMap S L) = C c * (X - C x) :=
    ⟨h.leadingCoeff, mt leadingCoeff_eq_zero.mp h0, hph.trans hlin⟩
  have hc₀ : (p.map (algebraMap S L)).coeff 0 = -(c * x) := by simp [hpc]
  have hc₁ : (p.map (algebraMap S L)).coeff 1 = c := by simp [hpc]
  have hx : algebraMap S L (-p.coeff 0 / p.coeff 1) = x := by
    rw [map_div₀, map_neg, ← coeff_map, ← coeff_map, hc₀, hc₁, neg_neg, mul_div_cancel_left₀ x hc0]
  rw [← hx]
  exact Subtype.mem (-p.coeff 0 / p.coeff 1)

theorem map_map_specialize {S L E : Type*} [CommRing S] [CommRing L] [CommRing E]
    (φ : S →+* L) (ι : L →+* E) (a : S) (Φ : Polynomial (Polynomial ℤ)) :
    ((Φ.map (eval₂RingHom (Int.castRingHom S) a)).map φ).map ι =
      Φ.map (eval₂RingHom (Int.castRingHom E) (ι (φ a))) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp
  · simp [Polynomial.eval₂_X]

theorem map_specialize {L E : Type*} [CommRing L] [CommRing E]
    (ι : L →+* E) (a : L) (Φ : Polynomial (Polynomial ℤ)) :
    (Φ.map (eval₂RingHom (Int.castRingHom L) a)).map ι =
      Φ.map (eval₂RingHom (Int.castRingHom E) (ι a)) := by
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp
  · simp [Polynomial.eval₂_X]

end Key1
p2m_reactivate "P2MW.S_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne.Key1"

open Key1 in

theorem solution
    (d ℓ ℓ' : ℕ) [NeZero d] [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    qExpand ℚ d jq ∈ IntermediateField.adjoin ℚ
      {qExpand ℚ (d * ℓ) jq, qExpand ℚ (d * ℓ') jq, qExpand ℚ (d * ℓ * ℓ') jq} := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩

  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_unit (ℓ * ℓ') (mul_ne_zero hℓ.ne_zero hℓ'.ne_zero)
  have hζ' : IsPrimitiveRoot (ζ : CyclotomicField (ℓ * ℓ') ℚ) (ℓ' * ℓ) := by
    rwa [Nat.mul_comm ℓ' ℓ]
  obtain ⟨dataℓ⟩ := data_exists ℓ
  obtain ⟨dataℓ'⟩ := data_exists ℓ'

  set S : IntermediateField ℚ (LaurentSeries ℚ) := IntermediateField.adjoin ℚ
      {qExpand ℚ (d * ℓ) jq, qExpand ℚ (d * ℓ') jq, qExpand ℚ (d * ℓ * ℓ') jq} with hS
  have hA : qExpand ℚ (d * ℓ) jq ∈ S :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  have hB : qExpand ℚ (d * ℓ') jq ∈ S :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  refine mem_of_common_simple_root S (coeffEmb (CyclotomicField (ℓ * ℓ') ℚ))
    (dataℓ.Φ.map (eval₂RingHom (Int.castRingHom S) ⟨qExpand ℚ (d * ℓ) jq, hA⟩))
    (dataℓ'.Φ.map (eval₂RingHom (Int.castRingHom S) ⟨qExpand ℚ (d * ℓ') jq, hB⟩))
    (qExpand ℚ d jq) (slotMultiset ζ ℓ ℓ' d) (slotMultiset ζ ℓ' ℓ d) ?_ ?_
    (slotMultiset_nodup ℓ ℓ' d ζ hζ)
    (coeffEmb_qExpand_mem_slotMultiset ζ ℓ ℓ' d)
    (coeffEmb_qExpand_mem_slotMultiset ζ ℓ' ℓ d)
    (slotMultiset_meet ℓ ℓ' d hne ζ hζ)
  ·
    rw [map_map_specialize]
    exact map_eval₂_eq_slotMultiset_prod ℓ ℓ' d ζ hζ dataℓ
  · rw [map_map_specialize]
    exact map_eval₂_eq_slotMultiset_prod ℓ' ℓ d ζ hζ' dataℓ'

end
p2m_reactivate "P2MW.S_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne.Key1"

#print axioms Key1.map_eval₂_eq_slotMultiset_prod
#print axioms Key1.coeffEmb_qExpand_mem_slotMultiset
#print axioms Key1.exists_primitiveRoot_unit
#print axioms Key1.data_exists
#print axioms Key1.slotMultiset_nodup
#print axioms Key1.slotMultiset_meet
#print axioms Key1.mem_of_common_simple_root
#print axioms Key1.map_map_specialize
#print axioms solution
#check @solution

end S_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne
end P2MW
export P2MW.S_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne (solution)
