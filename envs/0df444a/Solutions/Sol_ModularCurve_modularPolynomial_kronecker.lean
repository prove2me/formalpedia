-- Prove2me | solution 1 for ModularCurve.modularPolynomial_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/01d76157-c3ab-582d-972b-e127d444eaa1

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_ModularCurve_PhiGen_splits_of_prime
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_coeffMap_injective
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Algebra.CharP.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularPolynomial_kronecker
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve ModularCurve.PhiGen"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqModC_rat map_jqModC coeffMap_qExpand PhiGen.splits_prime_at_slot PhiGen.splits_of_prime qExpand_jqModC_eq_pow_unconditional transcendental_jqModC coeffMap_injective"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

variable {K : Type*} [Field K] [Algebra ℚ K]

def TS (K : Type*) [Field K] [Algebra ℚ K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (coeffEmb K jq))

theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * algebraMap ℚ K (jq.coeff n) := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff]

theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) : (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, coeff_jq_neg_one, map_one, mul_one, zpow_neg_one]

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) : (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    have hn : n < -1 := by
      by_contra hcon
      push Not at hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      exact absurd hk (not_lt.mpr this)
    rw [TS_coeff_mul, coeff_jq_of_lt hn, map_zero, mul_zero]
  · exact TS_coeff_of_not_dvd e u hd

theorem TS_ne_zero (e : ℕ) [NeZero e] (u : Kˣ) : TS K e u ≠ 0 := by
  intro h
  have := TS_coeff_neg (K := K) e u
  rw [h, HahnSeries.coeff_zero] at this
  exact (u⁻¹).ne_zero this.symm

theorem TS_injective {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (h : TS K e u = TS K e' u') :
    e = e' ∧ u = u' := by
  have key : ∀ {a a' : ℕ} [NeZero a] [NeZero a'] {v v' : Kˣ}, TS K a v = TS K a' v' → a ≤ a' := by
    intro a a' _ _ v v' hh
    by_contra hlt
    push Not at hlt
    have h1 := TS_coeff_neg (K := K) a v
    have hlt' : (-(a : ℤ)) < -(a' : ℤ) := by
      have : (a' : ℤ) < a := by exact_mod_cast hlt
      omega
    have h2 : (TS K a' v').coeff (-(a : ℤ)) = 0 := TS_coeff_of_lt a' v' hlt'
    rw [← hh, h1] at h2
    exact (v⁻¹).ne_zero h2
  have hee : e = e' := le_antisymm (key h) (key h.symm)
  subst hee
  refine ⟨rfl, ?_⟩
  have h1 := TS_coeff_neg (K := K) e u
  rw [h, TS_coeff_neg] at h1
  exact (inv_injective (Units.val_injective h1)).symm

theorem qTwist_TS (v : Kˣ) (e : ℕ) [NeZero e] (u : Kˣ) : qTwist v (TS K e u) = TS K e (v ^ (e : ℤ) * u) := by
  rw [TS, qTwist_qExpand, qTwist_qTwist]; rfl

theorem qExpand_TS (m e : ℕ) [NeZero m] [NeZero e] (u : Kˣ) : qExpand K m (TS K e u) = TS K (m * e) u := by
  rw [TS, qExpand_qExpand]; rfl

theorem TS_congr {e e' : ℕ} [NeZero e] [NeZero e'] (h : e = e') (u : Kˣ) : TS K e u = TS K e' u := by
  subst h; rfl

theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb K (qExpand ℚ n x) = qExpand K n (coeffEmb K x) :=
  coeffMap_qExpand (algebraMap ℚ K) n x

theorem iota_jqN (N d : ℕ) [NeZero N] [NeZero d] :
    coeffEmb K (qExpand ℚ N (jqN d)) = TS K (N * d) 1 := by
  rw [jqN, coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand, TS, qTwist_one_apply]

theorem iota_jq (N : ℕ) [NeZero N] : coeffEmb K (qExpand ℚ N jq) = TS K N 1 := by
  rw [coeffEmb_qExpand, TS, qTwist_one_apply]

theorem conj_zero_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) : conj p ζ (0 : Fin (p + 1)) = TS K (p * p) 1 := by
  rw [conj_zero, TS, qTwist_one_apply]

theorem conj_succ_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (b : Fin p) : conj p ζ b.succ = TS K 1 (ζ ^ (b : ℕ)) := by
  rw [conj_succ, TS, qExpand_one_apply]

theorem qTwist_iota_of_pow_eq_one (N : ℕ) [NeZero N] (v : Kˣ) (hv : v ^ N = 1) (x : LaurentSeries ℚ) :
    qTwist v (coeffEmb K (qExpand ℚ N x)) = coeffEmb K (qExpand ℚ N x) := by
  rw [coeffEmb_qExpand, qTwist_qExpand]
  have : v ^ (N : ℤ) = 1 := by exact_mod_cast hv
  rw [this, qTwist_one_apply]

end ModularCurve.W1

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqModC_rat map_jqModC coeffMap_qExpand PhiGen.splits_prime_at_slot PhiGen.splits_of_prime qExpand_jqModC_eq_pow_unconditional transcendental_jqModC coeffMap_injective"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

variable {K : Type*} [Field K] [Algebra ℚ K]

def qTwistEquiv (u : Kˣ) : LaurentSeries K ≃+* LaurentSeries K where
  toFun := qTwist u
  invFun := qTwist u⁻¹
  left_inv := fun f => by
    show qTwist u⁻¹ (qTwist u f) = f
    rw [qTwist_qTwist, inv_mul_cancel, qTwist_one_apply]
  right_inv := fun f => by
    show qTwist u (qTwist u⁻¹ f) = f
    rw [qTwist_qTwist, mul_inv_cancel, qTwist_one_apply]
  map_mul' := map_mul _
  map_add' := map_add _

omit [Algebra ℚ K] in
@[scoped simp] theorem qTwistEquiv_apply (u : Kˣ) (f : LaurentSeries K) : qTwistEquiv u f = qTwist u f := rfl

omit [Algebra ℚ K] in
theorem coe_qTwistEquiv (u : Kˣ) : ((qTwistEquiv u : LaurentSeries K ≃+* LaurentSeries K) : LaurentSeries K →+* LaurentSeries K) = qTwist u :=
  RingHom.ext fun _ => rfl

theorem qTwist_TS_one_cycle (ζ : Kˣ) {p : ℕ} (hζp : ζ ^ p = 1) (b : ℕ) :
    qTwist ζ (TS K 1 (ζ ^ b)) = TS K 1 (ζ ^ ((b + 1) % p)) := by
  rw [qTwist_TS]
  congr 1
  have : ζ ^ ((1 : ℕ) : ℤ) * ζ ^ b = ζ ^ (b + 1) := by rw [zpow_natCast, pow_one, pow_succ']
  rw [this]
  conv_lhs => rw [← Nat.mod_add_div (b + 1) p, pow_add, pow_mul, hζp, one_pow, mul_one]

theorem phiProd_conj_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    phiProd p (conj p ζ) = (Polynomial.X - Polynomial.C (TS K (p * p) 1)) *
      ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) := by
  rw [phiProd, Fin.prod_univ_succ, conj_zero_eq]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun b => Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) p]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [conj_succ_eq]

theorem roots_phiProd_conj (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    (phiProd p (conj p ζ)).roots = TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b)) := by
  classical
  rw [phiProd_conj_eq]
  have h1 : (Polynomial.X - Polynomial.C (TS K (p * p) 1) : Polynomial (LaurentSeries K)) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have h2 : (∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => Polynomial.X_sub_C_ne_zero _
  rw [Polynomial.roots_mul (mul_ne_zero h1 h2), Polynomial.roots_X_sub_C, Finset.prod_eq_multiset_prod,
    Finset.range_val]
  have hm : (Multiset.map (fun b => Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) (Multiset.range p)) =
      ((Multiset.range p).map (fun b => TS K 1 (ζ ^ b))).map (fun a => Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]; rfl
  rw [hm, Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

theorem roots_phiProd_conj_nodup (p : ℕ) [hp : Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    (TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b))).Nodup := by
  refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hmem
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hmem
    have := (TS_injective hb).1
    have h2 := hp.out.two_le
    nlinarith
  · refine (Multiset.nodup_range p).map_on fun b hb b' hb' hbb' => ?_
    rw [Multiset.mem_range] at hb hb'
    have hu := (TS_injective hbb').2
    have hζu : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.mp hζ
    exact hζu.pow_inj hb hb' hu

theorem exists_isPrimitiveRoot_cyclotomicField (N : ℕ) [NeZero N] :
    ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z N := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ) (Set.mem_singleton N) (NeZero.ne N)

def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  ((exists_isPrimitiveRoot_cyclotomicField N).choose_spec.isUnit (NeZero.ne N)).unit

theorem cycUnit_spec (N : ℕ) [NeZero N] :
    IsPrimitiveRoot ((cycUnit N : (CyclotomicField N ℚ)ˣ) : CyclotomicField N ℚ) N := by
  rw [cycUnit, IsUnit.unit_spec]
  exact (exists_isPrimitiveRoot_cyclotomicField N).choose_spec

theorem cycUnit_pow (N : ℕ) [NeZero N] : cycUnit N ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, (cycUnit_spec N).pow_eq_one, Units.val_one])

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqModC_rat map_jqModC coeffMap_qExpand PhiGen.splits_prime_at_slot PhiGen.splits_of_prime qExpand_jqModC_eq_pow_unconditional transcendental_jqModC coeffMap_injective"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in

theorem isPrimitiveRoot_pow_div {N : ℕ} [NeZero N] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N)
    {p : ℕ} (hpN : p ∣ N) : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hd0 : N / p ≠ 0 := by
    intro h0
    have hc := Nat.div_mul_cancel hpN
    rw [h0, zero_mul] at hc
    exact hN hc.symm
  have h := hζ.pow_of_dvd hd0 (Nat.div_dvd_of_dvd hpN)
  rw [Nat.div_div_self hpN hN] at h
  rwa [← Units.val_pow_eq_pow_val] at h

theorem qExpand_qTwist_TS (e : ℕ) [NeZero e] (u : Kˣ) (m : ℕ) [NeZero m] (w : Kˣ) :
    qExpand K e (qTwist u (TS K m w)) = TS K (e * m) (u ^ (m : ℤ) * w) := by
  rw [qTwist_TS, qExpand_TS]

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqModC_rat map_jqModC coeffMap_qExpand PhiGen.splits_prime_at_slot PhiGen.splits_of_prime qExpand_jqModC_eq_pow_unconditional transcendental_jqModC coeffMap_injective"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem prod_form_ne_zero (N : ℕ) (ζ : Kˣ) (p : ℕ) [NeZero p] (e : ℕ) [NeZero e]
    (u : Kˣ) :
    (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)))) *
        ∏ b ∈ Finset.range p,
          (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))) ≠ 0 :=
  mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero

theorem roots_prime_at_slot (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))).roots
      = (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq))) ::ₘ
          (Multiset.range p).map
            (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq))) := by
  rw [ModularCurve.PhiGen.splits_prime_at_slot N ζ hζ p hpN data e u,
    Polynomial.roots_mul (prod_form_ne_zero N ζ p e u), Polynomial.roots_X_sub_C,
    Finset.prod_eq_multiset_prod, Finset.range_val,
    show (Multiset.range p).map
          (fun b => Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq))))
        = ((Multiset.range p).map
            (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))).map
            (fun a => Polynomial.X - Polynomial.C a) from
      (Multiset.map_map (fun a => Polynomial.X - Polynomial.C a)
        (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))
        (Multiset.range p)).symm,
    Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

theorem roots_prime_at_slot_nodup (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (e : ℕ) [NeZero e] (u : Kˣ) :
    ((qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq))) ::ₘ
        (Multiset.range p).map
          (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))).Nodup := by
  have hζp : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := isPrimitiveRoot_pow_div hζ hpN
  rw [Multiset.nodup_cons]
  constructor
  ·
    intro hmem
    obtain ⟨b, hb, heq⟩ := Multiset.mem_map.mp hmem
    have h := (TS_injective (K := K) (e := e) (e' := p * (p * e))
      (u := u * ζ ^ (b * (N / p))) (u' := u ^ (p * p)) heq).1
    have hp2 : 2 ≤ p := hp.out.two_le
    have he1 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
    have hmono : 2 * (2 * e) ≤ p * (p * e) := Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
    rw [← h] at hmono
    omega
  ·
    refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range p)
    intro b hb b' hb' heq
    rw [Multiset.mem_range] at hb hb'
    have h := (TS_injective (K := K) (e := e) (e' := e)
      (u := u * ζ ^ (b * (N / p))) (u' := u * ζ ^ (b' * (N / p))) heq).2
    have h2 : ζ ^ (b * (N / p)) = ζ ^ (b' * (N / p)) := mul_left_cancel h
    have h3 : (ζ ^ (N / p)) ^ b = (ζ ^ (N / p)) ^ b' := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (N / p) b, Nat.mul_comm (N / p) b']
      exact h2
    have h4 : ((ζ ^ (N / p) : Kˣ) : K) ^ b = ((ζ ^ (N / p) : Kˣ) : K) ^ b' := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h3]
    exact hζp.pow_inj hb hb' h4

theorem roots_prime_at_slot_roots_nodup (N : ℕ) [NeZero N] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) N) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))).roots.Nodup := by
  rw [roots_prime_at_slot N ζ hζ p hpN data e u]
  exact roots_prime_at_slot_nodup N ζ hζ p hpN e u

theorem isRoot_prime_at_slot_iff (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) (y : LaurentSeries K) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))).IsRoot y ↔
      y = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)) ∨
        ∃ b < p, y = qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)) := by
  have hne : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))) ≠ 0 := by
    rw [ModularCurve.PhiGen.splits_prime_at_slot N ζ hζ p hpN data e u]
    exact prod_form_ne_zero N ζ p e u
  rw [← Polynomial.mem_roots hne, roots_prime_at_slot N ζ hζ p hpN data e u,
    Multiset.mem_cons, Multiset.mem_map]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mp hb, rfl⟩
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mpr hb, rfl⟩

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqModC_rat map_jqModC coeffMap_qExpand PhiGen.splits_prime_at_slot PhiGen.splits_of_prime qExpand_jqModC_eq_pow_unconditional transcendental_jqModC coeffMap_injective"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

def phiAtSeed {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (data : ModularPolynomialData n) (x : R) :
    Polynomial R :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)

theorem phiAtSeed_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) (f : R →+* S) :
    (phiAtSeed data x).map f = phiAtSeed data (f x) := by
  rw [phiAtSeed, phiAtSeed, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp

theorem phiAtSeed_monic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).Monic :=
  data.monic.map _

theorem phiAtSeed_natDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).natDegree = dedekindPsi n := by
  rw [phiAtSeed, data.monic.natDegree_map, data.natDegree_eq]

theorem phiAtSeed_jq_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) :
    (phiAtSeed data jq).eval (jqN n) = 0 := by
  have h := data.eval_eq_zero
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2 <;> try rfl
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtJ_X]

theorem phiAtSeed_eval_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x y : R) (f : R →+* S) (h : (phiAtSeed data x).eval y = 0) :
    (phiAtSeed data (f x)).eval (f y) = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom, h, map_zero]

theorem phiAtSeed_jqN_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :
    (phiAtSeed data (jqN M)).eval (jqN (M * n)) = 0 := by
  have h := phiAtSeed_eval_map data jq (jqN n) (qExpand ℚ M) (phiAtSeed_jq_eval n data)
  rwa [jqN, qExpand_qExpand] at h

theorem phiAtSeed_iota_eval {K : Type*} [Field K] [Algebra ℚ K] (A : ℕ) [NeZero A] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :
    (phiAtSeed data (coeffEmb K (qExpand ℚ A (jqN M)))).eval (coeffEmb K (qExpand ℚ A (jqN (M * n)))) = 0 :=
  phiAtSeed_eval_map data _ _ ((coeffEmb K).comp (qExpand ℚ A)) (phiAtSeed_jqN_eval n data M)

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqModC_rat map_jqModC coeffMap_qExpand PhiGen.splits_prime_at_slot PhiGen.splits_of_prime qExpand_jqModC_eq_pow_unconditional transcendental_jqModC coeffMap_injective"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

section kronTransport

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem kron_coeffMap_qTwist (σ : R →+* S) (u : Rˣ) (f : LaurentSeries R) :
    coeffMap σ (qTwist u f) = qTwist (Units.map σ.toMonoidHom u) (coeffMap σ f) := by
  ext k
  simp only [coeffMap_coeff, qTwist_coeff, map_mul]
  congr 1
  rw [← map_zpow, Units.coe_map]
  rfl

private theorem kron_comp_evalAtJ {L : Type*} [CommRing L] (φ : LaurentSeries ℚ →+* L) :
    φ.comp evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom L) (φ jq) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have h1 : evalAtJ (Polynomial.C a) = ((a : ℤ) : LaurentSeries ℚ) := by
      simp [evalAtJ]
    rw [RingHom.comp_apply, h1, map_intCast, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    simp
  · rw [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

end kronTransport
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"

section kronModel

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

omit hℓ in

private theorem kron_root_pow :
    (AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ)) ^ ℓ = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one ℓ ℤ
  have hmk : AdjoinRoot.mk (Polynomial.cyclotomic ℓ ℤ) (Polynomial.X ^ ℓ - 1) = 0 := by
    rw [hc, map_mul, AdjoinRoot.mk_self, zero_mul]
  have h0 : Polynomial.aeval (AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ))
      (Polynomial.X ^ ℓ - 1 : Polynomial ℤ) = 0 := by
    rw [AdjoinRoot.aeval_eq]
    exact hmk
  rw [map_sub, map_pow, Polynomial.aeval_X, map_one] at h0
  exact sub_eq_zero.mp h0

private def kronZeta : (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ))ˣ where
  val := AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ)
  inv := (AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ)) ^ (ℓ - 1)
  val_inv := by
    rw [← pow_succ']
    rw [Nat.sub_add_cancel hℓ.out.one_le]
    exact kron_root_pow ℓ
  inv_val := by
    rw [← pow_succ]
    rw [Nat.sub_add_cancel hℓ.out.one_le]
    exact kron_root_pow ℓ

private def kronTheta : AdjoinRoot (Polynomial.cyclotomic ℓ ℤ) →+* ZMod ℓ :=
  AdjoinRoot.lift (Int.castRingHom (ZMod ℓ)) 1 (by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int,
      Polynomial.eval_one_cyclotomic_prime, ZMod.natCast_self])

private def kronIota : AdjoinRoot (Polynomial.cyclotomic ℓ ℤ) →+* CyclotomicField ℓ ℚ :=
  AdjoinRoot.lift (Int.castRingHom (CyclotomicField ℓ ℚ))
    ((cycUnit ℓ : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) (by
      rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
      exact Polynomial.IsRoot.eq_zero
        ((cycUnit_spec ℓ).isRoot_cyclotomic hℓ.out.pos))

private theorem kronTheta_root :
    kronTheta ℓ (AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ)) = 1 :=
  AdjoinRoot.lift_root _

private theorem kronIota_root :
    kronIota ℓ (AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ))
      = ((cycUnit ℓ : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) :=
  AdjoinRoot.lift_root _

private theorem kronTheta_units_zeta :
    Units.map (kronTheta ℓ).toMonoidHom (kronZeta ℓ) = 1 :=
  Units.ext (by rw [Units.coe_map, Units.val_one]; exact kronTheta_root ℓ)

private theorem kronIota_units_zeta :
    Units.map (kronIota ℓ).toMonoidHom (kronZeta ℓ) = cycUnit ℓ :=
  Units.ext (by rw [Units.coe_map]; exact kronIota_root ℓ)

private theorem kronIota_injective : Function.Injective (kronIota ℓ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [kronIota, AdjoinRoot.lift_mk] at ha
  rw [AdjoinRoot.mk_eq_zero]
  have hq : Polynomial.aeval ((cycUnit ℓ : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ)
      (g.map (Int.castRingHom ℚ)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap ℚ (CyclotomicField ℓ ℚ)).comp (Int.castRingHom ℚ)
        = Int.castRingHom (CyclotomicField ℓ ℚ) from RingHom.ext_int _ _]
    exact ha
  have hdvd : Polynomial.cyclotomic ℓ ℚ ∣ g.map (Int.castRingHom ℚ) := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat (cycUnit_spec ℓ) hℓ.out.pos]
    exact minpoly.dvd ℚ _ hq
  rw [← Polynomial.map_cyclotomic_int ℓ ℚ] at hdvd
  exact (Polynomial.map_dvd_map (Int.castRingHom ℚ) Int.cast_injective
    (Polynomial.cyclotomic.monic ℓ ℤ)).mp hdvd

private theorem kron_charP_laurent : CharP (LaurentSeries (ZMod ℓ)) ℓ := by
  constructor
  intro x
  rw [← map_natCast (HahnSeries.C : ZMod ℓ →+* LaurentSeries (ZMod ℓ)) x,
    ← map_zero (HahnSeries.C : ZMod ℓ →+* LaurentSeries (ZMod ℓ)),
    HahnSeries.C_injective.eq_iff]
  exact CharP.cast_eq_zero_iff (ZMod ℓ) ℓ x

private theorem kron_charP_poly : CharP (Polynomial (LaurentSeries (ZMod ℓ))) ℓ := by
  haveI := kron_charP_laurent ℓ
  constructor
  intro x
  rw [← map_natCast (Polynomial.C : LaurentSeries (ZMod ℓ) →+* Polynomial (LaurentSeries (ZMod ℓ))) x,
    ← map_zero (Polynomial.C : LaurentSeries (ZMod ℓ) →+* Polynomial (LaurentSeries (ZMod ℓ))),
    Polynomial.C_injective.eq_iff]
  exact CharP.cast_eq_zero_iff (LaurentSeries (ZMod ℓ)) ℓ x

omit hℓ in

private theorem kron_coeffEmb_jq :
    coeffEmb (CyclotomicField ℓ ℚ) jq = jqModC (CyclotomicField ℓ ℚ) := by
  rw [coeffEmb, ← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (CyclotomicField ℓ ℚ))

private theorem kron_specialized (data : ModularPolynomialData ℓ) :
    phiAtSeed data (jqModC (ZMod ℓ))
      = (Polynomial.X - Polynomial.C (jqModC (ZMod ℓ) ^ ℓ))
        * (Polynomial.X ^ ℓ - Polynomial.C (jqModC (ZMod ℓ))) := by
  classical

  have hK := ModularCurve.PhiGen.splits_of_prime ℓ (cycUnit ℓ) (cycUnit_spec ℓ) data
  have hLK : data.Φ.map (((coeffEmb (CyclotomicField ℓ ℚ)).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiAtSeed data (qExpand (CyclotomicField ℓ ℚ) ℓ (jqModC (CyclotomicField ℓ ℚ))) := by
    have hseed : ((coeffEmb (CyclotomicField ℓ ℚ)).comp (qExpand ℚ ℓ)) jq
        = qExpand (CyclotomicField ℓ ℚ) ℓ (jqModC (CyclotomicField ℓ ℚ)) := by
      rw [RingHom.comp_apply, coeffEmb_qExpand, kron_coeffEmb_jq]
    rw [kron_comp_evalAtJ, hseed, phiAtSeed]

  have hseedO : coeffMap (kronIota ℓ)
      (qExpand (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) ℓ
        (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ))))
      = qExpand (CyclotomicField ℓ ℚ) ℓ (jqModC (CyclotomicField ℓ ℚ)) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (kronIota ℓ)
  have hmapProd :
      ((Polynomial.X - Polynomial.C (qExpand (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) (ℓ * ℓ)
          (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)))))
        * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (qTwist ((kronZeta ℓ) ^ (b : ℕ))
            (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)))))).map (coeffMap (kronIota ℓ))
      = phiProd ℓ (conj ℓ (cycUnit ℓ)) := by
    rw [phiProd, Fin.prod_univ_succ, Polynomial.map_mul]
    congr 1
    · rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, conj_zero]
      congr 2
      rw [coeffMap_qExpand, kron_coeffEmb_jq]
      congr 1
      exact map_jqModC (kronIota ℓ)
    · rw [← Polynomial.coe_mapRingHom, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        conj_succ, kron_coeffMap_qTwist, map_pow, kronIota_units_zeta, kron_coeffEmb_jq]
      exact congrArg
        (fun z => Polynomial.X - Polynomial.C (qTwist (cycUnit ℓ ^ (b : ℕ)) z))
        (map_jqModC (kronIota ℓ))
  have hO : phiAtSeed data
      (qExpand (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) ℓ
        (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ))))
      = (Polynomial.X - Polynomial.C (qExpand (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) (ℓ * ℓ)
          (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)))))
        * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (qTwist ((kronZeta ℓ) ^ (b : ℕ))
            (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ))))) := by
    apply Polynomial.map_injective (coeffMap (kronIota ℓ))
      (ModularCurve.coeffMap_injective (kronIota_injective ℓ))
    rw [phiAtSeed_map, hseedO, hmapProd, ← hLK]
    exact hK

  have hPush := congrArg (Polynomial.map (coeffMap (kronTheta ℓ))) hO
  rw [phiAtSeed_map] at hPush
  have hseedθ : coeffMap (kronTheta ℓ)
      (qExpand (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) ℓ
        (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ))))
      = qExpand (ZMod ℓ) ℓ (jqModC (ZMod ℓ)) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (kronTheta ℓ)
  rw [hseedθ] at hPush
  have hmapθ :
      ((Polynomial.X - Polynomial.C (qExpand (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) (ℓ * ℓ)
          (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)))))
        * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (qTwist ((kronZeta ℓ) ^ (b : ℕ))
            (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)))))).map (coeffMap (kronTheta ℓ))
      = (Polynomial.X - Polynomial.C (qExpand (ZMod ℓ) (ℓ * ℓ) (jqModC (ZMod ℓ))))
        * (Polynomial.X - Polynomial.C (jqModC (ZMod ℓ))) ^ ℓ := by
    rw [Polynomial.map_mul]
    congr 1
    · rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      rw [coeffMap_qExpand]
      congr 1
      exact map_jqModC (kronTheta ℓ)
    · rw [← Polynomial.coe_mapRingHom, map_prod]
      have hfac : ∀ b : Fin ℓ,
          (Polynomial.mapRingHom (coeffMap (kronTheta ℓ)))
            (Polynomial.X - Polynomial.C (qTwist ((kronZeta ℓ) ^ (b : ℕ))
              (jqModC (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)))))
          = Polynomial.X - Polynomial.C (jqModC (ZMod ℓ)) := by
        intro b
        rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
          kron_coeffMap_qTwist, map_pow, kronTheta_units_zeta, one_pow, qTwist_one_apply]
        congr 2
        exact map_jqModC (kronTheta ℓ)
      rw [Finset.prod_congr rfl fun b _ => hfac b, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
  rw [hmapθ] at hPush

  haveI := kron_charP_laurent ℓ
  haveI := kron_charP_poly ℓ
  have hpow : qExpand (ZMod ℓ) ℓ (jqModC (ZMod ℓ)) = jqModC (ZMod ℓ) ^ ℓ :=
    ModularCurve.qExpand_jqModC_eq_pow_unconditional (ZMod ℓ)
  have hfrob : (Polynomial.X - Polynomial.C (jqModC (ZMod ℓ))) ^ ℓ
      = Polynomial.X ^ ℓ - Polynomial.C (jqModC (ZMod ℓ) ^ ℓ) := by
    rw [sub_pow_char, Polynomial.C_pow]
  have hspread : qExpand (ZMod ℓ) (ℓ * ℓ) (jqModC (ZMod ℓ))
      = qExpand (ZMod ℓ) ℓ (jqModC (ZMod ℓ)) ^ ℓ :=
    ((qExpand_qExpand ℓ ℓ (jqModC (ZMod ℓ))).symm).trans
      ((congrArg (qExpand (ZMod ℓ) ℓ) hpow).trans
        (map_pow (qExpand (ZMod ℓ) ℓ) (jqModC (ZMod ℓ)) ℓ))
  rw [hspread, hfrob, ← hpow] at hPush
  apply Polynomial.map_injective (qExpand (ZMod ℓ) ℓ) (qExpand_injective ℓ)
  rw [phiAtSeed_map, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, map_pow]
  exact hPush

end kronModel
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqModC_rat map_jqModC coeffMap_qExpand PhiGen.splits_prime_at_slot PhiGen.splits_of_prime qExpand_jqModC_eq_pow_unconditional transcendental_jqModC coeffMap_injective" end ModularCurve
p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.phiAtSeed_map_intCast_zmod_eq (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (data : ModularPolynomialData ℓ) : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (ZMod ℓ))) (jqModC (ZMod ℓ))) = (Polynomial.X - Polynomial.C (jqModC (ZMod ℓ) ^ ℓ)) * (Polynomial.X ^ ℓ - Polynomial.C (jqModC (ZMod ℓ))) :=
  kron_specialized ℓ data

p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.modularPolynomial_kronecker (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (data : ModularPolynomialData ℓ) : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) = (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := by
  classical

  have hcomp : (Polynomial.eval₂RingHom
        (algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ))) (jqModC (ZMod ℓ))).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ)))
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (ZMod ℓ))) (jqModC (ZMod ℓ)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      exact map_intCast (algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ))) a
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]

  have hmap0 : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))))
      - ((Polynomial.C Polynomial.X ^ ℓ - Polynomial.X)
        * (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ))).map
        (Polynomial.eval₂RingHom
          (algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ))) (jqModC (ZMod ℓ))) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_map, hcomp,
      ModularCurve.phiAtSeed_map_intCast_zmod_eq ℓ data]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    rw [show (Polynomial.eval₂RingHom
        (algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ))) (jqModC (ZMod ℓ)))
        Polynomial.X = jqModC (ZMod ℓ) from by
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]]
    rw [← Polynomial.C_pow]
    ring

  have hcoeff : ∀ n, ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))))
      - ((Polynomial.C Polynomial.X ^ ℓ - Polynomial.X)
        * (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ))).coeff n = 0 := by
    intro n
    by_contra hne
    refine ModularCurve.transcendental_jqModC (ZMod ℓ) ⟨_, hne, ?_⟩
    have h := congrArg (fun P : Polynomial (LaurentSeries (ZMod ℓ)) => P.coeff n) hmap0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    rw [Polynomial.aeval_def]
    exact h
  refine sub_eq_zero.mp (Polynomial.ext fun n => ?_)
  rw [hcoeff n, Polynomial.coeff_zero]

end
p2m_reactivate "P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve.W1"

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_modularPolynomial_kronecker.ModularCurve in

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (data : ModularPolynomialData ℓ) : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) = (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) :=
  ModularCurve.modularPolynomial_kronecker ℓ data

#print axioms solution

end S_ModularCurve_modularPolynomial_kronecker
end P2MW
export P2MW.S_ModularCurve_modularPolynomial_kronecker (solution)
