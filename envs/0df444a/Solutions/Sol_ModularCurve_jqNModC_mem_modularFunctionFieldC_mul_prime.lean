-- Prove2me | solution 1 for ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c0a268f2-8b0d-5141-bca9-ff57618a2bb4

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm
import Theorems.Thm_Polynomial_mem_range_of_unique_common_root
import Theorems.Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve ModularCurve.PhiGen"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeff_jqModC_neg_one order_jqModC PhiGen.splits_prime_at_slot_of_isPrimitiveRoot exists_phiIrreducible_evalSymm minpoly_jqNModC_map_eq_prod_slots"
namespace W1
p2m_open "ModularCurve"

variable {K : Type*} [Field K]

def TS (K : Type*) [Field K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (jqModC K))

theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * (jqModC K).coeff n := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff]

theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem coeff_jqModC_of_lt {n : ℤ} (hn : n < -1) : (jqModC K).coeff n = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [ModularCurve.order_jqModC]
  exact hn

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) : (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, ModularCurve.coeff_jqModC_neg_one, mul_one, zpow_neg_one]

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) : (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    have hn : n < -1 := by
      by_contra hcon
      push Not at hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      exact absurd hk (not_lt.mpr this)
    rw [TS_coeff_mul, coeff_jqModC_of_lt hn, mul_zero]
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

theorem qExpand_qTwist_TS (e : ℕ) [NeZero e] (u : Kˣ) (m : ℕ) [NeZero m] (w : Kˣ) :
    qExpand K e (qTwist u (TS K m w)) = TS K (e * m) (u ^ (m : ℤ) * w) := by
  rw [qTwist_TS, qExpand_TS]

theorem jqModC_eq_TS : jqModC K = TS K 1 1 := by
  rw [TS, qTwist_one_apply, qExpand_one_apply]

theorem jqNModC_eq_TS (d : ℕ) [NeZero d] : jqNModC K d = TS K d 1 := by
  rw [jqNModC, TS, qTwist_one_apply]

theorem qExpand_jqNModC (A d : ℕ) [NeZero A] [NeZero d] : qExpand K A (jqNModC K d) = TS K (A * d) 1 := by
  rw [jqNModC_eq_TS, qExpand_TS]

theorem qExpand_jqModC_eq_TS (A : ℕ) [NeZero A] : qExpand K A (jqModC K) = TS K A 1 := by
  rw [TS, qTwist_one_apply]

theorem qTwist_qExpand_of_pow_eq_one (A : ℕ) [NeZero A] (v : Kˣ) (hv : v ^ A = 1) (x : LaurentSeries K) :
    qTwist v (qExpand K A x) = qExpand K A x := by
  rw [qTwist_qExpand]
  have : v ^ (A : ℤ) = 1 := by exact_mod_cast hv
  rw [this, qTwist_one_apply]

end ModularCurve.W1

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeff_jqModC_neg_one order_jqModC PhiGen.splits_prime_at_slot_of_isPrimitiveRoot exists_phiIrreducible_evalSymm minpoly_jqNModC_map_eq_prod_slots"
namespace W1
p2m_open "ModularCurve"

section transport

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qTwist (σ : R →+* S) (u : Rˣ) (f : LaurentSeries R) :
    coeffMap σ (qTwist u f) = qTwist (Units.map σ.toMonoidHom u) (coeffMap σ f) := by
  ext k
  simp only [coeffMap_coeff, qTwist_coeff, map_mul]
  congr 1
  rw [← map_zpow, Units.coe_map]
  rfl

end transport

variable {K : Type*} [Field K]

theorem coeffMap_TS {L : Type*} [Field L] (σ : L →+* K) (e : ℕ) [NeZero e] (u : Lˣ) :
    coeffMap σ (TS L e u) = TS K e (Units.map σ.toMonoidHom u) := by
  rw [TS, TS, coeffMap_qExpand, coeffMap_qTwist]
  exact congrArg (fun z => qExpand K e (qTwist (Units.map σ.toMonoidHom u) z)) (map_jqModC σ)

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

@[scoped simp] theorem qTwistEquiv_apply (u : Kˣ) (f : LaurentSeries K) : qTwistEquiv u f = qTwist u f := rfl

theorem coe_qTwistEquiv (u : Kˣ) :
    ((qTwistEquiv u : LaurentSeries K ≃+* LaurentSeries K) : LaurentSeries K →+* LaurentSeries K) = qTwist u :=
  RingHom.ext fun _ => rfl

theorem qTwist_TS_one_cycle (ζ : Kˣ) {p : ℕ} (hζp : ζ ^ p = 1) (b : ℕ) :
    qTwist ζ (TS K 1 (ζ ^ b)) = TS K 1 (ζ ^ ((b + 1) % p)) := by
  rw [qTwist_TS]
  congr 1
  have : ζ ^ ((1 : ℕ) : ℤ) * ζ ^ b = ζ ^ (b + 1) := by rw [zpow_natCast, pow_one, pow_succ']
  rw [this]
  conv_lhs => rw [← Nat.mod_add_div (b + 1) p, pow_add, pow_mul, hζp, one_pow, mul_one]

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

theorem units_pow_eq_one_of_isPrimitiveRoot {N : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N) : ζ ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one])

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeff_jqModC_neg_one order_jqModC PhiGen.splits_prime_at_slot_of_isPrimitiveRoot exists_phiIrreducible_evalSymm minpoly_jqNModC_map_eq_prod_slots"
namespace W1
p2m_open "ModularCurve"

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

theorem phiAtSeed_eval_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x y : R) (f : R →+* S) (h : (phiAtSeed data x).eval y = 0) :
    (phiAtSeed data (f x)).eval (f y) = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom, h, map_zero]

theorem phiAtSeed_jqNModC_eval {R : Type*} [CommRing R] (n : ℕ) [NeZero n] (data : ModularPolynomialData n)
    (d : ℕ) [NeZero d] : (phiAtSeed data (jqNModC R d)).eval (jqNModC R (d * n)) = 0 := by
  have h := data.eval_jqNModC_mul_eq_zero R d
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2 <;> try rfl
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp

theorem phiAtSeed_jqNModC_eval_symm {R : Type*} [CommRing R] (n : ℕ) [NeZero n] (data : ModularPolynomialData n)
    (hsymm : EvalSymm data.Φ) (d : ℕ) [NeZero d] :
    (phiAtSeed data (jqNModC R (d * n))).eval (jqNModC R d) = 0 := by
  have h := data.eval_jqNModC_of_mul_eq_zero hsymm R d
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2 <;> try rfl
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp

theorem phiAtSeed_TS_eval {K : Type*} [Field K] (A : ℕ) [NeZero A] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n) (d : ℕ) [NeZero d] :
    (phiAtSeed data (TS K (A * d) 1)).eval (TS K (A * (d * n)) 1) = 0 := by
  have h := phiAtSeed_eval_map data _ _ (qExpand K A) (phiAtSeed_jqNModC_eval (R := K) n data d)
  rwa [qExpand_jqNModC, qExpand_jqNModC] at h

theorem phiAtSeed_TS_eval_symm {K : Type*} [Field K] (A : ℕ) [NeZero A] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n) (hsymm : EvalSymm data.Φ) (d : ℕ) [NeZero d] :
    (phiAtSeed data (TS K (A * (d * n)) 1)).eval (TS K (A * d) 1) = 0 := by
  have h := phiAtSeed_eval_map data _ _ (qExpand K A) (phiAtSeed_jqNModC_eval_symm (R := K) n data hsymm d)
  rwa [qExpand_jqNModC, qExpand_jqNModC] at h

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeff_jqModC_neg_one order_jqModC PhiGen.splits_prime_at_slot_of_isPrimitiveRoot exists_phiIrreducible_evalSymm minpoly_jqNModC_map_eq_prod_slots"
namespace W1
p2m_open "ModularCurve"

variable {K : Type*} [Field K]

private theorem prod_form_ne_zero (ζ : Kˣ) (p : ℕ) [NeZero p] (e : ℕ) [NeZero e] (u : Kˣ) :
    (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)))) *
        ∏ b ∈ Finset.range p,
          (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) ≠ 0 :=
  mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero

theorem roots_prime_at_slot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).roots
      = (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))) ::ₘ
          (Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) := by
  rw [ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u,
    Polynomial.roots_mul (prod_form_ne_zero ζ p e u), Polynomial.roots_X_sub_C,
    Finset.prod_eq_multiset_prod, Finset.range_val,
    show (Multiset.range p).map
          (fun b => Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K))))
        = ((Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))).map
            (fun a => Polynomial.X - Polynomial.C a) from
      (Multiset.map_map (fun a => Polynomial.X - Polynomial.C a)
        (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) (Multiset.range p)).symm,
    Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

theorem roots_prime_at_slot_nodup (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    ((qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))) ::ₘ
        (Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))).Nodup := by
  rw [Multiset.nodup_cons]
  constructor
  · intro hmem
    obtain ⟨b, hb, heq⟩ := Multiset.mem_map.mp hmem
    have h := (TS_injective (K := K) (e := e) (e' := p * (p * e)) (u := u * ζ ^ b) (u' := u ^ (p * p)) heq).1
    have hp2 : 2 ≤ p := hp.out.two_le
    have he1 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
    have hmono : 2 * (2 * e) ≤ p * (p * e) := Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
    rw [← h] at hmono
    omega
  · refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range p)
    intro b hb b' hb' heq
    rw [Multiset.mem_range] at hb hb'
    have h := (TS_injective (K := K) (e := e) (e' := e) (u := u * ζ ^ b) (u' := u * ζ ^ b') heq).2
    have h2 : ζ ^ b = ζ ^ b' := mul_left_cancel h
    have h3 : ((ζ : Kˣ) : K) ^ b = ((ζ : Kˣ) : K) ^ b' := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2]
    exact hζ.pow_inj hb hb' h3

theorem roots_prime_at_slot_roots_nodup (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).roots.Nodup := by
  rw [roots_prime_at_slot p ζ hζ data e u]
  exact roots_prime_at_slot_nodup p ζ hζ e u

theorem isRoot_prime_at_slot_iff (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) (y : LaurentSeries K) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).IsRoot y ↔
      y = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)) ∨
        ∃ b < p, y = qExpand K e (qTwist (u * ζ ^ b) (jqModC K)) := by
  have hne : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))) ≠ 0 := by
    rw [ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u]
    exact prod_form_ne_zero ζ p e u
  rw [← Polynomial.mem_roots hne, roots_prime_at_slot p ζ hζ data e u, Multiset.mem_cons, Multiset.mem_map]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mp hb, rfl⟩
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mpr hb, rfl⟩

theorem roots_phiAtSeed_TS (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (phiAtSeed data (TS K (p * e) (u ^ p))).roots
      = TS K (p * (p * e)) (u ^ (p * p)) ::ₘ (Multiset.range p).map (fun b => TS K e (u * ζ ^ b)) :=
  roots_prime_at_slot p ζ hζ data e u

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeff_jqModC_neg_one order_jqModC PhiGen.splits_prime_at_slot_of_isPrimitiveRoot exists_phiIrreducible_evalSymm minpoly_jqNModC_map_eq_prod_slots"
namespace W1
p2m_open "ModularCurve"

variable {K : Type*} [Field K]

theorem jqNModC_mem_mffC_mul_prime_of_prod (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ₁ : Kˣ) (ζ₂ : Kˣ) (hζ₂ : IsPrimitiveRoot (ζ₂ : K) p)
    (hprod : (minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M)).map
        ((qExpand K M).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            (LaurentSeries K)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
            letI : NeZero a := ⟨h⟩
            qExpand K (a * a) (qTwist (ζ₁ ^ (b * a)) (jqModC K))))) :
    jqNModC K M ∈ modularFunctionFieldC K (M * p) := by
  classical
  obtain ⟨data, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hp2 : 2 ≤ p := hp.out.two_le

  have hjNmem : jqNModC K (M * p) ∈ modularFunctionFieldC K (M * p) := jqNModC_mem K (M * p)
  have hle : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ modularFunctionFieldC K (M * p) :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem K (M * p)))
  letI : Algebra (modularFunctionFieldC K (M * p)) (LaurentSeries K) :=
    ((qExpand K (M * p)).comp (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))).toAlgebra

  set A : Polynomial (modularFunctionFieldC K (M * p)) :=
    phiAtSeed data (⟨jqNModC K (M * p), hjNmem⟩ : modularFunctionFieldC K (M * p)) with hA

  let ι₀ : (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) →+* modularFunctionFieldC K (M * p) :=
    { toFun := fun x => ⟨(x : LaurentSeries K), hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  set m : Polynomial (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :=
    minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M) with hm
  have hm0 : Polynomial.aeval (jqNModC K M) m = 0 := minpoly.aeval _ _
  set B : Polynomial (modularFunctionFieldC K (M * p)) := m.map ι₀ with hB

  have hmapA : A.map (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))
      = phiAtSeed data (qExpand K (M * p) (jqNModC K (M * p))) :=
    phiAtSeed_map data _ _
  have hseed : qExpand K (M * p) (jqNModC K (M * p))
      = qExpand K (p * (M * p * M)) (qTwist ((1 : Kˣ) ^ p) (jqModC K)) := by
    have h2 : TS K (M * p * (M * p)) 1 = TS K (p * (M * p * M)) ((1 : Kˣ) ^ p) := by
      rw [one_pow]
      exact TS_congr (by ring) 1
    exact (qExpand_jqNModC (M * p) (M * p)).trans h2
  have hdist : qExpand K (M * p) (jqNModC K M)
      = qExpand K (M * p * M) (qTwist (1 * ζ₂ ^ 0) (jqModC K)) := by
    rw [pow_zero, mul_one]
    exact qExpand_jqNModC (M * p) M

  have hrootA : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 ↔
      (y = qExpand K (p * (p * (M * p * M))) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ∨
        ∃ c < p, y = qExpand K (M * p * M) (qTwist (1 * ζ₂ ^ c) (jqModC K))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA, hseed]
    exact isRoot_prime_at_slot_iff p ζ₂ hζ₂ data (M * p * M) 1 y

  have hcomp : (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K)).comp ι₀
      = (qExpand K (M * p)).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K)) :=
    RingHom.ext fun _ => rfl

  have hbig : (qExpand K (M * p)).comp
        (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K))
      = (qExpand K p).comp ((qExpand K M).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K))) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    rw [qExpand_qExpand]
    exact qExpand_congr (Nat.mul_comm M p) _

  have hBroot : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 →
      ∃ a : ℕ, a ∣ M ∧ ∃ b : ℕ, b < M / a ∧ ∃ (_ : NeZero a), y = TS K (p * (a * a)) (ζ₁ ^ (b * a)) := by
    intro y hy
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map, hcomp, hbig, ← Polynomial.map_map,
      hprod] at hy
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_filter,
      Finset.mem_range, Nat.mem_divisors, sub_eq_zero] at hy
    obtain ⟨a, ⟨haM, -⟩, b, ⟨hb, -⟩, hy⟩ := hy
    have ha0 : a ≠ 0 := fun h0 => NeZero.ne M (Nat.eq_zero_of_zero_dvd (h0 ▸ haM))
    haveI : NeZero a := ⟨ha0⟩
    refine ⟨a, haM, b, hb, inferInstance, ?_⟩
    rw [hy, dif_neg ha0]
    show qExpand K p (qExpand K (a * a) (qTwist (ζ₁ ^ (b * a)) (jqModC K)))
      = qExpand K (p * (a * a)) (qTwist (ζ₁ ^ (b * a)) (jqModC K))
    rw [qExpand_qExpand]

  have hA0 : A ≠ 0 := (phiAtSeed_monic data _).ne_zero
  have hAs : (A.map (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))).Splits := by
    rw [hmapA, hseed, phiAtSeed,
      ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ₂ hζ₂ data (M * p * M) 1]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _)
  have hAnd : (A.map (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))).roots.Nodup := by
    rw [hmapA, hseed, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup p ζ₂ hζ₂ data (M * p * M) 1

  have hxA : Polynomial.aeval (qExpand K (M * p) (jqNModC K M)) A = 0 :=
    (hrootA _).mpr (Or.inr ⟨0, hp.out.pos, hdist⟩)
  have hxB : Polynomial.aeval (qExpand K (M * p) (jqNModC K M)) B = 0 := by
    have hm0' := hm0
    rw [Polynomial.aeval_def] at hm0'
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map, hcomp, Polynomial.eval_map,
      ← Polynomial.hom_eval₂, hm0', map_zero]

  have huniq : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 →
      y = qExpand K (M * p) (jqNModC K M) := by
    intro y hyA hyB
    obtain ⟨a, haM, b, hb, ha, hy⟩ := hBroot y hyB
    have haM' : a ≤ M := Nat.le_of_dvd hM0 haM
    have h3 : a * a ≤ M * M := Nat.mul_le_mul haM' haM'
    have hMM : 0 < M * M := Nat.mul_pos hM0 hM0
    have h5 : M * p * M = p * (M * M) := by ring
    rcases (hrootA y).mp hyA with hy1 | ⟨c, hc, hy1⟩
    · exfalso
      have hTS : TS K (p * (p * (M * p * M))) ((1 : Kˣ) ^ (p * p)) = TS K (p * (a * a)) (ζ₁ ^ (b * a)) := by
        rw [← hy]
        exact hy1.symm
      have he : p * (p * (M * p * M)) = p * (a * a) := (TS_injective hTS).1
      have h6 : p * (M * p * M) = a * a := Nat.eq_of_mul_eq_mul_left hp.out.pos he
      rw [h5] at h6
      have h7 : 2 * (2 * (M * M)) ≤ p * (p * (M * M)) := Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
      omega
    · have hTS : TS K (M * p * M) (1 * ζ₂ ^ c) = TS K (p * (a * a)) (ζ₁ ^ (b * a)) := by
        rw [← hy]
        exact hy1.symm
      obtain ⟨he, hu⟩ := TS_injective hTS
      rw [h5] at he
      have h6 : M * M = a * a := Nat.eq_of_mul_eq_mul_left hp.out.pos he
      have haM2 : a = M := (Nat.mul_self_inj.mp h6).symm
      rw [haM2, Nat.div_self hM0] at hb
      have hb0 : b = 0 := Nat.lt_one_iff.mp hb
      rw [hb0, Nat.zero_mul, pow_zero, one_mul] at hu
      have hval : ((ζ₂ : Kˣ) : K) ^ c = 1 := by
        have h := congrArg Units.val hu
        rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
      have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt ((hζ₂.pow_eq_one_iff_dvd c).mp hval) hc
      rw [hc0] at hy1
      exact hy1.trans hdist.symm

  have hrange := Polynomial.mem_range_of_unique_common_root A B hA0 hAs hAnd _ hxA hxB huniq
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hrange
  have hf' : qExpand K (M * p) (f : LaurentSeries K) = qExpand K (M * p) (jqNModC K M) := hf
  have hval : (f : LaurentSeries K) = jqNModC K M := qExpand_injective (M * p) hf'
  rw [← hval]
  exact f.2

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeff_jqModC_neg_one order_jqModC PhiGen.splits_prime_at_slot_of_isPrimitiveRoot exists_phiIrreducible_evalSymm minpoly_jqNModC_map_eq_prod_slots" end ModularCurve
p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime {K : Type*} [Field K]
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    jqNModC K M ∈ modularFunctionFieldC K (M * p) :=
  jqNModC_mem_mffC_mul_prime_of_prod M p (ζ ^ (M * p / M)) (ζ ^ (M * p / p))
    (isPrimitiveRoot_pow_div hζ (dvd_mul_left p M))
    (ModularCurve.minpoly_jqNModC_map_eq_prod_slots M (ζ ^ (M * p / M)) (isPrimitiveRoot_pow_div hζ (dvd_mul_right M p))
      hall)

end
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve.W1"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.ModularCurve in

theorem solution {K : Type*} [Field K]
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    jqNModC K M ∈ modularFunctionFieldC K (M * p) :=
  ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime M p ζ hζ hall

#print axioms solution

end S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime
end P2MW
export P2MW.S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime (solution)
