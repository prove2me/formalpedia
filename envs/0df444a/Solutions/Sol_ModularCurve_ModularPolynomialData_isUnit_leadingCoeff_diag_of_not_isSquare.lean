-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/275c90a1-2f8f-5135-bc89-8293fe48778f

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_PhiGen_evalAtJ_injective
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve ModularCurve.PhiGen"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

section U2Kit

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in

private theorem w1_order_eq {x : LaurentSeries K} {a : ℤ}
    (hne : x.coeff a ≠ 0) (hlow : ∀ k, k < a → x.coeff k = 0) :
    x.order = a ∧ x.leadingCoeff = x.coeff a := by
  have hx0 : x ≠ 0 := fun h0 => hne (by simp [h0])
  have h1 : x.order = a := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hne) (not_lt.mp fun hlt => ?_)
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hlow _ hlt))
  exact ⟨h1, by rw [HahnSeries.leadingCoeff_eq, h1]⟩

private theorem w1_order_TS (e : ℕ) [NeZero e] (u : Kˣ) :
    (TS K e u).order = -(e : ℤ) ∧ (TS K e u).leadingCoeff = ((u⁻¹ : Kˣ) : K) := by
  have h := w1_order_eq (x := TS K e u) (a := -(e : ℤ))
    (by rw [TS_coeff_neg]; exact Units.ne_zero _) (fun k hk => TS_coeff_of_lt (K := K) e u hk)
  exact ⟨h.1, by rw [h.2, TS_coeff_neg]⟩

omit [Algebra ℚ K] in

private theorem w1_order_sub_right {x y : LaurentSeries K}
    (h : y.order < x.order) (hy : y ≠ 0) :
    (x - y).order = y.order ∧ (x - y).leadingCoeff = -y.leadingCoeff := by
  have hat : (x - y).coeff y.order = -y.leadingCoeff := by
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order h, zero_sub,
      HahnSeries.leadingCoeff_eq]
  have h' := w1_order_eq (x := x - y) (a := y.order)
    (by rw [hat, neg_ne_zero]; exact fun h0 => hy (HahnSeries.leadingCoeff_eq_zero.mp h0))
    (fun k hk => by
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order (hk.trans h),
        HahnSeries.coeff_eq_zero_of_lt_order hk, sub_zero])
  exact ⟨h'.1, by rw [h'.2, hat]⟩

omit [Algebra ℚ K] in

private theorem w1_order_sub_left {x y : LaurentSeries K}
    (h : x.order < y.order) (hx : x ≠ 0) :
    (x - y).order = x.order ∧ (x - y).leadingCoeff = x.leadingCoeff := by
  have hat : (x - y).coeff x.order = x.leadingCoeff := by
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order h, sub_zero,
      HahnSeries.leadingCoeff_eq]
  have h' := w1_order_eq (x := x - y) (a := x.order)
    (by rw [hat]; exact fun h0 => hx (HahnSeries.leadingCoeff_eq_zero.mp h0))
    (fun k hk => by
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order hk,
        HahnSeries.coeff_eq_zero_of_lt_order (hk.trans h), sub_zero])
  exact ⟨h'.1, by rw [h'.2, hat]⟩

omit [Algebra ℚ K] in

private theorem w1_prod_ne_zero_leadingCoeff {α : Type*} (s : Finset α)
    (F : α → LaurentSeries K) (h : ∀ i ∈ s, F i ≠ 0) :
    (∏ i ∈ s, F i) ≠ 0 ∧ (∏ i ∈ s, F i).leadingCoeff = ∏ i ∈ s, (F i).leadingCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h0, hlc⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha0 : F a ≠ 0 := h a (Finset.mem_insert_self a s)
    have hne : (F a).leadingCoeff * (∏ i ∈ s, F i).leadingCoeff ≠ 0 :=
      mul_ne_zero (fun hz => ha0 (HahnSeries.leadingCoeff_eq_zero.mp hz))
        (fun hz => h0 (HahnSeries.leadingCoeff_eq_zero.mp hz))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨mul_ne_zero ha0 h0,
      by rw [HahnSeries.leadingCoeff_mul_of_ne_zero hne, hlc]⟩

private theorem w1_slot_factor (N a b : ℕ) [NeZero N] [NeZero a] (hN : ¬ IsSquare N)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    (TS K N 1 - TS K (a * a) (ζ ^ (b * a))) ≠ 0 ∧
      (TS K N 1 - TS K (a * a) (ζ ^ (b * a))).leadingCoeff ^ (2 * N) = 1 := by
  have hne : a * a ≠ N := fun h => hN ⟨a, h.symm⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  ·
    obtain ⟨hoN, hlN⟩ := w1_order_TS (K := K) N 1
    obtain ⟨hoa, _⟩ := w1_order_TS (K := K) (a * a) (ζ ^ (b * a))
    have hord : (TS K N 1).order < (TS K (a * a) (ζ ^ (b * a))).order := by
      rw [hoN, hoa]
      push_cast
      omega
    obtain ⟨_, hlc⟩ := w1_order_sub_left hord (TS_ne_zero (K := K) N 1)
    have hlc1 : (TS K N 1 - TS K (a * a) (ζ ^ (b * a))).leadingCoeff = 1 := by
      rw [hlc, hlN, inv_one, Units.val_one]
    refine ⟨fun h0 => one_ne_zero (α := K) ?_, by rw [hlc1, one_pow]⟩
    rw [← hlc1, h0, HahnSeries.leadingCoeff_eq_zero.mpr rfl]
  ·
    obtain ⟨hoN, _⟩ := w1_order_TS (K := K) N 1
    obtain ⟨hoa, hla⟩ := w1_order_TS (K := K) (a * a) (ζ ^ (b * a))
    have hord : (TS K (a * a) (ζ ^ (b * a))).order < (TS K N 1).order := by
      rw [hoN, hoa]
      push_cast
      omega
    obtain ⟨_, hlc⟩ := w1_order_sub_right hord (TS_ne_zero (K := K) (a * a) (ζ ^ (b * a)))
    have hlcv : (TS K N 1 - TS K (a * a) (ζ ^ (b * a))).leadingCoeff =
        -((ζ : K) ^ (b * a))⁻¹ := by
      rw [hlc, hla, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have hvne : -((ζ : K) ^ (b * a))⁻¹ ≠ 0 := by
      rw [neg_ne_zero]
      exact inv_ne_zero (pow_ne_zero _ (Units.ne_zero ζ))
    refine ⟨fun h0 => hvne ?_, ?_⟩
    · rw [← hlcv, h0, HahnSeries.leadingCoeff_eq_zero.mpr rfl]
    · have hzN : (ζ : K) ^ N = 1 := hζ.pow_eq_one
      have hv : (((ζ : K) ^ (b * a)) ^ (2 * N) : K) = 1 := by
        rw [← pow_mul, show b * a * (2 * N) = N * (2 * (b * a)) by ring, pow_mul, hzN, one_pow]
      have heven : Even (2 * N) := ⟨N, by ring⟩
      rw [hlcv, heven.neg_pow, inv_pow, hv, inv_one]

end U2Kit
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"

open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

private theorem w1_evalAtJGen_injective : Function.Injective evalAtJGen := by
  have h : Function.Injective ((algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) ∘ evalAtJGen) := by
    rw [← RingHom.coe_comp, algebraMap_comp_evalAtJGen]
    exact evalAtJ_injective
  exact h.of_comp

private theorem w1_aeval_jqN_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.aeval_def, Polynomial.eval₂_map,
    algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

private theorem w1_natDegree_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

private theorem w1_toAdjoin_eq_minpoly (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN N) := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) := ⟨data.toAdjoin, data.toAdjoin_monic, by
    simpa [Polynomial.aeval_def] using w1_aeval_jqN_toAdjoin data⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN N)).natDegree = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_dedekindPsi N
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ (w1_aeval_jqN_toAdjoin data)) ?_
  rw [hdeg, w1_natDegree_toAdjoin]

private theorem w1_diag_lc_pow (N : ℕ) [NeZero N] (hN : ¬ IsSquare N)
    (data : ModularPolynomialData N) :
    (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff ^ (2 * N) = 1 := by
  classical
  set D : Polynomial ℤ := data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X with hD
  set K := CyclotomicField N ℚ with hK
  set ζ : Kˣ := cycUnit N with hζdef
  have hζ := cycUnit_spec N
  set f : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ N) with hf
  set W : LaurentSeries ℚ := evalAtJ D with hW

  have hcensus := minpoly_jqN_map_eq_prod_slots (K := K) N ζ hζ
    (fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩)

  have hhom : ((((coeffEmb K).comp (qExpand ℚ N)).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).comp evalAtJGen) = f.comp evalAtJ := by
    rw [RingHom.comp_assoc, algebraMap_comp_evalAtJGen, hf]
  have hmaps : data.Φ.map (f.comp evalAtJ) =
      ∏ a ∈ N.divisors, ∏ b ∈ (Finset.range (N / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
        (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))) := by
    rw [← hcensus, ← w1_toAdjoin_eq_minpoly N data, ModularPolynomialData.toAdjoin,
      Polynomial.map_map, hhom]

  have hfjq : f jq = TS K N 1 := iota_jq N
  have hfact : f W = ∏ a ∈ N.divisors, ∏ b ∈ (Finset.range (N / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
      (TS K N 1 - (if h : a = 0 then 0 else
        letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))) := by
    have h1 : f W = (data.Φ.map (f.comp evalAtJ)).eval (f jq) := by
      rw [hW, ← RingHom.comp_apply, hD, Polynomial.hom_eval₂, RingHom.comp_id,
        Polynomial.eval₂_eq_eval_map, RingHom.comp_apply, evalAtJ_X]
    rw [h1, hmaps, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hfjq]

  have hinner : ∀ a ∈ N.divisors,
      (∏ b ∈ (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
        (TS K N 1 - (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))))) ≠ 0 ∧
      ((∏ b ∈ (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
        (TS K N 1 - (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))))).leadingCoeff)
        ^ (2 * N) = 1 := by
    intro a ha
    have ha0 : a ≠ 0 := (Nat.pos_of_mem_divisors ha).ne'
    haveI : NeZero a := ⟨ha0⟩
    have hdval : ∀ b : ℕ, (if h : a = 0 then (0 : LaurentSeries K) else
        letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))) =
        TS K (a * a) (ζ ^ (b * a)) := fun b => by rw [dif_neg ha0]; rfl
    simp only [hdval]
    obtain ⟨hne, hlc⟩ := w1_prod_ne_zero_leadingCoeff (K := K)
      ((Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1))
      (fun b => TS K N 1 - TS K (a * a) (ζ ^ (b * a)))
      (fun b _ => (w1_slot_factor N a b hN ζ hζ).1)
    refine ⟨hne, ?_⟩
    rw [hlc, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun b _ => (w1_slot_factor N a b hN ζ hζ).2

  obtain ⟨houter_ne, houter_lc⟩ := w1_prod_ne_zero_leadingCoeff (K := K) N.divisors _
    (fun a ha => (hinner a ha).1)
  have hfW_ne : f W ≠ 0 := by rw [hfact]; exact houter_ne
  have hfW_pow : (f W).leadingCoeff ^ (2 * N) = 1 := by
    rw [hfact, houter_lc, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun a ha => (hinner a ha).2

  have hW_ne : W ≠ 0 := fun h0 => hfW_ne (by rw [h0, map_zero])
  have hD0 : D ≠ 0 := fun h0 => hW_ne (by rw [hW, h0, map_zero])
  have hEJ : evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [evalAtJ, Polynomial.coe_eval₂RingHom]
  have hsum : evalAtJ D = ∑ i ∈ Finset.range (D.natDegree + 1), (D.coeff i) • jq ^ i := by
    rw [hEJ]
    show Polynomial.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq D = _
    rw [Polynomial.eval₂_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => (zsmul_eq_mul _ _).symm
  have hWcoeff : ∀ m : ℤ, W.coeff m =
      ∑ i ∈ Finset.range (D.natDegree + 1), (D.coeff i) • (jq ^ i).coeff m := by
    intro m
    rw [hW, hsum, HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ => HahnSeries.coeff_smul
  have hlow : ∀ m : ℤ, m < -(D.natDegree : ℤ) → W.coeff m = 0 := by
    intro m hm
    rw [hWcoeff]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [coeff_jq_pow_of_lt, smul_zero]
    have : i ≤ D.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    omega
  have htop : W.coeff (-(D.natDegree : ℤ)) = (D.leadingCoeff : ℚ) := by
    rw [hWcoeff]
    rw [Finset.sum_eq_single D.natDegree]
    · rw [coeff_jq_pow_self, Polynomial.leadingCoeff]
      rw [zsmul_eq_mul, mul_one]
    · intro i hi hne
      have hilt : i < D.natDegree :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      rw [coeff_jq_pow_of_lt (by omega), smul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr D.natDegree.lt_succ_self) h

  have hPcoeff : ∀ m : ℤ, (f W).coeff ((N : ℤ) * m) = algebraMap ℚ K (W.coeff m) := by
    intro m
    rw [hf, RingHom.comp_apply, coeffEmb_coeff, qExpand_coeff_mul]
  have hPnd : ∀ k : ℤ, ¬ (N : ℤ) ∣ k → (f W).coeff k = 0 := by
    intro k hk
    rw [hf, RingHom.comp_apply, coeffEmb_coeff, qExpand_coeff_of_not_dvd N W hk, map_zero]
  have hcoeff_at : (f W).coeff ((N : ℤ) * (-(D.natDegree : ℤ))) =
      algebraMap ℚ K ((D.leadingCoeff : ℚ)) := by
    rw [hPcoeff, htop]
  have hlcD : (f W).leadingCoeff = algebraMap ℚ K ((D.leadingCoeff : ℚ)) := by
    have hne_at : (f W).coeff ((N : ℤ) * (-(D.natDegree : ℤ))) ≠ 0 := by
      rw [hcoeff_at]
      intro h0
      have : (D.leadingCoeff : ℚ) = 0 := (algebraMap ℚ K).injective (by rw [h0, map_zero])
      exact Polynomial.leadingCoeff_ne_zero.mpr hD0 (by exact_mod_cast this)
    have hbelow : ∀ k : ℤ, k < (N : ℤ) * (-(D.natDegree : ℤ)) → (f W).coeff k = 0 := by
      intro k hk
      by_cases hdvd : (N : ℤ) ∣ k
      · obtain ⟨m, rfl⟩ := hdvd
        rw [hPcoeff]
        have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        rw [hlow m (lt_of_mul_lt_mul_left hk hNpos.le), map_zero]
      · exact hPnd _ hdvd
    obtain ⟨_, hlc_eq⟩ := w1_order_eq hne_at hbelow
    rw [hlc_eq, hcoeff_at]

  have hQpow : ((D.leadingCoeff : ℚ)) ^ (2 * N) = 1 := by
    refine (algebraMap ℚ K).injective ?_
    rw [map_pow, map_one, ← hlcD]
    exact hfW_pow
  exact_mod_cast hQpow

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_prime_at_slot minpoly_jqN_map_eq_prod_slots finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full" namespace ModularPolynomialData p2m_export "ModularCurve.ModularPolynomialData" "toAdjoin toAdjoin_monic monic eval_eq_zero natDegree_eq Φ" end ModularCurve.ModularPolynomialData
p2m_open_scoped "ModularCurve ModularCurve.ModularPolynomialData" in

private theorem ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare
    (N : ℕ) [NeZero N] (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) :
    IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff := by
  have h := ModularCurve.W1.w1_diag_lc_pow N hN data
  have h1 : (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff.natAbs
      ^ (2 * N) = 1 := by
    have h' := congrArg Int.natAbs h
    rwa [Int.natAbs_pow] at h'
  have h2 : (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff.natAbs = 1 := by
    rcases Nat.pow_eq_one.mp h1 with h' | h'
    · exact h'
    · have := NeZero.ne N
      omega
  exact Int.isUnit_iff.mpr ((Int.natAbs_eq_iff.mp h2).imp id (by simp))

p2m_open_scoped "ModularCurve ModularCurve.ModularPolynomialData" in

theorem ModularCurve.ModularPolynomialData.leadingCoeff_diag_sq_eq_one
    (N : ℕ) [NeZero N] (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff ^ 2 = 1 := by
  rcases Int.isUnit_iff.mp
    (ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare N hN data)
    with h | h <;> rw [h] <;> norm_num

end
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve.W1"

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.ModularCurve in

theorem solution (N : ℕ) [NeZero N] (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) : IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff :=
  ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare N hN data

#print axioms solution

end S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare (solution)
