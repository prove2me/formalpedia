-- Prove2me | solution 1 for ModularCurve.relfinrank_qExpand_full
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/deeaf788-3129-5550-ad6c-589e3226ea8c

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_Polynomial_irreducible_of_transitive_ringAut
import Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_jqN_prime_not_mem_full
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Relrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_qExpand_full
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve ModularCurve.PhiGen"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionField modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm coeffMap_qExpand PhiGen.splits_prime_at_slot exists_phiIrreducible_evalSymm dedekindPsi_prime jqN_prime_not_mem_full finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionField modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm coeffMap_qExpand PhiGen.splits_prime_at_slot exists_phiIrreducible_evalSymm dedekindPsi_prime jqN_prime_not_mem_full finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionField modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm coeffMap_qExpand PhiGen.splits_prime_at_slot exists_phiIrreducible_evalSymm dedekindPsi_prime jqN_prime_not_mem_full finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionField modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm coeffMap_qExpand PhiGen.splits_prime_at_slot exists_phiIrreducible_evalSymm dedekindPsi_prime jqN_prime_not_mem_full finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionField modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm coeffMap_qExpand PhiGen.splits_prime_at_slot exists_phiIrreducible_evalSymm dedekindPsi_prime jqN_prime_not_mem_full finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
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
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp [evalAtJ_X]

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
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionField modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm coeffMap_qExpand PhiGen.splits_prime_at_slot exists_phiIrreducible_evalSymm dedekindPsi_prime jqN_prime_not_mem_full finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

private theorem jqN_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) : jqN n = jqN m := by
  subst h; rfl

private theorem g2_relfinrank_union_left (E : IntermediateField ℚ (LaurentSeries ℚ))
    (α : LaurentSeries ℚ) :
    IntermediateField.relfinrank E
      (IntermediateField.adjoin ℚ ((E : Set (LaurentSeries ℚ)) ∪ {α}))
      = Module.finrank E (IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ))) := by
  have h : E ≤ IntermediateField.adjoin ℚ ((E : Set (LaurentSeries ℚ)) ∪ {α}) := by
    intro x hx
    exact IntermediateField.subset_adjoin _ _ (Set.mem_union_left _ hx)
  have hEq : IntermediateField.adjoin E ((E : Set (LaurentSeries ℚ)) ∪ {α})
      = IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ)) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · exact (IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ))).algebraMap_mem ⟨x, hx⟩
      · exact IntermediateField.subset_adjoin _ _ rfl
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
  rw [IntermediateField.relfinrank_eq_finrank_of_le h, IntermediateField.extendScalars_adjoin h,
    hEq]

section g2core

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem g2_coeffEmb_injective : Function.Injective (coeffEmb K) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries K => z.coeff k) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ K).injective this

variable (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)]

private theorem g2_zeta_mod (a : ℕ) :
    (cycUnit ℓ) ^ a = (cycUnit ℓ) ^ (a % ℓ) := by
  conv_lhs => rw [← Nat.div_add_mod a ℓ]
  rw [pow_add, pow_mul, cycUnit_pow, one_pow, one_mul]

private theorem g2_seed_eq :
    coeffEmb (CyclotomicField ℓ ℚ) (jqN ℓ)
      = qExpand (CyclotomicField ℓ ℚ) (ℓ * 1)
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ ℓ) (coeffEmb (CyclotomicField ℓ ℚ) jq)) := by
  rw [jqN, coeffEmb_qExpand, one_pow, qTwist_one_apply]
  exact qExpand_congr (mul_one ℓ).symm _

private theorem g2_y0_eq :
    coeffEmb (CyclotomicField ℓ ℚ) (jqN (ℓ * ℓ))
      = qExpand (CyclotomicField ℓ ℚ) (ℓ * (ℓ * 1))
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ (ℓ * ℓ))
            (coeffEmb (CyclotomicField ℓ ℚ) jq)) := by
  rw [jqN, coeffEmb_qExpand, one_pow, qTwist_one_apply]
  exact qExpand_congr (by ring) _

private theorem g2_twist_fix (x : LaurentSeries ℚ) :
    qTwist (cycUnit ℓ) (coeffEmb (CyclotomicField ℓ ℚ) (qExpand ℚ ℓ x))
      = coeffEmb (CyclotomicField ℓ ℚ) (qExpand ℚ ℓ x) := by
  rw [coeffEmb_qExpand, qTwist_qExpand, zpow_natCast, cycUnit_pow, qTwist_one_apply]

end g2core
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"

theorem phiAtSeed_eval_symm {n : ℕ} [NeZero n] (data : ModularPolynomialData n)
    (hs : EvalSymm data.Φ) (x y : LaurentSeries ℚ) :
    (phiAtSeed data x).eval y = (phiAtSeed data y).eval x := by
  have key : ∀ z : LaurentSeries ℚ, Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) z =
      (Polynomial.aeval (R := ℤ) z).toRingHom := fun z =>
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  rw [phiAtSeed, phiAtSeed, Polynomial.eval_map, Polynomial.eval_map, key, key]
  exact hs x y

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionField modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand EvalSymm coeffMap_qExpand PhiGen.splits_prime_at_slot exists_phiIrreducible_evalSymm dedekindPsi_prime jqN_prime_not_mem_full finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full" end ModularCurve
p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.finrank_adjoin_jq_of_subset_range_qExpand (F : IntermediateField ℚ (LaurentSeries ℚ)) (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)] (hF : (F : Set (LaurentSeries ℚ)) ⊆ Set.range (qExpand ℚ ℓ)) (hmem : jqN ℓ ∈ F) (hnot : jqN (ℓ * ℓ) ∉ F) : Module.finrank F (IntermediateField.adjoin F ({jq} : Set (LaurentSeries ℚ))) = ℓ + 1 := by
  classical
  obtain ⟨data, -, hs⟩ := exists_phiIrreducible_evalSymm ℓ
  set jlF : F := ⟨jqN ℓ, hmem⟩ with hjlF
  set Q : Polynomial F := phiAtSeed data jlF with hQdef
  have hQmonic : Q.Monic := phiAtSeed_monic data jlF
  have hQdeg : Q.natDegree = ℓ + 1 := by
    rw [hQdef, phiAtSeed_natDegree, dedekindPsi_prime hl.out]
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) = phiAtSeed data (jqN ℓ) := by
    rw [hQdef, phiAtSeed_map]; rfl
  have h1ℓ : jqN (1 : ℕ) = jq := by
    rw [jqN]; exact qExpand_one_apply jq
  have hbase : (phiAtSeed data (jqN ℓ)).eval jq = 0 := by
    rw [phiAtSeed_eval_symm data hs]
    have h := phiAtSeed_jqN_eval ℓ data 1
    rwa [jqN_congr (one_mul ℓ), h1ℓ] at h
  have hQjq : Polynomial.aeval jq Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    exact hbase
  have hint : IsIntegral F jq := ⟨Q, hQmonic, by rwa [Polynomial.aeval_def] at hQjq⟩

  letI : Algebra F (LaurentSeries (CyclotomicField ℓ ℚ)) :=
    ((coeffEmb (CyclotomicField ℓ ℚ)).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : ∀ a : F, algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a
      = coeffEmb (CyclotomicField ℓ ℚ) (a : LaurentSeries ℚ) := fun a => rfl
  have hQmapL : Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))
      = phiAtSeed data (qExpand (CyclotomicField ℓ ℚ) (ℓ * 1)
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ ℓ) (coeffEmb (CyclotomicField ℓ ℚ) jq))) := by
    rw [RingHom.algebraMap_toAlgebra, ← Polynomial.map_map, hQmap, phiAtSeed_map, g2_seed_eq]
  have hQroots : (Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots
      = (qExpand (CyclotomicField ℓ ℚ) (ℓ * (ℓ * 1))
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ (ℓ * ℓ)) (coeffEmb (CyclotomicField ℓ ℚ) jq)))
        ::ₘ (Multiset.range ℓ).map
          (fun c => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq)) := by
    rw [hQmapL, phiAtSeed,
      roots_prime_at_slot ℓ (cycUnit ℓ) (cycUnit_spec ℓ) ℓ (dvd_refl ℓ) data 1 1]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [Nat.div_self hl.out.pos, mul_one, one_mul, qExpand_one_apply]
  have hQnodup : (Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots.Nodup := by
    rw [hQmapL, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup ℓ (cycUnit ℓ) (cycUnit_spec ℓ) ℓ (dvd_refl ℓ) data 1 1
  have hQsplits : (Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).Splits := by
    rw [Polynomial.splits_iff_card_roots, hQroots, Multiset.card_cons, Multiset.card_map,
      Multiset.card_range, hQmonic.natDegree_map, hQdeg]
  have hσfix : ∀ a : F,
      (qTwistEquiv (cycUnit ℓ)) (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a)
        = algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a := by
    intro a
    obtain ⟨x, hx⟩ := hF a.2
    rw [halg, ← hx, qTwistEquiv_apply, g2_twist_fix]
  have hcycle : ∀ i < ℓ,
      (qTwistEquiv (cycUnit ℓ)) (qTwist (cycUnit ℓ ^ i) (coeffEmb (CyclotomicField ℓ ℚ) jq))
        = qTwist (cycUnit ℓ ^ ((i + 1) % ℓ)) (coeffEmb (CyclotomicField ℓ ℚ) jq) := by
    intro i _
    rw [qTwistEquiv_apply, qTwist_qTwist, ← pow_succ', g2_zeta_mod ℓ (i + 1)]
  have hy₀ : (qExpand (CyclotomicField ℓ ℚ) (ℓ * (ℓ * 1))
      (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ (ℓ * ℓ)) (coeffEmb (CyclotomicField ℓ ℚ) jq)))
      ∉ (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ))).range := by
    rintro ⟨f, hf⟩
    rw [halg] at hf
    have hval : (f : LaurentSeries ℚ) = jqN (ℓ * ℓ) := by
      apply g2_coeffEmb_injective (K := CyclotomicField ℓ ℚ)
      rw [hf, g2_y0_eq]
    exact hnot (hval ▸ f.2)
  have hirr : Irreducible Q :=
    Polynomial.irreducible_of_transitive_ringAut Q hQmonic hQsplits (qTwistEquiv (cycUnit ℓ))
      hσfix _ _ ℓ hQroots hQnodup hcycle hy₀
  have hmin : Q = minpoly F jq := minpoly.eq_of_irreducible_of_monic hirr hQjq hQmonic
  rw [IntermediateField.adjoin.finrank hint, ← hmin, hQdeg]

p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.finrank_adjoin_jq_of_subset_range_qExpand_of_mem (F : IntermediateField ℚ (LaurentSeries ℚ)) (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)] (hF : (F : Set (LaurentSeries ℚ)) ⊆ Set.range (qExpand ℚ ℓ)) (hmem : jqN ℓ ∈ F) (hin : jqN (ℓ * ℓ) ∈ F) : Module.finrank F (IntermediateField.adjoin F ({jq} : Set (LaurentSeries ℚ))) = ℓ := by
  classical
  obtain ⟨data, -, hs⟩ := exists_phiIrreducible_evalSymm ℓ
  set jlF : F := ⟨jqN ℓ, hmem⟩ with hjlF
  set j2F : F := ⟨jqN (ℓ * ℓ), hin⟩ with hj2F
  set Q : Polynomial F := phiAtSeed data jlF with hQdef
  have hQmonic : Q.Monic := phiAtSeed_monic data jlF
  have hQdeg : Q.natDegree = ℓ + 1 := by
    rw [hQdef, phiAtSeed_natDegree, dedekindPsi_prime hl.out]
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) = phiAtSeed data (jqN ℓ) := by
    rw [hQdef, phiAtSeed_map]; rfl
  have h1ℓ : jqN (1 : ℕ) = jq := by
    rw [jqN]; exact qExpand_one_apply jq
  have hbase : (phiAtSeed data (jqN ℓ)).eval jq = 0 := by
    rw [phiAtSeed_eval_symm data hs]
    have h := phiAtSeed_jqN_eval ℓ data 1
    rwa [jqN_congr (one_mul ℓ), h1ℓ] at h
  have hQjq : Polynomial.aeval jq Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    exact hbase
  have hint : IsIntegral F jq := ⟨Q, hQmonic, by rwa [Polynomial.aeval_def] at hQjq⟩

  have hQj2 : Q.IsRoot j2F := by
    have h0m : algebraMap F (LaurentSeries ℚ) (Q.eval j2F) = algebraMap F (LaurentSeries ℚ) 0 := by
      rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hQmap]
      exact phiAtSeed_jqN_eval ℓ data ℓ
    exact (algebraMap F (LaurentSeries ℚ)).injective h0m
  set P : Polynomial F := Q /ₘ (Polynomial.X - Polynomial.C j2F) with hPdef
  have hfact : (Polynomial.X - Polynomial.C j2F) * P = Q :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQj2
  have hPmonic : P.Monic :=
    Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C j2F)
      (by rw [hfact]; exact hQmonic)
  have hPdeg : P.natDegree = ℓ := by
    have h := congrArg Polynomial.natDegree hfact
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C j2F) hPmonic,
      Polynomial.natDegree_X_sub_C, hQdeg] at h
    omega
  have hne : jq ≠ jqN (ℓ * ℓ) := by
    intro h
    have hA : jq.coeff (-1 : ℤ) = 1 := coeff_jq_neg_one
    have hB : (jqN (ℓ * ℓ)).coeff (-1 : ℤ) = 0 := by
      rw [jqN]
      refine qExpand_coeff_of_not_dvd (ℓ * ℓ) jq ?_
      intro hdvd
      have h4 : (4 : ℕ) ≤ ℓ * ℓ := Nat.mul_le_mul hl.out.two_le hl.out.two_le
      have h1 : ((ℓ * ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp hdvd
      have h2 : ((ℓ * ℓ : ℕ) : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
      have h3 : (4 : ℤ) ≤ ((ℓ * ℓ : ℕ) : ℤ) := by exact_mod_cast h4
      linarith
    rw [h, hB] at hA
    exact zero_ne_one hA
  have hProot : Polynomial.aeval jq P = 0 := by
    have h : Polynomial.aeval jq ((Polynomial.X - Polynomial.C j2F) * P) = 0 := by
      rw [hfact]; exact hQjq
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    rcases mul_eq_zero.mp h with h1' | h2'
    · exact absurd (sub_eq_zero.mp h1') hne
    · exact h2'
  have hdvd : minpoly F jq ∣ P := minpoly.dvd F jq hProot

  letI : Algebra F (LaurentSeries (CyclotomicField ℓ ℚ)) :=
    ((coeffEmb (CyclotomicField ℓ ℚ)).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : ∀ a : F, algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a
      = coeffEmb (CyclotomicField ℓ ℚ) (a : LaurentSeries ℚ) := fun a => rfl
  have hσfixR : ∀ a : F,
      qTwist (cycUnit ℓ) (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a)
        = algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a := by
    intro a
    obtain ⟨x, hx⟩ := hF a.2
    rw [halg, ← hx, g2_twist_fix]

  have hW0 : (minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ))) ≠ 0 :=
    ((minpoly.monic hint).map _).ne_zero
  have hWdeg : ((minpoly F jq).map
      (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).natDegree
      = (minpoly F jq).natDegree := (minpoly.monic hint).natDegree_map _
  have hWfix : ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).map
      (qTwist (cycUnit ℓ)) = (minpoly F jq).map
        (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ))) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext hσfixR
  have hstab : ∀ y : LaurentSeries (CyclotomicField ℓ ℚ),
      ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval y = 0 →
      ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval
        (qTwist (cycUnit ℓ) y) = 0 := by
    intro y hy
    have h2 : (((minpoly F jq).map
        (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).map (qTwist (cycUnit ℓ))).eval
        (qTwist (cycUnit ℓ) y)
        = qTwist (cycUnit ℓ)
            (((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval y) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [hWfix] at h2
    rw [h2, hy, map_zero]
  have hkill0 : ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval
      (coeffEmb (CyclotomicField ℓ ℚ) jq) = 0 := by
    have hV : ((minpoly F jq).map (algebraMap F (LaurentSeries ℚ))).eval jq = 0 := by
      have h := minpoly.aeval F jq
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
    have hWV : (minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))
        = ((minpoly F jq).map (algebraMap F (LaurentSeries ℚ))).map
            (coeffEmb (CyclotomicField ℓ ℚ)) := by
      rw [Polynomial.map_map]; rfl
    rw [hWV, Polynomial.eval_map, Polynomial.eval₂_hom, hV, map_zero]
  have horbit : ∀ c : ℕ, ((minpoly F jq).map
      (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval
        (qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq)) = 0 := by
    intro c
    induction c with
    | zero => rw [pow_zero, qTwist_one_apply]; exact hkill0
    | succ c ih =>
      have h := hstab _ ih
      rwa [qTwist_qTwist, ← pow_succ'] at h
  have hdist : Set.InjOn (fun c : ℕ => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq))
      ↑(Finset.range ℓ) := by
    intro a ha b hb h
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    have hTS : TS (CyclotomicField ℓ ℚ) 1 (cycUnit ℓ ^ a)
        = TS (CyclotomicField ℓ ℚ) 1 (cycUnit ℓ ^ b) :=
      congrArg (qExpand (CyclotomicField ℓ ℚ) 1) h
    have hu : (cycUnit ℓ) ^ a = (cycUnit ℓ) ^ b := (TS_injective hTS).2
    have hval : ((cycUnit ℓ : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ^ a
        = ((cycUnit ℓ : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ^ b := by
      have h2 := congrArg Units.val hu
      rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h2
    exact (cycUnit_spec ℓ).pow_inj ha hb hval
  have hcard : ℓ ≤ (minpoly F jq).natDegree := by
    have hsub : (Finset.range ℓ).image
        (fun c => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq))
        ⊆ ((minpoly F jq).map
            (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots.toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨c, -, rfl⟩ := hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hW0, horbit c⟩
    calc ℓ = ((Finset.range ℓ).image
          (fun c => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq))).card := by
          rw [Finset.card_image_of_injOn hdist, Finset.card_range]
    _ ≤ ((minpoly F jq).map
          (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots.toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ Multiset.card ((minpoly F jq).map
          (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots :=
        Multiset.toFinset_card_le _
    _ ≤ ((minpoly F jq).map
          (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).natDegree :=
        Polynomial.card_roots' _
    _ = (minpoly F jq).natDegree := hWdeg
  have hle : (minpoly F jq).natDegree ≤ ℓ := by
    have h := Polynomial.natDegree_le_of_dvd hdvd hPmonic.ne_zero
    rwa [hPdeg] at h
  rw [IntermediateField.adjoin.finrank hint]
  exact le_antisymm hle hcard

p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.relfinrank_qExpand_full (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] : IntermediateField.relfinrank ((modularFunctionFieldFull N).map (qExpandₐ ℓ)) (modularFunctionFieldFull (N * ℓ)) = if ℓ ∣ N then ℓ else ℓ + 1 := by
  classical
  have hFr : (((modularFunctionFieldFull N).map (qExpandₐ ℓ) :
      IntermediateField ℚ (LaurentSeries ℚ)) : Set (LaurentSeries ℚ))
      ⊆ Set.range (qExpand ℚ ℓ) := by
    rintro x hx
    rw [IntermediateField.coe_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    exact ⟨e, rfl⟩
  have hjqfull : jq ∈ modularFunctionFieldFull N := by
    have h := jqd_mem_full N (one_dvd N)
    rwa [qExpand_one_apply] at h
  have hmemF : jqN ℓ ∈ (modularFunctionFieldFull N).map (qExpandₐ ℓ) := by
    rw [IntermediateField.mem_map]
    exact ⟨jq, hjqfull, by rw [qExpandₐ_apply, jqN]⟩
  have hall : ∀ d : ℕ, d ∣ N → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
      ∧ modularFunctionField d = modularFunctionFieldFull d := by
    intro d _ _
    exact ⟨ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi d,
      ModularCurve.modularFunctionField_eq_full d⟩
  have hmulsq : qExpand ℚ ℓ (jqN ℓ) = jqN (ℓ * ℓ) := by
    rw [jqN, jqN, qExpand_qExpand]
  have hiff : jqN (ℓ * ℓ) ∈ (modularFunctionFieldFull N).map (qExpandₐ ℓ) ↔ ℓ ∣ N := by
    constructor
    · intro hin
      by_contra hnd
      rw [IntermediateField.mem_map] at hin
      obtain ⟨e, he, heq⟩ := hin
      rw [qExpandₐ_apply] at heq
      have he2 : e = jqN ℓ := by
        apply qExpand_injective ℓ
        rw [heq, ← hmulsq]
      rw [he2] at he
      exact ModularCurve.jqN_prime_not_mem_full N ℓ hnd hall he
    · intro hdvdN
      rw [IntermediateField.mem_map]
      refine ⟨jqN ℓ, ?_, by rw [qExpandₐ_apply, hmulsq]⟩
      show qExpand ℚ ℓ jq ∈ modularFunctionFieldFull N
      exact jqd_mem_full N hdvdN
  have hgen : modularFunctionFieldFull (N * ℓ)
      = IntermediateField.adjoin ℚ
          ((((modularFunctionFieldFull N).map (qExpandₐ ℓ) :
            IntermediateField ℚ (LaurentSeries ℚ)) : Set (LaurentSeries ℚ)) ∪ {jq}) := by
    refine le_antisymm ?_ ?_
    · rw [← ModularCurve.modularFunctionField_eq_full (N * ℓ), modularFunctionField,
        IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_union_right _ rfl)
      · refine IntermediateField.subset_adjoin _ _ (Set.mem_union_left _ ?_)
        show qExpand ℚ (N * ℓ) jq ∈ (modularFunctionFieldFull N).map (qExpandₐ ℓ)
        rw [IntermediateField.mem_map]
        refine ⟨jqN N, ?_, ?_⟩
        · show qExpand ℚ N jq ∈ modularFunctionFieldFull N
          exact jqd_mem_full N dvd_rfl
        · rw [qExpandₐ_apply, jqN, qExpand_qExpand]
          exact qExpand_congr (mul_comm ℓ N) jq
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · exact full_degeneracy_map_le N ℓ hx
      · have h := jqd_mem_full (N * ℓ) (one_dvd _)
        rwa [qExpand_one_apply] at h
  rw [hgen, g2_relfinrank_union_left]
  by_cases hd : ℓ ∣ N
  · rw [if_pos hd]
    exact ModularCurve.finrank_adjoin_jq_of_subset_range_qExpand_of_mem _ ℓ hFr hmemF
      (hiff.mpr hd)
  · rw [if_neg hd]
    exact ModularCurve.finrank_adjoin_jq_of_subset_range_qExpand _ ℓ hFr hmemF
      (fun hin => hd (hiff.mp hin))

end
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve.W1"

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_relfinrank_qExpand_full.ModularCurve in

theorem solution (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] : IntermediateField.relfinrank ((modularFunctionFieldFull N).map (qExpandₐ ℓ)) (modularFunctionFieldFull (N * ℓ)) = if ℓ ∣ N then ℓ else ℓ + 1 :=
  ModularCurve.relfinrank_qExpand_full N ℓ

#print axioms solution

end S_ModularCurve_relfinrank_qExpand_full
end P2MW
export P2MW.S_ModularCurve_relfinrank_qExpand_full (solution)
