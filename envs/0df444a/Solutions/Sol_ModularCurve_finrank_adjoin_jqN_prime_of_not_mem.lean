-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqN_prime_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/005b469a-1b37-5b01-8c3c-3e6435a8c493

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_PhiGen_splits_of_prime
import Theorems.Thm_Polynomial_irreducible_of_transitive_ringAut
import Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

noncomputable section

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve ModularCurve.PhiGen"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_of_prime exists_phiIrreducible_evalSymm dedekindPsi_prime"
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
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_of_prime exists_phiIrreducible_evalSymm dedekindPsi_prime"
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
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_of_prime exists_phiIrreducible_evalSymm dedekindPsi_prime"
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
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_of_prime exists_phiIrreducible_evalSymm dedekindPsi_prime"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem coeffEmb_injective' : Function.Injective (coeffEmb K) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries K => z.coeff k) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ K).injective this

theorem iota_injective (A : ℕ) [NeZero A] : Function.Injective ((coeffEmb K).comp (qExpand ℚ A)) :=
  coeffEmb_injective'.comp (qExpand_injective A)

theorem phiAtSeed_iota_jq_eq_phiProd (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) :
    phiAtSeed data (coeffEmb K (qExpand ℚ p jq)) = phiProd p (conj p ζ) := by
  rw [← ModularCurve.PhiGen.splits_of_prime p ζ hζ data, phiAtSeed]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtJ_X]

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve.W1"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand coeffMap_qExpand PhiGen.splits_of_prime exists_phiIrreducible_evalSymm dedekindPsi_prime" end ModularCurve
p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.finrank_adjoin_jqN_prime_of_not_mem (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpF : jqN p ∉ F) : Module.finrank F (IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ))) = p + 1 := by
  classical

  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
  set jF : F := ⟨jq, hj⟩ with hjF
  set P : Polynomial F := phiAtSeed data jF with hP
  have hPmonic : P.Monic := phiAtSeed_monic data jF
  have hPdeg : P.natDegree = p + 1 := by rw [hP, phiAtSeed_natDegree, dedekindPsi_prime hp.out]
  have hPmap : P.map (algebraMap F (LaurentSeries ℚ)) = phiAtSeed data jq := by
    rw [hP, phiAtSeed_map]; rfl
  have hProot : Polynomial.aeval (jqN p) P = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hPmap]
    simpa using phiAtSeed_jqN_eval p data 1
  have hα : IsIntegral F (jqN p) := ⟨P, hPmonic, by rwa [Polynomial.aeval_def] at hProot⟩

  let K := CyclotomicField p ℚ
  let ζ : Kˣ := cycUnit p
  have hζ : IsPrimitiveRoot (ζ : K) p := cycUnit_spec p
  let ι : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ p)
  letI : Algebra F (LaurentSeries K) := (ι.comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : ∀ a : F, algebraMap F (LaurentSeries K) a = ι a := fun a => rfl

  have hPmapL : P.map (algebraMap F (LaurentSeries K)) = phiProd p (conj p ζ) := by
    rw [RingHom.algebraMap_toAlgebra, ← Polynomial.map_map, hPmap, phiAtSeed_map]
    exact phiAtSeed_iota_jq_eq_phiProd p ζ hζ data

  have hirr : Irreducible P := by
    refine Polynomial.irreducible_of_transitive_ringAut P hPmonic ?_ (qTwistEquiv ζ) ?_ (TS K (p * p) 1)
      (fun b => TS K 1 (ζ ^ b)) p ?_ ?_ ?_ ?_
    · rw [hPmapL, phiProd]
      exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
    · intro a
      rw [halg, qTwistEquiv_apply]
      exact qTwist_iota_of_pow_eq_one p ζ (cycUnit_pow p) a
    · rw [hPmapL, roots_phiProd_conj]
    · rw [hPmapL, roots_phiProd_conj]; exact roots_phiProd_conj_nodup p ζ hζ
    · intro i _
      rw [qTwistEquiv_apply]
      exact qTwist_TS_one_cycle ζ (cycUnit_pow p) i
    · rintro ⟨f, hf⟩
      rw [halg] at hf
      have : (f : LaurentSeries ℚ) = jqN p := by
        apply iota_injective (K := K) p
        change ι f = coeffEmb K (qExpand ℚ p (jqN p))
        rw [hf, iota_jqN]
      exact hpF (this ▸ f.2)

  have hmin : P = minpoly F (jqN p) := minpoly.eq_of_irreducible_of_monic hirr hProot hPmonic
  rw [IntermediateField.adjoin.finrank hα, ← hmin, hPdeg]

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.ModularCurve in

theorem solution (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpF : jqN p ∉ F) : Module.finrank F (IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ))) = p + 1 :=
  ModularCurve.finrank_adjoin_jqN_prime_of_not_mem F hj p hpF

#print axioms solution

end
end S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem (solution)
