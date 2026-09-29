-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.red_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d806e199-67e7-5bd7-a07d-686d4eaabf29

import Mathlib
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_red_surjective

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPModel.FibreModel jqModC jqModC_eq_map_intCast modularFunctionFieldC modularFunctionFieldFull coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single laurentBaseChange"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar constantsHom affineBaseFin FibreModel"
namespace FibreModel
p2m_export "ModularCurve.CharPModel.FibreModel" "constFin_mem integralFin piFin_const frac_piFin piFin BFin ker_piFin piFin_j jBar_mem"
namespace RedSurj
p2m_open "ModularCurve.CharPModel.FibreModel ModularCurve.CharPModel ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_red_surjective.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_red_surjective.ModularCurve.CharPModel AlgebraicCurve Polynomial"

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

theorem red_eq_zero_of_mem_maximalIdeal (fm : FibreModel N A ℓ k red) {m : A}
    (hm : m ∈ IsLocalRing.maximalIdeal A) : red m = 0 := by
  have h : (⟨constantsHom N A m, fm.constFin_mem m⟩ : fm.BFin) ∈ RingHom.ker fm.piFin := by
    rw [fm.ker_piFin]
    exact Ideal.subset_span ⟨m, hm, rfl⟩
  rw [RingHom.mem_ker, fm.piFin_const] at h
  exact (map_eq_zero_iff _ (algebraMap k (modularFunctionFieldC k N)).injective).mp h

theorem isUnit_of_red_ne_zero (fm : FibreModel N A ℓ k red) {a : A} (ha : red a ≠ 0) : IsUnit a := by
  by_contra h
  exact ha (red_eq_zero_of_mem_maximalIdeal fm ((IsLocalRing.mem_maximalIdeal a).mpr h))

theorem exists_multiset_prod_eq_of_monic (P : Polynomial A) (hP : P.Monic) :
    ∃ s : Multiset A, (s.map fun a => X - C a).prod = P := by
  classical
  have hmon' : (P.map (algebraMap A (AlgebraicClosure ℚ))).Monic := hP.map _
  have hsplit : (P.map (algebraMap A (AlgebraicClosure ℚ))).Splits := IsAlgClosed.splits _

  have hroot : ∀ r ∈ (P.map (algebraMap A (AlgebraicClosure ℚ))).roots, r ∈ A := by
    intro r hr
    have hr0 : Polynomial.eval₂ (algebraMap A (AlgebraicClosure ℚ)) r P = 0 := by
      rw [Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hmon'.ne_zero).mp hr
    have hint : IsIntegral A r := ⟨P, hP, hr0⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := AlgebraicClosure ℚ)).mp hint
    rw [← hy]
    exact y.2
  refine ⟨(P.map (algebraMap A (AlgebraicClosure ℚ))).roots.pmap (fun r hr => (⟨r, hr⟩ : A)) hroot, ?_⟩
  apply Polynomial.map_injective (algebraMap A (AlgebraicClosure ℚ)) Subtype.val_injective
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_pmap]
  have hfun : (fun (r : AlgebraicClosure ℚ) (hr : r ∈ A) =>
      ((Polynomial.map (algebraMap A (AlgebraicClosure ℚ))) ∘ fun a : A => X - C a) ⟨r, hr⟩)
      = fun r _ => X - C r := by
    funext r hr
    simp
  rw [hfun, Multiset.pmap_eq_map (fun r : AlgebraicClosure ℚ => r ∈ A)]
  exact (hsplit.eq_prod_roots_of_monic hmon').symm

theorem mem_range_of_root (fm : FibreModel N A ℓ k red) {Q : Polynomial k} (hQ0 : Q ≠ 0)
    (hQc : ∀ i, Q.coeff i ∈ Set.range red) {κ : k} (hκ : Q.eval κ = 0) : κ ∈ Set.range red := by
  classical

  obtain ⟨a₀, ha₀⟩ := hQc Q.natDegree
  have hlc : red a₀ = Q.leadingCoeff := ha₀
  have hlc0 : red a₀ ≠ 0 := by rw [hlc]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ0
  obtain ⟨u, hu⟩ := isUnit_of_red_ne_zero fm hlc0
  set Q' : Polynomial k := C (red (↑u⁻¹ : A)) * Q with hQ'
  have huinv : red (↑u⁻¹ : A) * red a₀ = 1 := by
    rw [← map_mul, ← hu, Units.inv_mul, map_one]
  have hQ'mon : Q'.Monic := by
    rw [hQ']
    exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hlc, huinv])
  have hQ'c : ∀ i, Q'.coeff i ∈ Set.range red := by
    intro i
    obtain ⟨aᵢ, haᵢ⟩ := hQc i
    refine ⟨↑u⁻¹ * aᵢ, ?_⟩
    rw [hQ', Polynomial.coeff_C_mul, map_mul, haᵢ]
  have hQ'κ : Q'.eval κ = 0 := by rw [hQ', Polynomial.eval_mul, Polynomial.eval_C, hκ, mul_zero]

  have hlifts : Q' ∈ Polynomial.lifts red := (Polynomial.lifts_iff_coeff_lifts _).mpr hQ'c
  obtain ⟨P, hPQ, -, hPmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hQ'mon

  obtain ⟨s, hs⟩ := exists_multiset_prod_eq_of_monic P hPmon
  have hev : (s.map fun a => κ - red a).prod = 0 := by
    have h1 : (P.map red).eval κ = 0 := by rw [hPQ]; exact hQ'κ
    rw [← hs, Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.eval_multiset_prod,
      Multiset.map_map] at h1
    have hfun : ((fun p : Polynomial k => p.eval κ) ∘ (Polynomial.map red) ∘ fun a : A => X - C a)
        = fun a => κ - red a := by
      funext a; simp
    rwa [hfun] at h1
  obtain ⟨a, -, ha⟩ : ∃ a ∈ s, κ - red a = 0 := by
    have := Multiset.prod_eq_zero_iff.mp hev
    obtain ⟨a, ha, h0⟩ := Multiset.mem_map.mp this
    exact ⟨a, ha, h0⟩
  exact ⟨a, (sub_eq_zero.mp ha).symm⟩

def Fr (fm : FibreModel N A ℓ k red) : Subfield k where
  toSubring := red.range
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    by_cases ha : red a = 0
    · exact ⟨0, by rw [ha, inv_zero, map_zero]⟩
    · obtain ⟨u, hu⟩ := isUnit_of_red_ne_zero fm ha
      refine ⟨↑u⁻¹, ?_⟩
      symm
      apply inv_eq_of_mul_eq_one_left
      rw [← map_mul, ← hu, Units.inv_mul, map_one]

theorem mem_Fr_iff (fm : FibreModel N A ℓ k red) {x : k} : x ∈ Fr fm ↔ x ∈ Set.range red := Iff.rfl

def K0 (fm : FibreModel N A ℓ k red) : Subfield (LaurentSeries k) := (coeffMap (Fr fm).subtype).fieldRange

theorem mem_K0_of_forall_coeff (fm : FibreModel N A ℓ k red) {x : LaurentSeries k}
    (h : ∀ n, x.coeff n ∈ Fr fm) : x ∈ K0 fm := by
  refine ⟨⟨fun n => ⟨x.coeff n, h n⟩, x.isPWO_support.mono (fun n hn h0 => hn (Subtype.ext h0))⟩, ?_⟩
  ext n
  rfl

theorem forall_coeff_of_mem_K0 (fm : FibreModel N A ℓ k red) {x : LaurentSeries k}
    (h : x ∈ K0 fm) (n : ℤ) : x.coeff n ∈ Fr fm := by
  obtain ⟨y, rfl⟩ := h
  rw [coeffMap_coeff]
  exact (y.coeff n).2

theorem coeff_mem_Fr_ringClosed (fm : FibreModel N A ℓ k red) :
    ∃ S : Subring (LaurentSeries k), ∀ x, x ∈ S ↔ ∀ n, x.coeff n ∈ Fr fm :=
  ⟨(K0 fm).toSubring, fun x => ⟨fun h n => forall_coeff_of_mem_K0 fm h n, fun h => mem_K0_of_forall_coeff fm h⟩⟩

theorem affineBaseFin_le_BFin (fm : FibreModel N A ℓ k red) : affineBaseFin N A ≤ fm.BFin := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | rfl)
  exacts [fm.constFin_mem a, fm.jBar_mem]

def piFinL (fm : FibreModel N A ℓ k red) : fm.BFin →+* LaurentSeries k :=
  (IntermediateField.val _).toRingHom.comp fm.piFin

theorem piFinL_apply (fm : FibreModel N A ℓ k red) (b : fm.BFin) :
    piFinL fm b = ((fm.piFin b : modularFunctionFieldC k N) : LaurentSeries k) := rfl

theorem piFinL_mem_K0_of_mem_affineBaseFin (fm : FibreModel N A ℓ k red) {x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)}
    (hx : x ∈ affineBaseFin N A) : piFinL fm ⟨x, affineBaseFin_le_BFin fm hx⟩ ∈ K0 fm := by

  let T : Subring fm.BFin := (K0 fm).toSubring.comap (piFinL fm)
  have hle : affineBaseFin N A ≤ T.map fm.BFin.subtype := by
    refine Subring.closure_le.mpr ?_
    rintro y (⟨a, rfl⟩ | rfl)
    · refine ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, ?_, rfl⟩
      show piFinL fm ⟨constantsHom N A a, fm.constFin_mem a⟩ ∈ K0 fm
      rw [piFinL_apply, fm.piFin_const]
      apply mem_K0_of_forall_coeff
      intro n
      show (algebraMap k (LaurentSeries k) (red a)).coeff n ∈ Fr fm
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
      split_ifs
      · exact ⟨a, rfl⟩
      · exact (Fr fm).zero_mem
    · refine ⟨⟨jBar N, fm.jBar_mem⟩, ?_, rfl⟩
      show piFinL fm ⟨jBar N, fm.jBar_mem⟩ ∈ K0 fm
      rw [piFinL_apply, fm.piFin_j]
      apply mem_K0_of_forall_coeff
      intro n
      show (jqModC k).coeff n ∈ Fr fm
      rw [jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
      exact intCast_mem (Fr fm) _
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, affineBaseFin_le_BFin fm hx⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem isIntegral_piFinL (fm : FibreModel N A ℓ k red) (b : fm.BFin) : IsIntegral (K0 fm) (piFinL fm b) := by
  obtain ⟨p, hpm, hpev⟩ := fm.integralFin b
  let incl : affineBaseFin N A →+* fm.BFin := Subring.inclusion (affineBaseFin_le_BFin fm)
  let θ : affineBaseFin N A →+* K0 fm :=
    ((piFinL fm).comp incl).codRestrict _ (fun x => piFinL_mem_K0_of_mem_affineBaseFin fm x.2)
  refine ⟨p.map θ, hpm.map θ, ?_⟩
  have h0 : Polynomial.eval₂ incl b p = 0 := by
    apply Subtype.val_injective
    have := Polynomial.hom_eval₂ p incl fm.BFin.subtype b
    rw [show fm.BFin.subtype.comp incl = (affineBaseFin N A).subtype from RingHom.ext fun _ => rfl] at this
    rw [show ((Polynomial.eval₂ incl b p : fm.BFin) : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = fm.BFin.subtype (Polynomial.eval₂ incl b p) from rfl, this]
    exact hpev
  rw [Polynomial.eval₂_map, show (algebraMap (K0 fm) (LaurentSeries k)).comp θ = (piFinL fm).comp incl from
    RingHom.ext fun _ => rfl, ← Polynomial.hom_eval₂, h0, map_zero]

def coeffPoly (P : Polynomial (LaurentSeries k)) (n : ℤ) : Polynomial k :=
  Polynomial.ofFinsupp (.ofCoeff (P.toFinsupp.coeff.mapRange (fun c => c.coeff n) (by simp)))

theorem coeff_coeffPoly (P : Polynomial (LaurentSeries k)) (n : ℤ) (i : ℕ) :
    (coeffPoly P n).coeff i = (P.coeff i).coeff n := by
  rcases P with ⟨f⟩
  rfl

def coeffAddHom (n : ℤ) : LaurentSeries k →+ k where
  toFun x := x.coeff n
  map_zero' := rfl
  map_add' x y := HahnSeries.coeff_add

theorem eval_coeffPoly_of_eval_algebraMap (P : Polynomial (LaurentSeries k)) (κ : k) (n : ℤ) :
    (coeffPoly P n).eval κ = (P.eval (algebraMap k (LaurentSeries k) κ)).coeff n := by
  classical
  have hdeg : (coeffPoly P n).natDegree ≤ P.natDegree := by
    refine (Polynomial.natDegree_le_iff_coeff_eq_zero).mpr (fun i hi => ?_)
    rw [coeff_coeffPoly, Polynomial.coeff_eq_zero_of_natDegree_lt hi, HahnSeries.coeff_zero]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le le_rfl)]
  rw [show (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (algebraMap k (LaurentSeries k) κ) ^ i).coeff n
      = coeffAddHom n (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (algebraMap k (LaurentSeries k) κ) ^ i)
      from rfl, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coeff_coeffPoly]
  show (P.coeff i).coeff n * κ ^ i = (P.coeff i * (algebraMap k (LaurentSeries k) κ) ^ i).coeff n
  rw [← map_pow, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, mul_comm (P.coeff i),
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]

theorem red_surjective (fm : FibreModel N A ℓ k red) : Function.Surjective red := by
  classical
  intro κ

  obtain ⟨b, c, hc0, hbc⟩ := fm.frac_piFin (algebraMap k (modularFunctionFieldC k N) κ)
  set κ' : LaurentSeries k := algebraMap k (LaurentSeries k) κ with hκ'
  have hβ := isIntegral_piFinL fm b
  have hγ := isIntegral_piFinL fm c
  have hγ0 : piFinL fm c ≠ 0 := fun h =>
    hc0 ((map_eq_zero_iff _ (IntermediateField.val (modularFunctionFieldC k N)).toRingHom.injective).mp h)
  have hrel : κ' * piFinL fm c = piFinL fm b := by
    have := congrArg (fun z : modularFunctionFieldC k N => (z : LaurentSeries k)) hbc
    simpa [piFinL_apply] using this
  have hκalg : IsAlgebraic (K0 fm) κ' := by
    have : κ' = piFinL fm b * (piFinL fm c)⁻¹ := by
      rw [← hrel, mul_inv_cancel_right₀ hγ0]
    rw [this]
    exact (hβ.isAlgebraic).mul (hγ.isAlgebraic).inv

  obtain ⟨P, hP0, hPκ⟩ := hκalg
  set P' : Polynomial (LaurentSeries k) := P.map (K0 fm).subtype with hP'
  have hP'0 : P' ≠ 0 := (Polynomial.map_ne_zero_iff (K0 fm).subtype.injective).mpr hP0
  have hP'κ : P'.eval κ' = 0 := by
    rw [hP', Polynomial.eval_map]
    exact hPκ
  have hlc : P'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP'0
  set n : ℤ := P'.leadingCoeff.order with hn
  set Q : Polynomial k := coeffPoly P' n with hQ
  have hQ0 : Q ≠ 0 := by
    intro h
    have := congrArg (fun q : Polynomial k => q.coeff P'.natDegree) h
    simp only [hQ, coeff_coeffPoly, Polynomial.coeff_zero] at this
    exact hlc (HahnSeries.coeff_order_eq_zero.mp this)
  have hQc : ∀ i, Q.coeff i ∈ Set.range red := by
    intro i
    rw [hQ, coeff_coeffPoly, hP', Polynomial.coeff_map]
    exact forall_coeff_of_mem_K0 fm (P.coeff i).2 n
  have hQκ : Q.eval κ = 0 := by
    rw [hQ, eval_coeffPoly_of_eval_algebraMap, ← hκ', hP'κ, HahnSeries.coeff_zero]
  exact mem_range_of_root fm hQ0 hQc hQκ

end ModularCurve.CharPModel.FibreModel.RedSurj

end

open _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_red_surjective.ModularCurve.CharPModel in
theorem solution
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ]
    (red : A →+* k) (fm : FibreModel N A ℓ k red) :
    Function.Surjective red :=
  ModularCurve.CharPModel.FibreModel.RedSurj.red_surjective fm

end S_ModularCurve_CharPModel_FibreModel_red_surjective
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_red_surjective (solution)
