-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/05b45a4a-8194-53b9-8462-8409b0cde59c

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_exists_coeffEmb_basis_of_forall_coeffMap_mem
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

open AlgebraicCurve

namespace J3C2

open ModularCurve

section QInt

variable (q : ℕ) [hq : Fact q.Prime]

private def IsQInt_j3 (r : ℚ) : Prop := 0 ≤ padicValRat q r

omit hq in
private theorem isQInt_zero_j3 : IsQInt_j3 q 0 := by
  simp [IsQInt_j3]

omit hq in
private theorem isQInt_intCast_j3 (z : ℤ) : IsQInt_j3 q (z : ℚ) := by
  rw [IsQInt_j3, padicValRat.of_int]
  exact Int.natCast_nonneg _

omit hq in
private theorem isQInt_one_j3 : IsQInt_j3 q 1 := by
  simpa using isQInt_intCast_j3 q 1

private theorem isQInt_add_j3 {r s : ℚ} (hr : IsQInt_j3 q r) (hs : IsQInt_j3 q s) :
    IsQInt_j3 q (r + s) := by
  by_cases h : r + s = 0
  · rw [h]; exact isQInt_zero_j3 q
  · exact (le_min hr hs).trans (padicValRat.min_le_padicValRat_add h)

omit hq in
private theorem isQInt_neg_j3 {r : ℚ} (hr : IsQInt_j3 q r) : IsQInt_j3 q (-r) := by
  rw [IsQInt_j3, padicValRat.neg]; exact hr

private theorem isQInt_sub_j3 {r s : ℚ} (hr : IsQInt_j3 q r) (hs : IsQInt_j3 q s) :
    IsQInt_j3 q (r - s) := by
  rw [sub_eq_add_neg]; exact isQInt_add_j3 q hr (isQInt_neg_j3 q hs)

private theorem isQInt_mul_j3 {r s : ℚ} (hr : IsQInt_j3 q r) (hs : IsQInt_j3 q s) :
    IsQInt_j3 q (r * s) := by
  by_cases hr0 : r = 0
  · rw [hr0, zero_mul]; exact isQInt_zero_j3 q
  by_cases hs0 : s = 0
  · rw [hs0, mul_zero]; exact isQInt_zero_j3 q
  rw [IsQInt_j3, padicValRat.mul hr0 hs0]
  exact add_nonneg hr hs

private theorem isQInt_sum_j3 {ι : Type*} (s : Finset ι) {f : ι → ℚ}
    (h : ∀ i ∈ s, IsQInt_j3 q (f i)) : IsQInt_j3 q (∑ i ∈ s, f i) :=
  Finset.sum_induction _ _ (fun _ _ ha hb => isQInt_add_j3 q ha hb) (isQInt_zero_j3 q) h

private theorem isQInt_inv_mul_j3 {u c : ℚ} (hu : u ≠ 0)
    (h : c ≠ 0 → padicValRat q u ≤ padicValRat q c) : IsQInt_j3 q (u⁻¹ * c) := by
  by_cases hc : c = 0
  · rw [hc, mul_zero]; exact isQInt_zero_j3 q
  rw [IsQInt_j3, padicValRat.mul (inv_ne_zero hu) hc, padicValRat.inv]
  linarith [h hc]

private theorem mem_of_isQInt_j3 {L : Type*} [Field L] [CharZero L] (B : ValuationSubring L)
    (hqB : ¬IsUnit ((q : ℕ) : B)) {r : ℚ} (hr : IsQInt_j3 q r) : (r : L) ∈ B := by
  have hp : q.Prime := hq.out

  have hden : ¬q ∣ r.den := by
    intro hd
    have hnum : ¬(q : ℤ) ∣ r.num := by
      intro h
      have h1 : q ∣ r.num.natAbs := Int.natCast_dvd.mp h
      have h2 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1 hd
      rw [r.reduced] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have hv : padicValRat q r = -(padicValNat q r.den : ℤ) := by
      rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum]; ring
    have h1 : 1 ≤ padicValNat q r.den := one_le_padicValNat_of_dvd r.den_nz hd
    have : (0 : ℤ) ≤ -(padicValNat q r.den : ℤ) := hv ▸ hr
    omega

  have hcop : Nat.Coprime q r.den := (Nat.Prime.coprime_iff_not_dvd hp).mpr hden
  have hbez : ((q : ℕ) : B) * (Nat.gcdA q r.den : B) + ((r.den : ℕ) : B) * (Nat.gcdB q r.den : B) =
      1 := by
    have h := Nat.gcd_eq_gcd_ab q r.den
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    have h' := congrArg (fun z : ℤ => (z : B)) h
    push_cast at h'
    exact h'.symm
  have hqm : ((q : ℕ) : B) * (Nat.gcdA q r.den : B) ∈ nonunits B := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hqB)
  have hunit : IsUnit (((r.den : ℕ) : B) * (Nat.gcdB q r.den : B)) := by
    have h1 : ((r.den : ℕ) : B) * (Nat.gcdB q r.den : B) =
        1 - ((q : ℕ) : B) * (Nat.gcdA q r.den : B) := by
      rw [← hbez]; ring
    rw [h1]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hqm
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hunit

  have hden0 : ((r.den : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hinv : ((r.den : ℕ) : L)⁻¹ = (((u⁻¹ : Bˣ) : B) : L) := by
    apply inv_eq_of_mul_eq_one_right
    have : (((u : B) : L)) = ((r.den : ℕ) : L) := by rw [hu]; rfl
    rw [← this, ← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [Rat.cast_def, div_eq_mul_inv, hinv]
  exact mul_mem (intCast_mem B r.num) ((u⁻¹ : Bˣ) : B).2

end QInt

section Echelon

variable (q : ℕ) [hq : Fact q.Prime]

private def QIntSeries_j3 (x : LaurentSeries ℚ) : Prop := ∀ m, IsQInt_j3 q (x.coeff m)

omit hq in
private theorem qIntSeries_zero_j3 : QIntSeries_j3 q 0 := fun _ => by
  rw [HahnSeries.coeff_zero]; exact isQInt_zero_j3 q

private theorem qIntSeries_add_j3 {x y : LaurentSeries ℚ} (hx : QIntSeries_j3 q x)
    (hy : QIntSeries_j3 q y) : QIntSeries_j3 q (x + y) := fun m => by
  rw [HahnSeries.coeff_add]; exact isQInt_add_j3 q (hx m) (hy m)

private theorem qIntSeries_sub_j3 {x y : LaurentSeries ℚ} (hx : QIntSeries_j3 q x)
    (hy : QIntSeries_j3 q y) : QIntSeries_j3 q (x - y) := fun m => by
  rw [HahnSeries.coeff_sub]; exact isQInt_sub_j3 q (hx m) (hy m)

private theorem qIntSeries_smul_j3 {c : ℚ} (hc : IsQInt_j3 q c) {x : LaurentSeries ℚ}
    (hx : QIntSeries_j3 q x) : QIntSeries_j3 q (c • x) := fun m => by
  rw [HahnSeries.coeff_smul, smul_eq_mul]; exact isQInt_mul_j3 q hc (hx m)

private theorem qIntSeries_sum_j3 {ι : Type*} (s : Finset ι) {x : ι → LaurentSeries ℚ}
    (h : ∀ i ∈ s, QIntSeries_j3 q (x i)) : QIntSeries_j3 q (∑ i ∈ s, x i) := fun m => by
  rw [HahnSeries.coeff_sum]; exact isQInt_sum_j3 q s fun i hi => h i hi m

private theorem exists_pivot_j3 {x : LaurentSeries ℚ} (hx : QIntSeries_j3 q x) (h0 : x ≠ 0) :
    ∃ κ : ℤ, x.coeff κ ≠ 0 ∧ QIntSeries_j3 q ((x.coeff κ)⁻¹ • x) := by
  classical
  have hex : ∃ v : ℕ, ∃ m, x.coeff m ≠ 0 ∧ padicValRat q (x.coeff m) = v := by
    obtain ⟨m, hm⟩ := HahnSeries.support_nonempty_iff.mpr h0
    rw [HahnSeries.mem_support] at hm
    exact ⟨(padicValRat q (x.coeff m)).toNat, m, hm, (Int.toNat_of_nonneg (hx m)).symm⟩
  obtain ⟨κ, hκ0, hκv⟩ := Nat.find_spec hex
  refine ⟨κ, hκ0, fun m => ?_⟩
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  refine isQInt_inv_mul_j3 q hκ0 fun hm => ?_
  have hmin := Nat.find_min' hex ⟨m, hm, (Int.toNat_of_nonneg (hx m)).symm⟩
  rw [hκv, ← Int.toNat_of_nonneg (hx m)]
  exact_mod_cast hmin

private theorem echelon_j3 : ∀ (n : ℕ) (e : Fin n → LaurentSeries ℚ), LinearIndependent ℚ e →
    (∀ l, QIntSeries_j3 q (e l)) →
    ∃ (κ : Fin n → ℤ) (e' : Fin n → LaurentSeries ℚ),
      (∀ j, e' j ∈ Submodule.span ℚ (Set.range e)) ∧
      (∀ i j, (e' j).coeff (κ i) = if i = j then 1 else 0) ∧
      (∀ j, QIntSeries_j3 q (e' j)) ∧
      (∀ l, e l = ∑ j, (e l).coeff (κ j) • e' j)
  | 0, _, _, _ => ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, fun i => i.elim0, fun j => j.elim0,
      fun l => l.elim0⟩
  | n + 1, e, hli, hint => by
    classical
    have hli' : LinearIndependent ℚ (Fin.cons (e 0) (Fin.tail e) : Fin (n + 1) → LaurentSeries ℚ) := by
      rw [Fin.cons_self_tail]; exact hli
    obtain ⟨htail, hnot⟩ := linearIndependent_finCons.mp hli'
    obtain ⟨κ', e'', hspan, hδ, hqi, hrep⟩ :=
      echelon_j3 n (Fin.tail e) htail (fun l => hint l.succ)
    have hsub : Submodule.span ℚ (Set.range (Fin.tail e)) ≤ Submodule.span ℚ (Set.range e) :=
      Submodule.span_mono (Set.range_comp_subset_range Fin.succ e)
    have hspan' : ∀ j, e'' j ∈ Submodule.span ℚ (Set.range e) := fun j => hsub (hspan j)

    obtain ⟨x, hxdef⟩ : ∃ x : LaurentSeries ℚ, x = e 0 - ∑ j, (e 0).coeff (κ' j) • e'' j :=
      ⟨_, rfl⟩
    have hxspan : x ∈ Submodule.span ℚ (Set.range e) := by
      rw [hxdef]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hspan' j))
    have hx0 : x ≠ 0 := by
      intro h
      apply hnot
      rw [hxdef, sub_eq_zero] at h
      rw [h]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hspan j)
    have hxq : QIntSeries_j3 q x := by
      rw [hxdef]
      exact qIntSeries_sub_j3 q (hint 0)
        (qIntSeries_sum_j3 q _ fun j _ => qIntSeries_smul_j3 q (hint 0 _) (hqi j))
    have hxκ : ∀ i, x.coeff (κ' i) = 0 := fun i => by
      rw [hxdef, HahnSeries.coeff_sub, HahnSeries.coeff_sum]
      simp only [HahnSeries.coeff_smul, smul_eq_mul, hδ, mul_boole, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, sub_self]
    obtain ⟨κ₀, hu, hq0⟩ := exists_pivot_j3 q hxq hx0
    obtain ⟨e₀, he₀⟩ : ∃ e₀ : LaurentSeries ℚ, e₀ = (x.coeff κ₀)⁻¹ • x := ⟨_, rfl⟩
    have he₀κ₀ : e₀.coeff κ₀ = 1 := by
      rw [he₀, HahnSeries.coeff_smul, smul_eq_mul, inv_mul_cancel₀ hu]
    have he₀κ : ∀ i, e₀.coeff (κ' i) = 0 := fun i => by
      rw [he₀, HahnSeries.coeff_smul, smul_eq_mul, hxκ, mul_zero]
    have he₀span : e₀ ∈ Submodule.span ℚ (Set.range e) := by
      rw [he₀]; exact Submodule.smul_mem _ _ hxspan
    have he₀q : QIntSeries_j3 q e₀ := by rw [he₀]; exact hq0
    refine ⟨Fin.cons κ₀ κ', Fin.cons e₀ (fun j => e'' j - (e'' j).coeff κ₀ • e₀), ?_, ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_)
      · rw [Fin.cons_zero]; exact he₀span
      · rw [Fin.cons_succ]
        exact Submodule.sub_mem _ (hspan' j) (Submodule.smul_mem _ _ he₀span)
    · refine Fin.cases ?_ (fun i => ?_) <;> refine Fin.cases ?_ (fun j => ?_)
      · simp only [Fin.cons_zero, if_true]
        exact he₀κ₀
      · simp only [Fin.cons_zero, Fin.cons_succ, (Fin.succ_ne_zero j).symm, if_false]
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_smul, smul_eq_mul, he₀κ₀, mul_one, sub_self]
      · simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero i, if_false]
        exact he₀κ i
      · simp only [Fin.cons_succ, Fin.succ_inj]
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_smul, smul_eq_mul, he₀κ i, mul_zero, sub_zero]
        exact hδ i j
    · refine Fin.cases ?_ (fun j => ?_)
      · rw [Fin.cons_zero]; exact he₀q
      · rw [Fin.cons_succ]
        exact qIntSeries_sub_j3 q (hqi j) (qIntSeries_smul_j3 q (hqi j κ₀) he₀q)
    · intro l
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', rfl⟩
      · have hcoef : x.coeff κ₀ = (e 0).coeff κ₀ - ∑ j, (e 0).coeff (κ' j) * (e'' j).coeff κ₀ := by
          rw [hxdef, HahnSeries.coeff_sub, HahnSeries.coeff_sum]
          simp only [HahnSeries.coeff_smul, smul_eq_mul]
        have hsum : ∑ j, (e 0).coeff (κ' j) • e'' j = e 0 - x := by rw [hxdef, sub_sub_cancel]
        calc e 0 = (e 0 - x) + x.coeff κ₀ • e₀ := by
                rw [he₀, smul_smul, mul_inv_cancel₀ hu, one_smul, sub_add_cancel]
          _ = (∑ j, (e 0).coeff (κ' j) • e'' j) +
                ((e 0).coeff κ₀ - ∑ j, (e 0).coeff (κ' j) * (e'' j).coeff κ₀) • e₀ := by
                rw [hsum, hcoef]
          _ = (e 0).coeff κ₀ • e₀ + ∑ j, (e 0).coeff (κ' j) • (e'' j - (e'' j).coeff κ₀ • e₀) := by
                simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, sub_smul, Finset.sum_smul]
                abel
      · have hl : e l'.succ = ∑ j, (e l'.succ).coeff (κ' j) • e'' j := hrep l'
        have hcoef : (e l'.succ).coeff κ₀ = ∑ j, (e l'.succ).coeff (κ' j) * (e'' j).coeff κ₀ := by
          conv_lhs => rw [hl]
          rw [HahnSeries.coeff_sum]
          simp only [HahnSeries.coeff_smul, smul_eq_mul]
        calc e l'.succ = ∑ j, (e l'.succ).coeff (κ' j) • e'' j := hl
          _ = (e l'.succ).coeff κ₀ • e₀ +
                ∑ j, (e l'.succ).coeff (κ' j) • (e'' j - (e'' j).coeff κ₀ • e₀) := by
                rw [hcoef]
                simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
                abel

end Echelon

section Lift

variable {L : Type*} [CommRing L]

private def liftSeries_j3 (S : Subring L) (x : LaurentSeries L) (h : ∀ m, x.coeff m ∈ S) :
    LaurentSeries S where
  coeff m := ⟨x.coeff m, h m⟩
  isPWO_support' := by
    refine x.isPWO_support.mono fun m hm => ?_
    rw [Function.mem_support] at hm
    rw [HahnSeries.mem_support]
    exact fun h0 => hm (Subtype.ext h0)

private theorem coe_liftSeries_coeff_j3 (S : Subring L) (x : LaurentSeries L) (h : ∀ m, x.coeff m ∈ S)
    (m : ℤ) : (((liftSeries_j3 S x h).coeff m : S) : L) = x.coeff m :=
  rfl

private theorem coeffMap_liftSeries_j3 (S : Subring L) (x : LaurentSeries L)
    (h : ∀ m, x.coeff m ∈ S) : coeffMap S.subtype (liftSeries_j3 S x h) = x := by
  ext m
  rfl

end Lift

section Denominators

private theorem coeffMap_qExpand_bdj3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffMap_jqModC_int_bdj3 :
    coeffMap (Int.castRingHom ℚ) (jqModC ℤ) = jq :=
  (map_jqModC (Int.castRingHom ℚ)).trans jqModC_rat

private theorem coeffMap_injective_bdj3 :
    Function.Injective (coeffMap (Int.castRingHom ℚ) : LaurentSeries ℤ → LaurentSeries ℚ) := by
  intro x y h
  ext k
  have hk := congrArg (fun s : LaurentSeries ℚ => s.coeff k) h
  simpa only [coeffMap_coeff, eq_intCast, Int.cast_inj] using hk

private theorem coeffMap_aeval_bdj3 (p : Polynomial ℤ) :
    coeffMap (Int.castRingHom ℚ) (Polynomial.aeval (jqModC ℤ) p) =
      Polynomial.aeval jq (p.map (Int.castRingHom ℚ)) := by
  rw [Polynomial.map_aeval_eq_aeval_map (φ := Int.castRingHom ℚ)
      (ψ := coeffMap (Int.castRingHom ℚ)) (RingHom.ext_int _ _) p (jqModC ℤ),
    coeffMap_jqModC_int_bdj3]

private theorem exists_mul_eq_of_mem_bdj3 {N : ℕ} [NeZero N] {x : LaurentSeries ℚ}
    (hx : x ∈ modularFunctionFieldFull N) :
    ∃ a b : LaurentSeries ℤ, b ≠ 0 ∧
      x * coeffMap (Int.castRingHom ℚ) b = coeffMap (Int.castRingHom ℚ) a := by
  rw [modularFunctionFieldFull] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨d, hd, -, rfl⟩ := hy
      haveI := hd
      exact ⟨qExpand ℤ d (jqModC ℤ), 1, one_ne_zero, by
        rw [map_one, mul_one, coeffMap_qExpand_bdj3, coeffMap_jqModC_int_bdj3]⟩
  | algebraMap r =>
      refine ⟨HahnSeries.single 0 r.num, HahnSeries.single 0 (r.den : ℤ),
        HahnSeries.single_ne_zero (by exact_mod_cast r.den_nz), ?_⟩
      rw [coeffMap_single, coeffMap_single, algebraMap_apply_eq_single,
        HahnSeries.single_mul_single, add_zero, eq_intCast, eq_intCast, Int.cast_natCast,
        Rat.mul_den_eq_num]
  | add y z _ _ hy hz =>
      obtain ⟨a, b, hb, h⟩ := hy
      obtain ⟨a', b', hb', h'⟩ := hz
      refine ⟨a * b' + a' * b, b * b', mul_ne_zero hb hb', ?_⟩
      rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']
      ring
  | inv y _ hy =>
      obtain ⟨a, b, hb, h⟩ := hy
      by_cases hy0 : y = 0
      · exact ⟨0, 1, one_ne_zero, by rw [hy0, inv_zero, zero_mul, map_zero]⟩
      · have ha : a ≠ 0 := by
          rintro rfl
          rw [map_zero, mul_eq_zero] at h
          exact h.elim hy0
            ((map_ne_zero_iff (coeffMap (Int.castRingHom ℚ)) coeffMap_injective_bdj3).mpr hb)
        exact ⟨b, a, ha, by rw [← h, inv_mul_cancel_left₀ hy0]⟩
  | mul y z _ _ hy hz =>
      obtain ⟨a, b, hb, h⟩ := hy
      obtain ⟨a', b', hb', h'⟩ := hz
      refine ⟨a * a', b * b', mul_ne_zero hb hb', ?_⟩
      rw [map_mul, map_mul, ← h, ← h']
      ring

private theorem exists_intPoly_bdj3 (p : Polynomial ℚ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ p' : Polynomial ℤ,
      p'.map (Int.castRingHom ℚ) = Polynomial.C (m : ℚ) * p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨m, hm, p', hp'⟩ := hp
      obtain ⟨k, hk, q', hq'⟩ := hq
      refine ⟨m * k, mul_ne_zero hm hk, Polynomial.C (k : ℤ) * p' + Polynomial.C (m : ℤ) * q', ?_⟩
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_C, hp', hq', map_natCast (Int.castRingHom ℚ) k,
        map_natCast (Int.castRingHom ℚ) m, Nat.cast_mul, Polynomial.C_mul]
      ring
  | monomial n r =>
      refine ⟨r.den, r.den_nz, Polynomial.monomial n r.num, ?_⟩
      rw [Polynomial.map_monomial, Polynomial.C_mul_monomial, eq_intCast, Rat.den_mul_eq_num]

private theorem isIntegralElem_mul_bdj3 {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : Polynomial B) (hP : P.Monic) (y s : B) (hy : P.eval y = 0)
    (hcoef : ∀ i, i < P.natDegree → P.coeff i * s ^ (P.natDegree - i) ∈ Set.range φ) :
    φ.IsIntegralElem (s * y) := by
  have hlifts : P.scaleRoots s ∈ Polynomial.lifts φ := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i => ?_
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i P.natDegree with hi | rfl | hi
    · exact hcoef i hi
    · exact ⟨1, by rw [hP.coeff_natDegree, one_mul, Nat.sub_self, pow_zero, map_one]⟩
    · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul, map_zero]⟩
  obtain ⟨Q, hQmap, -, hQmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts
      ((Polynomial.monic_scaleRoots_iff s).mpr hP)
  refine ⟨Q, hQmonic, ?_⟩
  rw [← Polynomial.eval_map, hQmap, Polynomial.scaleRoots_eval_mul, hy, mul_zero]

private theorem exists_monic_bdj3 {Y : LaurentSeries ℚ}
    (hint : IsIntegral ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) Y) :
    ∃ P : Polynomial (LaurentSeries ℚ), P.Monic ∧ P.eval Y = 0 ∧
      ∀ i, ∃ p : Polynomial ℚ, Polynomial.aeval jq p = P.coeff i := by
  obtain ⟨P, hPm, hPe⟩ := hint
  refine ⟨P.map (algebraMap _ (LaurentSeries ℚ)), hPm.map _, ?_, fun i => ?_⟩
  · rw [Polynomial.eval_map]
    exact hPe
  · rw [Polynomial.coeff_map]
    have hmem : algebraMap (↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) (LaurentSeries ℚ)
        (P.coeff i) ∈ (Polynomial.aeval (R := ℚ) jq).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval ℚ jq]
      exact (P.coeff i).2
    exact (AlgHom.mem_range _).mp hmem

private theorem exists_int_series_smul_j3 {N : ℕ} [NeZero N] (Y : LaurentSeries ℚ)
    (hY : Y ∈ ModularCurve.modularFunctionFieldFull N)
    (hint : IsIntegral ↥(Algebra.adjoin ℚ ({ModularCurve.jq} : Set (LaurentSeries ℚ))) Y) :
    ∃ D : ℕ, D ≠ 0 ∧ ∃ z : LaurentSeries ℤ,
      ModularCurve.coeffMap (Int.castRingHom ℚ) z = (D : ℚ) • Y := by
  obtain ⟨P, hPm, hPe, hPc⟩ := exists_monic_bdj3 hint
  choose pq hpq using hPc
  choose m hm pz hpz using fun i => exists_intPoly_bdj3 (pq i)
  obtain ⟨D, hD, hdvd⟩ : ∃ D : ℕ, D ≠ 0 ∧ ∀ i ∈ Finset.range P.natDegree, m i ∣ D :=
    ⟨∏ i ∈ Finset.range P.natDegree, m i, Finset.prod_ne_zero_iff.mpr fun i _ => hm i,
      fun i hi => Finset.dvd_prod_of_mem m hi⟩
  have hint' : (coeffMap (Int.castRingHom ℚ)).IsIntegralElem ((D : LaurentSeries ℚ) * Y) := by
    refine isIntegralElem_mul_bdj3 (coeffMap (Int.castRingHom ℚ)) P hPm Y (D : LaurentSeries ℚ)
      hPe fun i hi => ?_
    have hnat : D ^ (P.natDegree - 1 - i) * (D / m i) * m i = D ^ (P.natDegree - i) := by
      rw [mul_assoc, Nat.div_mul_cancel (hdvd i (Finset.mem_range.mpr hi)), ← pow_succ,
        show P.natDegree - 1 - i + 1 = P.natDegree - i by omega]
    refine ⟨((D ^ (P.natDegree - 1 - i) * (D / m i) : ℕ) : LaurentSeries ℤ) *
        Polynomial.aeval (jqModC ℤ) (pz i), ?_⟩
    rw [map_mul, map_natCast (coeffMap (Int.castRingHom ℚ)), coeffMap_aeval_bdj3, hpz, map_mul,
      Polynomial.aeval_C, map_natCast, hpq, ← mul_assoc, ← Nat.cast_mul, hnat, Nat.cast_pow]
    exact mul_comm _ _
  obtain ⟨a, b, hb, hab⟩ := exists_mul_eq_of_mem_bdj3 hY
  have hφb : coeffMap (Int.castRingHom ℚ) b ≠ 0 :=
    (map_ne_zero_iff (coeffMap (Int.castRingHom ℚ)) coeffMap_injective_bdj3).mpr hb
  obtain ⟨z, hz⟩ := exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div
    ((D : LaurentSeries ℚ) * Y)
    ⟨(D : LaurentSeries ℤ) * a, b, hb, by rw [eq_div_iff hφb, map_mul, map_natCast, mul_assoc, hab]⟩
    hint'
  exact ⟨D, hD, z, by rw [hz, ← HahnSeries.C_mul_eq_smul, map_natCast]⟩

end Denominators

section Conjugates

variable (N : ℕ) [NeZero N]

private def gens_j3 : Set ↥(modularFunctionFieldBar N) :=
  {⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))⟩,
    ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full N (dvd_refl N))⟩}

private noncomputable def S2_j3 : Subalgebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
  Algebra.adjoin (AlgebraicClosure ℚ) (gens_j3 N)

private def Good_j3 (x : LaurentSeries (AlgebraicClosure ℚ)) : Prop :=
  ∃ hx : x ∈ modularFunctionFieldBar N, IsIntegral ↥(S2_j3 N) (⟨x, hx⟩ : ↥(modularFunctionFieldBar N))

private theorem good_zero_j3 : Good_j3 N 0 :=
  ⟨zero_mem _, by
    have : (⟨0, zero_mem _⟩ : ↥(modularFunctionFieldBar N)) = 0 := rfl
    rw [this]; exact isIntegral_zero⟩

private theorem good_add_j3 {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : Good_j3 N x)
    (hy : Good_j3 N y) : Good_j3 N (x + y) := by
  obtain ⟨hxm, hxi⟩ := hx
  obtain ⟨hym, hyi⟩ := hy
  refine ⟨add_mem hxm hym, ?_⟩
  have : (⟨x + y, add_mem hxm hym⟩ : ↥(modularFunctionFieldBar N)) = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
  rw [this]
  exact hxi.add hyi

private theorem good_smul_j3 (c : AlgebraicClosure ℚ) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : Good_j3 N x) : Good_j3 N (c • x) := by
  obtain ⟨hxm, hxi⟩ := hx
  have hcm : c • x ∈ modularFunctionFieldBar N := by
    rw [← HahnSeries.single_zero_mul_eq_smul, ← algebraMap_laurentSeries_eq_single]
    exact mul_mem ((modularFunctionFieldBar N).algebraMap_mem c) hxm
  refine ⟨hcm, ?_⟩
  have he : (⟨c • x, hcm⟩ : ↥(modularFunctionFieldBar N)) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c * ⟨x, hxm⟩ := by
    apply Subtype.ext
    show c • x = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c * x
    rw [← HahnSeries.single_zero_mul_eq_smul, algebraMap_laurentSeries_eq_single]
  have hci : IsIntegral ↥(S2_j3 N) (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c) :=
    isIntegral_algebraMap (x := (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c,
      Subalgebra.algebraMap_mem _ c⟩ : ↥(S2_j3 N)))
  rw [he]
  exact hci.mul hxi

private theorem good_sum_j3 {ι : Type*} (s : Finset ι) {x : ι → LaurentSeries (AlgebraicClosure ℚ)}
    (h : ∀ i ∈ s, Good_j3 N (x i)) : Good_j3 N (∑ i ∈ s, x i) :=
  Finset.sum_induction _ _ (fun _ _ ha hb => good_add_j3 N ha hb) (good_zero_j3 N) h

private theorem arithmeticRingAut_mem_S2_j3 (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {s : ↥(modularFunctionFieldBar N)} (hs : s ∈ S2_j3 N) :
    arithmeticRingAut (modularFunctionFieldFull N) τ s ∈ S2_j3 N := by
  refine Algebra.adjoin_induction (p := fun s _ => arithmeticRingAut (modularFunctionFieldFull N) τ s ∈
      S2_j3 N) ?_ ?_ ?_ ?_ hs
  · rintro y hy
    refine Algebra.subset_adjoin ?_
    rcases hy with rfl | rfl
    · refine Or.inl ?_
      apply Subtype.ext
      show coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq) = _
      exact coeffMap_coeffEmb τ jq
    · refine Or.inr ?_
      apply Subtype.ext
      show coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
        (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq)) = _
      exact coeffMap_coeffEmb τ (qExpand ℚ N jq)
  · intro r
    rw [arithmeticRingAut_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  · intro y z _ _ hy hz
    rw [map_add]; exact add_mem hy hz
  · intro y z _ _ hy hz
    rw [map_mul]; exact mul_mem hy hz

private noncomputable def restrS2_j3 (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ↥(S2_j3 N) →+* ↥(S2_j3 N) :=
  (((arithmeticRingAut (modularFunctionFieldFull N) τ).toRingHom.comp (S2_j3 N).val.toRingHom)).codRestrict
    (S2_j3 N) fun s => arithmeticRingAut_mem_S2_j3 N τ s.2

private theorem good_coeffMap_j3 (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : Good_j3 N x) :
    Good_j3 N (coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x) := by
  obtain ⟨hxm, hxi⟩ := hx
  refine ⟨coeffMap_mem_laurentBaseChange τ hxm, ?_⟩
  have h := hxi.map_of_comp_eq (restrS2_j3 N τ)
    (arithmeticRingAut (modularFunctionFieldFull N) τ).toRingHom (RingHom.ext fun _ => rfl)
  exact h

private theorem good_sum_smul_j3 {ι : Type*} (s : Finset ι) (c : ι → AlgebraicClosure ℚ)
    {x : ι → LaurentSeries (AlgebraicClosure ℚ)} (h : ∀ i ∈ s, Good_j3 N (x i)) :
    Good_j3 N (∑ i ∈ s, c i • x i) :=
  good_sum_j3 N s fun i hi => good_smul_j3 N (c i) (h i hi)

end Conjugates

section Emb

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem coeffEmb_smul_j3 (r : ℚ) (x : LaurentSeries ℚ) :
    coeffEmb L (r • x) = algebraMap ℚ L r • coeffEmb L x := by
  rw [← HahnSeries.single_zero_mul_eq_smul, map_mul, coeffEmb, coeffMap_single,
    HahnSeries.single_zero_mul_eq_smul]

end Emb

section EmbMap

private theorem coeffMap_smul_j3 {L L' : Type*} [Field L] [Field L'] (ι : L →+* L') (c : L) (x : LaurentSeries L) :
    coeffMap ι (c • x) = ι c • coeffMap ι x := by
  rw [← HahnSeries.single_zero_mul_eq_smul, map_mul, coeffMap_single, HahnSeries.single_zero_mul_eq_smul]

end EmbMap

section Rational

variable (N : ℕ) [NeZero N]

omit [NeZero N] in

private theorem exists_finset_constants_j3 {f : LaurentSeries (AlgebraicClosure ℚ)}
    (hf : f ∈ modularFunctionFieldBar N) :
    ∃ T : Finset (AlgebraicClosure ℚ), f ∈ Subfield.closure
      (Set.range (fun c : (↑T : Set (AlgebraicClosure ℚ)) => HahnSeries.single (0 : ℤ) (c : AlgebraicClosure ℚ)) ∪
        ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (modularFunctionFieldFull N : Set (LaurentSeries ℚ))) := by
  have hf' : f ∈ Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
        ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (modularFunctionFieldFull N : Set (LaurentSeries ℚ))) := hf
  refine Subfield.closure_induction (p := fun x _ => ∃ T : Finset (AlgebraicClosure ℚ), x ∈ Subfield.closure
    (Set.range (fun c : (↑T : Set (AlgebraicClosure ℚ)) => HahnSeries.single (0 : ℤ) (c : AlgebraicClosure ℚ)) ∪
      ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (modularFunctionFieldFull N : Set (LaurentSeries ℚ))))
    ?_ ?_ ?_ ?_ ?_ ?_ hf'
  · rintro x (⟨c, rfl⟩ | hx)
    · refine ⟨{c}, Subfield.subset_closure (Or.inl ⟨⟨c, by simp⟩, ?_⟩)⟩
      exact (algebraMap_laurentSeries_eq_single (AlgebraicClosure ℚ) c).symm
    · exact ⟨∅, Subfield.subset_closure (Or.inr hx)⟩
  · exact ⟨∅, one_mem _⟩
  · rintro x y - - ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
    classical
    refine ⟨T₁ ∪ T₂, add_mem (Subfield.closure_mono ?_ h₁) (Subfield.closure_mono ?_ h₂)⟩
    · refine Set.union_subset_union_left _ ?_
      rintro _ ⟨⟨c, hc⟩, rfl⟩
      exact ⟨⟨c, by rw [Finset.coe_union]; exact Or.inl hc⟩, rfl⟩
    · refine Set.union_subset_union_left _ ?_
      rintro _ ⟨⟨c, hc⟩, rfl⟩
      exact ⟨⟨c, by rw [Finset.coe_union]; exact Or.inr hc⟩, rfl⟩
  · rintro x - ⟨T₁, h₁⟩
    exact ⟨T₁, neg_mem h₁⟩
  · rintro x - ⟨T₁, h₁⟩
    exact ⟨T₁, inv_mem h₁⟩
  · rintro x y - - ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
    classical
    refine ⟨T₁ ∪ T₂, mul_mem (Subfield.closure_mono ?_ h₁) (Subfield.closure_mono ?_ h₂)⟩
    · refine Set.union_subset_union_left _ ?_
      rintro _ ⟨⟨c, hc⟩, rfl⟩
      exact ⟨⟨c, by rw [Finset.coe_union]; exact Or.inl hc⟩, rfl⟩
    · refine Set.union_subset_union_left _ ?_
      rintro _ ⟨⟨c, hc⟩, rfl⟩
      exact ⟨⟨c, by rw [Finset.coe_union]; exact Or.inr hc⟩, rfl⟩

private theorem rat_family_core_j3 (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (ι : L →+* AlgebraicClosure ℚ)
    (hιQ : ι.comp (algebraMap ℚ L) = algebraMap ℚ (AlgebraicClosure ℚ))
    (hsurj : ∀ σ : L ≃ₐ[ℚ] L, ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ι.comp (σ : L →+* L) = (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp ι)
    (f₀ : LaurentSeries L) (hgood : Good_j3 N (coeffMap ι f₀)) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ) (a : Fin n → AlgebraicClosure ℚ),
      LinearIndependent ℚ Y ∧ (∀ i, Good_j3 N (coeffEmb (AlgebraicClosure ℚ) (Y i))) ∧
        coeffMap ι f₀ = ∑ i, a i • coeffEmb (AlgebraicClosure ℚ) (Y i) := by
  classical

  let V : Submodule L (LaurentSeries L) :=
    Submodule.span L (Set.range fun σ : L ≃ₐ[ℚ] L => coeffMap (σ : L →+* L) f₀)
  haveI : FiniteDimensional L V := FiniteDimensional.span_of_finite L (Set.finite_range _)
  have hV : ∀ (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries L), x ∈ V → coeffMap (σ : L →+* L) x ∈ V := by
    intro σ x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨σ', rfl⟩
      refine Submodule.subset_span ⟨σ * σ', ?_⟩
      show coeffMap ((σ * σ' : L ≃ₐ[ℚ] L) : L →+* L) f₀ = coeffMap (σ : L →+* L) (coeffMap (σ' : L →+* L) f₀)
      rw [coeffMap_coeffMap]
      exact coeffMap_congr (RingHom.ext fun _ => rfl) _
    · rw [map_zero]; exact zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]; exact add_mem hx hy
    · intro c x _ hx
      rw [coeffMap_smul_j3]
      exact Submodule.smul_mem _ _ hx
  obtain ⟨n, Y, hYli, hYspan⟩ :=
    ModularCurve.exists_coeffEmb_basis_of_forall_coeffMap_mem L V hV

  have hf₀V : f₀ ∈ V := by
    refine Submodule.subset_span ⟨1, ?_⟩
    show coeffMap ((1 : L ≃ₐ[ℚ] L) : L →+* L) f₀ = f₀
    rw [show ((1 : L ≃ₐ[ℚ] L) : L →+* L) = RingHom.id L from RingHom.ext fun _ => rfl, coeffMap_id]
  have hf₀V' : f₀ ∈ Submodule.span L (Set.range fun i => coeffEmb L (Y i)) := by rw [hYspan]; exact hf₀V
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf₀V'

  have hgoodV : ∀ x ∈ V, Good_j3 N (coeffMap ι x) := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨σ, rfl⟩
      obtain ⟨τ, hτ⟩ := hsurj σ
      rw [coeffMap_coeffMap, hτ, ← coeffMap_coeffMap]
      exact good_coeffMap_j3 N τ hgood
    · rw [map_zero]; exact good_zero_j3 N
    · intro x y _ _ hx hy
      rw [map_add]; exact good_add_j3 N hx hy
    · intro c x _ hx
      rw [coeffMap_smul_j3]
      exact good_smul_j3 N _ hx
  have hιY : ∀ i, coeffMap ι (coeffEmb L (Y i)) = coeffEmb (AlgebraicClosure ℚ) (Y i) := fun i => by
    rw [coeffEmb, coeffMap_coeffMap, hιQ, coeffEmb]
  have hgoodY : ∀ i, Good_j3 N (coeffEmb (AlgebraicClosure ℚ) (Y i)) := fun i => by
    rw [← hιY]
    refine hgoodV _ ?_
    rw [← hYspan]
    exact Submodule.subset_span ⟨i, rfl⟩

  have hYli' : LinearIndependent ℚ Y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (coeffEmb L) hg
    rw [map_sum, map_zero] at h
    simp only [coeffEmb_smul_j3] at h
    have := (Fintype.linearIndependent_iff.mp hYli) (fun i => algebraMap ℚ L (g i)) h i
    exact (algebraMap ℚ L).injective (by rw [this, map_zero])
  refine ⟨n, Y, fun i => ι (c i), hYli', hgoodY, ?_⟩
  rw [← hc, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [coeffMap_smul_j3, hιY]

private theorem exists_rat_family_j3 {f : LaurentSeries (AlgebraicClosure ℚ)} (hgood : Good_j3 N f) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ) (a : Fin n → AlgebraicClosure ℚ),
      LinearIndependent ℚ Y ∧ (∀ i, Good_j3 N (coeffEmb (AlgebraicClosure ℚ) (Y i))) ∧
        f = ∑ i, a i • coeffEmb (AlgebraicClosure ℚ) (Y i) := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_constants_j3 N hgood.1

  let K₀ : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (↑T : Set (AlgebraicClosure ℚ))
  haveI : Finite (↑T : Set (AlgebraicClosure ℚ)) := (Finset.finite_toSet _).to_subtype
  haveI : FiniteDimensional ℚ K₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ K₀ (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ K₀ (AlgebraicClosure ℚ)
  haveI hLn : Normal ℚ L := normalClosure.normal ℚ K₀ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ L := IsGalois.mk
  let ι : L →+* AlgebraicClosure ℚ := algebraMap L (AlgebraicClosure ℚ)
  have hιQ : ι.comp (algebraMap ℚ L) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    (IsScalarTower.algebraMap_eq ℚ L (AlgebraicClosure ℚ)).symm
  have hsurj : ∀ σ : L ≃ₐ[ℚ] L, ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ι.comp (σ : L →+* L) = (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp ι := by
    intro σ
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := L)
      (E := AlgebraicClosure ℚ) σ
    refine ⟨τ, RingHom.ext fun x => ?_⟩
    show ι (σ x) = τ (ι x)
    rw [← hτ]
    exact AlgEquiv.restrictNormalHom_apply L τ x

  have hTL : ∀ c ∈ (↑T : Set (AlgebraicClosure ℚ)), c ∈ L := fun c hc =>
    IntermediateField.le_normalClosure K₀ (IntermediateField.subset_adjoin ℚ _ hc)
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : LaurentSeries L, coeffMap ι f₀ = f := by
    have hle : Subfield.closure
        (Set.range (fun c : (↑T : Set (AlgebraicClosure ℚ)) => HahnSeries.single (0 : ℤ) (c : AlgebraicClosure ℚ)) ∪
          ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (modularFunctionFieldFull N : Set (LaurentSeries ℚ))) ≤
        (coeffMap ι).fieldRange := by
      refine Subfield.closure_le.mpr ?_
      rintro x (⟨⟨c, hc⟩, rfl⟩ | ⟨z, -, rfl⟩)
      · exact ⟨HahnSeries.single 0 ⟨c, hTL c hc⟩, coeffMap_single ι 0 _⟩
      · refine ⟨coeffEmb L z, ?_⟩
        show coeffMap ι (coeffEmb L z) = coeffEmb (AlgebraicClosure ℚ) z
        rw [coeffEmb, coeffMap_coeffMap, hιQ, coeffEmb]
    obtain ⟨f₀, hf₀⟩ := hle hT
    exact ⟨f₀, hf₀⟩
  rw [← hf₀] at hgood ⊢
  exact rat_family_core_j3 N L ι hιQ hsurj f₀ hgood

private theorem isIntegral_adjoin_jq_j3 {Y : LaurentSeries ℚ}
    (h : Good_j3 N (coeffEmb (AlgebraicClosure ℚ) Y)) :
    IsIntegral ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) Y := by
  obtain ⟨hmem, hi⟩ := h
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N

  obtain ⟨J', hJ'⟩ : ∃ J' : LaurentSeries (AlgebraicClosure ℚ), J' = coeffEmb (AlgebraicClosure ℚ) jq :=
    ⟨_, rfl⟩
  obtain ⟨JN', hJN'⟩ : ∃ JN' : LaurentSeries (AlgebraicClosure ℚ),
      JN' = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) := ⟨_, rfl⟩
  let S₂' : Subalgebra (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    Algebra.adjoin (AlgebraicClosure ℚ) {J', JN'}
  let S₁' : Subalgebra (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    Algebra.adjoin (AlgebraicClosure ℚ) {J'}

  have hval : ∀ s : ↥(S2_j3 N), ((s : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ S₂' := by
    intro s
    refine Algebra.adjoin_induction
      (p := fun (t : ↥(modularFunctionFieldBar N)) _ => (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ S₂')
      ?_ ?_ ?_ ?_ s.2
    · rintro t (rfl | rfl)
      · show coeffEmb (AlgebraicClosure ℚ) jq ∈ S₂'
        rw [← hJ']
        exact Algebra.subset_adjoin (Set.mem_insert _ _)
      · show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) ∈ S₂'
        rw [← hJN']
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    · intro r; exact Subalgebra.algebraMap_mem _ r
    · intro t t' _ _ ht ht'; exact add_mem ht ht'
    · intro t t' _ _ ht ht'; exact mul_mem ht ht'
  let φ : ↥(S2_j3 N) →+* ↥S₂' :=
    ((modularFunctionFieldBar N).val.toRingHom.comp (S2_j3 N).val.toRingHom).codRestrict S₂' hval
  have hi₂ : IsIntegral ↥S₂' (coeffEmb (AlgebraicClosure ℚ) Y) :=
    hi.map_of_comp_eq φ (modularFunctionFieldBar N).val.toRingHom (RingHom.ext fun _ => rfl)

  have hle : S₁' ≤ S₂' := Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  letI : Algebra ↥S₁' ↥S₂' := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥S₁' ↥S₂' (LaurentSeries (AlgebraicClosure ℚ)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hJmem : J' ∈ S₁' := Algebra.subset_adjoin rfl
  have hJNint : IsIntegral ↥S₁' JN' := by
    refine ⟨data.Φ.map (Polynomial.aeval (R := ℤ) (⟨J', hJmem⟩ : ↥S₁')).toRingHom,
      data.monic.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥S₁' (LaurentSeries (AlgebraicClosure ℚ))).comp
        (Polynomial.aeval (R := ℤ) (⟨J', hJmem⟩ : ↥S₁')).toRingHom =
        (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
      refine Polynomial.ringHom_ext (fun z => by simp) ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      exact hJ'
    rw [hcomp, hJN', show qExpand ℚ N jq = jqN N from rfl, ← Polynomial.hom_eval₂,
      data.eval_eq_zero, map_zero]
  haveI : Algebra.IsIntegral ↥S₁' ↥S₂' := by
    refine ⟨fun s => ?_⟩
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥S₁' ↥S₂' (LaurentSeries (AlgebraicClosure ℚ)))
      (fun a b hab => Subtype.ext hab)]
    show IsIntegral ↥S₁' (s : LaurentSeries (AlgebraicClosure ℚ))
    refine Algebra.adjoin_induction
      (p := fun (t : LaurentSeries (AlgebraicClosure ℚ)) _ => IsIntegral ↥S₁' t) ?_ ?_ ?_ ?_ s.2
    · rintro t (rfl | rfl)
      · exact isIntegral_algebraMap (x := (⟨t, hJmem⟩ : ↥S₁'))
      · exact hJNint
    · intro r
      exact isIntegral_algebraMap (x := algebraMap (AlgebraicClosure ℚ) ↥S₁' r)
    · intro t t' _ _ ht ht'
      exact ht.add ht'
    · intro t t' _ _ ht ht'
      exact ht.mul ht'
  have hi₃ : IsIntegral ↥S₁' (coeffEmb (AlgebraicClosure ℚ) Y) := isIntegral_trans _ hi₂

  have hi₄ : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
      ({coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq} : Set (LaurentSeries (AlgebraicClosure ℚ))))
      (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) Y) := by
    have hJ'' : J' = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq := hJ'
    rw [← hJ'']
    exact hi₃
  exact ModularCurve.isIntegral_adjoin_of_isIntegral_adjoin_coeffMap (algebraMap ℚ (AlgebraicClosure ℚ))
    jq Y hi₄

private theorem coeffEmb_mem_fieldOver_j3 (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull N) :
    coeffEmb (AlgebraicClosure ℚ) x ∈ NodeLocalized.fieldOver N K := by
  have hgen := ModularCurve.functionFieldGeneration N
  have hfull_le : modularFunctionFieldFull N ≤ modularFunctionField N := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨d, hd, hdN, rfl⟩
    exact hgen d hdN hd
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {jq, qExpand ℚ N jq}) :=
    hfull_le hx
  refine Subfield.closure_induction
    (p := fun x _ => coeffEmb (AlgebraicClosure ℚ) x ∈ NodeLocalized.fieldOver N K) ?_ ?_ ?_ ?_ ?_ ?_ hx'
  · rintro t (⟨r, rfl⟩ | ht)
    · refine Subfield.subset_closure (Or.inl ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) r, K.algebraMap_mem r⟩, ?_⟩)
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
          (algebraMap ℚ (AlgebraicClosure ℚ) r) = coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r)
      rw [algebraMap_laurentSeries_eq_single ℚ r, coeffEmb, coeffMap_single,
        algebraMap_laurentSeries_eq_single]
    · rcases ht with rfl | rfl
      · refine Subfield.subset_closure (Or.inr (Or.inl ?_))
        show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq = jqModC (AlgebraicClosure ℚ)
        rw [← jqModC_rat]; exact map_jqModC _
      · refine Subfield.subset_closure (Or.inr (Or.inr ?_))
        show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N
        rw [coeffSemilinearAut.coeffMap_qExpand, ← jqModC_rat]
        exact congrArg _ (map_jqModC _)
  · simp only [map_one]; exact one_mem _
  · intro t t' _ _ ht ht'; simp only [map_add]; exact add_mem ht ht'
  · intro t _ ht; simp only [map_neg]; exact neg_mem ht
  · intro t _ ht; simp only [map_inv₀]; exact inv_mem ht
  · intro t t' _ _ ht ht'; simp only [map_mul]; exact mul_mem ht ht'

end Rational

end J3C2

open ModularCurve J3C2 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (h₀ : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (y₁ : LaurentSeries A)
    (hy₁ : coeffMap A.subtype y₁ ∈ modularFunctionFieldBar N)
    (hred : coeffMap (NodeLocalized.redRestrict red K) h₀ = coeffMap red y₁)
    (hint :
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) (⟨coeffMap A.subtype y₁, hy₁⟩ : ↥(modularFunctionFieldBar N))) :
    ∃ (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g : ↥(modularFunctionFieldBar N)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver N K ∧
      coeffMap (NodeLocalized.coeffSubring A K).subtype y = (g : LaurentSeries (AlgebraicClosure ℚ)) ∧
      coeffMap (NodeLocalized.redRestrict red K) h₀ = coeffMap (NodeLocalized.redRestrict red K) y ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g := by
  classical
  have hgoodf : J3C2.Good_j3 N (coeffMap A.subtype y₁) := ⟨hy₁, hint⟩

  have hqA : ¬IsUnit ((q : ℕ) : A) := fun hu => by
    have hu' := hu.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at hu'
    exact not_isUnit_zero hu'

  obtain ⟨n, Y, a, hYli, hgoodY, hfY⟩ := J3C2.exists_rat_family_j3 N hgoodf
  have hYfull : ∀ i, Y i ∈ modularFunctionFieldFull N := fun i =>
    ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      (Y i) (hgoodY i).1
  have hYint : ∀ i, IsIntegral ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (Y i) := fun i =>
    J3C2.isIntegral_adjoin_jq_j3 N (hgoodY i)

  choose D hD0 z hz using fun i => J3C2.exists_int_series_smul_j3 (Y i) (hYfull i) (hYint i)

  let e : Fin n → LaurentSeries ℚ := fun i => (D i : ℚ) • Y i
  have heq : ∀ i, QIntSeries_j3 q (e i) := fun i m => by
    have h := congrArg (fun x => HahnSeries.coeff x m) (hz i)
    simp only [coeffMap_coeff] at h
    show IsQInt_j3 q (((D i : ℚ) • Y i).coeff m)
    rw [← h]
    exact isQInt_intCast_j3 q _
  have heli : LinearIndependent ℚ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h' : ∑ i, (g i * D i) • Y i = 0 := by
      rw [← hg]; exact Finset.sum_congr rfl fun i _ => by rw [← smul_smul]
    have := (Fintype.linearIndependent_iff.mp hYli) (fun i => g i * D i) h' i
    exact (mul_eq_zero.mp this).resolve_right (Nat.cast_ne_zero.mpr (hD0 i))
  obtain ⟨κ, e', he'span, hδ, he'q, hrep⟩ := J3C2.echelon_j3 q n e heli heq

  have hsmul_full : ∀ (r : ℚ) {x : LaurentSeries ℚ}, x ∈ modularFunctionFieldFull N →
      r • x ∈ modularFunctionFieldFull N := fun r x hx => by
    rw [← HahnSeries.single_zero_mul_eq_smul, ← algebraMap_laurentSeries_eq_single]
    exact mul_mem ((modularFunctionFieldFull N).algebraMap_mem r) hx
  have hespan_full : ∀ x ∈ Submodule.span ℚ (Set.range e), x ∈ modularFunctionFieldFull N := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact hsmul_full _ (hYfull i)
    · exact zero_mem _
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro r x _ hx; exact hsmul_full r hx
  have he'full : ∀ j, e' j ∈ modularFunctionFieldFull N := fun j => hespan_full _ (he'span j)
  let E' : Fin n → LaurentSeries (AlgebraicClosure ℚ) := fun j => coeffEmb (AlgebraicClosure ℚ) (e' j)
  have hgoode : ∀ i, Good_j3 N (coeffEmb (AlgebraicClosure ℚ) (e i)) := fun i => by
    show Good_j3 N (coeffEmb (AlgebraicClosure ℚ) ((D i : ℚ) • Y i))
    rw [coeffEmb_smul_j3]
    exact good_smul_j3 N _ (hgoodY i)
  have hgoodspan : ∀ x ∈ Submodule.span ℚ (Set.range e), Good_j3 N (coeffEmb (AlgebraicClosure ℚ) x) := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact hgoode i
    · rw [map_zero]; exact good_zero_j3 N
    · intro x y _ _ hx hy
      rw [map_add]; exact good_add_j3 N hx hy
    · intro r x _ hx
      rw [coeffEmb_smul_j3]; exact good_smul_j3 N _ hx
  have hgoodE' : ∀ j, Good_j3 N (E' j) := fun j => hgoodspan _ (he'span j)

  have hfsum : coeffMap A.subtype y₁ = ∑ i, (a i * ((D i : ℕ) : AlgebraicClosure ℚ)⁻¹) •
      coeffEmb (AlgebraicClosure ℚ) (e i) := by
    rw [hfY]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_smul]
    congr 1
    show coeffEmb (AlgebraicClosure ℚ) (Y i) = _ • coeffEmb (AlgebraicClosure ℚ) ((D i : ℚ) • Y i)
    rw [coeffEmb_smul_j3, smul_smul, map_natCast, inv_mul_cancel₀
      (Nat.cast_ne_zero.mpr (hD0 i) : ((D i : ℕ) : AlgebraicClosure ℚ) ≠ 0), one_smul]
  have hEspan : ∀ i, coeffEmb (AlgebraicClosure ℚ) (e i) ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range E') := by
    intro i
    rw [hrep i, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [coeffEmb_smul_j3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hfspan : coeffMap A.subtype y₁ ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range E') := by
    rw [hfsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hEspan i)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hfspan
  have hE'κ : ∀ i j, (E' j).coeff (κ i) = if i = j then 1 else 0 := fun i j => by
    show (coeffEmb (AlgebraicClosure ℚ) (e' j)).coeff (κ i) = _
    rw [coeffEmb_coeff, hδ i j]
    split_ifs <;> simp
  have hbκ : ∀ i, b i = ((y₁.coeff (κ i) : A) : AlgebraicClosure ℚ) := fun i => by
    have h := congrArg (fun x => HahnSeries.coeff x (κ i)) hb
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, hE'κ, mul_boole,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    rw [h]
    rfl

  have hcoeff : ∀ m, ((y₁.coeff m : A) : AlgebraicClosure ℚ) =
      ∑ j, ((y₁.coeff (κ j) : A) : AlgebraicClosure ℚ) * algebraMap ℚ (AlgebraicClosure ℚ) ((e' j).coeff m) := by
    intro m
    have h := congrArg (fun x => HahnSeries.coeff x m) hb
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, hbκ] at h
    exact h.symm

  have hρA : ∀ j m, algebraMap ℚ (AlgebraicClosure ℚ) ((e' j).coeff m) ∈ A := fun j m => by
    rw [eq_ratCast (algebraMap ℚ (AlgebraicClosure ℚ))]
    exact J3C2.mem_of_isQInt_j3 q A hqA (he'q j m)
  have hρ : ∀ j m, algebraMap ℚ (AlgebraicClosure ℚ) ((e' j).coeff m) ∈ NodeLocalized.coeffSubring A K :=
    fun j m => Subring.mem_inf.mpr ⟨hρA j m, K.algebraMap_mem _⟩
  let g : LaurentSeries (AlgebraicClosure ℚ) :=
    ∑ j, ((h₀.coeff (κ j) : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) • E' j
  have hgcoeff : ∀ m, g.coeff m = ∑ j, ((h₀.coeff (κ j) : ↥(NodeLocalized.coeffSubring A K)) :
      AlgebraicClosure ℚ) * algebraMap ℚ (AlgebraicClosure ℚ) ((e' j).coeff m) := fun m => by
    show (∑ j, _ • E' j).coeff m = _
    rw [HahnSeries.coeff_sum]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    rfl
  have hgmem : ∀ m, g.coeff m ∈ NodeLocalized.coeffSubring A K := fun m => by
    rw [hgcoeff]
    exact sum_mem fun j _ => mul_mem (h₀.coeff (κ j)).2 (hρ j m)
  let y : LaurentSeries ↥(NodeLocalized.coeffSubring A K) := J3C2.liftSeries_j3 _ g hgmem
  have hgood_g : Good_j3 N g := good_sum_smul_j3 N _ _ fun j _ => hgoodE' j
  obtain ⟨hgBar, hgint⟩ := hgood_g
  refine ⟨y, ⟨g, hgBar⟩, ?_, ?_, ?_, hgint⟩
  ·
    show g ∈ NodeLocalized.fieldOver N K
    refine sum_mem fun j _ => ?_
    rw [← HahnSeries.single_zero_mul_eq_smul, ← algebraMap_laurentSeries_eq_single]
    refine mul_mem (Subfield.subset_closure (Or.inl ⟨⟨_, (Subring.mem_inf.mp (h₀.coeff (κ j)).2).2⟩, rfl⟩)) ?_
    exact J3C2.coeffEmb_mem_fieldOver_j3 N K (he'full j)
  ·
    exact J3C2.coeffMap_liftSeries_j3 _ g hgmem
  ·
    ext m
    rw [coeffMap_coeff, coeffMap_coeff]
    have hredm : ∀ m, NodeLocalized.redRestrict red K (h₀.coeff m) = red (y₁.coeff m) := fun m => by
      have h := congrArg (fun x => HahnSeries.coeff x m) hred
      simpa only [coeffMap_coeff] using h
    rw [hredm m]

    have hAinj : Function.Injective A.subtype := fun u v huv => Subtype.ext huv
    have hRinj : Function.Injective (NodeLocalized.coeffSubring A K).subtype := fun u v huv => Subtype.ext huv
    have h1 : y₁.coeff m =
        ∑ j, y₁.coeff (κ j) * (⟨algebraMap ℚ (AlgebraicClosure ℚ) ((e' j).coeff m), hρA j m⟩ : A) := by
      apply hAinj
      rw [map_sum]
      simp only [map_mul]
      exact hcoeff m
    have h2 : y.coeff m = ∑ j, h₀.coeff (κ j) *
        (⟨algebraMap ℚ (AlgebraicClosure ℚ) ((e' j).coeff m), hρ j m⟩ : ↥(NodeLocalized.coeffSubring A K)) := by
      apply hRinj
      rw [map_sum]
      simp only [map_mul]
      exact hgcoeff m
    rw [h1, h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hredm (κ j)]
    rfl

end S_ModularCurve_NodeLocalized_exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral (solution)
