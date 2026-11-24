-- Prove2me | solution 1 for GlobalTheory.SS.exists_polynomial_leading_quotient_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:18.91519+00:00
-- url     : https://prove2.me/submissions/c9900fc1-52fd-4e3c-96d2-b50e7dbb7886

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLeadingQuotientWeightedArcs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma weight_fin_two (m n : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.weight (![m, n] : Fin 2 → ℕ) e = m * e 0 + n * e 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, mul_comm]
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma leading_polynomial_eq_zero_iff_lt_weightedOrder {k : Type} [Field k] {m n : ℕ} (hm : 1 ≤ m)
    (f : MvPowerSeries (Fin 2) k) {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)) = 0 ↔
      (D : ℕ∞) < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f := by
  have hcoeff : ∀ e ∈ S,
      (∑ e' ∈ S, Polynomial.C (MvPowerSeries.coeff e' f) * Polynomial.X ^ (e' 1)).coeff (e 1) =
        MvPowerSeries.coeff e f := by
    intro e he
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single e]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · intro e' he' hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h1
      apply hne
      have w1 := (hS e').1 he'
      have w2 := (hS e).1 he
      rw [weight_fin_two] at w1 w2
      rw [h1] at w2
      have h0 : e' 0 = e 0 :=
        Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel (w1.trans w2.symm))
      ext i
      fin_cases i
      · exact h0
      · exact h1.symm
    · intro h; exact absurd he h
  constructor
  · intro h0
    by_contra hlt
    push_neg at hlt
    have heq : MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f = D := le_antisymm hlt hD
    obtain ⟨e, hne, hwe⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder
      (![m, n] : Fin 2 → ℕ) (f := f) (by rw [heq]; rfl)
    rw [heq, Nat.cast_inj] at hwe
    have := hcoeff e ((hS e).2 hwe)
    rw [h0, Polynomial.coeff_zero] at this
    exact hne this.symm
  · intro hlt
    refine Finset.sum_eq_zero fun e he => ?_
    rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (by rw [(hS e).1 he]; exact hlt),
      map_zero, zero_mul]
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma prod_pow_fin_two {k : Type} [Field k] (z w : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    (e.prod fun s j => (![z, w] : Fin 2 → PowerSeries k) s ^ j) = z ^ e 0 * w ^ e 1 := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open PowerSeries in
private lemma coeff_pow_mul_pow_of_le_order {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order) (a b : ℕ) :
    (∀ j < m * a + n * b, coeff j (z ^ a * w ^ b) = 0) ∧
      coeff (m * a + n * b) (z ^ a * w ^ b) = coeff m z ^ a * coeff n w ^ b := by
  obtain ⟨z', rfl⟩ : X ^ m ∣ z := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hz)
  obtain ⟨w', rfl⟩ : X ^ n ∣ w := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hw)
  have hprod : (X ^ m * z') ^ a * (X ^ n * w') ^ b = X ^ (m * a + n * b) * (z' ^ a * w' ^ b) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
  rw [hprod]
  refine ⟨fun j hj => by rw [coeff_X_pow_mul', if_neg (by omega)], ?_⟩
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff, map_mul, map_pow,
    map_pow]
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_zero_of_lt {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {f : MvPowerSeries (Fin 2) k}
    {D : ℕ} (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f) {j : ℕ}
    (hj : j < D) : PowerSeries.coeff j (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) = 0 := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases hlt : Finsupp.weight (![m, n] : Fin 2 → ℕ) e < D
  · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
      (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
  · rw [weight_fin_two] at hlt
    rw [prod_pow_fin_two, ← PowerSeries.coeff,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 j (by omega), smul_zero]
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_pow_mul_eval_leading {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {s t : k}
    (hzs : PowerSeries.coeff m z = s ^ m) (hwt : PowerSeries.coeff n w = s ^ n * t)
    {f : MvPowerSeries (Fin 2) k} {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    PowerSeries.coeff D (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) =
      s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := S)]
  · rw [Polynomial.eval_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hwe := (hS e).1 he
    rw [weight_fin_two] at hwe
    rw [prod_pow_fin_two, ← PowerSeries.coeff, ← hwe,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).2, hzs, hwt]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul]
    rw [pow_add, pow_mul, pow_mul]
    ring
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.mem_coe, hS]
    by_contra hne
    apply he
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
        (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
    · rw [weight_fin_two] at hgt
      rw [prod_pow_fin_two, ← PowerSeries.coeff,
        (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 D (by omega), smul_zero]
end GlobalTheory.SS
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
open GlobalTheory GlobalTheory.SS
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace GlobalTheory.SS
namespace _root_.GlobalTheory.SS
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  intro k _ _ m n hm hn r h d hd hdh
  have hfin : ((MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat : ℕ∞) =
      MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d :=
    ENat.coe_toNat ((MvPowerSeries.weightedOrder_eq_top_iff _).not.2 hd)
  set D := (MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat with hD_def
  have hWpos : ∀ x, (![m, n] : Fin 2 → ℕ) x ≠ 0 := by
    intro x; fin_cases x <;> simp <;> omega
  set S := (Finsupp.finite_of_nat_weight_le _ hWpos D).toFinset.filter
    fun e => Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D with hS_def
  have hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D := by
    intro e
    simp only [hS_def, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have hDd : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d := hfin.le
  have hDh : ∀ i, (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i) :=
    fun i => hfin.le.trans (hdh i)
  refine ⟨∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e d) * Polynomial.X ^ (e 1),
    fun i => ∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e (h i)) * Polynomial.X ^ (e 1), ?_, ?_, ?_⟩
  · intro h0
    have := (leading_polynomial_eq_zero_iff_lt_weightedOrder hm d hDd S hS).1 h0
    rw [hfin] at this
    exact lt_irrefl _ this
  · intro i
    rw [leading_polynomial_eq_zero_iff_lt_weightedOrder hm (h i) (hDh i) S hS, hfin]
  · intro s t z w hs0 hz hw hzs hwt hPd
    have hz0 : PowerSeries.coeff 0 z = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hm) hz)
    have hw0 : PowerSeries.coeff 0 w = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hn) hw)
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hz0 hw0
    have hsub : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
        fin_cases i
        · exact hz0
        · exact hw0
    have factor : ∀ f : MvPowerSeries (Fin 2) k,
        (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f →
        ∃ g : PowerSeries k, MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f =
          PowerSeries.X ^ D * g ∧ PowerSeries.constantCoeff g =
            s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
      intro f hf
      obtain ⟨g, hg⟩ := PowerSeries.X_pow_dvd_iff.2 fun j hj =>
        coeff_subst_eq_zero_of_lt hz hw hsub hf hj
      refine ⟨g, hg, ?_⟩
      have := coeff_subst_eq_pow_mul_eval_leading hz hw hsub hzs hwt hf S hS
      rw [hg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff] at this
      exact this
    obtain ⟨gd, hgd, hgd0⟩ := factor d hDd
    have hgd0' : PowerSeries.constantCoeff gd ≠ 0 := by
      rw [hgd0]; exact mul_ne_zero (pow_ne_zero _ hs0) hPd
    refine ⟨?_, fun i => (factor (h i) (hDh i)).choose * gd⁻¹, fun i => ?_⟩
    · rw [hgd]
      exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
        fun h0 => hgd0' (by rw [h0, map_zero])
    · obtain ⟨hgi, hgi0⟩ := (factor (h i) (hDh i)).choose_spec
      constructor
      · rw [hgd, hgi, show (factor (h i) (hDh i)).choose * gd⁻¹ * (PowerSeries.X ^ D * gd) =
          PowerSeries.X ^ D * (factor (h i) (hDh i)).choose * (gd * gd⁻¹) by ring,
          PowerSeries.mul_inv_cancel _ hgd0', _root_.mul_one]
      · rw [map_mul, PowerSeries.constantCoeff_inv, hgi0, hgd0]
        field_simp
end _root_.GlobalTheory.SS
end GlobalTheory.SS
