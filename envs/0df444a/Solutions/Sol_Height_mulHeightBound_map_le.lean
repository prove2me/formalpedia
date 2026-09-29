-- Prove2me | solution 1 for Height.mulHeightBound_map_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c48dd8c7-704b-50c9-9651-e63305fd057d

import Mathlib
import Theorems.Thm_Height_logHeight_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Height_mulHeightBound_map_le

open Height NumberField

section helpers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

open NumberField.InfinitePlace in
open scoped Classical in

private lemma mwabs_sum_mult_comap [Algebra K L] (v : InfinitePlace K) :
    ∑ w ∈ Finset.univ.filter
        (fun w : InfinitePlace L => w.comap (algebraMap K L) = v), w.mult
      = v.mult * Module.finrank K L := by
  have hmem : ∀ w : InfinitePlace L,
      w ∈ placesOver L v ↔ w.comap (algebraMap K L) = v := by
    intro w
    constructor
    · intro h
      have : w.1.LiesOver v.1 := h
      exact LiesOver.comap_eq w v
    · intro h
      exact ⟨congrArg Subtype.val h⟩
  have hset : Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v)
      = (placesOver L v).toFinset := by
    ext w
    simp [hmem w]
  have hPU : (placesOver L v).toFinset
      = (ramifiedPlacesOver L v).toFinset ∪ (unramifiedPlacesOver L v).toFinset := by
    rw [← Set.toFinset_union, Set.toFinset_inj]
    exact (union_ramifiedPlacesOver_unramifiedPlacesOver L v).symm
  have hdisj : Disjoint ((ramifiedPlacesOver L v).toFinset)
      ((unramifiedPlacesOver L v).toFinset) := by
    rw [Set.disjoint_toFinset]
    exact disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v
  have hU : ∀ w ∈ (unramifiedPlacesOver L v).toFinset, w.mult = v.mult := by
    intro w hw
    have hw' := Set.mem_toFinset.mp hw
    have hlies : w.1.LiesOver v.1 := hw'.1
    rw [← hw'.2.eq, LiesOver.comap_eq w v]
  have hR : ∀ w ∈ (ramifiedPlacesOver L v).toFinset, w.mult = 2 := by
    intro w hw
    have hw' := Set.mem_toFinset.mp hw
    exact mult_isComplex ⟨w, hw'.2.isComplex⟩
  rw [hset, hPU, Finset.sum_union hdisj, Finset.sum_congr rfl hR, Finset.sum_congr rfl hU,
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
  have hcard := unramifedPlacesOver_ncard_add_eq_finrank (K := K) (L := L) (v := v)
  rcases (ramifiedPlacesOver L v).eq_empty_or_nonempty with hE | ⟨w₀, hw₀⟩
  · rw [hE] at hcard ⊢
    simp only [Set.ncard_empty, mul_zero, zero_add, zero_mul, add_zero] at hcard ⊢
    rw [hcard]
    ring
  · haveI hlies : w₀.1.LiesOver v.1 := hw₀.1
    have hreal : v.IsReal := hw₀.2.liesOver_isReal_under (v := v)
    have hmv : v.mult = 1 := mult_isReal ⟨v, hreal⟩
    rw [hmv]
    omega

open scoped Classical in

private lemma mwabs_arch [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    (∏ w : InfinitePlace L, (⨆ i, w (algebraMap K L (x i))) ^ w.mult)
      = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) ^ Module.finrank K L := by
  rw [← Finset.prod_fiberwise Finset.univ
    (fun w : InfinitePlace L => w.comap (algebraMap K L))
    (fun w => (⨆ i, w (algebraMap K L (x i))) ^ w.mult), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hfib : ∀ w ∈ Finset.univ.filter
      (fun w : InfinitePlace L => w.comap (algebraMap K L) = v),
      (⨆ i, w (algebraMap K L (x i))) ^ w.mult = (⨆ i, v (x i)) ^ w.mult := by
    intro w hw
    have hcom : w.comap (algebraMap K L) = v := (Finset.mem_filter.mp hw).2
    have hsup : (⨆ i, w (algebraMap K L (x i))) = ⨆ i, v (x i) := by
      refine iSup_congr fun i => ?_
      rw [← hcom, NumberField.InfinitePlace.comap_apply]
    rw [hsup]
  rw [Finset.prod_congr rfl hfib, Finset.prod_pow_eq_pow_sum, mwabs_sum_mult_comap v, pow_mul]

private lemma mhb_arch_tuple_pos {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    0 < ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  refine Finset.prod_pos fun v _ => pow_pos ?_ _
  exact lt_of_lt_of_le (NumberField.InfinitePlace.pos_iff.mpr hi₀) (Finite.le_ciSup (fun i => v (x i)) i₀)

private lemma mhb_finprod_tuple [Algebra K L] {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (x i)))
      = (∏ᶠ v : FinitePlace K, ⨆ i, v (x i)) ^ Module.finrank K L := by
  have hxL : (fun i => algebraMap K L (x i)) ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    refine Function.ne_iff.mpr ⟨j, fun hcontra => hj ?_⟩
    have : algebraMap K L (x j) = 0 := by simpa using hcontra
    exact (map_eq_zero (algebraMap K L)).mp this

  have hlog := Height.logHeight_algebraMap (K := K) (L := L) x
  have hposK : 0 < mulHeight x := Height.mulHeight_pos x
  have hposL : 0 < mulHeight (fun i => algebraMap K L (x i)) := Height.mulHeight_pos _
  have hmul : mulHeight (fun i => algebraMap K L (x i)) = mulHeight x ^ Module.finrank K L := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr hposL) (Set.mem_Ioi.mpr (pow_pos hposK _))
    rw [Real.log_pow]
    exact hlog
  rw [NumberField.mulHeight_eq hxL, NumberField.mulHeight_eq hx, mul_pow, mwabs_arch x] at hmul
  exact mul_left_cancel₀ (pow_ne_zero _ (mhb_arch_tuple_pos hx).ne') hmul

end helpers

section scale

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

private theorem mhb_iSup_max_iSup_eq {ι' : Type*} [Finite ι'] [Nonempty ι'] (S : ι' → Type*)
    [∀ j, Finite (S j)] (a : (j : ι') → S j → ℝ) (_ha : ∀ j s, 0 ≤ a j s) :
    (⨆ j, max (⨆ s, a j s) 1) = ⨆ i : Option (Σ j, S j), i.elim 1 (fun js => a js.1 js.2) := by
  have hR1 : (1 : ℝ) ≤ ⨆ i : Option (Σ j, S j), i.elim 1 (fun js => a js.1 js.2) :=
    Finite.le_ciSup_of_le (f := fun i : Option (Σ j, S j) => i.elim 1 (fun js => a js.1 js.2)) none le_rfl
  have hRa : ∀ j s, a j s ≤ ⨆ i : Option (Σ j, S j), i.elim 1 (fun js => a js.1 js.2) := fun j s =>
    Finite.le_ciSup_of_le (f := fun i : Option (Σ j, S j) => i.elim 1 (fun js => a js.1 js.2)) (some ⟨j, s⟩) le_rfl
  obtain ⟨j₀⟩ := ‹Nonempty ι'›
  have hL1 : (1 : ℝ) ≤ ⨆ j, max (⨆ s, a j s) 1 :=
    Finite.le_ciSup_of_le (f := fun j => max (⨆ s, a j s) 1) j₀ (le_max_right _ _)
  have hLa : ∀ j s, a j s ≤ ⨆ j, max (⨆ s, a j s) 1 := fun j s =>
    Finite.le_ciSup_of_le (f := fun j => max (⨆ s, a j s) 1) j
      (le_trans (Finite.le_ciSup (fun s => a j s) s) (le_max_left _ _))
  refine le_antisymm ?_ ?_
  · refine Real.iSup_le (fun j => max_le ?_ hR1) (le_trans zero_le_one hR1)
    exact Real.iSup_le (fun s => hRa j s) (le_trans zero_le_one hR1)
  · refine Real.iSup_le (fun i => ?_) (le_trans zero_le_one hL1)
    cases i with
    | none => exact hL1
    | some js => exact hLa js.1 js.2

private def mhb_tuple {ι ι' : Type*} (p : ι' → MvPolynomial ι K) : Option (Σ j, ↥(p j).support) → K :=
  fun i => i.elim 1 (fun js => MvPolynomial.coeff (↑js.2) (p js.1))

private theorem mhb_tuple_ne_zero {ι ι' : Type*} (p : ι' → MvPolynomial ι K) : mhb_tuple p ≠ 0 := by
  intro h
  have := congrFun h none
  simp [mhb_tuple] at this

private theorem mhb_local_K {ι ι' : Type*} [Finite ι'] [Nonempty ι'] (p : ι' → MvPolynomial ι K)
    (v : FinitePlace K) :
    (⨆ j, max (⨆ s : (p j).support, v (MvPolynomial.coeff s (p j))) 1) = ⨆ i, v (mhb_tuple p i) := by
  rw [mhb_iSup_max_iSup_eq (fun j => ↥(p j).support) (fun j s => v (MvPolynomial.coeff (↑s) (p j)))
    (fun j s => apply_nonneg v _)]
  refine iSup_congr fun i => ?_
  cases i with
  | none => simp [mhb_tuple]
  | some js => rfl

private theorem mhb_local_L [Algebra K L] {ι ι' : Type*} [Finite ι'] [Nonempty ι'] (p : ι' → MvPolynomial ι K)
    (w : FinitePlace L) :
    (⨆ j, max (⨆ s : (MvPolynomial.map (algebraMap K L) (p j)).support,
        w (MvPolynomial.coeff s (MvPolynomial.map (algebraMap K L) (p j)))) 1)
      = ⨆ i, w (algebraMap K L (mhb_tuple p i)) := by
  classical
  have hf : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  rw [mhb_iSup_max_iSup_eq (fun j => ↥(MvPolynomial.map (algebraMap K L) (p j)).support)
    (fun j s => w (MvPolynomial.coeff (↑s) (MvPolynomial.map (algebraMap K L) (p j)))) (fun j s => apply_nonneg w _)]

  let e : (Σ j, ↥(p j).support) ≃ (Σ j, ↥(MvPolynomial.map (algebraMap K L) (p j)).support) :=
    Equiv.sigmaCongrRight fun j => Equiv.subtypeEquivRight fun s => by
      rw [MvPolynomial.support_map_of_injective _ hf]
  rw [← (Equiv.optionCongr e).surjective.iSup_comp]
  refine iSup_congr fun i => ?_
  cases i with
  | none => simp [mhb_tuple]
  | some js =>
    simp only [Equiv.optionCongr_apply, Option.map_some, Option.elim_some, mhb_tuple]
    rw [MvPolynomial.coeff_map]
    rfl

private theorem mhb_nf {M : Type*} [Field M] [NumberField M] {ι ι' : Type*} (q : ι' → MvPolynomial ι M) :
    mulHeightBound q = (∏ v : InfinitePlace M, (⨆ j, (AddMonoidAlgebra.coeff (q j)).sum fun _ c => v c) ^ v.mult) *
      ∏ᶠ v : FinitePlace M, ⨆ j, max (⨆ s : (q j).support, v (MvPolynomial.coeff s (q j))) 1 := by
  rw [mulHeightBound_eq, prod_archAbsVal_eq]
  rfl

open scoped Classical in

private theorem mhb_arch [Algebra K L] {ι ι' : Type*} (p : ι' → MvPolynomial ι K) :
    (∏ w : InfinitePlace L, (⨆ j, (AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap K L) (p j))).sum fun _ c => w c) ^ w.mult)
      = (∏ v : InfinitePlace K, (⨆ j, (AddMonoidAlgebra.coeff (p j)).sum fun _ c => v c) ^ v.mult) ^ Module.finrank K L := by
  have hf : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  rw [← Finset.prod_fiberwise Finset.univ
    (fun w : InfinitePlace L => w.comap (algebraMap K L))
    (fun w => (⨆ j, (AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap K L) (p j))).sum fun _ c => w c) ^ w.mult), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hfib : ∀ w ∈ Finset.univ.filter
      (fun w : InfinitePlace L => w.comap (algebraMap K L) = v),
      (⨆ j, (AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap K L) (p j))).sum fun _ c => w c) ^ w.mult
        = (⨆ j, (AddMonoidAlgebra.coeff (p j)).sum fun _ c => v c) ^ w.mult := by
    intro w hw
    have hcom : w.comap (algebraMap K L) = v := (Finset.mem_filter.mp hw).2
    have hsup : (⨆ j, (AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap K L) (p j))).sum fun _ c => w c)
        = ⨆ j, (AddMonoidAlgebra.coeff (p j)).sum fun _ c => v c := by
      refine iSup_congr fun j => ?_
      rw [MvPolynomial.sum_def, MvPolynomial.sum_def, MvPolynomial.support_map_of_injective _ hf]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [MvPolynomial.coeff_map, ← hcom, NumberField.InfinitePlace.comap_apply]
    rw [hsup]
  rw [Finset.prod_congr rfl hfib, Finset.prod_pow_eq_pow_sum, mwabs_sum_mult_comap v, pow_mul]

private theorem mhb_arch_nonneg {M : Type*} [Field M] [NumberField M] {ι ι' : Type*} (q : ι' → MvPolynomial ι M) :
    0 ≤ ∏ v : InfinitePlace M, (⨆ j, (AddMonoidAlgebra.coeff (q j)).sum fun _ c => v c) ^ v.mult :=
  Finset.prod_nonneg fun v _ => pow_nonneg
    (Real.iSup_nonneg fun j => by
      rw [MvPolynomial.sum_def]
      exact Finset.sum_nonneg fun s _ => apply_nonneg v _) _

private theorem mhb_fin_nonneg {M : Type*} [Field M] [NumberField M] {ι ι' : Type*} (q : ι' → MvPolynomial ι M) :
    0 ≤ ∏ᶠ v : FinitePlace M, ⨆ j, max (⨆ s : (q j).support, v (MvPolynomial.coeff s (q j))) 1 :=
  finprod_nonneg fun v => Real.iSup_nonneg fun j => le_trans zero_le_one (le_max_right _ _)

end scale

open scoped Classical in
theorem solution {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {ι ι' : Type*} [Finite ι] [Finite ι'] (p : ι' → MvPolynomial ι K) :
    Height.mulHeightBound (fun j => MvPolynomial.map (algebraMap K L) (p j))
      ≤ Height.mulHeightBound p ^ Module.finrank K L := by
  rw [mhb_nf, mhb_nf, mul_pow, mhb_arch p]
  rcases isEmpty_or_nonempty ι' with hι | hι
  ·
    have hA : (∏ v : InfinitePlace K, (⨆ j, (AddMonoidAlgebra.coeff (p j)).sum fun _ c => v c) ^ v.mult) = 0 := by
      obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
      apply Finset.prod_eq_zero (Finset.mem_univ v₀)
      rw [Real.iSup_of_isEmpty, zero_pow (NumberField.InfinitePlace.mult_pos).ne']
    haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)
    haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
    have hn : 0 < Module.finrank K L := Module.finrank_pos
    rw [hA, zero_pow hn.ne', zero_mul, zero_mul]
  · have hfin : (∏ᶠ w : FinitePlace L, ⨆ j, max (⨆ s : (MvPolynomial.map (algebraMap K L) (p j)).support,
        w (MvPolynomial.coeff s (MvPolynomial.map (algebraMap K L) (p j)))) 1)
        = (∏ᶠ v : FinitePlace K, ⨆ j, max (⨆ s : (p j).support, v (MvPolynomial.coeff s (p j))) 1)
          ^ Module.finrank K L := by
      rw [finprod_congr (mhb_local_L p), finprod_congr (mhb_local_K p)]
      exact mhb_finprod_tuple (mhb_tuple_ne_zero p)
    rw [hfin]

end S_Height_mulHeightBound_map_le
end P2MW
export P2MW.S_Height_mulHeightBound_map_le (solution)
