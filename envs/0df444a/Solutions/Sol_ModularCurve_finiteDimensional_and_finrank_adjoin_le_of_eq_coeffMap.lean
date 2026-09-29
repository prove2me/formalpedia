-- Prove2me | solution 1 for ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/dc78e285-f6a2-511c-b921-94f50248da88

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve IntermediateField Polynomial HahnSeries
open scoped MatrixGroups

namespace QExpDegTransfer

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem coeff_smul' {L : Type*} [Field L] (r : L) (x : LaurentSeries L) (n : ℤ) :
    (r • x).coeff n = r * x.coeff n := by
  rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) : coeffMap φ (intSeriesC K₀ p) = intSeriesC K p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map φ),
    ← PowerSeries.map_comp, RingHom.ext_int (φ.comp (Int.castRingHom K₀)) (Int.castRingHom K)]

theorem coeffMap_injective : Function.Injective (coeffMap φ) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries K => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact φ.injective this

theorem coeffMap_mem {x : LaurentSeries K₀} (hx : x ∈ qExpFunctionFieldC K₀ Γ) :
    coeffMap φ x ∈ qExpFunctionFieldC K Γ := by

  let T : Subfield (LaurentSeries K₀) := (qExpFunctionFieldC K Γ).toSubfield.comap (coeffMap φ)
  have hgen : intFormRatiosC K₀ Γ ⊆ (T : Set (LaurentSeries K₀)) := by
    rintro y ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    change coeffMap φ (intSeriesC K₀ pf / intSeriesC K₀ pg) ∈ qExpFunctionFieldC K Γ
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
    refine div_mem_qExpFunctionFieldC f g hf hg ?_
    rw [← coeffMap_intSeriesC φ]
    exact fun h => hg0 (coeffMap_injective φ (h.trans (map_zero _).symm))
  have hconst : Set.range (algebraMap K₀ (LaurentSeries K₀)) ⊆ (T : Set (LaurentSeries K₀)) := by
    rintro y ⟨c, rfl⟩
    change coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c) ∈ qExpFunctionFieldC K Γ
    rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (qExpFunctionFieldC K Γ).algebraMap_mem _
  have hle : (qExpFunctionFieldC K₀ Γ).toSubfield ≤ T := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield]
    exact Subfield.closure_le.mpr (Set.union_subset hconst hgen)
  exact hle hx

def iota : qExpFunctionFieldC K₀ Γ →+* qExpFunctionFieldC K Γ where
  toFun y := ⟨coeffMap φ y, coeffMap_mem φ Γ y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_iota (y : qExpFunctionFieldC K₀ Γ) :
    ((iota φ Γ y : qExpFunctionFieldC K Γ) : LaurentSeries K) = coeffMap φ y := rfl

theorem linearIndependent_coeffMap {ι : Type*} {v : ι → LaurentSeries K₀} (hv : LinearIndependent K₀ v) :
    LinearIndependent K (fun i => coeffMap φ (v i)) := by
  classical
  letI : Algebra K₀ K := φ.toAlgebra
  have hφ : ∀ c : K₀, algebraMap K₀ K c = φ c := fun _ => rfl
  rw [linearIndependent_iff']
  intro s c hsum i hi
  let W : Submodule K₀ K := Submodule.span K₀ (Set.range fun j : s => c j)
  haveI : Module.Finite K₀ W := Module.Finite.span_of_finite K₀ (Set.finite_range _)
  let b := Module.finBasis K₀ W
  have hcW : ∀ j : s, c j ∈ W := fun j => Submodule.subset_span ⟨j, rfl⟩
  let a : s → Fin (Module.finrank K₀ W) → K₀ := fun j l => b.repr ⟨c j, hcW j⟩ l
  have hca : ∀ j : s, c j = ∑ l, a j l • (b l : K) := by
    intro j
    have h1 := b.sum_repr ⟨c j, hcW j⟩
    have h2 := congrArg (Submodule.subtype W) h1
    rw [map_sum] at h2
    simp only [Submodule.subtype_apply, Submodule.coe_smul] at h2
    exact h2.symm
  have hcoeff : ∀ n : ℤ, ∑ j ∈ s, c j * φ ((v j).coeff n) = 0 := by
    intro n
    have := congrArg (fun x : LaurentSeries K => x.coeff n) hsum
    simpa [HahnSeries.coeff_sum, coeff_smul', coeffMap_coeff] using this
  have hbi : LinearIndependent K₀ (fun l' => (b l' : K)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hv' : LinearIndependent K₀ (fun j : s => v j) := hv.comp _ Subtype.val_injective
  have hrel : ∀ l, ∑ j : s, a j l • v j = 0 := by
    intro l
    ext n
    have h1 : ∑ l', (∑ j : s, a j l' * (v j).coeff n) • (b l' : K) = 0 := by
      have h0 := hcoeff n
      rw [← Finset.sum_coe_sort] at h0
      simp_rw [hca, Finset.sum_mul] at h0
      rw [Finset.sum_comm] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, hφ]; ring
    have := Fintype.linearIndependent_iff.mp hbi (fun l' => ∑ j : s, a j l' * (v j).coeff n) h1 l
    rw [HahnSeries.coeff_sum]
    simpa [coeff_smul'] using this
  have ha : ∀ (j : s) l, a j l = 0 := fun j l =>
    Fintype.linearIndependent_iff.mp hv' (fun j => a j l) (hrel l) j
  rw [show c i = c (⟨i, hi⟩ : s) from rfl, hca]
  simp [ha]

section Transfer

variable {φ Γ}
variable (x₀ : qExpFunctionFieldC K₀ Γ) (x : qExpFunctionFieldC K Γ)
  (hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀))
  (hx : (x : LaurentSeries K) = coeffMap φ (x₀ : LaurentSeries K₀))

local notation "E₀" => (qExpFunctionFieldC K₀ Γ)
local notation "E" => (qExpFunctionFieldC K Γ)

include hx₀ in

theorem transcendental_x₀ : Transcendental K₀ x₀ := by
  have hinj : Function.Injective (algebraMap E₀ (LaurentSeries K₀)) := Subtype.val_injective
  exact (transcendental_algebraMap_iff hinj).mp hx₀

include hx₀ in

theorem linearIndependent_pow_smul {ι : Type*} [Fintype ι] (v : ι → E₀)
    (hv : LinearIndependent (IntermediateField.adjoin K₀ ({x₀} : Set E₀)) v) (N : ℕ) :
    LinearIndependent K₀ (fun p : ι × Fin N => (x₀ : E₀) ^ (p.2 : ℕ) * v p.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha

  let A : ι → IntermediateField.adjoin K₀ ({x₀} : Set E₀) := fun i =>
    ⟨∑ m : Fin N, a (i, m) • (x₀ : E₀) ^ (m : ℕ), by
      refine sum_mem fun m _ => IntermediateField.smul_mem _ ?_
      exact pow_mem (IntermediateField.mem_adjoin_simple_self K₀ x₀) _⟩
  have hsum : ∑ i, A i • v i = 0 := by
    have : ∑ i, A i • v i = ∑ p : ι × Fin N, a p • ((x₀ : E₀) ^ (p.2 : ℕ) * v p.1) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      change (∑ m : Fin N, a (i, m) • (x₀ : E₀) ^ (m : ℕ)) * v i = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_mul_assoc]
    rw [this]; exact ha
  have hA : ∀ i, A i = 0 := Fintype.linearIndependent_iff.mp hv A hsum

  intro p
  obtain ⟨i, m⟩ := p

  have hAi : ∑ m : Fin N, a (i, m) • ((x₀ : E₀) : LaurentSeries K₀) ^ (m : ℕ) = 0 := by
    have h1 : ((A i : E₀) : LaurentSeries K₀) = 0 := by rw [hA i]; rfl
    have h2 : ((A i : E₀) : LaurentSeries K₀)
        = ∑ m : Fin N, a (i, m) • ((x₀ : E₀) : LaurentSeries K₀) ^ (m : ℕ) := by
      change ((∑ m : Fin N, a (i, m) • (x₀ : E₀) ^ (m : ℕ) : E₀) : LaurentSeries K₀) = _
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [IntermediateField.coe_smul, SubmonoidClass.coe_pow]
    rw [← h2]; exact h1
  let P : K₀[X] := ∑ m : Fin N, Polynomial.monomial (m : ℕ) (a (i, m))
  have hP : Polynomial.aeval ((x₀ : E₀) : LaurentSeries K₀) P = 0 := by
    rw [map_sum, ← hAi]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.aeval_monomial, Algebra.smul_def]
  have hP0 : P = 0 := by
    by_contra hne
    exact hx₀ ⟨P, hne, hP⟩
  have := congrArg (fun Q : K₀[X] => Q.coeff (m : ℕ)) hP0
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single m] at this
  · simpa using this
  · intro m' _ hm'
    rw [if_neg]
    exact fun h => hm' (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ m) h

include hx₀ hx in
set_option maxHeartbeats 1600000 in

theorem linearIndependent_iota {ι : Type*} [Fintype ι] (v : ι → E₀)
    (hv : LinearIndependent (IntermediateField.adjoin K₀ ({x₀} : Set E₀)) v) :
    LinearIndependent (IntermediateField.adjoin K ({x} : Set E)) (fun i => iota φ Γ (v i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne

  have hrep : ∀ i, ∃ r s : K[X], (c i : E) = Polynomial.aeval (x : E) r / Polynomial.aeval (x : E) s := by
    intro i
    exact (IntermediateField.mem_adjoin_simple_iff (F := K) (α := x) (c i : E)).mp (c i).2
  choose r s hrs using hrep

  let s' : ι → K[X] := fun i => if Polynomial.aeval (x : E) (s i) = 0 then 1 else s i
  have hs' : ∀ i, Polynomial.aeval (x : E) (s' i) ≠ 0 := by
    intro i
    simp only [s']
    split_ifs with h
    · rw [map_one]; exact one_ne_zero
    · exact h
  let r' : ι → K[X] := fun i => if Polynomial.aeval (x : E) (s i) = 0 then 0 else r i
  have hrs' : ∀ i, (c i : E) * Polynomial.aeval (x : E) (s' i) = Polynomial.aeval (x : E) (r' i) := by
    intro i
    simp only [s', r']
    split_ifs with h
    · rw [hrs i, h, div_zero, zero_mul, map_zero]
    · rw [hrs i, div_mul_cancel₀ _ h]

  let D : K[X] := ∏ i, s' i
  have hD : Polynomial.aeval (x : E) D ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hs' i
  let P : ι → K[X] := fun i => r' i * ∏ j ∈ Finset.univ.erase i, s' j
  have hPc : ∀ i, Polynomial.aeval (x : E) (P i) = (c i : E) * Polynomial.aeval (x : E) D := by
    intro i
    simp only [P, D]
    rw [map_mul, ← hrs', mul_assoc, ← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

  have hrel : ∑ i, Polynomial.aeval (x : E) (P i) • (iota φ Γ (v i) : E) = 0 := by
    have : ∑ i, Polynomial.aeval (x : E) (P i) • (iota φ Γ (v i) : E)
        = Polynomial.aeval (x : E) D * ∑ i, (c i : E) • (iota φ Γ (v i) : E) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hPc, smul_eq_mul, smul_eq_mul]; ring
    rw [this]
    have h0 : ∑ i, (c i : E) • (iota φ Γ (v i) : E) = 0 := by
      have := hc
      simpa only [IntermediateField.smul_def] using this
    rw [h0, mul_zero]
  have hPi₀ : P i₀ ≠ 0 := by
    intro h
    have := hPc i₀
    rw [h, map_zero] at this
    exact mul_ne_zero (fun h0 => hi₀ (ZeroMemClass.coe_eq_zero.mp h0)) hD this.symm

  let N : ℕ := (Finset.univ.sup fun i => (P i).natDegree) + 1
  have hdeg : ∀ i, (P i).natDegree < N := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (P i).natDegree) (Finset.mem_univ i))

  have hind₀ := linearIndependent_pow_smul x₀ hx₀ v hv N
  have hind₀' : LinearIndependent K₀
      (fun p : ι × Fin N => (((x₀ : E₀) ^ (p.2 : ℕ) * v p.1 : E₀) : LaurentSeries K₀)) :=
    hind₀.map' (IntermediateField.val E₀).toLinearMap
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hindK := linearIndependent_coeffMap φ hind₀'

  have hexp : ∑ p : ι × Fin N, (P p.1).coeff (p.2 : ℕ) •
      coeffMap φ (((x₀ : E₀) ^ ((p.2 : ℕ)) * v p.1 : E₀) : LaurentSeries K₀) = 0 := by
    have e1 : ∀ i, Polynomial.aeval (x : E) (P i) = ∑ m : Fin N, (P i).coeff (m : ℕ) • (x : E) ^ (m : ℕ) := by
      intro i
      rw [Polynomial.aeval_eq_sum_range' (hdeg i), Finset.sum_range]
    have := congrArg (fun z : E => (z : LaurentSeries K)) hrel
    simp only [IntermediateField.coe_sum, ZeroMemClass.coe_zero] at this
    rw [← this, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e1, Finset.sum_smul, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ← hx, smul_eq_mul,
      MulMemClass.coe_mul, IntermediateField.coe_smul, SubmonoidClass.coe_pow, coe_iota, smul_mul_assoc]
  have hzero := Fintype.linearIndependent_iff.mp hindK (fun p => (P p.1).coeff (p.2 : ℕ)) hexp
  apply hPi₀
  ext m
  rw [Polynomial.coeff_zero]
  by_cases hm : m < N
  · exact hzero (i₀, ⟨m, hm⟩)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i₀) (not_lt.mp hm))

end Transfer

end QExpDegTransfer
p2m_reactivate "P2MW.S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap.QExpDegTransfer"

open QExpDegTransfer in

theorem solution
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))
    (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀))
    (hx : (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀))
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
      (ModularCurve.qExpFunctionFieldC K Γ)] :
    FiniteDimensional (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ) ∧
      Module.finrank (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
          (ModularCurve.qExpFunctionFieldC K₀ Γ) ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) := by
  classical
  set n : ℕ := Module.finrank (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
    (qExpFunctionFieldC K Γ) with hn

  have hbound : ∀ s : Finset (qExpFunctionFieldC K₀ Γ),
      LinearIndependent (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
        (fun i : s => (i : qExpFunctionFieldC K₀ Γ)) → s.card ≤ n := by
    intro s hs
    have h := linearIndependent_iota x₀ x hx₀ hx (fun i : s => (i : qExpFunctionFieldC K₀ Γ)) hs
    have := h.fintype_card_le_finrank
    rwa [Fintype.card_coe] at this
  have hrank : Module.rank (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
      (qExpFunctionFieldC K₀ Γ) ≤ n := rank_le hbound
  have hfin : FiniteDimensional (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
      (qExpFunctionFieldC K₀ Γ) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := n)))
  exact ⟨hfin, Module.finrank_le_of_rank_le hrank⟩

end
end S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap (solution)
