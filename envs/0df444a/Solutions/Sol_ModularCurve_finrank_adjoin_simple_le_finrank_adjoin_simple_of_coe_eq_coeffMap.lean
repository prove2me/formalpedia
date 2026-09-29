-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b1e70410-1539-56a2-b0f2-66e82bfbad07

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

import Theorems.Thm_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve Polynomial
open scoped IntermediateField

theorem solution
    {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (F₀ : IntermediateField k₀ (LaurentSeries k₀)) (F : IntermediateField k (LaurentSeries k))
    (ι : ↥F₀ →+* ↥F) (hι : ∀ x : ↥F₀, ((ι x : ↥F) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀))
    (t₀ : ↥F₀) (ht₀ : Transcendental k₀ t₀) [FiniteDimensional ↥k⟮ι t₀⟯ ↥F] :
    Module.finrank ↥k₀⟮t₀⟯ ↥F₀ ≤ Module.finrank ↥k⟮ι t₀⟯ ↥F := by
  classical
  set t : ↥F := ι t₀ with htdef
  by_cases hfin : FiniteDimensional ↥k₀⟮t₀⟯ ↥F₀
  swap
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _
  haveI := hfin
  haveI : Module.Free ↥k₀⟮t₀⟯ ↥F₀ := Module.Free.of_divisionRing _ _
  haveI : Module.Free ↥k⟮t⟯ ↥F := Module.Free.of_divisionRing _ _
  set n := Module.finrank ↥k₀⟮t₀⟯ ↥F₀ with hn
  let B := Module.finBasis ↥k₀⟮t₀⟯ ↥F₀
  suffices hli : LinearIndependent ↥k⟮t⟯ (fun i : Fin n => (ι (B i) : ↥F)) by
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  rw [Fintype.linearIndependent_iff]
  intro c hc

  have hrep : ∀ i, ∃ rs : k[X] × k[X], (aeval t rs.2 : ↥F) ≠ 0 ∧
      ((c i : ↥k⟮t⟯) : ↥F) = aeval t rs.1 / aeval t rs.2 := by
    intro i
    obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_simple_iff k ((c i : ↥k⟮t⟯) : ↥F)).mp (c i).2
    by_cases hs : (aeval t s : ↥F) = 0
    · refine ⟨(0, 1), by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [h, hs, div_zero, map_zero, map_one, zero_div]
    · exact ⟨(r, s), hs, h⟩
  choose rs hs hcrs using hrep

  set D : ↥F := ∏ j, (aeval t (rs j).2 : ↥F) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  set P : Fin n → k[X] := fun i => (rs i).1 * ∏ j ∈ Finset.univ.erase i, (rs j).2 with hP
  have hPt : ∀ i, (aeval t (P i) : ↥F) = ((c i : ↥k⟮t⟯) : ↥F) * D := by
    intro i
    have hDi : D = (aeval t (rs i).2 : ↥F) * ∏ j ∈ Finset.univ.erase i, (aeval t (rs j).2 : ↥F) := by
      rw [hD, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    rw [hP]
    simp only [map_mul, map_prod]
    rw [hcrs, hDi]
    field_simp
    rw [mul_div_assoc, div_self (hs i), mul_one]
  have hsmul : ∀ i, c i • (ι (B i) : ↥F) = ((c i : ↥k⟮t⟯) : ↥F) * (ι (B i) : ↥F) := fun i => by
    rw [IntermediateField.smul_def, smul_eq_mul]
  have hrel : ∑ i, (aeval t (P i) : ↥F) * (ι (B i) : ↥F) = 0 := by
    have h1 : (∑ i, c i • (ι (B i) : ↥F)) * D = 0 := by rw [hc, zero_mul]
    rw [Finset.sum_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hPt, hsmul]; ring

  set N : ℕ := Finset.univ.sup fun i => (P i).natDegree with hN
  have hPN : ∀ i, (P i).natDegree < N + 1 := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (P i).natDegree) (Finset.mem_univ i))

  let g : ↥k₀⟮t₀⟯ := IntermediateField.AdjoinSimple.gen k₀ t₀
  have hg : algebraMap ↥k₀⟮t₀⟯ ↥F₀ g = t₀ := IntermediateField.AdjoinSimple.algebraMap_gen k₀ t₀
  have hgtr : Transcendental k₀ g := by
    rw [← transcendental_algebraMap_iff (algebraMap ↥k₀⟮t₀⟯ ↥F₀).injective, hg]; exact ht₀
  have hpow : LinearIndependent k₀ (fun m : Fin (N + 1) => g ^ (m : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha m
    have hinj := transcendental_iff_injective.mp hgtr
    set Q : k₀[X] := ∑ m : Fin (N + 1), C (a m) * X ^ (m : ℕ) with hQ
    have hQ0 : aeval g Q = 0 := by
      rw [hQ, map_sum]
      simp only [map_mul, aeval_C, map_pow, aeval_X, ← Algebra.smul_def]
      exact ha
    have hQz : Q = 0 := hinj (by rw [hQ0, map_zero])
    have := congrArg (fun q : k₀[X] => q.coeff m) hQz
    simp only [hQ, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single m (fun b _ hb => if_neg (fun h => hb (Fin.ext h).symm)) (fun h => absurd (Finset.mem_univ m) h)] at this
    simpa using this

  obtain ⟨W, hW, hw⟩ : ∃ W : Fin (N + 1) × Fin n → ↥F₀,
      (∀ x, W x = t₀ ^ ((x.1 : Fin (N + 1)) : ℕ) * (B x.2 : ↥F₀)) ∧ LinearIndependent k₀ W := by
    refine ⟨_, ?_, linearIndependent_smul hpow B.linearIndependent⟩
    intro x
    simp only [Algebra.smul_def, map_pow, hg]

  have key : ∀ {m : ℕ} (v : Fin m → ↥F₀), LinearIndependent k₀ v →
      LinearIndependent k (fun j => (ι (v j) : ↥F)) := by
    intro m v hv
    have h1 := hv.map' (LinearMap.inl k₀ ↥F₀ ↥F₀) (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
    have h2 := ModularCurve.linearIndependent_map_prod_of_coe_eq_coeffMap σ F₀ F ι hι
      (v := fun j => (v j, (0 : ↥F₀))) h1
    simp only [map_zero] at h2
    exact LinearIndependent.of_comp (LinearMap.inl k ↥F ↥F) h2
  set e := (finProdFinEquiv (m := N + 1) (n := n)) with he
  have hwFin : LinearIndependent k₀ (W ∘ e.symm) := (linearIndependent_equiv e.symm).mpr hw
  have hkFin : LinearIndependent k ((fun x => (ι (W x) : ↥F)) ∘ e.symm) := key _ hwFin
  have hk'' : LinearIndependent k (fun x => (ι (W x) : ↥F)) := (linearIndependent_equiv e.symm).mp hkFin

  have hιw : ∀ x, (ι (W x) : ↥F) = t ^ ((x.1 : Fin (N + 1)) : ℕ) * (ι (B x.2) : ↥F) := by
    intro x
    rw [hW, map_mul, map_pow]
  have hcoef := Fintype.linearIndependent_iff.mp hk'' (fun x => (P x.2).coeff ((x.1 : Fin (N + 1)) : ℕ)) (by
    calc ∑ x : Fin (N + 1) × Fin n, ((P x.2).coeff ((x.1 : Fin (N + 1)) : ℕ)) • (ι (W x) : ↥F)
        = ∑ i : Fin n, ∑ m : Fin (N + 1), ((P i).coeff (m : ℕ)) • (t ^ (m : ℕ) * (ι (B i) : ↥F)) := by
          rw [Fintype.sum_prod_type_right]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
          rw [hιw]
      _ = ∑ i : Fin n, (aeval t (P i) : ↥F) * (ι (B i) : ↥F) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [aeval_eq_sum_range' (hPN i), Finset.sum_range (fun m => (P i).coeff m • t ^ m), Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [smul_mul_assoc]
      _ = 0 := hrel)
  intro i
  have hPi : P i = 0 := by
    ext m
    rw [coeff_zero]
    by_cases hm : m < N + 1
    · exact hcoef (⟨m, hm⟩, i)
    · exact coeff_eq_zero_of_natDegree_lt (by have := hPN i; omega)
  have hprod : (∏ j ∈ Finset.univ.erase i, (rs j).2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => fun h0 => hs j (by rw [h0, map_zero])
  have hr : (rs i).1 = 0 := by
    have h1 := hPi
    rw [hP] at h1
    simp only at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hprod
  apply Subtype.ext
  rw [hcrs, hr, map_zero, zero_div, ZeroMemClass.coe_zero]

end S_ModularCurve_finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap (solution)
