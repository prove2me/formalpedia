-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.cech2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:35.669745+00:00
-- url     : https://prove2.me/submissions/35174310-a4e1-48a3-94d1-7c651efeceeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_IsSec_extend
import Theorems.Thm_GlobalTheory_CatCoh_Desc_IsSec_kill
import Theorems.Thm_GlobalTheory_CatCoh_Desc_exists_partition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Filter
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
universe v u w
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F} (H : HasLoc F) {T : C} {ι : Type} [Fintype ι] {b : ι → F.obj T}
  (hb : Ideal.span (Set.range b) = ⊤)
include H hb
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution (c : ι → ι → ι → ∀ S, (T ⟶ S) → F.obj S)
    (hs : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) ∧
      IsUnit (mp F u (b k))) (c i j k))
    (hc : ∀ l i j k S u, IsUnit (mp F u (b l)) → IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      IsUnit (mp F u (b k)) → c i j k S u - c l j k S u + c l i k S u - c l i j S u = 0) :
    ∃ e : ι → ι → ∀ S, (T ⟶ S) → F.obj S,
      (∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (e i j)) ∧
      ∀ i j k S u, IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) → IsUnit (mp F u (b k)) →
        c i j k S u = e j k S u - e i k S u + e i j S u := by
  obtain ⟨N, hN⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    IsSec.extend H (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j)
      (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (b l)
      (s := c l i j) fun S S' u ψ h ↦ hs l i j S S' u ψ ⟨⟨h.2, h.1.1⟩, h.1.2⟩).exists
  choose h hh hh' using hN
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    eventually_all.2 fun k ↦
    IsSec.kill H (P := fun S u ↦ (IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) ∧
        IsUnit (mp F u (b k))) (b := b i * b j * b k)
      (fun _ _ ↦ by rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff]) (b l)
      (s := fun S u ↦ mp F u (b l) ^ N * c i j k S u - (h l j k S u - h l i k S u + h l i j S u))
      (fun S S' u ψ hu ↦ by
        simp only [hs i j k S S' u ψ hu, hh l i j S S' u ψ hu.1, hh l j k S S' u ψ ⟨hu.1.2, hu.2⟩,
          hh l i k S S' u ψ ⟨hu.1.1, hu.2⟩, mp_comp, map_sub, map_add, map_mul, map_pow])
      fun S u hu hl ↦ by
        rw [hh' l i j S u hu.1 hl, hh' l j k S u ⟨hu.1.2, hu.2⟩ hl, hh' l i k S u ⟨hu.1.1, hu.2⟩ hl]
        linear_combination mp F u (b l) ^ N * hc l i j k S u hl hu.1.1 hu.1.2 hu.2).exists
  obtain ⟨r, hr⟩ := exists_partition hb (M + N)
  refine ⟨fun i j S u ↦ ∑ l, mp F u (r l * b l ^ M) * h l i j S u, fun i j S S' u ψ hu ↦ ?_,
    fun i j k S u hi hj hk ↦ ?_⟩
  · simp only [map_sum, map_mul, mp_comp, fun l ↦ hh l i j S S' u ψ hu]
  · rw [← one_mul (c i j k S u), ← hr S u, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, map_pow]
    linear_combination mp F u (r l) * hM l i j k S u ⟨⟨hi, hj⟩, hk⟩
end GlobalTheory.CatCoh.Desc
