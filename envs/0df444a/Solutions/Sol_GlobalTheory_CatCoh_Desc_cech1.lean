-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.cech1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:33.498163+00:00
-- url     : https://prove2.me/submissions/e5fae915-dd53-4989-9f22-f6db418122bb

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
theorem _root_.solution (c : ι → ι → ∀ S, (T ⟶ S) → F.obj S)
    (hs : ∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (c i j))
    (hc : ∀ i j k S u, IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) → IsUnit (mp F u (b k)) →
      c j k S u - c i k S u + c i j S u = 0) :
    ∃ e : ι → ∀ S, (T ⟶ S) → F.obj S, (∀ i, IsSec F (fun S u ↦ IsUnit (mp F u (b i))) (e i)) ∧
      ∀ i j S u, IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) → c i j S u = e j S u - e i S u := by
  obtain ⟨N, hN⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦
    IsSec.extend H (P := fun S u ↦ IsUnit (mp F u (b i))) (b := b i) (fun _ _ ↦ Iff.rfl) (b l)
      (s := c l i) fun S S' u ψ h ↦ hs l i S S' u ψ ⟨h.2, h.1⟩).exists
  choose h hh hh' using hN
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    IsSec.kill H (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j)
      (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (b l)
      (s := fun S u ↦ mp F u (b l) ^ N * c i j S u - (h l j S u - h l i S u))
      (fun S S' u ψ hu ↦ by
        simp only [hs i j S S' u ψ hu, hh l i S S' u ψ hu.1, hh l j S S' u ψ hu.2, mp_comp, map_sub,
          map_mul, map_pow])
      fun S u hu hl ↦ by
        rw [hh' l i S u hu.1 hl, hh' l j S u hu.2 hl]
        linear_combination mp F u (b l) ^ N * hc l i j S u hl hu.1 hu.2).exists
  obtain ⟨r, hr⟩ := exists_partition hb (M + N)
  refine ⟨fun i S u ↦ ∑ l, mp F u (r l * b l ^ M) * h l i S u, fun i S S' u ψ hu ↦ ?_,
    fun i j S u hi hj ↦ ?_⟩
  · simp only [map_sum, map_mul, mp_comp, fun l ↦ hh l i S S' u ψ hu]
  · rw [← one_mul (c i j S u), ← hr S u, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, map_pow]
    linear_combination mp F u (r l) * hM l i j S u ⟨hi, hj⟩
end GlobalTheory.CatCoh.Desc
