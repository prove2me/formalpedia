-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.glue_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:21.643934+00:00
-- url     : https://prove2.me/submissions/c92204ca-1262-4cf7-8c46-ba0d2de46408

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
theorem _root_.solution : Glue F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro s hs
  obtain ⟨N, hN⟩ := (eventually_all.2 fun l ↦ IsSec.extend H (P := fun _ _ ↦ True) (b := 1)
    (by simp) (b l) (s := s) fun S S' u ψ h ↦ hs S S' u ψ ⟨l, h.2⟩).exists
  choose h hh hh' using hN
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦
    IsSec.kill H (P := fun S u ↦ IsUnit (mp F u (b i))) (b := b i) (fun _ _ ↦ Iff.rfl) (b l)
      (s := fun S u ↦ mp F u (b l) ^ N * s S u - h l S u)
      (fun S S' u ψ hu ↦ by
        simp only [hs S S' u ψ ⟨i, hu⟩, hh l S S' u ψ trivial, mp_comp, map_sub, map_mul, map_pow])
      fun S u _ hl ↦ by rw [hh' l S u trivial hl, sub_self]).exists
  obtain ⟨r, hr⟩ := exists_partition hb (M + N)
  refine ⟨∑ l, r l * b l ^ M * h l T (𝟙 T), fun S u ⟨i, hi⟩ ↦ ?_⟩
  rw [← one_mul (s S u), ← hr S u, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, map_mul, map_pow, ← hh l _ _ _ u trivial, Category.id_comp]
  linear_combination -mp F u (r l) * hM l i S u hi
end GlobalTheory.CatCoh.Desc
