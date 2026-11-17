-- Prove2me | solution 1 for N25.cusp_coefficient_embedding
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:29.839208+00:00
-- url     : https://prove2.me/submissions/419c34c6-4f3a-4302-b32e-04958299c1d8

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

namespace N25

private theorem coefficient_generation
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (κ : xHFunctionFieldBar 25 H25 →+* laurentBaseChange ℂ (xHFunctionField 25 H25))
    (hκ : ∀ x, (κ x : LaurentSeries ℂ) = coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ))) :
    IntermediateField.adjoin ℂ (Set.range κ) = ⊤ := by
  let K := AlgebraicClosure ℚ
  let F₀ := xHFunctionField 25 H25
  let F := xHFunctionFieldBar 25 H25
  let Fℂ := laurentBaseChange ℂ F₀
  have hrat : ι.comp (algebraMap ℚ K) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hratseries (z : LaurentSeries ℚ) : coeffMap ι (coeffEmb K z) = coeffEmb ℂ z := by
    rw [coeffEmb,coeffMap_coeffMap,hrat]
    rfl
  let E := IntermediateField.adjoin ℂ (Set.range κ)
  have hall (z : LaurentSeries ℂ) (hz : z∈Fℂ) : (⟨z,hz⟩ : Fℂ)∈E := by
    have hz₀ : z∈IntermediateField.adjoin ℂ
        (coeffEmb ℂ '' (F₀ : Set (LaurentSeries ℚ))) := hz
    revert hz
    induction hz₀ using IntermediateField.adjoin_induction with
    | mem z hz =>
      obtain ⟨q,hq,rfl⟩ := hz
      intro hz'
      let qK : F := ⟨coeffEmb K q,coeffEmb_mem_laurentBaseChange K hq⟩
      have he : κ qK = (⟨coeffEmb ℂ q,hz'⟩ : Fℂ) := Subtype.ext ((hκ qK).trans (hratseries q))
      rw [←he]
      exact IntermediateField.subset_adjoin ℂ _ ⟨qK,rfl⟩
    | algebraMap c =>
      intro hz
      exact E.algebraMap_mem c
    | add x y hx hy ihx ihy =>
      intro hz
      change (⟨x,hx⟩ : Fℂ) + (⟨y,hy⟩ : Fℂ)∈E
      exact E.add_mem (ihx hx) (ihy hy)
    | inv x hx ih =>
      intro hz
      change (⟨x,hx⟩ : Fℂ)⁻¹∈E
      exact E.inv_mem (ih hx)
    | mul x y hx hy ihx ihy =>
      intro hz
      change (⟨x,hx⟩ : Fℂ) * (⟨y,hy⟩ : Fℂ)∈E
      exact E.mul_mem (ihx hx) (ihy hy)
  apply top_unique
  intro x _
  exact hall x x.2

/-- The natural coefficient embedding generates the complex field after extending constants. -/
theorem _root_.solution
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 N25.H25
    let F := xHFunctionFieldBar 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    ∃ κ : F →+* Fℂ,
      (∀ x : F, (κ x : LaurentSeries ℂ) = coeffMap ι (x : LaurentSeries K)) ∧
      (∀ a : K, κ (algebraMap K F a) = algebraMap ℂ Fℂ (ι a)) ∧
      (letI : Algebra K ℂ := ι.toAlgebra
       letI : Algebra K Fℂ := ((algebraMap ℂ Fℂ).comp ι).toAlgebra
       letI : Algebra F Fℂ := κ.toAlgebra
       IsScalarTower K ℂ Fℂ ∧ IsScalarTower K F Fℂ ∧
         IntermediateField.adjoin ℂ (Set.range κ) = ⊤) := by
  let K := AlgebraicClosure ℚ
  let F₀ := xHFunctionField 25 H25
  let F := xHFunctionFieldBar 25 H25
  let Fℂ := laurentBaseChange ℂ F₀
  have hrat : ι.comp (algebraMap ℚ K) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hconst (a : K) : coeffMap ι (algebraMap K (LaurentSeries K) a) =
      algebraMap ℂ (LaurentSeries ℂ) (ι a) := by
    rw [algebraMap_laurentSeries_eq_single,algebraMap_laurentSeries_eq_single,coeffMap_single]
  have hratseries (z : LaurentSeries ℚ) : coeffMap ι (coeffEmb K z) = coeffEmb ℂ z := by
    rw [coeffEmb,coeffMap_coeffMap,hrat]
    rfl
  have hmem (x : LaurentSeries K) (hx : x∈F) : coeffMap ι x∈Fℂ := by
    change x∈laurentBaseChange K F₀ at hx
    rw [mem_laurentBaseChange_iff] at hx
    induction hx using Subfield.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a,rfl⟩ | ⟨z,hz,rfl⟩
      · rw [hconst]
        exact Fℂ.algebraMap_mem _
      · rw [hratseries]
        exact coeffEmb_mem_laurentBaseChange ℂ hz
    | one => simpa using Fℂ.one_mem
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | neg x _ hx => simpa using neg_mem hx
    | inv x _ hx => simpa using inv_mem hx
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  let κ : F →+* Fℂ :=
    { toFun := fun x => ⟨coeffMap ι (x : LaurentSeries K),hmem x x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hκconst (a : K) : κ (algebraMap K F a) = algebraMap ℂ Fℂ (ι a) := by
    apply Subtype.ext
    exact hconst a
  refine ⟨κ,fun _ => rfl,hκconst,?_⟩
  letI : Algebra K ℂ := ι.toAlgebra
  letI : Algebra K Fℂ := ((algebraMap ℂ Fℂ).comp ι).toAlgebra
  letI : Algebra F Fℂ := κ.toAlgebra
  refine ⟨?_,?_,?_⟩
  · constructor
    intro a b c
    change algebraMap ℂ Fℂ (ι a*b)*c = algebraMap ℂ Fℂ (ι a)*(algebraMap ℂ Fℂ b*c)
    rw [map_mul]
    ring
  · constructor
    intro a b c
    change κ (algebraMap K F a*b)*c = algebraMap ℂ Fℂ (ι a)*(κ b*c)
    rw [map_mul,hκconst]
    ring
  · exact coefficient_generation ι κ (fun _ => rfl)

end N25
