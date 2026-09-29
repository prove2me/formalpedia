-- Prove2me | solution 1 for ModularCurve.FullLevel.isAlgebraic_adjoin_j_of_mem_subfield_fieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ac518683-d963-58e6-84b5-877aae477187

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isAlgebraic_adjoin_j_of_mem_subfield_fieldBar

set_option autoImplicit false

namespace LevelFieldAlgSol

open Polynomial

theorem isAlgebraic_of_subset {K : Type*} [CommRing K]
    {ι₁ ι₂ : Type*} [SetLike ι₁ K] [SetLike ι₂ K] [SubringClass ι₁ K] [SubringClass ι₂ K]
    (R₁ : ι₁) (R₂ : ι₂) (h : ∀ y : K, y ∈ R₁ → y ∈ R₂)
    [Algebra R₁ K] [Algebra R₂ K]
    (h₁ : ∀ y : R₁, algebraMap R₁ K y = y) (h₂ : ∀ y : R₂, algebraMap R₂ K y = y)
    {x : K} (hx : IsAlgebraic R₁ x) : IsAlgebraic R₂ x := by
  let f : R₁ →+* R₂ :=
    { toFun := fun y => ⟨(y : K), h y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hf : Function.Injective f := by
    intro a b hab
    have : ((f a : R₂) : K) = (f b : K) := by rw [hab]
    exact Subtype.ext (by simpa [f] using this)
  have hcomp : (algebraMap R₂ K).comp f = (RingHom.id K).comp (algebraMap R₁ K) := by
    ext y
    simp [f, h₁, h₂]
  simpa using hx.ringHom_of_comp_eq f (RingHom.id K) hf hcomp

theorem isAlgebraic_adjoin_int_of_isAlgebraic_intermediateField_adjoin
    {k K : Type*} [Field k] [Field K] [CharZero K] [Algebra k K]
    (halg : ∀ c : k, IsAlgebraic ℤ c) (j x : K)
    (hx : IsAlgebraic ↥(IntermediateField.adjoin k ({j} : Set K)) x) :
    IsAlgebraic ↥(Algebra.adjoin ℤ ({j} : Set K)) x := by
  classical
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have hx₁ : IsAlgebraic ↥(Algebra.adjoin k ({j} : Set K)) x :=
    (IsFractionRing.isAlgebraic_iff (↥(Algebra.adjoin k ({j} : Set K)))
      (↥(IntermediateField.adjoin k ({j} : Set K))) K).mpr hx

  set s : Set K := Set.range (algebraMap k K) ∪ {j} with hs
  have hx₂ : IsAlgebraic ↥(Algebra.adjoin ℤ s) x := by
    refine isAlgebraic_of_subset (Algebra.adjoin k ({j} : Set K)) (Algebra.adjoin ℤ s) ?_
      (fun y => rfl) (fun y => rfl) hx₁
    intro y hy

    let T : Subalgebra k K :=
      { carrier := (Algebra.adjoin ℤ s : Set K)
        mul_mem' := fun ha hb => mul_mem ha hb
        one_mem' := one_mem _
        add_mem' := fun ha hb => add_mem ha hb
        zero_mem' := zero_mem _
        algebraMap_mem' := fun c => Algebra.subset_adjoin (Or.inl ⟨c, rfl⟩) }
    have hle : Algebra.adjoin k ({j} : Set K) ≤ T :=
      Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin (Or.inr hz))
    exact hle hy

  refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := ℤ) (s := s) (t := ({j} : Set K)) ?_ hx₂
  rintro y ⟨hy, hyj⟩
  rcases hy with ⟨c, rfl⟩ | hy
  · have hc : IsAlgebraic ℤ (algebraMap k K c) := (halg c).algebraMap
    obtain ⟨p, hp0, hpc⟩ := hc
    have hinj : Function.Injective (algebraMap ℤ ↥(Algebra.adjoin ℤ ({j} : Set K))) := by
      intro a b hab
      have hab' := congrArg (fun z : ↥(Algebra.adjoin ℤ ({j} : Set K)) => (z : K)) hab
      simpa using hab'
    refine ⟨p.map (algebraMap ℤ _), ?_, ?_⟩
    · rwa [Polynomial.map_ne_zero_iff hinj]
    · rw [Polynomial.aeval_map_algebraMap]
      exact hpc
  · exact absurd hy hyj

end LevelFieldAlgSol

open ModularCurve ModularCurve.FullLevel

namespace LevelFieldAlgSol

theorem main (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (jK : ↥(fieldBar q M')) (hjK : ((jK : LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) jq)
    (A₀ : Type) [CommRing A₀] (F₀ : Subfield ↥(fieldBar q M')) (hjF₀ : jK ∈ F₀) [Algebra A₀ ↥F₀] (x : ↥F₀) :
    IsAlgebraic ↥(Algebra.adjoin A₀ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) x := by
  classical

  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (q ^ 2 * M') (levelH q M'))
  have hK : fieldBar q M' = laurentBaseChange (AlgebraicClosure ℚ)
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) := rfl
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jK} : Set ↥(fieldBar q M')))
      ↥(fieldBar q M') :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (ModularCurve.translation_mem_GammaH _ _)
      (AlgebraicClosure ℚ) (fieldBar q M') hK jK hjK
  have hxK : IsAlgebraic ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jK} : Set ↥(fieldBar q M')))
      (x : ↥(fieldBar q M')) :=
    Algebra.IsAlgebraic.isAlgebraic _

  have hxZ : IsAlgebraic ↥(Algebra.adjoin ℤ ({jK} : Set ↥(fieldBar q M'))) (x : ↥(fieldBar q M')) :=
    LevelFieldAlgSol.isAlgebraic_adjoin_int_of_isAlgebraic_intermediateField_adjoin
      (fun c => (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
        ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c)) jK _ hxK

  let g : ↥F₀ →ₐ[ℤ] ↥(fieldBar q M') := (F₀.subtype).toIntAlgHom
  have hg : Function.Injective g := Subtype.val_injective
  have hmap : (Algebra.adjoin ℤ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀)).map g =
      Algebra.adjoin ℤ ({jK} : Set ↥(fieldBar q M')) := by
    rw [AlgHom.map_adjoin]
    congr 1
    rw [Set.image_singleton]
    rfl
  let f : ↥(Algebra.adjoin ℤ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) →+*
      ↥(Algebra.adjoin ℤ ({jK} : Set ↥(fieldBar q M'))) :=
    { toFun := fun y => ⟨g y, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨y, y.2, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [← hmap] at hz
    obtain ⟨y, hy, rfl⟩ := Subalgebra.mem_map.mp hz
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcomp : (algebraMap ↥(Algebra.adjoin ℤ ({jK} : Set ↥(fieldBar q M'))) ↥(fieldBar q M')).comp f =
      (g : ↥F₀ →+* ↥(fieldBar q M')).comp
        (algebraMap ↥(Algebra.adjoin ℤ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ↥F₀) := by
    ext y
    rfl
  have hx0 : IsAlgebraic ↥(Algebra.adjoin ℤ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) x :=
    IsAlgebraic.of_ringHom_of_comp_eq f (g : ↥F₀ →+* ↥(fieldBar q M')) (a := x) hxZ hf hg hcomp

  refine LevelFieldAlgSol.isAlgebraic_of_subset (Algebra.adjoin ℤ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀))
    (Algebra.adjoin A₀ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ?_ (fun y => rfl) (fun y => rfl) hx0
  intro y hy

  let T : Subalgebra ℤ ↥F₀ :=
    { carrier := (Algebra.adjoin A₀ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀) : Set ↥F₀)
      mul_mem' := fun ha hb => mul_mem ha hb
      one_mem' := one_mem _
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      algebraMap_mem' := fun n => by
        simp }
  have hleT : Algebra.adjoin ℤ ({(⟨jK, hjF₀⟩ : ↥F₀)} : Set ↥F₀) ≤ T :=
    Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz)
  exact hleT hy

end LevelFieldAlgSol

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (A₀ : Type) [CommRing A₀]
    (F₀ : Subfield ↥(fieldBar q M'))
    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)
    [Algebra A₀ ↥F₀] :
    ∀ x : ↥F₀, IsAlgebraic ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) x :=
  fun x => LevelFieldAlgSol.main q M' _ rfl A₀ F₀ hjF₀ x

end S_ModularCurve_FullLevel_isAlgebraic_adjoin_j_of_mem_subfield_fieldBar
end P2MW
export P2MW.S_ModularCurve_FullLevel_isAlgebraic_adjoin_j_of_mem_subfield_fieldBar (solution)
