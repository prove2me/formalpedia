-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_rational_presentation_at_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:14:58.793093+00:00
-- url     : https://prove2.me/submissions/0df44b72-7717-4684-855b-d80665a41f4a

import Mathlib

open IntermediateField IntermediateField.algebraAdjoinAdjoin

theorem solution
    (k E : Type) [Field k] [Field E] [Algebra k E]
    [Algebra.EssFiniteType k E] (y : E) (hy : Transcendental k y) :
    ∃ (K : IntermediateField k E) (f : RatFunc K →ₐ[K] E),
      f RatFunc.X = y ∧
      (letI : Algebra (RatFunc K) E := f.toRingHom.toAlgebra
       FiniteDimensional (RatFunc K) E) := by
  have h1 : AlgebraicIndepOn k id ({y} : Set E) := by
    unfold AlgebraicIndepOn
    rw [algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set E))]
    exact hy
  obtain ⟨t, hyt, ht⟩ := exists_isTranscendenceBasis_superset h1
  have hyt' : y ∈ t := hyt rfl
  set S' : Set E := t \ {y} with hS'
  have hins : insert y S' = t := by
    rw [hS', Set.insert_diff_singleton, Set.insert_eq_of_mem hyt']
  have hind : AlgebraicIndepOn k id (insert y S') := by
    rw [hins]; exact ht.1
  have hyS : y ∉ S' := fun h => h.2 rfl
  obtain ⟨-, htr⟩ := (AlgebraicIndepOn.insert_iff hyS).mp hind
  have htr' : Transcendental (Algebra.adjoin k S') y := by
    have hid : (id '' S') = S' := Set.image_id S'
    rw [hid] at htr; exact htr
  set K : IntermediateField k E := IntermediateField.adjoin k S' with hK
  have hyK : Transcendental K y := htr'.extendScalars K
  let e := RatFunc.algEquivOfTranscendental y hyK
  let L : IntermediateField K E := K⟮y⟯
  let f : RatFunc K →ₐ[K] E := L.val.comp e.toAlgHom
  refine ⟨K, f, ?_, ?_⟩
  · simp [f, e]
  · letI : Algebra (RatFunc K) E := f.toRingHom.toAlgebra
    letI : Algebra (RatFunc K) L := e.toRingHom.toAlgebra
    haveI : IsScalarTower (RatFunc K) L E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : Module.Finite (RatFunc K) L :=
      Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) L) e.surjective
    haveI : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : Algebra.EssFiniteType L E := Algebra.EssFiniteType.of_comp k L E
    haveI : Algebra.IsAlgebraic L E := by
      have halg := ht.isAlgebraic_field
      constructor; intro x
      have hx := halg.isAlgebraic x
      have hset : Set.range ((↑) : t → E) = S' ∪ {y} := by
        rw [Subtype.range_coe, Set.union_singleton, hins]
      have hle : (IntermediateField.adjoin k (Set.range ((↑) : t → E))).toSubalgebra ≤
          (L.restrictScalars k).toSubalgebra := by
        rw [hset, ← adjoin_adjoin_left]
      exact IsAlgebraic.tower_top_of_subalgebra_le hle hx
    haveI : Module.Finite L E := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact Module.Finite.trans L E
