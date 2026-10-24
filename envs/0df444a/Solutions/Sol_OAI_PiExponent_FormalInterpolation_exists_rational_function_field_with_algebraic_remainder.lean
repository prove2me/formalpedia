-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_rational_function_field_with_algebraic_remainder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:45:26.342084+00:00
-- url     : https://prove2.me/submissions/ba2b9353-29c1-4269-8210-ecefad32ec86

import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.EssentialFiniteness

theorem solution
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (y : E) (hy : Transcendental k y) :
    ∃ (K : IntermediateField k E) (f : RatFunc K →ₐ[K] E),
      f RatFunc.X = y ∧ Function.Injective f ∧
      (letI : Algebra (RatFunc K) E := f.toRingHom.toAlgebra
       Algebra.IsAlgebraic (RatFunc K) E) := by
  classical
  have hind : AlgebraicIndepOn k id ({y} : Set E) := by
    show AlgebraicIndependent k (fun i : ({y} : Set E) => (i : E))
    rw [algebraicIndependent_singleton_iff ⟨y, rfl⟩]; exact hy
  obtain ⟨t, hyt, ht⟩ := exists_isTranscendenceBasis_superset hind
  have hyt' : y ∈ t := hyt rfl
  set s : Set E := t \ {y} with hs
  have h1 : Transcendental (Algebra.adjoin k s) y := by
    have := ht.1.transcendental_adjoin (s := {z : t | (z : E) ≠ y}) (i := ⟨y, hyt'⟩) (by simp)
    have hs' : ((↑) : t → E) '' {z : t | (z : E) ≠ y} = s := by
      ext z; simp [hs, and_comm]
    rw [hs'] at this
    exact this
  set K := IntermediateField.adjoin k s with hK
  have h2 : Transcendental K y := by
    open IntermediateField.algebraAdjoinAdjoin in
    exact h1.extendScalars K
  have hinj : Function.Injective (Polynomial.aeval (R := K) y) := (transcendental_iff_injective).1 h2
  let f : RatFunc K →ₐ[K] E := RatFunc.liftAlgHom (Polynomial.aeval (R := K) y)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have hfX : f RatFunc.X = y := by
    rw [← RatFunc.algebraMap_X, ← div_one (algebraMap _ _ Polynomial.X), ← map_one (algebraMap (Polynomial K) (RatFunc K))]
    simp only [f]
    rw [RatFunc.liftAlgHom_apply_div]
    simp
  have hfinj : Function.Injective f := f.toRingHom.injective
  refine ⟨K, f, hfX, hfinj, ?_⟩
  letI : Algebra (RatFunc K) E := f.toRingHom.toAlgebra
  -- algebraic over L' = k(t)
  set L' := IntermediateField.adjoin k (Set.range ((↑) : t → E)) with hL'
  have halg : Algebra.IsAlgebraic L' E := ht.isAlgebraic_field
  have hle : L' ≤ f.fieldRange.restrictScalars k := by
    rw [hL', IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, rfl⟩
    show (z : E) ∈ f.fieldRange
    rw [AlgHom.mem_fieldRange]
    by_cases hz : (z : E) = y
    · exact ⟨RatFunc.X, hz ▸ hfX⟩
    · have hzK : (z : E) ∈ K := IntermediateField.subset_adjoin k s ⟨z.2, hz⟩
      refine ⟨algebraMap K (RatFunc K) ⟨z, hzK⟩, ?_⟩
      rw [f.commutes]; rfl
  have hcont : ∀ x : L', ∃ r : RatFunc K, f r = x := by
    intro x
    have := hle x.2
    exact (AlgHom.mem_fieldRange).1 this
  choose ψf hψf using hcont
  let ψ : L' →+* RatFunc K :=
    { toFun := ψf
      map_one' := hfinj (by rw [hψf]; simp)
      map_mul' := fun a b => hfinj (by rw [hψf, map_mul, hψf, hψf]; simp)
      map_zero' := hfinj (by rw [hψf]; simp)
      map_add' := fun a b => hfinj (by rw [hψf, map_add, hψf, hψf]; simp) }
  have hψinj : Function.Injective ψ := ψ.injective
  refine Algebra.IsAlgebraic.ringHom_of_comp_eq (R := L') (A := E) (S := RatFunc K) (B := E)
    ψ (RingHom.id E) hψinj Function.surjective_id ?_
  ext x
  show f (ψf x) = x
  rw [hψf]
