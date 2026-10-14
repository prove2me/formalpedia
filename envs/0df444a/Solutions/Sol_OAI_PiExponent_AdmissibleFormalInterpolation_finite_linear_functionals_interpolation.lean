-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.finite_linear_functionals_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:46:22.380257+00:00
-- url     : https://prove2.me/submissions/518af74a-1f58-42d3-be99-41aea67453df

import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

theorem solution
    {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι]
    (f : ι → V →ₗ[K] K) (hf : LinearIndependent K f) :
    ∃ q : ι → V, ∀ i j, f i (q j) = if i = j then 1 else 0 := by
  classical
  -- Forgetting the linear-map structure is an injective linear map.
  let E : (V →ₗ[K] K) →ₗ[K] (V → K) :=
    { toFun := fun g => fun v => g v
      map_add' := by intro g h; rfl
      map_smul' := by intro c g; rfl }
  have hfun : LinearIndependent K (fun i v => f i v) := by
    exact hf.map_injOn E (by
      intro g hg h hh heq
      exact LinearMap.ext (congrFun heq))
  let L : V →ₗ[K] (ι → K) :=
    { toFun := fun v i => f i v
      map_add' := by
        intro x y
        ext i
        exact (f i).map_add x y
      map_smul' := by
        intro c x
        ext i
        exact (f i).map_smul c x }
  have hspan : Submodule.span K (Set.range (fun v : V => fun i => f i v)) = ⊤ := by
    exact (span_flip_eq_top_iff_linearIndependent (F := K)
      (f := fun i v => f i v)).2 hfun
  have hrange : LinearMap.range L =
      Submodule.span K (Set.range (fun v : V => fun i => f i v)) := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      exact Submodule.subset_span ⟨v, rfl⟩
    · apply Submodule.span_le.mpr
      rintro y ⟨v, rfl⟩
      exact ⟨v, rfl⟩
  have hsurj : Function.Surjective L := by
    apply LinearMap.range_eq_top.mp
    rw [hrange, hspan]
  choose q hq using fun j : ι => hsurj (Pi.single j (1 : K))
  refine ⟨q, ?_⟩
  intro i j
  simpa [L, Pi.single_apply] using congrFun (hq j) i