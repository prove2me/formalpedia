-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.exists_biorthogonal_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:17:28.455319+00:00
-- url     : https://prove2.me/submissions/7898b769-a9c8-4d81-abe1-f62091dbc051

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

theorem solution
    {K ι V : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommMonoid V] [Module K V]
    (L : ι → V →ₗ[K] K)
    (hL : LinearIndependent K L) :
    ∃ v : ι → V, ∀ i j, L i (v j) = if i = j then 1 else 0 := by
  classical
  -- Forgetting the linear-map structure is an injective linear map.
  have hinj : Function.Injective (LinearMap.ltoFun K V K K) := by
    intro f g h
    apply LinearMap.ext
    intro x
    exact congrFun h x
  have hfun : LinearIndependent K (fun i : ι => fun x : V => L i x) :=
    hL.map_injOn (LinearMap.ltoFun K V K K) hinj.injOn
  let T : V →ₗ[K] (ι → K) :=
    { toFun := fun x i => L i x
      map_add' := by
        intro x y
        funext i
        exact (L i).map_add x y
      map_smul' := by
        intro a x
        funext i
        exact (L i).map_smul a x }
  have hspan :
      Submodule.span K (Set.range (fun x : V => fun i : ι => L i x)) = ⊤ :=
    (span_flip_eq_top_iff_linearIndependent
      (ι := ι) (α := V) (F := K) (f := fun i : ι => fun x : V => L i x)).2 hfun
  have hle :
      Submodule.span K (Set.range (fun x : V => fun i : ι => L i x)) ≤ T.range := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hRange : T.range = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hle
  have hsurj : Function.Surjective T := LinearMap.range_eq_top.mp hRange
  choose v hv using fun j : ι =>
    hsurj (fun i : ι => if i = j then (1 : K) else 0)
  refine ⟨v, ?_⟩
  intro i j
  exact congrFun (hv j) i
