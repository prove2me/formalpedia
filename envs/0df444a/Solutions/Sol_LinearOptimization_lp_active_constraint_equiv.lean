-- Prove2me | solution 1 for LinearOptimization.lp_active_constraint_equiv
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T05:41:31.338432+00:00
-- url     : https://prove2.me/submissions/9c2718ff-39b9-4360-a2d7-b6047832b301

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.TFAE
import Definitions.Def_ActiveConstraints

open Matrix LinearOptimization

/-- Every linear functional on `Fin n → ℝ` is `v ↦ v ⬝ᵥ d` for a unique `d`. -/
private lemma dual_eq_dotProduct {n : ℕ} (f : Module.Dual ℝ (Fin n → ℝ)) :
    ∃ d : Fin n → ℝ, ∀ v, f v = v ⬝ᵥ d := by
  classical
  refine ⟨fun j => f (Pi.single j 1), fun v => ?_⟩
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ)) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  calc f v = f (∑ j, v j • (Pi.single j (1 : ℝ))) := by rw [← hv]
    _ = ∑ j, v j * f (Pi.single j 1) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; simp [smul_eq_mul]
    _ = v ⬝ᵥ (fun j => f (Pi.single j 1)) := rfl

/-- The subspace of vectors orthogonal to a fixed `d`. -/
private def orthTo {n : ℕ} (d : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | v ⬝ᵥ d = 0}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, add_dotProduct] at *
    rw [hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, smul_dotProduct] at *
    rw [hv, smul_zero]

theorem solution {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) (x' : Fin n → ℝ) :
    List.TFAE
      [ ∃ s : Finset ι, s.card = n ∧ (∀ i ∈ s, (C i).IsActiveAt x') ∧
          LinearIndependent ℝ (fun i : s => (C i.1).a),
        Submodule.span ℝ ((fun i => (C i).a) '' {i | (C i).IsActiveAt x'}) = ⊤,
        ∀ y : Fin n → ℝ,
          (∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ y = (C i).b) → y = x' ] := by
  classical
  have hfr : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  -- The image of the active constraint vectors.
  set S : Set (Fin n → ℝ) := (fun i => (C i).a) '' {i | (C i).IsActiveAt x'} with hS
  tfae_have 1 → 2 := by
    rintro ⟨s, hcard, hact, hli⟩
    have hcard' : Fintype.card {i // i ∈ s} = Module.finrank ℝ (Fin n → ℝ) := by
      rw [Fintype.card_coe, hcard, hfr]
    have htop : Submodule.span ℝ (Set.range (fun i : s => (C i.1).a)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' hcard'
    refine top_le_iff.mp ?_
    rw [← htop]
    refine Submodule.span_mono ?_
    rintro w ⟨i, rfl⟩
    exact ⟨i.1, hact i.1 i.2, rfl⟩
  tfae_have 2 → 3 := by
    intro h2 y hy
    have hmem : ∀ v : Fin n → ℝ, v ⬝ᵥ (y - x') = 0 := by
      have hsub : S ⊆ (orthTo (y - x') : Set (Fin n → ℝ)) := by
        rintro w ⟨i, hi, rfl⟩
        have h1 : (C i).a ⬝ᵥ x' = (C i).b := hi
        have h2' : (C i).a ⬝ᵥ y = (C i).b := hy i hi
        show (C i).a ⬝ᵥ (y - x') = 0
        rw [dotProduct_sub, h1, h2', sub_self]
      have : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ orthTo (y - x') := by
        rw [← h2]; exact Submodule.span_le.mpr hsub
      intro v; exact this (Submodule.mem_top)
    have hzero : (y - x') = 0 := dotProduct_self_eq_zero.mp (hmem (y - x'))
    exact sub_eq_zero.mp hzero
  tfae_have 3 → 1 := by
    intro h3
    -- Step A: the active vectors span everything.
    have h2 : Submodule.span ℝ S = ⊤ := by
      by_contra hne
      obtain ⟨f, hf0, hfmap⟩ :=
        Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
      obtain ⟨d, hd⟩ := dual_eq_dotProduct f
      have hzero : ∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ d = 0 := by
        intro i hi
        have : (C i).a ∈ Submodule.span ℝ S := Submodule.subset_span ⟨i, hi, rfl⟩
        have : f ((C i).a) ∈ Submodule.map f (Submodule.span ℝ S) :=
          Submodule.mem_map_of_mem this
        rw [hfmap, Submodule.mem_bot] at this
        rw [← hd]; exact this
      have hy : ∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ (x' + d) = (C i).b := by
        intro i hi
        rw [dotProduct_add, hzero i hi, add_zero]; exact hi
      have hxd : x' + d = x' := h3 (x' + d) hy
      have hd0 : d = 0 := by
        have := hxd
        simpa using congrArg (fun z => z - x') this
      refine hf0 (LinearMap.ext fun v => ?_)
      simp [hd v, hd0]
    -- Step B: extract `n` independent active vectors.
    set A : Set ι := {i | (C i).IsActiveAt x'} with hA
    set v : A → (Fin n → ℝ) := fun i => (C i.1).a with hv
    have hrange : Set.range v = S := by
      ext w
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i.1, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    obtain ⟨κ, α, hαinj, hspan, hli⟩ := exists_linearIndependent' ℝ v
    have hκtop : Submodule.span ℝ (Set.range (v ∘ α)) = ⊤ := by
      rw [hspan, hrange, h2]
    have : Finite κ := Finite.of_injective α hαinj
    haveI : Fintype κ := Fintype.ofFinite κ
    let bas : Module.Basis κ ℝ (Fin n → ℝ) := Module.Basis.mk hli (le_of_eq hκtop.symm)
    have hcardκ : Fintype.card κ = n := by
      have h := Module.finrank_eq_card_basis bas
      rw [hfr] at h
      exact h.symm
    -- assemble the finset
    have hinj : Function.Injective (fun k : κ => (α k).1) := by
      intro k₁ k₂ h
      exact hαinj (Subtype.ext h)
    refine ⟨Finset.image (fun k : κ => (α k).1) Finset.univ, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcardκ]
    · intro i hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
      obtain ⟨k, rfl⟩ := hi
      exact (α k).2
    · have hbij : Function.Bijective
          (fun k : κ => (⟨(α k).1, by simp⟩ : {i // i ∈ Finset.image (fun k : κ => (α k).1) Finset.univ})) := by
        constructor
        · intro k₁ k₂ h
          have hv : (α k₁).1 = (α k₂).1 := by simpa [Subtype.ext_iff] using h
          exact hinj hv
        · rintro ⟨i, hi⟩
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
          obtain ⟨k, hk⟩ := hi
          exact ⟨k, Subtype.ext hk⟩
      let e : κ ≃ {i // i ∈ Finset.image (fun k : κ => (α k).1) Finset.univ} :=
        Equiv.ofBijective _ hbij
      rw [← linearIndependent_equiv e]
      exact hli
  tfae_finish
