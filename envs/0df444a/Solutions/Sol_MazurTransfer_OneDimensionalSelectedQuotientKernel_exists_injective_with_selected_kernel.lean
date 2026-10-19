-- Prove2me | solution 1 for MazurTransfer.OneDimensionalSelectedQuotientKernel.exists_injective_with_selected_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T02:35:29.581697+00:00
-- url     : https://prove2.me/submissions/0beb069e-2de8-49bb-a59c-a5a20a720c64

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an extension of a scalar one-dimensional representation
by a one-dimensional quotient has an isomorphic character kernel for ANY
GIVEN surjection onto that SAME quotient. No distinctness of characters,
semisimplicity, splitting, or continuity assumption is introduced.
Named downstream consumer: exact sequences retaining the PREVIOUSLY
SELECTED piQuotient and piConjugateQuotient of the actual norm kernels.
-/
import Definitions.Def_MazurTransfer_IntertwiningMapOriginalKernelCoordinateData20261019
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace MazurTransfer.OneDimensionalSelectedQuotientProofHelpers20261019
open IntertwiningMapKernelCoordinates
variable {k G V B : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup B] [Module k B]
  [FiniteDimensional k V] [FiniteDimensional k B]
variable (σ : Representation k G k) (ρ : Representation k G V) (τ : Representation k G B)

theorem fieldSource_nonzero_bijective (f : Representation.IntertwiningMap σ τ)
    (hB : Module.finrank k B = 1) (hf : f.toLinearMap ≠ 0) : Function.Bijective f := by
  have hs (a : k) : f a = a • f 1 := by
    simpa only [smul_eq_mul, mul_one] using map_smul f a (1 : k)
  have h1 : f 1 ≠ 0 := by
    intro h
    apply hf
    apply LinearMap.ext
    intro a
    exact (hs a).trans (by rw [h, smul_zero]; rfl)
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    have h : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
    rw [hs] at h
    exact (smul_eq_zero.mp h).resolve_right h1
  · exact surjective_of_nonzero_of_finrank_eq_one hB hf

theorem selected_kernel_eq_of_annihilates
    (i : Representation.IntertwiningMap σ ρ) (p q : Representation.IntertwiningMap ρ τ)
    (hq : Function.Surjective q) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (h0 : (p.comp i).toLinearMap = 0) :
    LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap := by
  have hle : LinearMap.range i.toLinearMap ≤ LinearMap.ker p.toLinearMap := by
    rintro v ⟨a, rfl⟩
    exact LinearMap.congr_fun h0 a
  have hdq := q.toLinearMap.finrank_range_add_finrank_ker
  have hdp := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq, finrank_top] at hdq
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at hdp
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [hk]
  omega

theorem kernelRestriction_bijective_of_composite_bijective
    (i : Representation.IntertwiningMap σ ρ) (p q : Representation.IntertwiningMap ρ τ)
    (hq : Function.Surjective q)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hf : Function.Bijective (p.comp i)) :
    Function.Bijective (kernelRestriction ρ τ p q) := by
  constructor
  · intro x y hxy
    have hm : x.val - y.val ∈ LinearMap.ker q.toLinearMap := by
      change q (x.val - y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    rw [← hk] at hm
    obtain ⟨a, ha⟩ := hm
    change i a = x.val - y.val at ha
    have hfa : (p.comp i) a = 0 := by
      change p (i a) = 0
      have hx : p x.val = 0 := x.property
      have hy : p y.val = 0 := y.property
      rw [ha, map_sub, hx, hy, sub_zero]
    have ha0 : a = 0 := hf.1 (hfa.trans (map_zero (p.comp i)).symm)
    apply Subtype.ext
    apply sub_eq_zero.mp
    exact ha.symm.trans (by rw [ha0, map_zero])
  · intro b
    obtain ⟨v, hv⟩ := hq b
    obtain ⟨a, ha⟩ := hf.2 (p v)
    have hqi : q (i a) = 0 := by
      have hmem : i a ∈ LinearMap.range i.toLinearMap := ⟨a, rfl⟩
      rw [hk] at hmem
      exact hmem
    refine ⟨⟨v - i a, ?_⟩, ?_⟩
    · change p (v - i a) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr ha.symm
    · change q (v - i a) = b
      rw [map_sub, hqi, sub_zero, hv]

theorem exists_injective_with_selected_kernel
    (hB : Module.finrank k B = 1)
    (i : Representation.IntertwiningMap σ ρ) (q : Representation.IntertwiningMap ρ τ)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (p : Representation.IntertwiningMap ρ τ) (hp : Function.Surjective p) :
    ∃ j : Representation.IntertwiningMap σ ρ,
      Function.Injective j ∧ LinearMap.range j.toLinearMap = LinearMap.ker p.toLinearMap := by
  by_cases h0 : (p.comp i).toLinearMap = 0
  · exact ⟨i, hi, selected_kernel_eq_of_annihilates σ ρ τ i p q hq hp hk h0⟩
  · let f := p.comp i
    have hf : Function.Bijective f := fieldSource_nonzero_bijective σ τ f hB h0
    let r := kernelRestriction ρ τ p q
    have hr : Function.Bijective r :=
      kernelRestriction_bijective_of_composite_bijective σ ρ τ i p q hq hk hf
    let e := (r.ofBijective hr).symm
    let j := (kernelInclusion ρ τ p).comp (e.toIntertwiningMap.comp f)
    have hj : Function.Injective j :=
      (kernelInclusion_injective ρ τ p).comp (e.toLinearEquiv.injective.comp hf.1)
    have hs : Function.Surjective (e.toIntertwiningMap.comp f) :=
      e.toLinearEquiv.surjective.comp hf.2
    refine ⟨j, hj, ?_⟩
    calc
      LinearMap.range j.toLinearMap = LinearMap.range (kernelInclusion ρ τ p).toLinearMap := by
        exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)
      _ = LinearMap.ker p.toLinearMap := kernelInclusion_range ρ τ p

end MazurTransfer.OneDimensionalSelectedQuotientProofHelpers20261019

theorem solution : ∀ {k G V B : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup B] [Module k B]
    [FiniteDimensional k V] [FiniteDimensional k B]
    (σ : Representation k G k) (ρ : Representation k G V) (τ : Representation k G B)
    (hB : Module.finrank k B = 1)
    (i : Representation.IntertwiningMap σ ρ) (q : Representation.IntertwiningMap ρ τ)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (p : Representation.IntertwiningMap ρ τ) (hp : Function.Surjective p),
    ∃ j : Representation.IntertwiningMap σ ρ,
      Function.Injective j ∧ LinearMap.range j.toLinearMap = LinearMap.ker p.toLinearMap := by
  exact MazurTransfer.OneDimensionalSelectedQuotientProofHelpers20261019.exists_injective_with_selected_kernel
#print axioms solution
