-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.exists_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:40.291231+00:00
-- url     : https://prove2.me/submissions/a65fd2eb-fcd7-4487-8696-f3967ec36f5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
section Basic
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
private theorem semilinear_range_span_induction {a : V →ₛₗ[algebraMap K F] W}
    (h : Submodule.span F (Set.range a) = ⊤) (p : W → Prop) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hb : ∀ (c : F) v, p (c • a v)) (x : W) : p x := by
  have key : ∀ y ∈ Submodule.span F (Set.range a), ∀ c : F, p (c • y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact fun c => hb c v
    | zero => intro c; rw [smul_zero]; exact h0
    | add y z _ _ hy hz => intro c; rw [smul_add]; exact hadd _ _ (hy c) (hz c)
    | smul d y _ hy => intro c; rw [smul_smul]; exact hy (c * d)
  have hx : x ∈ Submodule.span F (Set.range a) := by rw [h]; exact Submodule.mem_top
  simpa using key x hx 1
end Basic
section Graph
variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  {V₀ V V' W W' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module F W']
  {J : Type} {P₀ P P' : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, AddCommGroup (P' j)] [∀ j, Module F (P' j)]
end Graph
end GlobalTheory.FieldBaseChange
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution {ι : Type} (b : Module.Basis ι K F) {a : V →ₛₗ[algebraMap K F] W}
    (h : Submodule.span F (Set.range a) = ⊤) {Λ : ι → W →+ V} (hΛ : ∀ i, IsCoord a (b.coord i) (Λ i))
    (x : W) : ∃ S : Finset ι, (∀ i ∉ S, Λ i x = 0) ∧
      ∀ S' : Finset ι, S ⊆ S' → x = ∑ i ∈ S', b i • a (Λ i x) := by
  classical
  refine semilinear_range_span_induction h
    (fun x => ∃ S : Finset ι, (∀ i ∉ S, Λ i x = 0) ∧
      ∀ S' : Finset ι, S ⊆ S' → x = ∑ i ∈ S', b i • a (Λ i x)) ?_ ?_ ?_ x
  · exact ⟨∅, fun i _ => map_zero _, fun S' _ => by simp⟩
  · rintro x y ⟨S₁, h₁, h₁'⟩ ⟨S₂, h₂, h₂'⟩
    refine ⟨S₁ ∪ S₂, fun i hi => ?_, fun S' hS' => ?_⟩
    · rw [Finset.mem_union, not_or] at hi
      rw [map_add, h₁ i hi.1, h₂ i hi.2, add_zero]
    · simp only [map_add, smul_add, Finset.sum_add_distrib]
      rw [← h₁' S' (Finset.union_subset_left hS'), ← h₂' S' (Finset.union_subset_right hS')]
  · intro c v
    refine ⟨(b.repr c).support, fun i hi => ?_, fun S' hS' => ?_⟩
    · rw [hΛ i c v, Module.Basis.coord_apply, Finsupp.notMem_support_iff.mp hi, zero_smul]
    · have hterm : ∀ i, b i • a (Λ i (c • a v)) = (b.repr c i • b i) • a v := by
        intro i
        rw [hΛ i c v, Module.Basis.coord_apply, LinearMap.map_smulₛₗ, smul_smul,
          Algebra.smul_def (b.repr c i) (b i), mul_comm (b i)]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.linearCombination_repr c]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ hS' (fun i r => r • b i) (fun i _ => zero_smul _ _)]
end GlobalTheory.FieldBaseChange
