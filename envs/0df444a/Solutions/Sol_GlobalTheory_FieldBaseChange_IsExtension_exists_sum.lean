-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.IsExtension.exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:09.487056+00:00
-- url     : https://prove2.me/submissions/1e59c5b1-22c1-4d5c-8a38-e6ba35a9d230

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
namespace IsExtension
theorem _root_.solution {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) (x : W) :
    ∃ (n : ℕ) (c : Fin n → F) (v : Fin n → V), x = ∑ i, c i • a (v i) := by
  refine semilinear_range_span_induction h.span
    (fun x => ∃ (n : ℕ) (c : Fin n → F) (v : Fin n → V), x = ∑ i, c i • a (v i)) ?_ ?_ ?_ x
  · exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  · rintro x y ⟨n, c, v, rfl⟩ ⟨m, c', v', rfl⟩
    refine ⟨n + m, Fin.append c c', Fin.append v v', ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro c v
    exact ⟨1, fun _ => c, fun _ => v, by simp⟩
end IsExtension
end GlobalTheory.FieldBaseChange
