-- Prove2me | solution 1 for GlobalTheory.exists_pair_dvd_of_bilinForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:40.439913+00:00
-- url     : https://prove2.me/submissions/f30ad6e2-2aec-4290-85e1-88adf598bdfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M]
omit [IsDomain R]
namespace GlobalTheory
theorem _root_.solution (B : LinearMap.BilinForm R M) (N : Submodule R M) :
    ∃ e ∈ N, ∃ f ∈ N, (∀ y ∈ N, B e f ∣ B e y) ∧ (∀ x ∈ N, B e f ∣ B x f) ∧
      (∀ x ∈ N, ∀ y ∈ N, B e y = 0 → B x f = 0 → B e f ∣ B x y) := by
  let S : Set (Ideal R) := {J | ∃ x ∈ N, ∃ y ∈ N, J = Ideal.span {B x y}}
  obtain ⟨J, ⟨e, he, f, hf, rfl⟩, hmax⟩ :=
    (wellFounded_gt (α := Ideal R)).has_min S ⟨_, 0, N.zero_mem, 0, N.zero_mem, rfl⟩
  have key : ∀ s : R, (∀ u v : R, ∃ x ∈ N, ∃ y ∈ N, B x y = u * B e f + v * s) → B e f ∣ s := by
    intro s hs
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span {B e f, s})).principal
    have hg' : Ideal.span {B e f, s} = Ideal.span {g} := hg
    have : g ∈ Ideal.span {B e f, s} := hg' ▸ Ideal.mem_span_singleton_self g
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 this
    obtain ⟨x, hx, y, hy, hxy⟩ := hs u v
    have h1 : Ideal.span {B e f} ≤ Ideal.span {g} :=
      hg' ▸ Ideal.span_mono (by simp)
    have h2 := hmax (Ideal.span {g}) ⟨x, hx, y, hy, by rw [hxy, huv]⟩
    have h3 : Ideal.span {B e f} = Ideal.span {g} := by
      by_contra hne
      exact h2 (lt_of_le_of_ne h1 hne)
    rw [← Ideal.mem_span_singleton, h3, ← hg']
    exact Ideal.subset_span (by simp)
  refine ⟨e, he, f, hf, fun y hy => key _ fun u v => ?_, fun x hx => key _ fun u v => ?_,
    fun x hx y hy h₁ h₂ => key _ fun u v => ?_⟩
  · exact ⟨e, he, u • f + v • y, N.add_mem (N.smul_mem _ hf) (N.smul_mem _ hy), by simp⟩
  · exact ⟨u • e + v • x, N.add_mem (N.smul_mem _ he) (N.smul_mem _ hx), f, hf, by simp⟩
  · exact ⟨u • e + v • x, N.add_mem (N.smul_mem _ he) (N.smul_mem _ hx), f + y,
      N.add_mem hf hy, by simp [h₁, h₂]⟩
end GlobalTheory
