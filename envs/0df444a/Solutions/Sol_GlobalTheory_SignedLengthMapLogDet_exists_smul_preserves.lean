-- Prove2me | solution 1 for GlobalTheory.SignedLengthMapLogDet.exists_smul_preserves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:04.369869+00:00
-- url     : https://prove2.me/submissions/7fc7dfbf-5ef3-41d2-b626-66c7eb10f034

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.SignedLengthMapLogDet
theorem _root_.solution (A : Submodule R V) [Submodule.IsLattice K A] (g : V →ₗ[K] V) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ A, r • g x ∈ A := by
  have one : ∀ v : V, ∃ r : R, r ≠ 0 ∧ r • v ∈ A := by
    intro v
    have hv : v ∈ Submodule.span K (A : Set V) := by
      rw [Submodule.IsLattice.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨r, hr, hx⟩ := hx
      obtain ⟨s, hs, hy⟩ := hy
      refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
      rw [smul_add]
      refine A.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact A.smul_mem _ hx
      · rw [mul_smul]; exact A.smul_mem _ hy
    | smul k x _ hx =>
      obtain ⟨r, hr, hx⟩ := hx
      obtain ⟨s, t, ht⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) k
      refine ⟨r * s, mul_ne_zero hr (nonZeroDivisors.coe_ne_zero s), ?_⟩
      rw [mul_smul, ← smul_assoc (s : R) k x, ← ht, algebraMap_smul, smul_comm]
      exact A.smul_mem _ hx
  have key : ∀ B : Submodule R V, B.FG → ∃ r : R, r ≠ 0 ∧ ∀ x ∈ B, r • x ∈ A := by
    intro B hB
    induction B, hB using Submodule.fg_sup_span_induction with
    | bot => exact ⟨1, one_ne_zero, by simp⟩
    | sup S v hS ih =>
      obtain ⟨r, hr, hS⟩ := ih
      obtain ⟨s, hs, hv⟩ := one v
      refine ⟨r * s, mul_ne_zero hr hs, fun x hx => ?_⟩
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [smul_add]
      refine A.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact A.smul_mem _ (hS y hy)
      · rw [smul_comm, mul_smul]; exact A.smul_mem _ (A.smul_mem _ hv)
  obtain ⟨r, hr, h⟩ := key (A.map (g.restrictScalars R))
    ((Submodule.IsLattice.fg (A := K) (M := A)).map _)
  exact ⟨r, hr, fun x hx => h _ ⟨x, hx, rfl⟩⟩
end GlobalTheory.SignedLengthMapLogDet
