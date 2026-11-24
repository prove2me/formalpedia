-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Bmp.sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:41.14805+00:00
-- url     : https://prove2.me/submissions/a35ff0a3-7f8d-4793-ad08-5dc486d21ee5

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
namespace GlobalTheory.ThK.Dbl.Bmp
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) [L.IsLattice K] {y : V}
    (hy : y ∉ L) : ∃ l : V →ₗ[K] K, (∀ z ∈ L, ψ (l z) = 1) ∧ ψ (l y) ≠ 1 := by
  classical
  haveI : Module.Free O L := Submodule.IsLattice.free K L
  let b := Module.Free.chooseBasis O L
  let v : Module.Free.ChooseBasisIndex O L → V := fun i => (b i : V)
  have hliO : LinearIndependent O v := b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : Submodule.span O (Set.range v) = L := by
    have hr : Set.range v = L.subtype '' Set.range b := by rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.IsLattice.span_eq_top (A := K) (M := L)]
    apply Submodule.span_le.mpr
    intro z hz
    have hz' : z ∈ Submodule.span O (Set.range v) := by rw [hspanO]; exact hz
    exact Submodule.span_le_restrictScalars O K _ hz'
  let bK := Module.Basis.mk hliK hspK
  have hrange : Set.range bK = Set.range v := by
    ext z
    simp only [Set.mem_range, bK, Module.Basis.mk_apply]
  have hmem : ∀ z, z ∈ L ↔ ∀ i, bK.repr z i ∈ Set.range (algebraMap O K) := by
    intro z
    rw [← Module.Basis.mem_span_iff_repr_mem O bK z, hrange, hspanO]
  obtain ⟨i, hi⟩ : ∃ i, bK.repr y i ∉ Set.range (algebraMap O K) := by
    by_contra hcon
    push_neg at hcon
    exact hy ((hmem y).mpr hcon)
  obtain ⟨t, ht⟩ : ∃ t : O, ψ (bK.repr y i * algebraMap O K t) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hi ((hψ _).mp hcon)
  have hψO : ∀ o : O, ψ (algebraMap O K o) = 1 := fun o => by
    have h1 := ((hψ (algebraMap O K o)).mpr ⟨o, rfl⟩) 1
    simpa using h1
  refine ⟨algebraMap O K t • bK.coord i, ?_, ?_⟩
  · intro z hz
    obtain ⟨o, ho⟩ := (hmem z).mp hz i
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [← ho, ← map_mul]
    exact hψO _
  · simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rwa [mul_comm]
end GlobalTheory.ThK.Dbl.Bmp
