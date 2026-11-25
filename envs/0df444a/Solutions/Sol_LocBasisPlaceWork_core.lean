-- Prove2me | solution 1 for LocBasisPlaceWork.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:13.321649+00:00
-- url     : https://prove2.me/submissions/433a3911-5c5a-4843-ade7-57fa6e002c4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear
import Theorems.Thm_LocBasisPlaceWork_span_clear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open LocBasisPlaceWork
namespace LocBasisPlaceWork
theorem _root_.solution {R A K : Type*} [CommRing R] [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field K] [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    [IsFractionRing A K] (M : Submonoid R) [IsLocalization M A] (N : ℕ)
    (L : Submodule R (Fin N → K)) (hL : L.FG)
    (hsp : Submodule.span K (L : Set (Fin N → K)) = ⊤) :
    ∃ P : Matrix (Fin N) (Fin N) K, P.det ≠ 0 ∧ (∀ a, ∃ s ∈ M, s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s ∈ M, ∃ c : Fin N → R, s • x = ∑ a, c a • P.transpose a := by
  obtain ⟨S, rfl⟩ := hL
  set LA : Submodule A (Fin N → K) := span A (S : Set (Fin N → K)) with hLA
  have : Module.Finite A LA := Module.Finite.iff_fg.mpr (Submodule.fg_span S.finite_toSet)
  have : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).mpr (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A LA := inferInstance
  let b := Module.Free.chooseBasis A LA
  let v : Module.Free.ChooseBasisIndex A LA → (Fin N → K) := fun i => (b i : Fin N → K)
  have hliA : LinearIndependent A v := b.linearIndependent.map' LA.subtype (ker_subtype _)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing A K).mp hliA
  have hsum : ∀ (y : Fin N → K) (hy : y ∈ LA), y = ∑ i, (b.repr ⟨y, hy⟩ i) • v i := by
    intro y hy
    have h2 := congrArg (fun z : LA => (z : Fin N → K)) (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hLAle : ∀ y ∈ LA, y ∈ span K (Set.range v) := by
    intro y hy
    rw [hsum y hy]
    refine sum_mem fun i _ => ?_
    rw [← algebraMap_smul K (b.repr ⟨y, hy⟩ i) (v i)]
    exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  have hspan : (⊤ : Submodule K (Fin N → K)) ≤ span K (Set.range v) := by
    rw [← hsp, Submodule.span_span_of_tower R K, Submodule.span_le]
    intro x hx
    exact hLAle x (subset_span hx)
  let bK := Module.Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A LA) = N := by
    have := Module.finrank_eq_card_basis bK
    simpa using this.symm
  let e := Fintype.equivFinOfCardEq hcard
  set P : Matrix (Fin N) (Fin N) K := (Matrix.of fun a i => v (e.symm a) i).transpose with hP
  have hcol : ∀ a, P.transpose a = v (e.symm a) := fun a => by ext i; simp [hP]
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hP, Matrix.det_transpose]
    have hrows : LinearIndependent K (fun a => (Matrix.of fun a i => v (e.symm a) i) a) :=
      hli.comp e.symm e.symm.injective
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero
  · intro a
    obtain ⟨s, hs, h⟩ := span_clear M (S : Set (Fin N → K)) (v (e.symm a)) (b (e.symm a)).2
    exact ⟨s, hs, by rw [hcol]; exact h⟩
  · intro x hx
    have hxA : x ∈ LA := Submodule.span_le_restrictScalars R A _ hx
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples M Finset.univ
      (fun i => b.repr ⟨x, hxA⟩ i)
    choose c hc using fun i => hs i (Finset.mem_univ i)
    refine ⟨(s : R), s.2, fun a => c (e.symm a), ?_⟩
    have hR : (∑ a, c (e.symm a) • P.transpose a) = ∑ i, c i • v i := by
      simp_rw [hcol]
      exact Equiv.sum_comp e.symm (fun i => c i • v i)
    rw [hR]
    conv_lhs => rw [hsum x hxA, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, ← hc i, algebraMap_smul]
end LocBasisPlaceWork
