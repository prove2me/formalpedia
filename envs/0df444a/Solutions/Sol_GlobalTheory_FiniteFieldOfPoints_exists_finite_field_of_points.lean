-- Prove2me | solution 1 for GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:26.615358+00:00
-- url     : https://prove2.me/submissions/30126547-7e6a-42ed-8285-f0a8475367e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteFieldOfPoints
import Theorems.Thm_GlobalTheory_FiniteFieldOfPoints_factor_of_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.FiniteFieldOfPoints
namespace GlobalTheory.FiniteFieldOfPoints
theorem _root_.solution (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C)
    (hφ : RingHom.Finite φ) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)), FiniteDimensional K ↥E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : ↥E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        RingHom.comp ψ φ = RingHom.comp j (RingHom.comp e (algebraMap K ↥E)) →
        ∃ (ψ₀ : C →+* K₂), RingHom.comp j ψ₀ = ψ := by
  classical
  letI : Algebra K C := φ.toAlgebra
  haveI : Module.Finite K C := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := C)
  have hint : ∀ c : C, IsIntegral K c := fun c => Algebra.IsIntegral.isIntegral c
  choose p hpm hpe using hint
  set P : K[X] := ∏ c ∈ s, p c with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ (fun c _ => hpm c)
  have hsf : IsSplittingField K
      (IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  refine ⟨IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)),
    IsSplittingField.finiteDimensional _ P, ?_⟩
  generalize IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)) = E at hsf ⊢
  intro K₂ Ω _ _ e j ψ hc
  have hspl : (P.map (algebraMap K E)).Splits := hsf.splits'
  have hspl2 : (P.map (e.comp (algebraMap K E))).Splits := by
    rw [← Polynomial.map_map]; exact hspl.map e
  have hgen : ∀ c ∈ s, ψ c ∈ j.range := by
    intro c hcs
    have h0 : eval₂ φ c P = 0 := by
      rw [hP, eval₂_finsetProd]
      exact Finset.prod_eq_zero hcs (hpe c)
    have h1 : ((P.map (e.comp (algebraMap K E))).map j).IsRoot (ψ c) := by
      rw [Polynomial.map_map, ← hc, IsRoot, eval_map, ← hom_eval₂, h0, map_zero]
    exact hspl2.mem_range_of_isRoot (hPm.map _).ne_zero h1
  apply factor_of_range
  intro c
  have hmem : c ∈ Submodule.span K (s : Set C) := by rw [hs]; trivial
  change ψ c ∈ j.range
  induction hmem using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    refine ⟨e (algebraMap K E a), ?_⟩
    exact (RingHom.congr_fun hc a).symm
end GlobalTheory.FiniteFieldOfPoints
