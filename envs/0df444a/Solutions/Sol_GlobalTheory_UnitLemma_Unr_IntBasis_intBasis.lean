-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.IntBasis.intBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:11.254917+00:00
-- url     : https://prove2.me/submissions/e553bb64-3770-463c-aea7-7d8ec60e515f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_le_one_iff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_exists_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr.IntBasis
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    letI : Algebra K.E K'.E := φ.toAlgebra;
    ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  intro K K' d φ h hd
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, key⟩ := exists_key h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : ∀ a : Fin d → K.E, ∃ m, ∀ k, adicVal K (a k) ≤ adicVal K (a m) := fun a =>
    Finite.exists_max (fun k => adicVal K (a k))
  have hli : LinearIndependent K.E w := by
    rw [Fintype.linearIndependent_iff]; intro g hg
    obtain ⟨m, hm⟩ := hmax g
    have hk := key g m hm
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
    rw [hg, map_zero] at hk
    have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
    intro k; have := hm k; rw [hgm, map_zero] at this
    exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; exact h.2.2.2.2.symm)
  refine ⟨B, fun z => ?_⟩
  have hz : ∑ k, φ (B.repr z k) * w k = z := by
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨m, hm⟩ := hmax (B.repr z)
  have hv := key _ m hm
  rw [hz] at hv
  rw [← adicVal_le_one_iff K' z]
  constructor
  · intro hzO k; rw [← adicVal_le_one_iff]; exact (hm k).trans (hv ▸ hzO)
  · intro hall; rw [hv]; exact (adicVal_le_one_iff K _).2 (hall m)
end GlobalTheory.UnitLemma.Unr.IntBasis
