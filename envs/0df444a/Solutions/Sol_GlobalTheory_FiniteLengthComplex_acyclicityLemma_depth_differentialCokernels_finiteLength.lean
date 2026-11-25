-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.acyclicityLemma_depth_differentialCokernels_finiteLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:13.217835+00:00
-- url     : https://prove2.me/submissions/28bc8c66-7d7f-4f42-9126-2c6648fe30f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_of_isFiniteLength
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_opcyclesShortComplex_shortExact
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_isIso_pOpcycles_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution [IsLocalRing R] (g : ℕ)
    (hX : ∀ i n, n < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.X i) n))
    (hH : ∀ i, IsFiniteLength R (C.homology i)) (i : ℕ) :
    (∀ n, n + i < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) ∧
      (i < g → IsZero (C.homology i)) := by
  have key : ∀ i, (∀ n, n + i < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) →
      i < g → IsZero (C.homology i) := by
    intro i h hi
    have h0 : Subsingleton (Abelian.Ext.{0} (C.homology i) (C.opcycles i) 0) :=
      subsingleton_ext_of_isFiniteLength _ 0 (h 0 (by omega)) _ (hH i)
    have h1 : Subsingleton (C.homology i ⟶ C.opcycles i) :=
      Ext.addEquiv₀.subsingleton_congr.mp h0
    exact IsZero.of_mono_eq_zero (C.homologyι i) (Subsingleton.elim _ _)
  induction i with
  | zero =>
    refine (fun h => ⟨h, key 0 h⟩) fun n hn => ?_
    have := isIso_pOpcycles_zero C
    have := hX 0 n (by omega)
    refine subsingleton_of_forall_eq 0 fun x => ?_
    rw [← Ext.comp_mk₀_id x, ← IsIso.inv_hom_id (C.pOpcycles 0), ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero, Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]
  | succ i ih =>
    refine (fun h => ⟨h, key (i + 1) h⟩) fun n hn => ?_
    have hS := opcyclesShortComplex_shortExact C i (ih.2 (by omega))
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl
      (@Subsingleton.elim _ (ih.1 (n + 1) (by omega)) _ _)
    rw [@Subsingleton.elim _ (hX (i + 1) n (by omega)) y 0]
    exact Ext.zero_comp _ _ _ _ _
end GlobalTheory.FiniteLengthComplex
