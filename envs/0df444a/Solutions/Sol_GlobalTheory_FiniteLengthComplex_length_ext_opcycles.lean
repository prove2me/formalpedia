-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.length_ext_opcycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:48.483227+00:00
-- url     : https://prove2.me/submissions/fe5ba0de-c2a6-4ba9-b3b4-f63ca9ed82cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_opcyclesShortComplex_shortExact

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
theorem _root_.solution (Y : ModuleCat.{0} R) (hP : ∀ i, Projective (C.X i)) (j : ℕ)
    (hH : ∀ i < j + 1, IsZero (C.homology i)) :
    Module.length R (Abelian.Ext.{0} (C.opcycles (j + 1)) Y (j + 1)) =
      Module.length R (Abelian.Ext.{0} (C.opcycles 0) Y 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R Y (zero_add 0))) := by
  have step : ∀ i, IsZero (C.homology i) → ∀ n,
      Module.length R (Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1)) =
      Module.length R (Abelian.Ext.{0} (C.opcycles i) Y n ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n))) := by
    intro i hi n
    have hS := opcyclesShortComplex_shortExact C i hi
    let δ : Abelian.Ext.{0} (C.opcycles i) Y n →ₗ[R]
        Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1) :=
      hS.extClass.precompOfLinear R Y (add_comm 1 n)
    have hsurj : Function.Surjective δ := fun x => by
      have : Projective (opcyclesShortComplex C i).X₂ := hP (i + 1)
      exact Ext.contravariant_sequence_exact₃ hS Y x (Ext.eq_zero_of_projective _) (add_comm 1 n)
    have hker : LinearMap.ker δ = LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n)) := by
      ext x
      refine ⟨fun hx => Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 n) hx, ?_⟩
      rintro ⟨y, rfl⟩
      exact hS.extClass_comp_assoc y (h := add_comm 1 n)
    rw [← hker]
    exact (δ.quotKerEquivOfSurjective hsurj).length_eq.symm
  induction j with
  | zero => exact step 0 (hH 0 (by omega)) 0
  | succ j ih =>
    rw [step (j + 1) (hH _ (by omega)) (j + 1), ← ih fun i hi => hH i (by omega)]
    refine (Submodule.quotEquivOfEqBot _ ?_).length_eq
    rw [LinearMap.range_eq_bot]
    ext x
    have := hP (j + 1 + 1)
    rw [Ext.eq_zero_of_projective x]
    simp
end GlobalTheory.FiniteLengthComplex
