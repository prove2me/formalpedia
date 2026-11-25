-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.length_ext_of_isFiniteLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:17.228134+00:00
-- url     : https://prove2.me/submissions/254baaef-40ea-4a89-a542-00c8fbb5a8f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_of_isZero_left
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_shortExact_submodule
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_nonempty_iso_residue
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_of_isFiniteLength

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
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution [IsLocalRing R] (Y : ModuleCat.{0} R) (g : ℕ)
    (hk : ∀ n, n ≠ g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (Abelian.Ext.{0} (ModuleCat.of R M) Y g) = Module.length R M *
      Module.length R (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y g) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    have := subsingleton_ext_of_isZero_left
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)) Y g
    rw [Module.length_eq_zero, Module.length_eq_zero (M := M), zero_mul]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have hS := shortExact_submodule N
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N), Module.length_eq_one R (M ⧸ N), add_mul, one_mul, ← ih,
      (extCongrLeft e Y g).length_eq, add_comm]
    refine Module.length_eq_add_of_exact
      ((Ext.mk₀ (ModuleCat.ofHom N.mkQ)).precompOfLinear R Y (zero_add g))
      ((Ext.mk₀ (ModuleCat.ofHom N.subtype)).precompOfLinear R Y (zero_add g)) ?_ ?_ ?_
    · cases g with
      | zero =>
        have := hS.epi_g
        exact Ext.precomp_mk₀_injective_of_epi Y (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
          (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).g
      | succ g =>
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y x hx (add_comm 1 g)
        rw [@Subsingleton.elim _ (subsingleton_ext_of_isFiniteLength Y g (hk g (by omega)) N hN) y 0]
        exact Ext.comp_zero _ _ _ _ _
    · intro x
      have := hk (g + 1) (by omega)
      have h3 := (extCongrLeft e Y (g + 1)).symm.toEquiv.subsingleton
      exact Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 g) (@Subsingleton.elim _ h3 _ _)
    · intro x
      refine ⟨fun hx => Ext.contravariant_sequence_exact₂ hS Y x hx, ?_⟩
      rintro ⟨y, rfl⟩
      change (Ext.mk₀ _).comp ((Ext.mk₀ _).comp y (zero_add g)) (zero_add g) = 0
      rw [Ext.mk₀_comp_mk₀_assoc, ← ModuleCat.ofHom_comp,
        (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero]
      simp
end GlobalTheory.FiniteLengthComplex
