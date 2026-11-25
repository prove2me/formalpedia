-- Prove2me | solution 1 for GlobalTheory.SerreRegular.projective_of_socle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:42.393631+00:00
-- url     : https://prove2.me/submissions/afd26134-b4dd-4ed0-804b-70ee7d89472f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular
namespace GlobalTheory.SerreRegular
theorem _root_.solution {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {a : A}
    (ha : a ≠ 0) (hm : ∀ y ∈ maximalIdeal A, a * y = 0) (n : ℕ) :
    ∀ (M : ModuleCat.{0} A) [Module.Finite A M], HasProjectiveDimensionLE M n →
      Module.Projective A M := by
  induction n with
  | zero =>
    intro M _ h
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one] at h
    exact (IsProjective.iff_projective M).mpr h
  | succ n ih =>
    intro M _ h
    have hfr : Module.Free (ResidueField A) (ResidueField A ⊗[A] M) :=
      Module.Free.of_divisionRing _ _
    let b := Module.finBasis (ResidueField A) (ResidueField A ⊗[A] M)
    choose v hv using fun i => TensorProduct.mk_surjective A M (ResidueField A)
      residue_surjective (b i)
    have hsp := IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
    let f := Fintype.linearCombination A v
    have hf : Function.Surjective f := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hP : Projective f.shortComplexKer.X₂ :=
      (IsProjective.iff_projective (_ → A)).mp inferInstance
    have hKn : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have hK : Module.Projective A (LinearMap.ker f) := ih _ hKn
    have hfree : Module.Free A (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
    have hkill : ∀ c : LinearMap.ker f, a • c = 0 := by
      intro c
      have h0 : ∑ i, residue A (c.1 i) • b i = 0 := by
        have h1 := congrArg (TensorProduct.mk A (ResidueField A) M 1) (LinearMap.mem_ker.mp c.2)
        rw [Fintype.linearCombination_apply, map_sum, map_zero] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hv]
        exact algebraMap_smul (ResidueField A) (c.1 i) (b i)
      have h2 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h0
      apply Subtype.ext
      funext i
      exact hm _ ((residue_eq_zero_iff _).mp (h2 i))
    have hsub : Subsingleton (LinearMap.ker f) := by
      by_contra hn
      rw [not_subsingleton_iff_nontrivial] at hn
      have : a ∈ Module.annihilator A (LinearMap.ker f) := Module.mem_annihilator.mpr hkill
      rw [Module.annihilator_eq_bot.mpr inferInstance] at this
      exact ha this
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.subsingleton_iff_eq_bot.mp hsub
    exact Module.Projective.of_equiv' (LinearEquiv.ofBijective f ⟨hinj, hf⟩)
end GlobalTheory.SerreRegular
