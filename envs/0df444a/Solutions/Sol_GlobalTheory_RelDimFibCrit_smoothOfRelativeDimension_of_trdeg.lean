-- Prove2me | solution 1 for GlobalTheory.RelDimFibCrit.smoothOfRelativeDimension_of_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:06:19.427797+00:00
-- url     : https://prove2.me/submissions/33517cbf-0666-4027-8929-13485ab6d458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothRelativeDimOfTrdeg
import Theorems.Thm_GlobalTheory_RelDimFibCrit_trdeg_residueField_of_minimal_in_fibre
import Theorems.Thm_GlobalTheory_RelDimFibCrit_exists_minimal_in_fibre
import Theorems.Thm_GlobalTheory_RelDimFibCrit_trdeg_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.RelDimFibCrit
namespace GlobalTheory.RelDimFibCrit
theorem _root_.solution : ∀ {X S : Scheme.{0}} (f : X ⟶ S) (n : ℕ), Smooth f →
    (∀ x : X, (∀ x' : X, f x' = f x → x' ⤳ x → x' = x) →
      @Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _ (f.residueFieldMap x).hom.toAlgebra = n) →
    SmoothOfRelativeDimension n f := by
  intro X S f n hf H
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨r, hr⟩ : ∃ r, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension r := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := hs
    letI := (f.appLE U V e).hom.toAlgebra
    exact ⟨_, ⟨_, _, _, ‹_›, P, rfl⟩⟩
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  obtain ⟨P₀, hP₀, -, hcomap, hmin⟩ :=
    exists_minimal_in_fibre (f.appLE U V e).hom (hV.primeIdealOf ⟨x, hx⟩).asIdeal inferInstance
  let p₀ : PrimeSpectrum Γ(X, V) := ⟨P₀, hP₀⟩
  have key := trdeg_residueField_of_minimal_in_fibre (f.appLE U V e).hom r hr P₀ (fun P' h1 h2 h3 => hmin P' h1 h2 (h3.trans hcomap))
  have h3 := trdeg_affine f U hU V hV e p₀
  have hm : ∀ x' : X, f x' = f (hV.fromSpec p₀) → x' ⤳ hV.fromSpec p₀ → x' = hV.fromSpec p₀ := by
    intro x' hfx hsp
    have hx'V : x' ∈ Set.range hV.fromSpec :=
      hV.range_fromSpec ▸ hsp.mem_open V.isOpen (hV.range_fromSpec ▸ ⟨p₀, rfl⟩)
    obtain ⟨p', rfl⟩ := hx'V
    have hle : p'.asIdeal ≤ P₀ := (PrimeSpectrum.le_iff_specializes p' p₀).2
      (hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 hsp)
    have h1 : ∀ q : PrimeSpectrum Γ(X, V),
        hU.fromSpec (Spec.map (f.appLE U V e) q) = f (hV.fromSpec q) := fun q => by
      show (Spec.map (f.appLE U V e) ≫ hU.fromSpec) q = (hV.fromSpec ≫ f) q
      rw [IsAffineOpen.SpecMap_appLE_fromSpec]
    have h2 := hU.fromSpec.isOpenEmbedding.injective ((h1 p').trans (hfx.trans (h1 p₀).symm))
    have hc : p'.asIdeal.comap (f.appLE U V e).hom = P₀.comap (f.appLE U V e).hom :=
      congrArg PrimeSpectrum.asIdeal h2
    have := hmin p'.asIdeal p'.isPrime hle (hc.trans hcomap)
    exact congrArg hV.fromSpec (PrimeSpectrum.ext this)
  have hn := H _ hm
  have : (r : Cardinal) = n := key.symm.trans (h3.symm.trans hn)
  obtain rfl : r = n := by exact_mod_cast this
  exact hr
end GlobalTheory.RelDimFibCrit
