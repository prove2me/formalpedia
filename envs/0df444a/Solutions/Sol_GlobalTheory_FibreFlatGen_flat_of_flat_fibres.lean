-- Prove2me | solution 1 for GlobalTheory.FibreFlatGen.flat_of_flat_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:41:43.668664+00:00
-- url     : https://prove2.me/submissions/c0528d5e-849a-422b-99ce-573520cf1923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RTensorInjectiveOfFlatBaseChange
import Theorems.Thm_GlobalTheory_FibreFlatGen_flat_of_injective_on_fibre
import Theorems.Thm_GlobalTheory_FibreFlatGen_lTensor_injective_of_fibre
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory GlobalTheory.FibreFlatGen
open LocalFlat
universe u
namespace GlobalTheory.FibreFlatGen
theorem _root_.solution {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal B B (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap B _) fun P _ => ?_
  let L := Localization.AtPrime P
  let q : Ideal A := P.under A
  haveI : P.LiesOver q := ⟨rfl⟩
  let A' := Localization.AtPrime q
  letI : Algebra A' L := Localization.AtPrime.algebraOfLiesOver q P
  haveI : IsScalarTower A A' L := inferInstance
  haveI : IsScalarTower R A' L := inferInstance
  haveI : Module.Flat A A' := IsLocalization.flat A' q.primeCompl
  haveI : Module.Flat B L := IsLocalization.flat L P.primeCompl
  haveI : Module.Flat R L := .trans R B L
  haveI : IsNoetherianRing A' := IsLocalization.isNoetherianRing q.primeCompl A' inferInstance
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing P.primeCompl L inferInstance
  haveI hl : IsLocalHom (algebraMap A' L) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q P (algebraMap A B) Ideal.LiesOver.over))
  let p : Ideal R := (IsLocalRing.maximalIdeal A').comap (algebraMap R A')
  haveI hF : Module.Flat (A' ⧸ p.map (algebraMap R A')) ((A' ⧸ p.map (algebraMap R A')) ⊗[A] B) := by
    let I := p.map (algebraMap R A')
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  haveI : Module.Flat A' L := by
    refine flat_of_injective_on_fibre p ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      have h0 : (IsLocalRing.maximalIdeal A').map (algebraMap A' L) ≤ IsLocalRing.maximalIdeal L :=
        ((IsLocalRing.local_hom_TFAE (algebraMap A' L)).out 0 2).mp hl
      exact (Ideal.map_mono Ideal.map_comap_le).trans h0
    · intro N' N _ _ _ _ _ _ _ _ ι hι
      exact lTensor_injective_of_fibre (A := A) (B := B) (A' := A') (L := L)
        (C := A' ⧸ p.map (algebraMap R A')) q.primeCompl ι hι
  exact .trans A A' L
end GlobalTheory.FibreFlatGen
