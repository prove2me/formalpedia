-- Prove2me | solution 1 for GlobalTheory.exists_etale_point_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:33.74845+00:00
-- url     : https://prove2.me/submissions/16ffe462-75b7-4c9f-9225-63c6bf7fe060

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Theorems.Thm_GlobalTheory_range_subset_opens_of_isLocalRing
import Theorems.Thm_GlobalTheory_exists_isAffineOpen_pair
import Theorems.Thm_GlobalTheory_algebraMap_eq_zero_iff_mem_maximalIdeal
import Theorems.Thm_GlobalTheory_exists_etale_algHom_lift_of_smooth
import Theorems.Thm_GlobalTheory_nonempty_algHom_of_smooth_of_isSepClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (B : Type u) [CommRing B] [IsLocalRing B]
    (K : Type*) [Field K] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K] [IsSepClosed K]
    (s : Spec (.of B) ⟶ S) (O : X.Opens) (hO : ∃ x ∈ O, f x = s (closedPoint B)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (_ : W →ₐ[B] K)
      (y : Spec (.of W) ⟶ X),
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B W)) ≫ s ∧ Set.range y ⊆ O := by
  obtain ⟨x, hxO, hfx⟩ := hO
  obtain ⟨U, V, hU, hV, hVU, hVO, hxV⟩ := _root_.GlobalTheory.exists_isAffineOpen_pair f x hxO
  have hsm := HasRingHomProperty.appLE @Smooth f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have hsU : Set.range s.base ⊆ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec]; exact _root_.GlobalTheory.range_subset_opens_of_isLocalRing s (hfx ▸ hVU hxV)
  set b : Γ(S, U) ⟶ CommRingCat.of B :=
    Spec.preimage (IsOpenImmersion.lift hU.fromSpec s hsU) with hb_def
  have hb : Spec.map b ≫ hU.fromSpec = s := by
    rw [hb_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  obtain ⟨P, hP⟩ : x ∈ Set.range hV.fromSpec.base := by rw [hV.range_fromSpec]; exact hxV
  have hPm : Ideal.comap (f.appLE U V hVU).hom P.asIdeal = Ideal.comap b.hom (maximalIdeal B) := by
    have e : hU.fromSpec.base ((Spec.map (f.appLE U V hVU)).base P) =
        hU.fromSpec.base ((Spec.map b).base (closedPoint B)) := by
      change (Spec.map (f.appLE U V hVU) ≫ hU.fromSpec).base P = (Spec.map b ≫ hU.fromSpec).base _
      rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, hb]
      change f.base (hV.fromSpec.base P) = _
      rw [hP, hfx]
    exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective e)
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(S, U) B := b.hom.toAlgebra
  letI : Algebra Γ(S, U) K := ((algebraMap B K).comp b.hom).toAlgebra
  haveI : IsScalarTower Γ(S, U) B K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Smooth Γ(S, U) Γ(X, V) := hsm
  haveI := P.isPrime
  obtain ⟨φ⟩ := _root_.GlobalTheory.nonempty_algHom_of_smooth_of_isSepClosed (K := K) P.asIdeal (by
    change Ideal.comap (f.appLE U V hVU).hom P.asIdeal = _
    rw [hPm]
    ext r
    change b.hom r ∈ maximalIdeal B ↔ algebraMap B K (b.hom r) = 0
    exact (_root_.GlobalTheory.algebraMap_eq_zero_iff_mem_maximalIdeal (b.hom r)).symm)
  obtain ⟨W, iW, iBW, hE, ψ, ε, hψ, -⟩ := _root_.GlobalTheory.exists_etale_algHom_lift_of_smooth (B := B) (K := K) φ
  refine ⟨W, iW, iBW, hE, ε, Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, ?_, ?_⟩
  · have e : f.appLE U V hVU ≫ CommRingCat.ofHom ψ = b ≫ CommRingCat.ofHom (algebraMap B W) := by
      ext r
      exact congrArg (fun k => k r) hψ
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← hb,
      ← Spec.map_comp_assoc, e, Spec.map_comp_assoc]
  · rintro _ ⟨z, rfl⟩
    apply hVO
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ)).base z, rfl⟩
end _root_.GlobalTheory
end GlobalTheory
