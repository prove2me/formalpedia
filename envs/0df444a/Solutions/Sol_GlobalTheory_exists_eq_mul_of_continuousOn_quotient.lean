-- Prove2me | solution 1 for GlobalTheory.exists_eq_mul_of_continuousOn_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:59.03869+00:00
-- url     : https://prove2.me/submissions/e87ee748-2e16-430b-9a18-a492b150e2ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqMulOfContinuousOnQuotient
import Theorems.Thm_GlobalTheory_ContinuousQuotient_exists_prime_of_not_dvd
import Theorems.Thm_GlobalTheory_ContinuousQuotient_exists_point_of_prime
import Theorems.Thm_GlobalTheory_ContinuousQuotient_dense_preimage
import Theorems.Thm_GlobalTheory_isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
import Theorems.Thm_GlobalTheory_polAV_isIntegral_of_isAlgClosed
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Topology
namespace GlobalTheory.ContinuousQuotient
private theorem valAt'_ne_zero_iff_top_le_preimage_basicOpen {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valAt' x U f ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  have hv : valAt' x U f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f) := by
    simp only [valAt', dif_pos h, valAt]
  have hb : x ⁻¹ᵁ X.basicOpen f = (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) := by
    rw [Scheme.preimage_basicOpen]
    have := (Sp ℂ).basicOpen_res (x.app U f) (homOfLE h).op
    rw [top_inf_eq] at this
    rw [← this]
    rfl
  rw [hv, hb]
  constructor
  · intro h0
    refine le_of_eq (Scheme.basicOpen_of_isUnit _ ?_).symm
    have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f)) :=
      isUnit_iff_ne_zero.2 h0
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  · intro h1 h0
    have hz : (x.appLE U ⊤ h).hom f = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom h0
      simpa using this
    rw [hz, Scheme.basicOpen_zero] at h1
    obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstance
    exact (h1 (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)).elim
private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) : valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  simp only [valAt', dif_pos h, valAt, map_mul]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
end GlobalTheory.ContinuousQuotient
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Topology
open GlobalTheory
open ContinuousQuotient
namespace GlobalTheory
theorem _root_.solution :
    ∀ (P : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (u : HolUnif P.A L P.g) (U : P.A.left.Opens) (a b : Γ(P.A.left, U)) (φ : (Fin P.g → ℂ) → ℂ), Out.Laws → IsAffineOpen U → b ≠ 0 → ContinuousOn φ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} → (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U a = φ z * valAt' (u.ex z).left U b) → ∃ c : Γ(P.A.left, U), a = c * b := by
  intro P L u U a b φ _ hU hb hφc hφ
  classical
  have hsm : Smooth P.A.hom := P.5.smooth
  obtain ⟨-, hnorm, hnoeth⟩ :=
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ P.A.left P.A.hom hsm
  have hint : IsIntegral P.A.left := polAV_isIntegral_of_isAlgClosed ℂ P
  have hne : Nonempty U := by
    rcases U.1.eq_empty_or_nonempty with h | h
    · have hU0 : U = ⊥ := SetLike.ext' h
      have : Subsingleton Γ(P.A.left, U) :=
        CommRingCat.subsingleton_of_isTerminal (P.A.left.sheaf.isTerminalOfEqEmpty hU0)
      exact absurd (Subsingleton.elim b 0) hb
    · simpa using h
  have : IsNoetherianRing Γ(P.A.left, U) := hnoeth.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(P.A.left, U) := by
    refine IsIntegrallyClosed.of_localization_maximal fun q _ hqm => ?_
    let y : PrimeSpectrum Γ(P.A.left, U) := ⟨q, hqm.isPrime⟩
    have hy : hU.fromSpec y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨y, rfl⟩
    letI := TopCat.Presheaf.algebra_section_stalk P.A.left.presheaf ⟨hU.fromSpec y, hy⟩
    have : IsLocalization.AtPrime (P.A.left.presheaf.stalk (hU.fromSpec y)) q :=
      hU.isLocalization_stalk' y hy
    obtain ⟨_, hic⟩ := hnorm (hU.fromSpec y)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv q.primeCompl
      (P.A.left.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime q)).toRingEquiv
  by_contra hnd
  obtain ⟨p, hp, s, r, hs, hr, hbs⟩ := ContinuousQuotient.exists_prime_of_not_dvd (a := a) hb
    (by rintro ⟨c, hc⟩; exact hnd ⟨c, by rw [hc, _root_.mul_comm]⟩)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hs
    have h0 : b * s = 0 := by rw [hbs, mul_zero]
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 hb
    · rw [h0]; exact p.zero_mem

  obtain ⟨x, hxU, hxs, hxp⟩ := ContinuousQuotient.exists_point_of_prime P.A hU p hs
  obtain ⟨z₀, hz₀⟩ := u.3 x

  obtain ⟨y, hyU, hyrb, -⟩ := ContinuousQuotient.exists_point_of_prime P.A hU ⊥ (s := r * b)
    (by rw [Ideal.mem_bot]; exact mul_ne_zero hr0 hb)
  obtain ⟨z₁, hz₁⟩ := u.3 y
  have hD := ContinuousQuotient.dense_preimage u (P.A.left.basicOpen (r * b))
    ⟨z₁, by rw [hz₁]; exact (valAt'_ne_zero_iff_top_le_preimage_basicOpen y.left hyU _).1 hyrb⟩
  set O : Set (Fin P.g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} with hO
  set D : Set (Fin P.g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.A.left.basicOpen (r * b)} with hDdef
  have hOo : IsOpen O := (u.8 U s).1
  have hDO : D ⊆ O := fun z hz =>
    hz.trans (Scheme.Hom.preimage_mono _ (P.A.left.basicOpen_le (r * b)))
  have hz₀O : z₀ ∈ O := by
    change ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U
    rw [hz₀]; exact hxU
  let G : (Fin P.g → ℂ) → ℂ := fun z =>
    valAt' (u.ex z).left U s - φ z * valAt' (u.ex z).left U r
  have hG : ContinuousWithinAt G O z₀ :=
    (((u.8 U s).2.continuousOn).sub (hφc.mul (u.8 U r).2.continuousOn)) z₀ hz₀O
  have hG0 : ∀ z ∈ O ∩ D, G z = 0 := by
    rintro z ⟨hzO, hzD⟩
    have hrb := (valAt'_ne_zero_iff_top_le_preimage_basicOpen (u.ex z).left hzO (r * b)).2 hzD
    rw [valAt'_mul_of_top_le_preimage_open _ hzO] at hrb
    have hbz : valAt' (u.ex z).left U b ≠ 0 := right_ne_zero_of_mul hrb
    have e1 := congrArg (valAt' (u.ex z).left U) hbs
    rw [valAt'_mul_of_top_le_preimage_open _ hzO, valAt'_mul_of_top_le_preimage_open _ hzO, hφ z hzO] at e1
    have e2 : valAt' (u.ex z).left U b * G z = 0 := by
      simp only [G]
      rw [_root_.mul_sub, e1]
      ring
    exact (mul_eq_zero.1 e2).resolve_left hbz
  have hcl : z₀ ∈ closure (O ∩ D) := hD.open_subset_closure_inter hOo hz₀O
  have hGz : G z₀ ∈ closure (G '' (O ∩ D)) := (hG.mono Set.inter_subset_left).mem_closure_image hcl
  have hsub : G '' (O ∩ D) ⊆ {0} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hG0 z hz
  have hGz0 : G z₀ = 0 := by
    simpa using closure_mono hsub hGz
  apply hxs
  have hrx : valAt' x.left U r = 0 := hxp r hr
  simp only [G, hz₀, hrx, mul_zero, sub_zero] at hGz0
  exact hGz0
end GlobalTheory
