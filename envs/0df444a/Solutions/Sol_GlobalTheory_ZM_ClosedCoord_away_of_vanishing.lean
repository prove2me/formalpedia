-- Prove2me | solution 1 for GlobalTheory.ZM.ClosedCoord.away_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:04.54219+00:00
-- url     : https://prove2.me/submissions/c7289d5f-a2e2-4592-a8b4-1a586c8912c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubsch
import Theorems.Thm_GlobalTheory_ZM_ClosedCoord_exists_homogenisation
import Theorems.Thm_GlobalTheory_ZM_ClosedCoord_eq_zero_of_away
import Theorems.Thm_GlobalTheory_ZM_ClosedCoord_awayUnit_coe
import Theorems.Thm_GlobalTheory_ZM_ClosedCoord_awayUnit_inv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ClosedCoord
open MvPolynomial
namespace GlobalTheory.ZM.ClosedCoord
theorem _root_.solution {R σ : Type} [CommRing R] [Finite σ]
    (P : ∀ (R' : Type) [CommRing R'], (R →+* R') → (σ → R') → Prop)
    (bc : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (φ : R' →+* R'') β v, P R' β v → P R'' (φ.comp β) (fun j => φ (v j)))
    (sc : ∀ (R' : Type) [CommRing R'] (u : R'ˣ) β v, P R' β v → P R' β (fun j => u * v j))
    (uni : ∀ (R' : Type) [CommRing R'] β v, P R' β v → Ideal.span (Set.range v) = ⊤)
    (ch : ∀ a, ∃ K : Ideal (MvPolynomial σ R), X a - 1 ∈ K ∧ ∀ (R' : Type) [CommRing R'] β w, w a = 1 →
      (P R' β w ↔ ∀ F ∈ K, eval₂ β w F = 0))
    (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R')
    (hv : ∀ F, (∀ (R'' : Type) [CommRing R''] β' w, P R'' β' w → eval₂ β' w F = 0) → eval₂ β v F = 0) (a : σ) :
    P (Localization.Away (v a)) ((algebraMap R' _).comp β) (fun j => algebraMap R' _ (v j)) := by
  classical
  choose K hK1 hK using ch
  have := Fintype.ofFinite σ

  have nrm : ∀ (A : Type) [CommRing A] β₀ (t : σ → A) (b : σ), P A β₀ t → ∀ F ∈ K b,
      eval₂ ((algebraMap A (Localization.Away (t b))).comp β₀)
        (fun j => ((awayUnit (t b))⁻¹ : (Localization.Away (t b))ˣ) * algebraMap A _ (t j)) F = 0 := by
    intro A _ β₀ t b ht
    exact (hK b _ _ _ (awayUnit_inv_mul _)).1 (sc _ _ _ _ (bc _ _ _ _ _ ht))
  suffices h : P (Localization.Away (v a)) ((algebraMap R' _).comp β)
      (fun j => ((awayUnit (v a))⁻¹ : (Localization.Away (v a))ˣ) * algebraMap R' _ (v j)) by
    have h2 := sc _ (awayUnit (v a)) _ _ h
    simpa only [Units.mul_inv_cancel_left] using h2
  refine (hK a _ _ _ (awayUnit_inv_mul _)).2 fun F hF => ?_
  obtain ⟨d, G, hG, hGF⟩ := exists_homogenisation a F
  have step : ∀ b, ∃ n : ℕ, X a ^ n * G ∈ K b := by
    intro b
    have hP : P (MvPolynomial σ R ⧸ K b) ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk _ (X j)) := by
      refine (hK b _ _ _ ?_).2 fun F' hF' => ?_
      · rw [← map_one (Ideal.Quotient.mk (K b)), Ideal.Quotient.eq]; exact hK1 b
      · have := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X F').symm
        rw [eval₂_eta, Ideal.Quotient.eq_zero_iff_mem.2 hF'] at this
        exact this
    have h1 := nrm _ _ _ a hP F hF
    rw [← hGF _ _ _ (awayUnit_inv_mul _), hG, (Units.isUnit _).pow d |>.mul_right_eq_zero] at h1
    have h2 := eval₂_comp_left (algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))))
      ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk (K b) (X j)) G
    have h3 := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X G)
    rw [eval₂_eta] at h3
    have h4 : algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))) (Ideal.Quotient.mk (K b) G) = 0 := by
      rw [h3]; exact h2.trans h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk (K b) (X a))) _ _).1 h4
    refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hn
  choose n hn using step
  have hH : eval₂ β v (X a ^ (∑ b, n b) * G) = 0 := by
    refine hv _ fun A _ β₀ t ht => eq_zero_of_away t (uni _ _ _ ht) _ fun b => ?_
    have hm : X a ^ (∑ b, n b) * G ∈ K b := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      rw [hm, pow_add, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hn b)
    have h1 := nrm _ _ _ b ht _ hm
    rw [eval₂_comp_left]
    rw [eval₂_mul, eval₂_pow, eval₂_X, hG, mul_pow, _root_.mul_mul_mul_comm, ← pow_add,
      (Units.isUnit _).pow _ |>.mul_right_eq_zero] at h1
    rw [eval₂_mul, eval₂_pow, eval₂_X]
    exact h1
  have h5 := congrArg (algebraMap R' (Localization.Away (v a))) hH
  rw [eval₂_mul, eval₂_pow, eval₂_X, map_mul, map_pow, map_zero, ← awayUnit_coe,
    (Units.isUnit _).pow _ |>.mul_right_eq_zero, eval₂_comp_left] at h5
  rw [← hGF _ _ _ (awayUnit_inv_mul _), hG]
  exact mul_eq_zero_of_right _ h5
end GlobalTheory.ZM.ClosedCoord
