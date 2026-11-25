-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.toSection_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:29.572206+00:00
-- url     : https://prove2.me/submissions/5a5b4846-0bbd-47e6-93fa-831099ddd9ea

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_mul_mem_awayDeg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_mk_mem_awayDeg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_exists_val_eq_of_mem_awayDeg_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mem_awayDeg_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_isLocallyFraction_mul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_isLocallyFraction_locMap
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_exists_section_of_isLocallyFraction_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_isLocallyFraction_val
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution {f u g : A} {e : ℕ} (hu : u ∈ 𝒜 1) (hg : g ∈ 𝒜 e)
    (hfug : f = u * g) (hf : f ∈ 𝒜 (e + 1)) (k : ℤ) :
    Function.Bijective (toSection hf (Nat.succ_pos e) k) := by
  set hd := Nat.succ_pos e
  have hk : (k.toNat : ℤ) - ((-k).toNat : ℤ) = k := by omega

  set c : Localization.Away f := Localization.mk (u ^ (-k).toNat * g ^ k.toNat) (fpow f k.toNat)
  set c' : Localization.Away f := Localization.mk (u ^ k.toNat * g ^ (-k).toNat) (fpow f (-k).toNat)
  have hc : c ∈ awayDeg 𝒜 hf hd (-k) := by
    refine mk_mem_awayDeg hf hd (j := (-k).toNat + k.toNat * e) ?_ ?_
    · have h1 := SetLike.pow_mem_graded (-k).toNat hu
      have h2 := SetLike.pow_mem_graded k.toNat hg
      have := SetLike.mul_mem_graded h1 h2
      simpa [smul_eq_mul, mul_comm] using this
    · push_cast; linarith
  have hc' : c' ∈ awayDeg 𝒜 hf hd k := by
    refine mk_mem_awayDeg hf hd (j := k.toNat + (-k).toNat * e) ?_ ?_
    · have h1 := SetLike.pow_mem_graded k.toNat hu
      have h2 := SetLike.pow_mem_graded (-k).toNat hg
      have := SetLike.mul_mem_graded h1 h2
      simpa [smul_eq_mul, mul_comm] using this
    · push_cast; linarith
  have hcc' : c * c' = 1 := by
    rw [Localization.mk_mul, ← fpow_add, ← Localization.mk_self (fpow f (k.toNat + (-k).toNat))]
    congr 1
    rw [coe_fpow, hfug]
    ring
  have hloc : ∀ x : Proj.basicOpen 𝒜 f,
      locMap x.1 (nmem_of_mem x) c * locMap x.1 (nmem_of_mem x) c' = 1 := fun x => by
    rw [← map_mul, hcc', map_one]
  have hiso := (Proj.basicOpenIsoAway 𝒜 f hf hd).commRingCatIsoToRingEquiv.bijective
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : ∀ x : Proj.basicOpen 𝒜 f, locMap x.1 (nmem_of_mem x) z.1 = 0 := fun x =>
      congrFun (congrArg val hz) x
    have hw : c * z.1 ∈ awayDeg 𝒜 hf hd 0 := by
      have := mul_mem_awayDeg hf hd hc z.2
      rwa [neg_add_cancel] at this
    obtain ⟨z₀, hz₀⟩ := exists_val_eq_of_mem_awayDeg_zero hf hd hw
    have h0 : (Proj.awayToSection 𝒜 f).hom z₀ = 0 := by
      apply Subtype.ext
      funext x
      apply HomogeneousLocalization.val_injective
      have h := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f z₀ x
      have h' : locMap x.1 (nmem_of_mem x) z₀.val = 0 := by
        rw [hz₀, map_mul, hz' x, mul_zero]
      exact h.trans (h'.trans HomogeneousLocalization.val_zero.symm)
    have hz0 : z₀ = 0 := by
      apply hiso.1
      exact h0.trans (map_zero _).symm
    have hcz : c * z.1 = 0 := by rw [← hz₀, hz0, HomogeneousLocalization.val_zero]
    apply Subtype.ext
    change z.1 = 0
    calc z.1 = c' * (c * z.1) := by rw [← mul_assoc, mul_comm c', hcc', one_mul]
      _ = 0 := by rw [hcz, mul_zero]
  · intro s
    have ht := isLocallyFraction_mul (neg_add_cancel k) (isLocallyFraction_locMap hf hd hc)
      (isLocallyFraction_val s)
    obtain ⟨t', ht'⟩ := exists_section_of_isLocallyFraction_zero _ ht
    obtain ⟨z₀, hz₀⟩ := hiso.2 t'
    have hz₀' : (Proj.awayToSection 𝒜 f).hom z₀ = t' := hz₀
    have hmem : c' * z₀.val ∈ awayDeg 𝒜 hf hd k := by
      have := mul_mem_awayDeg hf hd hc' (val_mem_awayDeg_zero hf hd z₀)
      rwa [add_zero] at this
    refine ⟨⟨c' * z₀.val, hmem⟩, ?_⟩
    subst hz₀'
    apply GroundTheory.Arith.SchemeCoh.ProjTwist.ext
    funext x
    have e1 : locMap x.1 (nmem_of_mem x) z₀.val =
        (((Proj.awayToSection 𝒜 f).hom z₀).1 x).val :=
      (ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f z₀ x).symm
    have e2 : (((Proj.awayToSection 𝒜 f).hom z₀).1 x).val =
        locMap x.1 (nmem_of_mem x) c * val s x := ht' x
    show locMap x.1 (nmem_of_mem x) (c' * z₀.val) = val s x
    rw [map_mul, e1, e2]
    linear_combination (val s x) * hloc x
end GroundTheory.Arith.SchemeCoh.ProjTwist
