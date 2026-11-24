-- Prove2me | solution 1 for GlobalTheory.HolHom.eq_of_fderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:22:51.754916+00:00
-- url     : https://prove2.me/submissions/da7c43cc-d6a7-442b-a02e-36200b8c3853

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt
import Theorems.Thm_GlobalTheory_HolHom_holAt_const
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt_constVec_iff
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt_const
import Theorems.Thm_GlobalTheory_HolHom_HolAt_exists_isDerivAt
import Theorems.Thm_GlobalTheory_HolHom_eq_of_isDerivAt_constVec
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_mul
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_inv
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_over
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt_mul
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt_inv
import Theorems.Thm_GlobalTheory_HolHom_map_zero_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}}
variable {G : Over S} [GrpObj G]
variable {y : Sp ℂ ⟶ S}
namespace GlobalTheory.HolHom
theorem _root_.solution {e e' : V → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w) (hol : IsHolTo Set.univ (fun z => (e z).left))
    (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd : ∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 = fderiv ℂ (fun z => valAt' (e' z).left U f) 0) : e = e' := by
  have h0 : e 0 = e' 0 := (map_zero_eq_one he).trans (map_zero_eq_one he').symm
  let j : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have hj : ∀ (x : Over.mk y ⟶ G) (z w : V), IsDerivAt (fun _ : V => x.left) z w (j ≫ x).left :=
    fun x z w => isDerivAt_const x.left z w
  have hc : ∀ x : Over.mk y ⟶ G, IsHolTo Set.univ (fun _ : V => x.left) :=
    fun x => isHolTo_of_holAt isOpen_univ fun z _ => holAt_const _ _
  have hdh := isHolTo_mul (y := fun _ => y) hol (isHolTo_inv (y := fun _ => y) hol')
  have at0 := fun {c : V → (Sp ℂ ⟶ G.left)} (h : IsHolTo Set.univ c) (z : V) => holAt_of_isHolTo h (Set.mem_univ z)
  have key : ∀ z w, IsDerivAt (fun t => (e t * (e' t)⁻¹).left) z w (constVec (e z * (e' z)⁻¹).left) := by
    intro z w
    obtain ⟨u, hu⟩ := (at0 hol 0).exists_isDerivAt w
    have hu' : IsDerivAt (fun t => (e' t).left) 0 w u :=
      ⟨hu.1.trans (congrArg (·.left) h0), fun U hU f => by
        have hU' : ⊤ ≤ (e 0).left ⁻¹ᵁ U := h0 ▸ hU
        rw [hu.2 U hU' f, hd U hU' f]⟩
    let v : epsPt y ⟶ G := Over.homMk u hu.over
    have h1 := isDerivAt_mul (at0 hol 0) (at0 (isHolTo_inv (y := fun _ => y) hol') 0) (v := v) hu
      (isDerivAt_inv (v := v) hu')
    have h2 := isDerivAt_mul (at0 (hc (e z)) 0) (at0 hdh 0) (hj _ 0 w) h1
    have h3 := isDerivAt_mul (at0 (isHolTo_mul (y := fun _ => y) (hc (e z)) hdh) 0) (at0 (hc (e' z)⁻¹) 0) h2 (hj _ 0 w)
    have h4 : ∀ t, e z * (e t * (e' t)⁻¹) * (e' z)⁻¹ = e (z + t) * (e' (z + t))⁻¹ := fun t => by
      rw [he, he', mul_inv_rev]; simp only [_root_.mul_assoc]
    rw [mul_inv_cancel, _root_.mul_one, ← MonObj.comp_mul] at h3
    simp only [h4] at h3
    have h5 : IsDerivAt (fun t => (e (z + t) * (e' (z + t))⁻¹).left) 0 w
        (constVec (e (z + 0) * (e' (z + 0))⁻¹).left) := by
      rw [add_zero]; exact h3
    refine (isDerivAt_constVec_iff (c := fun t => (e t * (e' t)⁻¹).left)).2 fun U hU f => ?_
    have h6 := (isDerivAt_constVec_iff (c := fun t => (e (z + t) * (e' (z + t))⁻¹).left)).1 h5 U
      (by simpa only [add_zero] using hU) f
    rwa [fderiv_comp_add_left (f := fun t => valAt' (e t * (e' t)⁻¹).left U f), add_zero] at h6
  funext z
  have := eq_of_isDerivAt_constVec (at0 hdh) key z 0
  rw [← mul_inv_eq_one]
  ext1
  rw [this, h0, mul_inv_cancel]
end GlobalTheory.HolHom
