-- Prove2me | solution 1 for GlobalTheory.HolHom.existsUnique_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:41.704163+00:00
-- url     : https://prove2.me/submissions/9e852e02-49d6-424e-bed7-6725a2991026

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_HolAt_precomp
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt0_iff
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_HolAt_exists_isDerivAt
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_over
import Theorems.Thm_GlobalTheory_HolHom_map_zero_eq_one
import Theorems.Thm_GlobalTheory_HolHom_eq_of_fderiv_eq
import Theorems.Thm_GlobalTheory_HolHom_eq_of_forall_fderiv_eq

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} {g : ℕ}
namespace GlobalTheory.HolHom
theorem _root_.solution [FiniteDimensional ℂ V] [GrpObj G] {y : Sp ℂ ⟶ S} {e : V → (Over.mk y ⟶ G)}
    {e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w) (hol : IsHolTo Set.univ (fun z => (e z).left))
    (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (hdiff : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = e' (h z) := by
  have h0 : e 0 = e' 0 := (map_zero_eq_one he).trans (map_zero_eq_one he').symm
  have hA := holAt_of_isHolTo hol (Set.mem_univ 0)
  have hA' := holAt_of_isHolTo hol' (Set.mem_univ 0)
  have hex : ∀ z : V, ∃ w, ∀ U : G.left.Opens, ⊤ ≤ (e' 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun t => valAt' (e' t).left U f) 0 w = fderiv ℂ (fun t => valAt' (e t).left U f) 0 z := by
    intro z
    obtain ⟨u, hu⟩ := hA.exists_isDerivAt z
    obtain ⟨w, hw, -⟩ := hdiff (Over.homMk u hu.over) (hu.1.trans (congrArg (·.left) h0))
    have hw' := (isDerivAt0_iff _ _ _).1 hw
    exact ⟨w, fun U hU f => (hw'.2 U hU f).symm.trans (hu.2 U (h0 ▸ hU :) f)⟩
  choose k hk using hex
  have chain : ∀ (h : V →ₗ[ℂ] (Fin g → ℂ)) (U : G.left.Opens), ⊤ ≤ (e' 0).left ⁻¹ᵁ U → ∀ (f : Γ(G.left, U)) (z : V),
      fderiv ℂ (fun t => valAt' (e' (h t)).left U f) 0 z = fderiv ℂ (fun t => valAt' (e' t).left U f) 0 (h z) := by
    intro h U hU f z
    have h1 : HasFDerivAt (fun t => valAt' (e' t).left U f) (fderiv ℂ (fun t => valAt' (e' t).left U f) 0)
        (LinearMap.toContinuousLinearMap h 0) := by
      rw [map_zero]; exact ((hA' U hU).2 f).hasFDerivAt
    exact congrArg (· z) (h1.comp 0 (LinearMap.toContinuousLinearMap h).hasFDerivAt).fderiv
  let h : V →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := k
      map_add' := fun z z' => eq_of_forall_fderiv_eq hA' hdiff fun U hU f => by
        rw [map_add, hk _ U hU, hk _ U hU, hk _ U hU, map_add]
      map_smul' := fun a z => eq_of_forall_fderiv_eq hA' hdiff fun U hU f => by
        rw [map_smul, hk _ U hU, hk _ U hU, map_smul, RingHom.id_apply] }
  refine ⟨h, congrFun (eq_of_fderiv_eq (e' := fun z => e' (h z)) he (fun z w => by rw [map_add, he']) hol ?_ ?_),
    fun h' hh' => LinearMap.ext fun z => eq_of_forall_fderiv_eq hA' hdiff fun U hU f => ?_⟩
  · exact isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_isHolTo hol' (Set.mem_univ (h z))).precomp
      (LinearMap.toContinuousLinearMap h).differentiableAt
  · intro U hU f
    ext z
    rw [chain h U (h0 ▸ hU :) f z]
    exact (hk z U (h0 ▸ hU :) f).symm
  · rw [← chain h' U hU f z]
    simp only [← hh']
    exact (hk z U hU f).symm
end GlobalTheory.HolHom
