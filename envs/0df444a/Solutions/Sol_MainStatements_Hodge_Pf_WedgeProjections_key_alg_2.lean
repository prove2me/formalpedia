-- Prove2me | solution 2 for MainStatements.Hodge.Pf.WedgeProjections.key_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:20.236489+00:00
-- url     : https://prove2.me/submissions/961e5acd-c4d6-4f35-a2d0-78ee34c2c004

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianWedgeProducts_ThetaMulti
import Theorems.Thm_P2M_MainStatements_Hodge_Pf_WedgeProjections_theta__Multi_85cb7f90be53

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.WedgeProjections
namespace MainStatements.Hodge.Pf.WedgeProjections
theorem _root_.solution {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V) (h11 : r₁ ∘ₗ p = LinearMap.id) (h12 : r₁ ∘ₗ q = 0)
    (h21 : r₂ ∘ₗ p = 0) (h22 : r₂ ∘ₗ q = LinearMap.id) (t : ⋀[K]^2 V)
    (ht : exteriorPower.map 2 (p + q) t = exteriorPower.map 2 p t + exteriorPower.map 2 q t) : t = 0 := by
  classical
  have e11 : ∀ x, r₁ (p x) = x := fun x => LinearMap.congr_fun h11 x
  have e12 : ∀ x, r₁ (q x) = 0 := fun x => LinearMap.congr_fun h12 x
  have e21 : ∀ x, r₂ (p x) = 0 := fun x => LinearMap.congr_fun h21 x
  have e22 : ∀ x, r₂ (q x) = x := fun x => LinearMap.congr_fun h22 x
  have hkill : ∀ g : Fin 2 → Module.Dual K V,
      exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 g) t = 0 := by
    intro g
    have hA : (theta r₁ r₂ g) ∘ₗ exteriorPower.map 2 (p + q) =
        exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 g) := by
      apply exteriorPower.linearMap_ext
      ext v
      simp [theta_ιMulti, exteriorPower.map_apply_ιMulti, e11, e12, e21, e22, Matrix.det_fin_two]
    have hB : (theta r₁ r₂ g) ∘ₗ exteriorPower.map 2 p = 0 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp [theta_ιMulti, exteriorPower.map_apply_ιMulti, e21]
    have hC : (theta r₁ r₂ g) ∘ₗ exteriorPower.map 2 q = 0 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp [theta_ιMulti, exteriorPower.map_apply_ιMulti, e12]
    have h0 := congrArg (theta r₁ r₂ g) ht
    rw [map_add] at h0
    have h1 := LinearMap.congr_fun hA t
    have h2 := LinearMap.congr_fun hB t
    have h3 := LinearMap.congr_fun hC t
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 h2 h3
    rw [← h1, h0, h2, h3, add_zero]
  obtain ⟨I, b⟩ := Module.Free.exists_basis K V
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  apply (b.exteriorPower 2).ext_elem
  intro s
  rw [exteriorPower.basis_repr_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact hkill _
end MainStatements.Hodge.Pf.WedgeProjections
