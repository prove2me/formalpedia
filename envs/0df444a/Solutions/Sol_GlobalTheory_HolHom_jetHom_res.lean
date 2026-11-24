-- Prove2me | solution 1 for GlobalTheory.HolHom.jetHom_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:12.144073+00:00
-- url     : https://prove2.me/submissions/06f19648-8f53-415e-bd28-28bc2e491440

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_valR_res

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (w : V) {U U' : X.Opens} (hle : U' ≤ U)
    (hU : ⊤ ≤ c z ⁻¹ᵁ U) (hU' : ⊤ ≤ c z ⁻¹ᵁ U') (f : Γ(X, U)) :
    jetHom h w U' hU' ((X.presheaf.map (homOfLE hle).op).hom f) = jetHom h w U hU f := by
  have : (fun t => valAt' (c t) U' ((X.presheaf.map (homOfLE hle).op).hom f)) =ᶠ[𝓝 z] fun t => valAt' (c t) U f :=
    (h U' hU').1.mono fun t ht => valR_res _ hle f ht
  have h0 := this.self_of_nhds
  beta_reduce at h0
  simp only [jetHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [this.fderiv_eq, h0]
end GlobalTheory.HolHom
