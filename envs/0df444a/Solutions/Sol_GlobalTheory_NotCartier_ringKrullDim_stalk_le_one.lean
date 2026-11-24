-- Prove2me | solution 1 for GlobalTheory.NotCartier.ringKrullDim_stalk_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:39.196625+00:00
-- url     : https://prove2.me/submissions/690f8fd7-438e-4f7c-9d15-6984c394acd7

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerNeBotAndNotEffCartier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
noncomputable section
open GlobalTheory GlobalTheory.NotCartier
namespace GlobalTheory.NotCartier
theorem _root_.solution {X : Scheme.{0}} [IsLocallyNoetherian X] (J : X.IdealSheafData) (x : X)
    (hx : x ∈ J.support) (hmin : ∀ z ∈ J.support, z ⤳ x → z = x) (V : X.affineOpens) (hxV : x ∈ V.1)
    (hP : (J.ideal V).IsPrincipal) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  haveI := IsLocallyNoetherian.component_noetherian V
  have hV : IsAffineOpen V.1 := V.2
  let p := hV.primeIdealOf ⟨x, hxV⟩
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hp : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hsupp : ∀ q : Spec Γ(X, V.1), hV.fromSpec q ∈ J.support ↔ J.ideal V ≤ q.asIdeal := by
    intro q
    have hqV : hV.fromSpec q ∈ V.1 := (Set.ext_iff.1 hV.range_fromSpec _).1 ⟨q, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hqV]
    change q ∈ hV.fromSpec ⁻¹' X.zeroLocus (J.ideal V : Set Γ(X, V.1)) ↔ _
    rw [hV.fromSpec_preimage_zeroLocus]
    exact Iff.rfl
  have hmem : p.asIdeal ∈ (J.ideal V).minimalPrimes := by
    refine ⟨⟨p.isPrime, (hsupp p).1 (hp ▸ hx)⟩, fun q hq hqp => ?_⟩
    let y : PrimeSpectrum Γ(X, V.1) := ⟨q, hq.1⟩
    have hsp : hV.fromSpec y ⤳ x := by
      have := ((PrimeSpectrum.le_iff_specializes y p).1 hqp).map hV.fromSpec.continuous
      rwa [hp] at this
    have hyx : hV.fromSpec y = hV.fromSpec p := (hmin _ ((hsupp y).2 hq.2) hsp).trans hp.symm
    have := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hyx)
    exact le_of_eq this.symm
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)]
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem
end GlobalTheory.NotCartier
