-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.smoothOfRelativeDimension_of_isRegluingBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/57bb5d91-4177-50ea-b676-70b6046503ca

import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S]
    (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (n : ℕ) [SmoothOfRelativeDimension n D₀.f] :
    SmoothOfRelativeDimension n D.f := by
  obtain ⟨-, -, ιD, hιopen, hιf, hιsurj, -, -⟩ := hD
  haveI : ∀ i, IsOpenImmersion (ιD i) := hιopen
  let 𝒱 : D.A.OpenCover := Scheme.Cover.mkOfCovers 𝒰.ι (fun i => (↑(𝒰.U i) : Scheme.{0})) ιD hιsurj
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension n) 𝒱]
  intro i
  show SmoothOfRelativeDimension n (ιD i ≫ D.f)
  rw [hιf i]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension n) inferInstance (𝒰.U i).ι

end S_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy (solution)
