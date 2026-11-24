-- Prove2me | solution 1 for GlobalTheory.FibreRegular.quot_localization_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:52.630864+00:00
-- url     : https://prove2.me/submissions/32ce491e-68ed-4a31-9828-ac369344e92b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothFibreRegularLocalRing
import Theorems.Thm_GlobalTheory_isRegularRing_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.FibreRegular
namespace GlobalTheory.FibreRegular
theorem _root_.solution (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal R) [p.IsPrime] (n : Ideal S) [n.IsPrime]
    (hn : n.comap (algebraMap R S) = p) :
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime n))) := by
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  let N : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P} := ⟨⟨n, inferInstance⟩, PrimeSpectrum.ext hn⟩
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (p.Fiber S),
      q.asIdeal.comap (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)) = n :=
    ⟨PrimeSpectrum.preimageEquivFiber R S P N,
      congrArg (fun z => z.1.asIdeal) ((PrimeSpectrum.preimageEquivFiber R S P).symm_apply_apply N)⟩
  subst hq
  have hreg : IsRegularRing (p.Fiber S) := GlobalTheory.isRegularRing_of_smooth p.ResidueField (p.Fiber S)
  have := isRegularRing_iff.mp hreg q.asIdeal
  exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ p q.asIdeal).toRingEquiv
end GlobalTheory.FibreRegular
