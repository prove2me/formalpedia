-- Prove2me | solution 1 for GlobalTheory.residueField_isAlgebraic_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:28.72327+00:00
-- url     : https://prove2.me/submissions/a6fd68e4-7abd-4a4a-8c3b-a94afc6d9e00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {A B : Type} [CommRing A] [CommRing B] (g : A →+* B), g.Etale →
    ∀ (P : Ideal B) [P.IsPrime],
    @Algebra.IsAlgebraic (P.comap g).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (P.comap g) P g rfl).toAlgebra := by
  intro A B _ _ g hg P _
  letI := g.toAlgebra
  have hE : Algebra.Etale A B := RingHom.etale_algebraMap.mp hg
  haveI : P.LiesOver (P.comap g) := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver (P.comap g) P
  haveI : Localization.AtPrime.IsLiesOverAlgebra (P.comap g) P := ⟨rfl⟩
  haveI : Algebra.EssFiniteType A B := inferInstance
  haveI : Algebra.IsUnramifiedAt A P := inferInstance
  have hsep : Algebra.IsSeparable (P.comap g).ResidueField P.ResidueField := inferInstance
  have halg := hsep.isAlgebraic
  convert halg using 1
  apply Algebra.algebra_ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  induction y using Localization.induction_on with
  | H y =>
    obtain ⟨a, s⟩ := y
    simp [Ideal.ResidueField.map, RingHom.algebraMap_toAlgebra, Localization.AtPrime.algebraOfLiesOver, Localization.mk_eq_mk']
end GlobalTheory
