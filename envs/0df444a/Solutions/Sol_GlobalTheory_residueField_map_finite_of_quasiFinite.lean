-- Prove2me | solution 1 for GlobalTheory.residueField_map_finite_of_quasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:31.081387+00:00
-- url     : https://prove2.me/submissions/a2fc379e-ed84-4983-be49-68c69911b3b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (h : f.QuasiFinite) :
    (IsLocalRing.ResidueField.map f).Finite := by
  algebraize [f]
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Algebra.QuasiFinite R (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.of_surjective_algHom (IsScalarTower.toAlgHom R S _)
      IsLocalRing.residue_surjective
  have : Algebra.QuasiFinite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    .of_restrictScalars R _ _
  have hfin : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp this
  have heq : IsLocalRing.ResidueField.map f =
      algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr hfin
end GlobalTheory
