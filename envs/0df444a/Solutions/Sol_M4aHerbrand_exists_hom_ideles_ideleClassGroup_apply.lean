-- Prove2me | solution 1 for M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5b9cf7d9-2c0a-5354-9e8b-77a642c1b1e1

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent.classAct_mk repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply principalIdeles IdeleClassGroup IdeleGaloisDescent"
namespace PiProof
p2m_open "M4aHerbrand"

variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

omit [NumberField E] in

theorem mk_smul (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : (IdeleClassGroup (𝓞 F) F)), g • c = D.classAct g c)
    (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ) :
    QuotientGroup.mk' (principalIdeles (𝓞 F) F) (g • x) = g • QuotientGroup.mk' (principalIdeles (𝓞 F) F) x := by
  rw [hactI, hact, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, IdeleGaloisDescent.classAct_mk]

end M4aHerbrand.PiProof

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (hact : ∀ (g : F ≃ₐ[E] F) (c : (IdeleClassGroup (𝓞 F) F)), g • c = D.classAct g c) :
    ∃ π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F),
      ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : (IdeleClassGroup (𝓞 F) F)) := by
  exact ⟨M4aHerbrand.repHomOfMulEquivariant (QuotientGroup.mk' (principalIdeles (𝓞 F) F))
      (M4aHerbrand.PiProof.mk_smul D hactI hact),
    fun x => M4aHerbrand.repHomOfMulEquivariant_hom_apply _ _ (Additive.ofMul x)⟩

end S_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply
end P2MW
export P2MW.S_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply (solution)
