-- Prove2me | solution 1 for M4aHerbrand.exists_hom_res_inf_decomp_ideles_adicCompletion_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0c45623e-aa58-5e6b-940f-a04daef48b3f

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_M4aHerbrand_exists_hom_res_inf_decomp_ideles_adicCompletion_apply
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_hom_res_inf_decomp_ideles_adicCompletion_apply.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart coe_finPart_apply IdeleGaloisDescent subsingleton_ideleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum"
namespace PrHProof
p2m_open "M4aHerbrand"

open scoped NumberField.PlaceTransport

variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

omit [NumberField E] in
theorem smul_eq_of_mem_decomp (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F)
    (hσ : σ ∈ NumberField.PlaceDecomp.decomp E F w) : σ • w = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, ← HeightOneSpectrum.intValuation_lt_one_iff_mem,
    ← HeightOneSpectrum.intValuation_lt_one_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
    ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  change w.valuation F (σ⁻¹ (algebraMap (𝓞 F) F x)) < 1 ↔ w.valuation F (algebraMap (𝓞 F) F x) < 1
  rw [NumberField.PlaceDecomp.valuation_apply_of_mem σ⁻¹ (inv_mem hσ)]

omit [NumberField E] in
theorem transport_eq_smul (w : HeightOneSpectrum (𝓞 F)) (σ : NumberField.PlaceDecomp.decomp E F w)
    (h : (σ : F ≃ₐ[E] F) • w = w) (x : w.adicCompletion F) :
    NumberField.PlaceTransport.transport (σ : F ≃ₐ[E] F) h x = σ • x := by
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [NumberField.PlaceTransport.transport_apply, NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_apply]

theorem finPart_unitsAct (D : IdeleGaloisDescent (𝓞 F) E F) (w : HeightOneSpectrum (𝓞 F))
    (σ : NumberField.PlaceDecomp.decomp E F w) (x : (AdeleRing (𝓞 F) F)ˣ) :
    finPart w (D.unitsAct (σ : F ≃ₐ[E] F) x) = σ • finPart w x := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _
  have hfix : (σ : F ≃ₐ[E] F) • w = w := smul_eq_of_mem_decomp w (σ : F ≃ₐ[E] F) σ.property
  apply Units.ext
  rw [NumberField.PlaceDecomp.coe_smul_units, coe_finPart_apply, coe_finPart_apply]
  change ((GenuineDescent.genuineDescentDatum E F).act (σ : F ≃ₐ[E] F) (x : AdeleRing (𝓞 F) F)).2 w
    = σ • ((x : AdeleRing (𝓞 F) F).2 w)
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E F (σ : F ≃ₐ[E] F) _ hfix, transport_eq_smul w σ hfix]

noncomputable def prHHom (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F)) :
    Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ H))
        (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
      Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ NumberField.PlaceDecomp.decomp E F w))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (finPart w)).toIntLinearMap, fun g => LinearMap.ext fun a => by
    change Additive.ofMul (finPart w (((g : F ≃ₐ[E] F))
        • (Additive.toMul : Additive (AdeleRing (𝓞 F) F)ˣ ≃ (AdeleRing (𝓞 F) F)ˣ) a))
      = Additive.ofMul ((Subgroup.inclusion (inf_le_right : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ NumberField.PlaceDecomp.decomp E F w) g)
          • finPart w ((Additive.toMul : Additive (AdeleRing (𝓞 F) F)ˣ ≃ (AdeleRing (𝓞 F) F)ˣ) a))
    rw [hactI, ← finPart_unitsAct D w (Subgroup.inclusion inf_le_right g)]
    rfl⟩

theorem prHHom_hom_apply (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (prHHom D hactI H w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x) := rfl

end M4aHerbrand.PrHProof

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F)) :
    ∃ prH : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ H))
            (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
          Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ NumberField.PlaceDecomp.decomp E F w))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ),
      ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x) := by
  exact ⟨fun w => M4aHerbrand.PrHProof.prHHom D hactI H w, fun w x => M4aHerbrand.PrHProof.prHHom_hom_apply D hactI H w x⟩

end S_M4aHerbrand_exists_hom_res_inf_decomp_ideles_adicCompletion_apply
end P2MW
export P2MW.S_M4aHerbrand_exists_hom_res_inf_decomp_ideles_adicCompletion_apply (solution)
