-- Prove2me | solution 1 for NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/55e9f4b4-eb0a-5555-899c-d7efb162efba

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_transport
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units

set_option autoImplicit false

open IsDedekindDomain NumberField in
open scoped NumberField.PlaceTransport in
theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K) :
    ∃ Φ : (NumberField.SIdele.obj E K S) →+ Additive (AdeleRing (𝓞 K) K)ˣ,
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
        Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x)))) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) := by
  obtain ⟨Φ, hinj, hrange, hfin, hinf, hdiag⟩ := NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport E K S
  refine ⟨Φ, hinj, hrange, fun g x => ?_, hdiag⟩
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 K) E K
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum E K := Subsingleton.elim _ _
  apply Additive.toMul.injective
  rw [toMul_ofMul]
  apply Units.ext
  change ((Additive.toMul (Φ ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
    (M4aHerbrand.GenuineDescent.genuineDescentDatum E K).act g ((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  refine Prod.ext (funext fun w' => ?_) (RestrictedProduct.ext _ _ fun w' => ?_)
  · rw [hinf g x (g⁻¹ • w') w' (smul_inv_smul g w')]
    exact (M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply E K g _ (smul_inv_smul g w')).symm
  · change ((Additive.toMul (Φ ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' =
      ((M4aHerbrand.GenuineDescent.genuineDescentDatum E K).act g
        ((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w'
    rw [hfin g x (g⁻¹ • w') w' (smul_inv_smul g w')]
    exact (M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E K g _ (smul_inv_smul g w')).symm

end S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units
end P2MW
export P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units (solution)
