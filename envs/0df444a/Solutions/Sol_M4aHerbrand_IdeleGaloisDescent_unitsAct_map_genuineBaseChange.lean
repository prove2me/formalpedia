-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4032917b-c350-52e6-8ba7-7460ebce103f

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_Bridge_genuineBeta_comp_of_tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "NumberField M4aHerbrand P2MW.S_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange.M4aHerbrand M4aHerbrand.GenuineDescent M4aHerbrand.Bridge"
open scoped TensorProduct

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent subsingleton_ideleGaloisDescent Bridge.genuineBeta_comp_of_tower"
namespace G1a
p2m_open "M4aHerbrand"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem genuine_act_genuineβ (g : L ≃ₐ[K] L) (a : AdeleRing (𝓞 K) K) :
    (genuineDescentDatum K L).act g (genuineβ K L a) = genuineβ K L a := by
  letI := (genuineβ K L).toAlgebra
  rw [genuineDescentDatum_act]
  change (genuineTensorEquiv K L) ((Algebra.TensorProduct.congr AlgEquiv.refl g)
    ((genuineTensorEquiv K L).symm (algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) a))) =
      algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) a
  rw [(genuineTensorEquiv K L).symm.commutes, AlgEquiv.commutes, AlgEquiv.commutes]

theorem genuine_act_algebraMap (g : L ≃ₐ[K] L) (l : L) :
    (genuineDescentDatum K L).act g (algebraMap L (AdeleRing (𝓞 L) L) l) = algebraMap L (AdeleRing (𝓞 L) L) (g l) :=
  (genuineDescentDatum K L).compat g l

theorem adele_induction {P : AdeleRing (𝓞 L) L → Prop}
    (hβ : ∀ a : AdeleRing (𝓞 K) K, ∀ l : L, P (genuineβ K L a * algebraMap L (AdeleRing (𝓞 L) L) l))
    (hadd : ∀ x y, P x → P y → P (x + y)) (y : AdeleRing (𝓞 L) L) : P y := by
  letI := (genuineβ K L).toAlgebra
  obtain ⟨t, rfl⟩ := (genuineTensorEquiv K L).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simpa using hβ 0 0
  | tmul a l =>
    have h : (genuineTensorEquiv K L) (a ⊗ₜ[K] l) = genuineβ K L a * algebraMap L (AdeleRing (𝓞 L) L) l := by
      rw [show a ⊗ₜ[K] l = (a ⊗ₜ[K] (1 : L)) * ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, genuineTensorEquiv_one_tmul]
      congr 1
      rw [show a ⊗ₜ[K] (1 : L) = algebraMap (AdeleRing (𝓞 K) K) ((AdeleRing (𝓞 K) K) ⊗[K] L) a by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply], AlgEquiv.commutes]
      rfl
    rw [h]
    exact hβ a l
  | add s t hs ht => rw [map_add]; exact hadd _ _ hs ht

end M4aHerbrand.G1a

open M4aHerbrand.G1a in
theorem solution
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (D'' : IdeleGaloisDescent (𝓞 M) E M)
    (σ : M ≃ₐ[E] M) (x : (AdeleRing (𝓞 F) F)ˣ) :
    D''.unitsAct σ (Units.map (genuineBaseChange F M).β.toMonoidHom x) =
      Units.map (genuineBaseChange F M).β.toMonoidHom (D.unitsAct (AlgEquiv.restrictNormalHom F σ) x) := by

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 M) E M
  obtain rfl : D = genuineDescentDatum E F := Subsingleton.elim _ _
  obtain rfl : D'' = genuineDescentDatum E M := Subsingleton.elim _ _
  apply Units.ext
  change (genuineDescentDatum E M).act σ (genuineβ F M (x : AdeleRing (𝓞 F) F)) =
    genuineβ F M ((genuineDescentDatum E F).act (AlgEquiv.restrictNormalHom F σ) (x : AdeleRing (𝓞 F) F))

  have htrans : ∀ a : AdeleRing (𝓞 E) E, genuineβ F M (genuineβ E F a) = genuineβ E M a := fun a =>
    RingHom.congr_fun (M4aHerbrand.Bridge.genuineBeta_comp_of_tower E F M) a
  refine adele_induction E F (P := fun y => (genuineDescentDatum E M).act σ (genuineβ F M y) =
    genuineβ F M ((genuineDescentDatum E F).act (AlgEquiv.restrictNormalHom F σ) y)) (fun a l => ?_) (fun y z hy hz => ?_) _
  · rw [map_mul, map_mul, map_mul, map_mul, htrans, genuine_act_genuineβ, genuine_act_genuineβ, htrans,
      genuineβ_compat F M, genuine_act_algebraMap, genuine_act_algebraMap,
      genuineβ_compat F M]
    congr 1
    exact congrArg _ (AlgEquiv.restrictNormal_commutes σ F l).symm
  · rw [map_add, map_add, hy, hz, map_add, map_add]

end S_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange (solution)
