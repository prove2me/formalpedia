-- Prove2me | solution 1 for GlobalTheory.SS.Dil.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:46.851004+00:00
-- url     : https://prove2.me/submissions/fc39ea77-d151-4750-a3ae-a8ce1efd7204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R B S W : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    [AddCommGroup W] [Module S W] (D : B → W) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = algebraMap B S x • D y + algebraMap B S y • D x)
    (hr : ∀ r, D (algebraMap R B r) = 0) :
    ∃ l : S ⊗[B] (KaehlerDifferential R B) →ₗ[S] W, ∀ b, l (1 ⊗ₜ KaehlerDifferential.D R B b) = D b := by
  letI : Module B W := Module.compHom W (algebraMap B S)
  letI : Module R W := Module.compHom W ((algebraMap B S).comp (algebraMap R B))
  have e1 : ∀ (b : B) (w : W), b • w = algebraMap B S b • w := fun _ _ => rfl
  have e2 : ∀ (b : R) (w : W), b • w = algebraMap B S (algebraMap R B b) • w := fun _ _ => rfl
  haveI : IsScalarTower R B W := ⟨fun r b w => by
    rw [e2, e1, e1, Algebra.smul_def, map_mul, mul_smul]⟩
  haveI : IsScalarTower B S W := ⟨fun r b w => by
    rw [e1, Algebra.smul_def, mul_smul]⟩
  let L : B →ₗ[R] W :=
    { toFun := D
      map_add' := ha
      map_smul' := fun r x => by
        rw [Algebra.smul_def, hm, hr, smul_zero, add_zero, RingHom.id_apply, e2] }
  let d : Derivation R B W := Derivation.mk' L (fun x y => hm x y)
  refine ⟨LinearMap.liftBaseChange S d.liftKaehlerDifferential, fun b => ?_⟩
  rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl
end GlobalTheory.SS.Dil
