-- Prove2me | solution 1 for KaehlerDifferential.D_ne_zero_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/95ed7aea-228a-552c-bed7-c51720bd6f7e

import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental

noncomputable section
p2m_open "Polynomial KaehlerDifferential P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental.KaehlerDifferential"

namespace KaehlerDifferential
p2m_export "KaehlerDifferential" "tensorKaehlerEquivOfFormallyEtale polynomialEquiv tensorKaehlerEquivOfFormallyEtale_apply mapBaseChange_tmul D map_D map"
namespace FF2
p2m_open "KaehlerDifferential"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} (hx : Transcendental K x)
  [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]

include hx in

private theorem exists_basis : ∃ b : Module.Basis Unit F Ω[F⁄K], b () = D K F x := by

  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) := RatFunc.algEquivOfTranscendental x hx
  letI algKx : Algebra K[X] (IntermediateField.adjoin K ({x} : Set F)) := (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))).toAlgebra
  letI algF : Algebra K[X] F := ((algebraMap (IntermediateField.adjoin K ({x} : Set F)) F).comp (algebraMap K[X] (IntermediateField.adjoin K ({x} : Set F)))).toAlgebra
  haveI : IsScalarTower K[X] (IntermediateField.adjoin K ({x} : Set F)) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K K[X] (IntermediateField.adjoin K ({x} : Set F)) := IsScalarTower.of_algebraMap_eq (fun c => by
    change _ = (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))) (C c)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_algHom]
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K), AlgEquiv.commutes])
  haveI : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({x} : Set F)) F, IsScalarTower.algebraMap_apply K[X] (IntermediateField.adjoin K ({x} : Set F)) F,
      ← IsScalarTower.algebraMap_apply K K[X] (IntermediateField.adjoin K ({x} : Set F))])

  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  haveI : Algebra.FormallyEtale K[X] (IntermediateField.adjoin K ({x} : Set F)) :=
    Algebra.FormallyEtale.of_equiv (R := K[X]) (A := RatFunc K) { e with commutes' := fun _ => rfl }
  haveI : Algebra.FormallyEtale (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.FormallyEtale.of_isSeparable (IntermediateField.adjoin K ({x} : Set F)) F
  haveI : Algebra.FormallyEtale K[X] F := Algebra.FormallyEtale.comp K[X] (IntermediateField.adjoin K ({x} : Set F)) F

  let b₀ : Module.Basis Unit K[X] Ω[K[X]⁄K] :=
    (Module.Basis.singleton Unit K[X]).map (polynomialEquiv K).symm
  have hb₀ : b₀ () = D K K[X] X := by simp [b₀]
  let ψ := tensorKaehlerEquivOfFormallyEtale K K[X] F
  refine ⟨(b₀.baseChange F).map ψ, ?_⟩
  have hX : algebraMap K[X] F X = x := by
    change algebraMap (IntermediateField.adjoin K ({x} : Set F)) F (e (algebraMap K[X] (RatFunc K) X)) = x
    rw [RatFunc.algebraMap_X]
    exact RatFunc.algEquivOfTranscendental_X x hx
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb₀, ψ,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D, hX]

end KaehlerDifferential.FF2

theorem solution (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0 := by
  obtain ⟨b, hb⟩ := KaehlerDifferential.FF2.exists_basis hx
  simpa [hb] using b.ne_zero ()

end

end S_KaehlerDifferential_D_ne_zero_of_transcendental
end P2MW
export P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental (solution)
