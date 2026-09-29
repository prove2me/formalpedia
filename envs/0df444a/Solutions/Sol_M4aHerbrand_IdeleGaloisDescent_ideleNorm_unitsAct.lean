-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.ideleNorm_unitsAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4cf14236-104f-5e71-874b-24ca7f62cc2e

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct

set_option autoImplicit false

open NumberField

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent"
p2m_open "M4aHerbrand"

namespace IdeleNormDescentAux

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped NNReal Pointwise

theorem distribHaarChar_mapEquiv_eq {A : Type*} [Ring A] [TopologicalSpace A]
    [IsTopologicalRing A] [LocallyCompactSpace A]
    (φ : A ≃+* A) (hφ : Continuous φ) (hφs : Continuous φ.symm) (u : Aˣ) :
    distribHaarChar A (Units.mapEquiv φ.toMulEquiv u) = distribHaarChar A u := by
  borelize A
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (PositiveCompacts A))
  set μ : Measure A := addHaarMeasure K₀ with hμ
  let φₜ : A ≃ₜ A := { toEquiv := φ.toEquiv, continuous_toFun := hφ, continuous_invFun := hφs }
  let φₘ : A ≃ᵐ A := φₜ.toMeasurableEquiv
  have hcoe : (φₘ : A → A) = φ := rfl
  have hcoes : (φₘ.symm : A → A) = φ.symm := rfl

  set ν : Measure A := Measure.map φₘ.symm μ with hν
  have hνapp : ∀ X : Set A, ν X = μ (φ '' X) := by
    intro X
    rw [hν, MeasurableEquiv.map_apply, ← MeasurableEquiv.image_eq_preimage_symm, hcoe]
  haveI : ν.IsAddHaarMeasure := by
    rw [hν, hcoes]
    exact AddEquiv.isAddHaarMeasure_map μ φ.symm.toAddEquiv hφs hφ
  haveI : ν.Regular := by
    rw [hν]
    exact Regular.map φₜ.symm

  set t : Set A := φ ⁻¹' (K₀ : Set A) with ht
  have hset : ((Units.mapEquiv φ.toMulEquiv u) • (K₀ : Set A)) = φ '' (u • t) := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨u • φ.symm k, ⟨φ.symm k, ?_, rfl⟩, ?_⟩
      · show φ (φ.symm k) ∈ (K₀ : Set A)
        rwa [RingEquiv.apply_symm_apply]
      · rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, map_mul,
          RingEquiv.apply_symm_apply, Units.coe_mapEquiv]
        rfl
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨φ y, hy, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, map_mul, Units.coe_mapEquiv]
      rfl
  have himg : φ '' t = (K₀ : Set A) := Set.image_preimage_eq _ φ.surjective
  have hK₀ : μ (K₀ : Set A) = 1 := by rw [hμ]; exact addHaarMeasure_self
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := (K₀ : Set A))
    (by rw [hK₀]; exact one_ne_zero) (by rw [hK₀]; exact ENNReal.one_ne_top) ?_
  rw [hset, ← hνapp, ← distribHaarChar_mul ν u t, hνapp, himg]

end IdeleNormDescentAux

end M4aHerbrand

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (D.unitsAct σ z) = NumberField.TateGlobal.ideleNorm L z := by
  have hcont : Continuous (D.act σ) := D.continuous_act σ
  have hsymm : Continuous (D.act σ).symm := by
    have h := D.continuous_act σ⁻¹
    rw [map_inv] at h
    exact h
  have hz : D.unitsAct σ z = Units.mapEquiv (D.act σ).toMulEquiv z := rfl
  unfold NumberField.TateGlobal.ideleNorm
  rw [hz, M4aHerbrand.IdeleNormDescentAux.distribHaarChar_mapEquiv_eq (D.act σ) hcont hsymm z]

end S_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct (solution)
