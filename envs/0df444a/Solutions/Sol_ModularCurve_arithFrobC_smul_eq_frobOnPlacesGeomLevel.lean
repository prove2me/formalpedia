-- Prove2me | solution 1 for ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/dd94e16e-d226-54e6-9434-20fa66cc6940

import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel.ModularCurve"
open scoped Pointwise

set_option autoImplicit false

namespace ModularCurve p2m_export "ModularCurve" "arithFrobC arithFrobC_smul_jq arithFrobC_smul_jqN jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem ModularPolynomialData frobeniusGeomLevel frobeniusGeomLevel_jq frobeniusGeomLevel_jqN mem_valuationSubring_iff_pow_mem frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.solution_aux_elt
    (ℓ : ℕ) (K : Type*) [Field K] [Fact ℓ.Prime] [CharP K ℓ] [PerfectField K]
    (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData ℓ) (hKr : ModularCurve.KroneckerCongruence ℓ data)
    (x : ModularCurve.modularFunctionFieldC K N) :
    ModularCurve.frobeniusGeomLevel K N data hKr x = ((ModularCurve.arithFrobC ℓ K N)⁻¹ • x) ^ ℓ := by
  haveI : CharP (modularFunctionFieldC K N) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldC K N)).injective ℓ

  let g : modularFunctionFieldC K N →+* modularFunctionFieldC K N :=
    (frobenius (modularFunctionFieldC K N) ℓ).comp
      (SemilinearAut.toRingAut (arithFrobC ℓ K N)⁻¹).toRingHom
  have hg : ∀ y, g y = ((arithFrobC ℓ K N)⁻¹ • y) ^ ℓ := fun y => rfl

  have hj : (arithFrobC ℓ K N)⁻¹ • (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)
      = ⟨jqModC K, jqModC_mem K N⟩ :=
    inv_smul_eq_iff.mpr (arithFrobC_smul_jq ℓ K N).symm
  have hjN : (arithFrobC ℓ K N)⁻¹ • (⟨jqNModC K N, jqNModC_mem K N⟩ : modularFunctionFieldC K N)
      = ⟨jqNModC K N, jqNModC_mem K N⟩ :=
    inv_smul_eq_iff.mpr (arithFrobC_smul_jqN ℓ K N).symm

  have hc : ∀ c : K, (SemilinearAut.baseAut (arithFrobC ℓ K N)⁻¹ c) ^ ℓ = c := by
    intro c
    rw [SemilinearAut.baseAut_inv]
    show ((frobeniusEquiv K ℓ).symm c) ^ ℓ = c
    rw [← frobeniusEquiv_def, RingEquiv.apply_symm_apply]
  suffices h : ∀ (y : LaurentSeries K) (hy : y ∈ modularFunctionFieldC K N),
      frobeniusGeomLevel K N data hKr ⟨y, hy⟩ = g ⟨y, hy⟩ by
    rw [← hg]; exact h x x.2
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [frobeniusGeomLevel_jq, hg, hj]
    · rw [frobeniusGeomLevel_jqN, hg, hjN]
  | algebraMap c =>
    show frobeniusGeomLevel K N data hKr (algebraMap K (modularFunctionFieldC K N) c)
      = g (algebraMap K (modularFunctionFieldC K N) c)
    rw [AlgHom.commutes, hg, SemilinearAut.smul_algebraMap, ← map_pow, hc]
  | add y z hy hz ihy ihz =>
    show frobeniusGeomLevel K N data hKr (⟨y, hy⟩ + ⟨z, hz⟩) = g (⟨y, hy⟩ + ⟨z, hz⟩)
    rw [map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
    show frobeniusGeomLevel K N data hKr (⟨y, hy⟩⁻¹) = g (⟨y, hy⟩⁻¹)
    rw [map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
    show frobeniusGeomLevel K N data hKr (⟨y, hy⟩ * ⟨z, hz⟩) = g (⟨y, hy⟩ * ⟨z, hz⟩)
    rw [map_mul, map_mul, ihy, ihz]

theorem solution
    (ℓ : ℕ) (K : Type*) [Field K] [Fact ℓ.Prime] [CharP K ℓ] [PerfectField K]
    (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData ℓ) (hKr : ModularCurve.KroneckerCongruence ℓ data)
    (w : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N)) :
    ModularCurve.arithFrobC ℓ K N • w = ModularCurve.frobOnPlacesGeomLevel K N data hKr w := by
  ext1
  refine SetLike.ext fun x => ?_
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    mem_frobOnPlacesGeomLevel_iff, ModularCurve.solution_aux_elt,
    ← mem_valuationSubring_iff_pow_mem (ℓ := ℓ)]

end S_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
end P2MW
export P2MW.S_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel (solution)
