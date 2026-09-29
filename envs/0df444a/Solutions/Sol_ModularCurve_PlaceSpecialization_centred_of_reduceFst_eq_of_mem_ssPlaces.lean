-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.centred_of_reduceFst_eq_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3c99287e-4e63-56c3-81a7-d81b3cb3809f

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence IsSupersingularPlace ssPlaces jGeomGen jNGeomGen IsCentreOf IsCentreOf.frobOnPlacesGeomLevel arithFrobC arithFrobC_smul_eq_frobOnPlacesGeomLevel"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple reduceFst sp d0_j d0_j_pole d1"
namespace LevelNCprime
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime]

theorem coeffEmb_qExpand_eq' (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n x)
      = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) x) := by
  ext m
  simp only [coeffEmb_coeff]
  by_cases h : (n : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

noncomputable def jLvl (N : ℕ) [NeZero N] : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem heckeAlphaBar_jLvl (N : ℕ) [NeZero N] :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (jLvl N) = ProlongationTuple.jFun N q := by
  apply Subtype.ext
  rw [coe_heckeAlphaBar]
  rfl

theorem heckeBetaBar_jLvl (N : ℕ) [NeZero N] :
    heckeBetaBar (AlgebraicClosure ℚ) N q (jLvl N) = ProlongationTuple.jQFun N q := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq)
    = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
  rw [coeffEmb_qExpand_eq']

theorem ramificationIndexAlong_pos {F F' : Type*} [Field F] [Field F'] [Algebra (AlgebraicClosure ℚ) F]
    [Algebra (AlgebraicClosure ℚ) F'] (φ : F →ₐ[AlgebraicClosure ℚ] F') (hφ : φ.toRingHom.IsIntegral)
    (V : Place (AlgebraicClosure ℚ) F') :
    0 < Place.ramificationIndexAlong φ V := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact V.ramificationIndex_pos (F := F)

theorem eq_of_ord_jGeomGen_sub_pos {k : Type*} [Field k] {N : ℕ} [NeZero N]
    {w : Place k ↥(modularFunctionFieldC k N)} {cc : k × k} (hcen : IsCentreOf k N cc w) (c : k)
    (hc : 0 < w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c)) : c = cc.1 := by
  have h1 := w.evalAt_congr hcen.jGeomGen_mem (w.algebraMap_mem' c) (Or.inr hc)
  rw [w.evalAt_algebraMap, hcen.evalAt_jGeomGen] at h1
  exact h1.symm

end ModularCurve.PlaceSpecialization.LevelNCprime

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"
open ModularCurve.PlaceSpecialization.LevelNCprime in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (w : Place k ↥(modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ((∃ x : A, red x = a ∧ 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ))) ∧
      (∃ y : A, red y = a ^ q ∧ 0 < V.ord (jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (y : AlgebraicClosure ℚ)))) := by

  set φ := frobOnPlacesGeomLevel k N data hKr with hφdef
  set Vα := V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα with hVα
  set Vβ := V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ with hVβ
  have hss : IsSupersingularPlace q N k w := hw
  have hcen : IsCentreOf k N (w.evalAt (jGeomGen k N), w.evalAt (jNGeomGen k N)) w :=
    hss.isCentreOf_evalAt

  have hfix' : φ (φ w) = w := by
    have h := hfix
    rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr,
      arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr] at h
    exact h

  have hFst : P.sp Vα = w := hV
  have hx : ∃ x : A, 0 < Vα.ord (jLvl N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (x : AlgebraicClosure ℚ)) := by
    by_contra hne
    have hle : ∀ x : A, Vα.ord (jLvl N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (x : AlgebraicClosure ℚ)) ≤ 0 :=
      fun x => not_lt.mp fun hlt => hne ⟨x, hlt⟩
    have hpole := P.d0_j_pole Vα hle
    rw [hFst] at hpole
    exact absurd hpole (not_lt.mpr (Place.ord_nonneg_of_mem _ hcen.jGeomGen_mem))
  obtain ⟨x, hxpos⟩ := hx
  have hredx : red x = a := by
    have hz := P.d0_j Vα x hxpos
    rw [hFst] at hz
    have := eq_of_ord_jGeomGen_sub_pos hcen (red x) hz
    rw [this]; exact ha

  have hSnd : P.sp Vβ = φ w := by
    rcases P.d1 V with h | h
    ·
      change P.sp Vα = φ (P.sp Vβ) at h
      rw [hFst] at h

      have h3 : φ (φ (φ (P.sp Vβ))) = φ (P.sp Vβ) := by rw [← h]; exact hfix'
      have h2 : φ (φ (P.sp Vβ)) = P.sp Vβ := frobOnPlacesGeomLevel_injective k N data hKr h3
      rw [h, h2]
    · change φ (P.sp Vα) = P.sp Vβ at h
      rw [hFst] at h
      exact h.symm

  have hcenφ := IsCentreOf.frobOnPlacesGeomLevel data hKr hcen
  have hy : ∃ y : A, 0 < Vβ.ord (jLvl N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (y : AlgebraicClosure ℚ)) := by
    by_contra hne
    have hle : ∀ y : A, Vβ.ord (jLvl N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (y : AlgebraicClosure ℚ)) ≤ 0 :=
      fun y => not_lt.mp fun hlt => hne ⟨y, hlt⟩
    have hpole := P.d0_j_pole Vβ hle
    rw [hSnd] at hpole
    exact absurd hpole (not_lt.mpr (Place.ord_nonneg_of_mem _ hcenφ.jGeomGen_mem))
  obtain ⟨y, hypos⟩ := hy
  have hredy : red y = a ^ q := by
    have hz := P.d0_j Vβ y hypos
    rw [hSnd] at hz
    have := eq_of_ord_jGeomGen_sub_pos hcenφ (red y) hz
    rw [this]
    show (w.evalAt (jGeomGen k N)) ^ q = a ^ q
    rw [ha]

  refine ⟨⟨x, hredx, ?_⟩, ⟨y, hredy, ?_⟩⟩
  · have hord := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V
      (jLvl N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (x : AlgebraicClosure ℚ))
    rw [map_sub, AlgHom.commutes, heckeAlphaBar_jLvl] at hord
    rw [hord]
    exact mul_pos (by exact_mod_cast ramificationIndexAlong_pos _ hα V) hxpos
  · have hord := Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V
      (jLvl N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (y : AlgebraicClosure ℚ))
    rw [map_sub, AlgHom.commutes, heckeBetaBar_jLvl] at hord
    rw [hord]
    exact mul_pos (by exact_mod_cast ramificationIndexAlong_pos _ hβ V) hypos

end S_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces (solution)
