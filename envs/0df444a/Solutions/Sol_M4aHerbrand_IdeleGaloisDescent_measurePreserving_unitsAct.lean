-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.measurePreserving_unitsAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c13a0d0a-9b5e-5cc0-8f50-8ae0b90fe721

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_measurePreserving_unitsAct

set_option autoImplicit false

open MeasureTheory NumberField

namespace K42G1

p2m_open "MeasureTheory Measure MeasureTheory.Measure Topology"

theorem eq_smul_of_sigmaCompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  ext s _hs
  have hcov : s = ⋃ n : ℕ, s ∩ compactCovering G n := by
    rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have hmono : Monotone fun n : ℕ => s ∩ compactCovering G n := fun m n hmn =>
    Set.inter_subset_inter_right _ (compactCovering_subset G hmn)
  rw [hcov, hmono.measure_iUnion, hmono.measure_iUnion]
  congr 1
  ext n
  rw [Measure.smul_apply]
  exact measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ
    ((isCompact_compactCovering G n).closure_of_subset Set.inter_subset_right)

theorem hsf_congr {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] {μ₁ μ₂ ν : Measure G} [IsHaarMeasure ν]
    [IsFiniteMeasureOnCompacts μ₁] [IsMulLeftInvariant μ₁]
    [IsFiniteMeasureOnCompacts μ₂] [IsMulLeftInvariant μ₂] (h : μ₁ = μ₂) :
    haarScalarFactor μ₁ ν = haarScalarFactor μ₂ ν := by
  subst h
  rfl

theorem haarScalarFactor_map_eq_one_of_iterate_eq_id {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [IsHaarMeasure ν] (φ : G ≃ₜ* G) {n : ℕ} (hn : n ≠ 0)
    (hφ : (⇑φ)^[n] = id) :
    haarScalarFactor (ν.map φ) ν = 1 := by
  have hmeas : Measurable (φ : G → G) := φ.continuous.measurable
  have step : ∀ (μ' : Measure G) [IsHaarMeasure μ'],
      haarScalarFactor (μ'.map φ) ν = haarScalarFactor μ' ν * haarScalarFactor (ν.map φ) ν := by
    intro μ' _
    rw [haarScalarFactor_eq_mul (μ'.map φ) (ν.map φ) ν, haarScalarFactor_map]
  let ψ : ℕ → (G ≃ₜ* G) := fun k => (fun e : G ≃ₜ* G => e.trans φ)^[k] (ContinuousMulEquiv.refl G)
  have hψ : ∀ k, (⇑(ψ k) : G → G) = (⇑φ)^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show (⇑((fun e : G ≃ₜ* G => e.trans φ)^[k + 1] (ContinuousMulEquiv.refl G)) : G → G) = (⇑φ)^[k + 1]
      rw [Function.iterate_succ_apply', Function.iterate_succ', ← ih]
      rfl
  have hk : ∀ k, haarScalarFactor (ν.map (ψ k)) ν = haarScalarFactor (ν.map φ) ν ^ k := by
    intro k
    induction k with
    | zero =>
      have h0 : ν.map (ψ 0) = ν := Measure.map_id
      rw [hsf_congr h0, haarScalarFactor_self, pow_zero]
    | succ k ih =>
      have h1 : ν.map (ψ (k + 1)) = (ν.map (ψ k)).map φ := by
        rw [show ψ (k + 1) = (ψ k).trans φ from Function.iterate_succ_apply' _ _ _]
        exact (Measure.map_map hmeas (ψ k).continuous.measurable).symm
      rw [hsf_congr h1, step, ih, pow_succ]
  have h2 : ν.map (ψ n) = ν := by
    rw [show (⇑(ψ n) : G → G) = id from (hψ n).trans hφ]
    exact Measure.map_id
  have hnn := hk n
  rw [hsf_congr h2, haarScalarFactor_self] at hnn
  have h' : ((haarScalarFactor (ν.map φ) ν : ℝ)) ^ n = 1 := by exact_mod_cast hnn.symm
  exact_mod_cast (pow_eq_one_iff_of_nonneg (NNReal.coe_nonneg _) hn).mp h'

end K42G1

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [ν.IsHaarMeasure] :
    MeasurePreserving (D.unitsAct σ) ν ν := by

  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

  have hcont : ∀ τ : L ≃ₐ[K] L, Continuous (D.unitsAct τ) := fun τ =>
    Continuous.units_map ((D.act τ).toMulEquiv.toMonoidHom) (D.continuous_act τ)
  have hinv : ∀ x, (D.unitsAct σ).symm x = D.unitsAct σ⁻¹ x := fun x => by
    rw [map_inv]; rfl
  let φ : (AdeleRing (𝓞 L) L)ˣ ≃ₜ* (AdeleRing (𝓞 L) L)ˣ :=
    { (D.unitsAct σ : (AdeleRing (𝓞 L) L)ˣ ≃* (AdeleRing (𝓞 L) L)ˣ) with
      continuous_toFun := hcont σ
      continuous_invFun := by
        change Continuous fun x => (D.unitsAct σ).symm x
        simp_rw [hinv]
        exact hcont σ⁻¹ }
  have hφ : (φ : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ) = D.unitsAct σ := rfl

  have hiter : ∀ (m : ℕ) (z : (AdeleRing (𝓞 L) L)ˣ), ((⇑φ)^[m]) z = D.unitsAct (σ ^ m) z := by
    intro m
    induction m with
    | zero => intro z; rw [Function.iterate_zero, pow_zero, map_one]; rfl
    | succ m ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, hφ, pow_succ', map_mul]
      rfl
  have hid : ((⇑φ)^[orderOf σ]) = id := by
    funext z
    rw [hiter, pow_orderOf_eq_one, map_one]
    rfl
  haveI : Measure.IsHaarMeasure (ν.map φ) := ContinuousMulEquiv.isHaarMeasure_map ν φ
  have hc := K42G1.haarScalarFactor_map_eq_one_of_iterate_eq_id ν φ (orderOf_pos σ).ne' hid
  have hmap : ν.map (D.unitsAct σ) = ν := by
    rw [← hφ]
    have h := K42G1.eq_smul_of_sigmaCompact (ν.map φ) ν
    rwa [hc, one_smul] at h
  exact ⟨(hcont σ).measurable, hmap⟩

end S_M4aHerbrand_IdeleGaloisDescent_measurePreserving_unitsAct
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_measurePreserving_unitsAct (solution)
