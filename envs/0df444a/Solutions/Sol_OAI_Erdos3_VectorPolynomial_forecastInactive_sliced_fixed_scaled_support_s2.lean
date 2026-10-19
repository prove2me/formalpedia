-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_scaled_support_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:50:57.521756+00:00
-- url     : https://prove2.me/submissions/8c7ece7e-e9a5-4c8d-a207-197c97701475

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedAxisCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    R j
local notation "scale" => basisAxisScale (b j) i
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

theorem forecastInactive_sliced_fixed_mem_physical_support
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)
    (c : ℤ) (hc : constantLaw c ≠ 0) (z : rows → ℤ)
    (hz : allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t) z ≠ 0) :
    allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows x z ≠ 0 := by
  unfold allocatedSupportedSlicedPhysicalGridPMF
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2 B U b hR hσ S q r H step lower hH hsubset hcell j i hgrid rows x]
  apply (PMF.mem_support_iff _ _).mp
  apply (PMF.mem_support_bind_iff _ _ z).mpr
  exact ⟨c, (PMF.mem_support_iff _ _).mpr hc, (PMF.mem_support_iff _ _).mpr hz⟩

theorem forecastInactive_sliced_fixed_scaled_support_s2_oai
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (c : ℤ) (hc : constantLaw c ≠ 0) (z : rows → ℤ)
    (hz : allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t) z ≠ 0)
    (t : rows) : |(z t : ℝ) / scale| ≤ radius := by
  let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  exact allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2 B U b hR hσ S q r H step lower hH hsubset hcell j i hσ1 rows x₀ z
    (forecastInactive_sliced_fixed_mem_physical_support B U b hR hσ S q r H step lower hH hsubset hcell j i
      hgrid rows x₀ c hc z hz) t

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_scaled_support_s2_oai.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_scaled_support_s2_oai.{uα, u_1, u_2, u_3, u_4}
