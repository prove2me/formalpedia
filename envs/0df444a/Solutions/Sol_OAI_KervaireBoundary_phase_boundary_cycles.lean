-- Prove2me | solution 1 for OAI.KervaireBoundary.phase_boundary_cycles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:55:44.881112+00:00
-- url     : https://prove2.me/submissions/90cc54b7-796c-458c-90c6-587d42a47d0b

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MixingOperators.lean:L350-L371
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireBoundary.phase_boundary_cycles. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Theorems.Thm_OAI_KervaireMatrix_phase_cycles

-- ---- from OAI.GroupTheory.Kervaire.MixingOperators ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder

namespace KervaireMixing

section
open Matrix KervaireMatrix KervaireRegular
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end KervaireMixing
namespace KervaireCycle
variable {D E B : Type*} [Monoid B]
end KervaireCycle
namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical
variable {D E A : Type*} [Fintype D] [Fintype E] [Group A]
end KervaireMatrix

namespace KervaireRegular
open KervaireSpectral KervaireTraceCalculus MeasureTheory
variable {A : Type*} [Group A]

end KervaireRegular

namespace KervaireCycle
open KervaireSpectral
variable {D B : Type*} [CommMonoid B]
lemma orbitWeight_eq_prod (σ : Equiv.Perm D) (b : D → B) (n : ℕ) (i : D) :
    orbitWeight σ b n i = ∏ j ∈ Finset.range n, b ((σ^j) i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [orbitWeight_succ,ih,Finset.prod_range_succ,mul_comm]

lemma orbitWeight_rotate_prod (d : ℕ) [NeZero d] (b : Fin d → B) :
    orbitWeight (finRotate d) b d 0 = ∏ i, b i := by
  rw [orbitWeight_eq_prod,← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  rw [rotate_pow_apply]
  simp

lemma orbitWeight_scalarRotation (d : ℕ) [NeZero d] (γ : Fin d → ℝ) :
    orbitWeight (finRotate d) (fun i ↦ scalarRotation (γ i)) d 0 = scalarRotation (∑ i, γ i) := by
  rw [orbitWeight_rotate_prod]
  exact (map_sum (show ℝ →+ Additive ℂ from
    { toFun := fun x ↦ Additive.ofMul (scalarRotation x)
      map_zero' := scalarRotation_zero
      map_add' := scalarRotation_add }) _ _).symm
end KervaireCycle

namespace KervaireBoundary
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical
variable {D Z A : Type*} [Fintype D] [Fintype Z] [Group A]

/-- Summation over the fibers of the explicit boundary-cycle decomposition. -/
lemma divergence_cycle (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D) (γ : D → ℝ) (z : Z) :
    (∑ d, if (e.symm d).1 = z then γ d else 0) = ∑ i, γ (e ⟨z,i⟩) := by
  rw [← e.sum_comp,Fintype.sum_sigma]
  simp

lemma total_cycle_length (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D) :
    (∑ z, (n z : ℝ)) = Fintype.card D - Fintype.card Z := by
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one] at hc
  have hr : (∑ z, (n z : ℝ)) + Fintype.card Z = Fintype.card D := by exact_mod_cast hc
  linarith

/-- Cycle phase specializes to prescribed real boundary fluxes. -/
lemma phase_boundary_cycles (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (σ : Equiv.Perm D) (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (γ : D → ℝ) (a : D → A) (η : Z → ℝ)
    (hη : ∀ z, (∑ d, if (e.symm d).1 = z then γ d else 0) = η z) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ (fun d ↦ scalarRotation (γ d)) a
      (fun d ↦ scalarRotation_unitary (γ d)))
    KervaireMatrix.phase (weightedShift σ (fun d ↦ scalarRotation (γ d)) a) =
      ((Fintype.card D : ℝ) - Fintype.card Z) / 2 +
        ∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _)
          (orbitWeight (finRotate (n z+1)) (fun i ↦ a (e ⟨z,i⟩)) (n z+1) 0) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ (fun d ↦ scalarRotation (γ d)) a
    (fun d ↦ scalarRotation_unitary (γ d)))
  change KervaireMatrix.phase (weightedShift σ (fun d ↦ scalarRotation (γ d)) a) = _
  rw [phase_cycles n e σ he _ _ (fun d ↦ scalarRotation_unitary (γ d)),Finset.sum_add_distrib,← Finset.sum_div,total_cycle_length n e]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  have hrot : orbitWeight (finRotate (n z+1))
      (fun i ↦ scalarRotation (γ (e ⟨z,i⟩))) (n z+1) 0 = scalarRotation (η z) := by
    rw [orbitWeight_scalarRotation,← divergence_cycle n e γ z,hη z]
  simp only [hrot]
end KervaireBoundary

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireBoundary
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireBoundary.phase_boundary_cycles := @_root_.OAI.KervaireBoundary.phase_boundary_cycles
