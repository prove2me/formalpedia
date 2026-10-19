-- Prove2me | solution 1 for OAI.KervaireBoundary.planar_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:54:57.621719+00:00
-- url     : https://prove2.me/submissions/a358a239-6db4-4560-8f61-7c0f8899413a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean:L269-L328
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireBoundary.planar_boundary. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Theorems.Thm_OAI_KervaireBoundary_exists_band_mixer
import Theorems.Thm_OAI_KervaireBoundary_phase_boundary_cycles
import Theorems.Thm_OAI_KervaireFlow_dual_connected
import Theorems.Thm_OAI_KervaireFlow_exists_flow
import Theorems.Thm_OAI_KervaireMatrix_monomial_star
import Theorems.Thm_OAI_KervaireMixing_phase_upper_of_fixed
import Theorems.Thm_OAI_KervaireRegular_trivial_of_boundary_inequalities

-- ---- from OAI.GroupTheory.Kervaire.SpectralMeasures ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The defining integration identity for the scalar spectral measure. -/
theorem integral_vectorMeasure (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂vectorMeasure U ξ = (inner ℂ ξ (cfcHom hU (complexify f) ξ)).re := by
  let fc : C_c(spectrum ℂ U, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (vectorFunctional U ξ) fc

theorem phase_exp_normalized (x : ℝ) :
    phase (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)) = Int.fract x := by
  rw [phase_exp]
  congr 1
  field_simp

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralApproximation ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The mass of a vector spectral measure is its value at the identity. -/
theorem integral_one_vectorMeasure (U : Operator H) [IsStarNormal U] (ξ : H) :
    ∫ _z : spectrum ℂ U, (1 : ℝ) ∂vectorMeasure U ξ = (vectorCLM ξ 1).re := by
  simpa using integral_vectorMeasure U ξ (1 : C(spectrum ℂ U, ℝ))

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.MatrixShifts ----
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

namespace KervaireMatrix

section
open KervaireRegular
open scoped Classical
variable {D A : Type*}

variable [Fintype D]

variable [Group A]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

variable [Fintype D]

/-- Multiplication proves the exact order of coefficient inverses on every boundary step. -/
theorem weightedShift_mul (σ τ : Equiv.Perm D) (u v : D → ℂ) (a b : D → A) :
    weightedShift σ u a * weightedShift τ v b =
      weightedShift (σ*τ) (fun d => u (τ d)*v d) (fun d => a (τ d)*b d) := by
  apply ext_delta
  rintro ⟨d,x⟩
  simp [mul_apply_eq_comp, smul_smul, mul_assoc, mul_comm (v d)]

end KervaireMatrix
namespace KervaireSpectral
end KervaireSpectral

end

end OAI

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

lemma groupPhase_one (z : ℂ) (hz : z ∈ unitary ℂ) :
    groupPhase z hz (1 : A) = KervaireSpectral.phase z := by
  let _ : Nontrivial ℓ²(A, ℂ) := by
    classical
    refine ⟨⟨delta (1 : A), 0, ?_⟩⟩
    intro h
    have hh := congrArg (fun f : ℓ²(A, ℂ) => f 1) h
    simp [delta] at hh
  let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨z,hz⟩ (leftOperator_unitary (1 : A)))
  change (∫ q : spectrum ℂ (z • leftOperator (1 : A)), KervaireSpectral.phase q
    ∂vectorMeasure (z • leftOperator (1 : A)) (delta 1)) = _
  have he (q : spectrum ℂ (z • leftOperator (1 : A))) : (q : ℂ) = z := by
    have hq : (q : ℂ) ∈ spectrum ℂ (algebraMap ℂ (Operator A) z) := by
      simpa only [Algebra.algebraMap_eq_smul_one,leftOperator_one] using q.property
    simpa only [spectrum.scalar_eq,Set.mem_singleton_iff] using hq
  trans ∫ _q : spectrum ℂ (z • leftOperator (1 : A)),
    KervaireSpectral.phase z * 1 ∂vectorMeasure (z • leftOperator (1 : A)) (delta 1)
  · apply integral_congr_ae
    filter_upwards [] with q
    simp [he q]
  · rw [integral_const_mul,integral_one_vectorMeasure]
    simp [vectorCLM_apply,delta]

lemma groupPhase_rotation_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    groupPhase (scalarRotation (-ε)) (scalarRotation_unitary _) (1 : A) = 1-ε := by
  rw [groupPhase_one]
  rw [show KervaireSpectral.phase (scalarRotation (-ε)) = Int.fract (-ε) from phase_exp_normalized _]
  rw [Int.fract_eq_iff]
  refine ⟨by linarith,by linarith, -1,?_⟩
  norm_num
  ring

end KervaireRegular

namespace KervaireCycle
open KervaireSpectral
variable {D B : Type*} [CommMonoid B]
end KervaireCycle

namespace KervaireBoundary
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical
variable {D Z A : Type*} [Fintype D] [Fintype Z] [Group A]

end KervaireBoundary

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.Traversal ----
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
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireTraversal

section
open Matrix KervaireFixed KervaireSignPairing
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K]
end

section
open Matrix KervaireFixed
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E]

end

open Matrix KervaireFixed
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
attribute [local instance] OAI.KervaireTraversal.instDecidableEqSlots
end KervaireTraversal

namespace KervaireMatrix
open Matrix KervaireRegular
open scoped Classical
variable {D : Type*} [Fintype D]

lemma monomial_unitary [DecidableEq D] (θ : Equiv.Perm D) (u : D → ℂ)
    (hu : ∀ d, u d ∈ unitary ℂ) : monomial θ u ∈ unitary (Matrix D D ℂ) := by
  rw [Unitary.mem_iff,monomial_star,monomial_mul,monomial_mul]
  constructor
  · simp only [inv_mul_cancel]
    change monomial (Equiv.refl D) (fun j ↦ star (u (θ.symm (θ j))) * u j) = 1
    simpa only [Equiv.symm_apply_apply,funext (fun j ↦ (hu j).1)] using monomial_one (D := D)
  · simp only [mul_inv_cancel]
    change monomial (Equiv.refl D) (fun j ↦ u (θ.symm j) * star (u (θ.symm j))) = 1
    simpa only [funext (fun j ↦ (hu (θ.symm j)).2)] using monomial_one (D := D)

omit [Fintype D] in
lemma monomial_selfadjoint (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → ℂ) (hu : ∀ d, u (θ d) = star (u d)) :
    star (monomial θ u) = monomial θ u := by
  have hi : θ⁻¹ = θ := by ext d; exact (θ.injective (by simp [hθ]))
  rw [monomial_star,hi]
  congr 1
  ext d
  simp [hu]

variable {A : Type*} [Group A]
lemma scalarTensor_monomial (θ : Equiv.Perm D) (u : D → ℂ) :
    scalarTensor (A := A) (monomial θ u) = weightedShift θ u (fun _ ↦ (1 : A)) := by
  ext f ⟨d,a⟩
  simp only [scalarTensor_apply,monomial]
  rw [Finset.sum_eq_single (θ⁻¹ d)]
  · simp [weightedShift,mul_apply_eq_comp]
  · intro j _ hj
    have h : d ≠ θ j := by intro he; apply hj; simp [he]
    simp [h]
  · simp
end KervaireMatrix

namespace KervaireMixing
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]
attribute [local instance] OAI.KervaireMixing.instDecidableEqSlot
end KervaireMixing

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.BoundaryFlow ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFlow

section
open scoped Classical
variable {D Z : Type*} [Fintype D] [Fintype Z]

end

variable {D Z : Type*}
end KervaireFlow
namespace KervaireBoundary

section
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot
lemma S_mul_bands (ρ : Equiv.Perm I) (a : I → A) (θ : Equiv.Perm (Slot I K)) (γ : Slot I K → ℝ) :
    S ρ a * scalarTensor (A := A) (monomial θ (fun d ↦ scalarRotation (γ d))) =
      weightedShift (successor ρ * θ) (fun d ↦ scalarRotation (γ d)) (fun d ↦ labels ρ a (θ d)) := by
  rw [scalarTensor_monomial,S]
  have he : labelledShift (successor (K := K) ρ) (labels ρ a) =
      weightedShift (successor ρ) (fun _ ↦ 1) (labels ρ a) := by
    simp [weightedShift,scalarDiagonal_one]
  rw [he,weightedShift_mul]
  simp only [one_mul,mul_one]

/-- The literal phase bound for every antisymmetric real choice of band phases. -/
lemma boundary_phase_upper [Nonempty I] [Nonempty K] (ρ : Equiv.Perm I) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (γ : Slot I K → ℝ) (hγ : ∀ d, γ (θ d) = -γ d) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (successor ρ * θ)
      (fun d ↦ scalarRotation (γ d)) (fun d ↦ labels ρ a (θ d)) (fun _ ↦ scalarRotation_unitary _))
    KervaireMatrix.phase (weightedShift (successor ρ * θ)
      (fun d ↦ scalarRotation (γ d)) (fun d ↦ labels ρ a (θ d))) ≤
        3/2 * (Fintype.card I : ℝ) * Fintype.card K - Fintype.card K := by
  obtain ⟨X,hX⟩ := exists_band_mixer s hs hsum θ hθ hop γ hγ
  have hTu := monomial_unitary θ (fun d ↦ scalarRotation (γ d)) (fun d ↦ scalarRotation_unitary _)
  have hTs := monomial_selfadjoint θ hθ (fun d ↦ scalarRotation (γ d)) (by
    intro d
    rw [hγ,star_scalarRotation])
  have hb := phase_upper_of_fixed ρ a _ hTu hTs X hX
  simpa only [S_mul_bands] using hb
end
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular KervaireMixing KervaireTraversal
open scoped Classical
variable {I K Z A : Type*} [Fintype I] [Fintype K] [Fintype Z] [Group A]
  [Nonempty I] [Nonempty K]
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot_1
theorem planar_boundary
    (ρ : Equiv.Perm I) (a : I → A) (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ Slot I K)
    (he : ∀ z i, ((successor (K := K) ρ : Equiv.Perm (Slot I K)) * θ) (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (hconn : ∀ d f, Relation.ReflTransGen (fun d f => f = successor ρ d ∨ f = θ d) d f)
    (hEuler : Fintype.card Z + 2*Fintype.card K = 2+Fintype.card I*Fintype.card K)
    (z₀ : Z)
    (hc : ∀ z, z ≠ z₀ → orbitWeight (finRotate (n z+1))
      (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0 = 1) :
    orbitWeight (finRotate (n z₀+1))
      (fun i ↦ labels ρ a (θ (e ⟨z₀,i⟩))) (n z₀+1) 0 = 1 := by
  let _ : Nonempty Z := ⟨z₀⟩
  let b : Slot I K → Z := fun d ↦ (e.symm d).1
  let c : Z → A := fun z ↦ orbitWeight (finRotate (n z+1))
    (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0
  have hb : Function.Surjective b := fun z ↦ ⟨e ⟨z,0⟩,by simp [b]⟩
  have hbcycle (d : Slot I K) : b (successor ρ (θ d)) = b d := by
    obtain ⟨⟨z,i⟩,rfl⟩ := e.surjective d
    change b (((successor (K := K) ρ : Equiv.Perm (Slot I K)) * θ) (e ⟨z,i⟩)) = _
    rw [he]
    simp [b]
  have hbconn := KervaireFlow.dual_connected b hb (successor ρ) θ hθ hbcycle hconn
  apply trivial_of_boundary_inequalities z₀ c
  intro ε hε hε1
  let η : Z → ℝ := fun z ↦ (if z = z₀ then (Fintype.card Z : ℝ)*ε else 0) - ε
  have ηroot : η z₀ = ((Fintype.card Z : ℝ)-1)*ε := by simp only [η,ite_true,eq_self]; ring
  have ηother (z : Z) (hz : z ≠ z₀) : η z = -ε := by simp [η,hz]
  have hη : ∑ z, η z = 0 := by
    simp [η,Finset.sum_sub_distrib]
  obtain ⟨γ,hγ,hdiv⟩ := KervaireFlow.exists_flow b θ hθ hbconn z₀ η hη
  have hu := boundary_phase_upper ρ a s hs hsum θ hθ hop γ hγ
  have hphase := phase_boundary_cycles n e ((successor (K := K) ρ : Equiv.Perm (Slot I K)) * θ) he γ
    (fun d ↦ labels ρ a (θ d)) η hdiv
  rw [hphase] at hu
  have hq : (Fintype.card Z : ℝ)+2*Fintype.card K = 2+(Fintype.card I : ℝ)*Fintype.card K := by
    exact_mod_cast hEuler
  have hsumphase : (∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z)) ≤
      (Fintype.card Z : ℝ)-1 := by
    simp only [Slot,Fintype.card_prod,Fintype.card_sum,Nat.cast_mul,Nat.cast_add] at hu
    change _ + (∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z)) ≤ _ at hu
    linarith
  have heq (z : Z) : groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z) =
      (1-ε) + if z = z₀ then groupPhase (scalarRotation (η z₀)) (scalarRotation_unitary _) (c z₀) - (1-ε) else 0 := by
    by_cases hz : z = z₀
    · subst z
      simp
    · have hcz : c z = 1 := hc z hz
      simp only [ite_eq_right hz,add_zero,hcz,ηother z hz,groupPhase_rotation_one hε hε1]
  have htotal : (∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z)) =
      groupPhase (scalarRotation (((Fintype.card Z : ℝ)-1)*ε)) (scalarRotation_unitary _) (c z₀)
        + ((Fintype.card Z : ℝ)-1)*(1-ε) := by
    rw [Finset.sum_congr rfl (fun z _ ↦ heq z)]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true,ηroot]
    ring
  rwa [htotal] at hsumphase
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
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular KervaireMixing KervaireTraversal
open scoped Classical
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot_1


theorem solution : type_of% @_root_.OAI.KervaireBoundary.planar_boundary := @_root_.OAI.KervaireBoundary.planar_boundary
