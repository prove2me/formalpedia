-- Prove2me | solution 1 for OAI.KervaireMixing.phase_upper_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:46:29.633111+00:00
-- url     : https://prove2.me/submissions/c795010d-08bf-40b7-a752-e2ecb28dd224

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Traversal.lean:L279-L329
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMixing.phase_upper_of_fixed. The node keeps its source
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
import Theorems.Thm_OAI_KervaireCentralizer_phase_subadditive
import Theorems.Thm_OAI_KervaireMatrix_phase_scalar_le_codim
import Theorems.Thm_OAI_KervaireMatrix_trace_mul_comm
import Theorems.Thm_OAI_KervaireMixing_phase_SJ

-- ---- from OAI.GroupTheory.Kervaire.MatrixTrace ----
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
variable {D A : Type*} [Group A]
variable [Fintype D]

end

section
open KervaireRegular
variable {D A : Type*} [Fintype D] [Group A]

end

section
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Group A]

theorem mem_algebra (T : Operator D A) : T ∈ algebra ↔ InCommutant T := by
  rw [algebra, KervaireCentralizer.algebra, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact ((h (right (D := D) a) ⟨a,rfl⟩).1).symm
  · intro h R hR
    obtain ⟨a,rfl⟩ := hR
    rw [right_star]
    exact ⟨(h a).symm, (h a⁻¹).symm⟩

variable [Fintype D]

/-- The vector family agrees exactly with the unnormalized matrix trace. -/
theorem trace_eq_vectorSum : (trace : Operator D A →L[ℂ] ℂ) =
    vectorSum (fun i : D => (delta (i,(1 : A)))) := rfl

/-- Subadditivity for the full arbitrary-group matrix algebra, with no approximation hypothesis. -/
theorem phase_mul_le [Nonempty D] (U V : algebra (D := D) (A := A))
    (hU : U ∈ unitary (algebra (D := D) (A := A)))
    (hV : V ∈ unitary (algebra (D := D) (A := A))) :
    let _ := isStarNormal_of_mem_unitary ((KervaireCentralizer.unitary_iff _ U).mp hU)
    let _ := isStarNormal_of_mem_unitary ((KervaireCentralizer.unitary_iff _ V).mp hV)
    let _ := isStarNormal_of_mem_unitary ((KervaireCentralizer.unitary_iff _ (U*V)).mp
      ((unitary _).mul_mem hU hV))
    phase ((U*V : algebra (D := D) (A := A)) : Operator D A) ≤
      phase (U : Operator D A) + phase (V : Operator D A) := by
  apply KervaireCentralizer.phase_subadditive _ _ _ U V hU hV
  intro X Y
  change vectorSum _ ((X : Operator D A)*(Y : Operator D A)) =
    vectorSum _ ((Y : Operator D A)*(X : Operator D A))
  rw [← trace_eq_vectorSum]
  exact trace_mul_comm ((mem_algebra _).mp X.property) ((mem_algebra _).mp Y.property)

end

open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

omit [Fintype D] in
theorem InCommutant.mul {S T : Operator D A} (hS : InCommutant S) (hT : InCommutant T) :
    InCommutant (S*T) := fun a => (hS a).mul_left (hT a)

end KervaireMatrix

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

/-- Scalar matrices lie in exactly the commutant required by the phase theorem. -/
theorem scalarTensor_mem_commutant (M : Matrix D D ℂ) :
    InCommutant (scalarTensor (A := A) M) := by
  intro a
  change scalarTensor M * (right (D := D) a).toContinuousLinearEquiv.toContinuousLinearMap = _
  ext f ⟨d,x⟩
  simp [mul_apply_eq_comp]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

/-- The commutant contains every group-labelled shift. -/
theorem labelledShift_mem_commutant (σ : Equiv.Perm D) (a : D → A) :
    InCommutant (labelledShift σ a) := by
  intro x
  change labelledShift σ a * (right (D := D) x : Operator D A) = _
  ext f ⟨d,y⟩
  simp [mul_apply_eq_comp, mul_assoc]

variable [Fintype D]

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

theorem mixingMatrix_unitary (X : Matrix.unitaryGroup K ℂ) :
    mixingMatrix (I := I) (X : Matrix K K ℂ) ∈ Matrix.unitaryGroup (Slot I K) ℂ := by
  rw [Unitary.mem_iff, mixingMatrix_star, mixingMatrix_sq]
  exact ⟨rfl,rfl⟩

omit [Fintype I] [Fintype K] in
theorem S_commutant (ρ : Equiv.Perm I) (a : I → A) : InCommutant (S (K := K) ρ a) :=
  labelledShift_mem_commutant _ _
theorem J_commutant (X : Matrix K K ℂ) : InCommutant (J (I := I) (A := A) X) :=
  scalarTensor_mem_commutant _

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

variable {A : Type*} [Group A]
end KervaireMatrix

namespace KervaireMixing
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]
attribute [local instance] OAI.KervaireMixing.instDecidableEqSlot
lemma phase_upper_of_fixed (ρ : Equiv.Perm I) (a : I → A)
    (T : Matrix (Slot I K) (Slot I K) ℂ)
    (hT : T ∈ unitary (Matrix (Slot I K) (Slot I K) ℂ)) (hTs : star T = T)
    (X : Matrix.unitaryGroup K ℂ)
    (hfix : 2 * Fintype.card K ≤ fixedDim (mixingMatrix (I := I) (X : Matrix K K ℂ) * T)) :
    let _ := isStarNormal_of_mem_unitary
      (mul_mem (S_unitary (K := K) ρ a) (scalarTensor_mem_unitary (A := A) hT))
    KervaireMatrix.phase (S ρ a * scalarTensor (A := A) T) ≤
      3 / 2 * (Fintype.card I : ℝ) * Fintype.card K - Fintype.card K := by
  let Q := mixingMatrix (I := I) (X : Matrix K K ℂ)
  have hQ : Q ∈ unitary (Matrix (Slot I K) (Slot I K) ℂ) := by
    constructor
    · convert (mixingMatrix_unitary (I := I) X).1 using 1
      ext i j
      simp [Matrix.one_apply]
    · convert (mixingMatrix_unitary (I := I) X).2 using 1
      ext i j
      simp [Matrix.one_apply]
  have hQs : star Q = Q := mixingMatrix_star _
  have hconj : Q * (Q*T) * star Q = star (Q*T) := by
    have hsq : Q*Q = 1 := by simpa only [hQs] using hQ.1
    rw [← mul_assoc,hsq,one_mul,star_mul,hTs]
  have hb := phase_scalar_le_codim (A := A) (Q*T) Q (mul_mem hQ hT) hQ hconj
  let U : algebra (D := Slot I K) (A := A) :=
    ⟨S ρ a * J (I := I) (X : Matrix K K ℂ),
      (mem_algebra _).mpr ((S_commutant ρ a).mul (J_commutant _))⟩
  let V : algebra (D := Slot I K) (A := A) :=
    ⟨scalarTensor (A := A) (Q*T), (mem_algebra _).mpr (scalarTensor_mem_commutant _)⟩
  have hU : U ∈ unitary (algebra (D := Slot I K) (A := A)) :=
    (KervaireCentralizer.unitary_iff _ U).mpr (mul_mem (S_unitary ρ a) (J_unitary X))
  have hV : V ∈ unitary (algebra (D := Slot I K) (A := A)) :=
    (KervaireCentralizer.unitary_iff _ V).mpr (scalarTensor_mem_unitary (mul_mem hQ hT))
  have hUV : ((U*V : algebra (D := Slot I K) (A := A)) : Operator (Slot I K) A) =
      S ρ a * scalarTensor (A := A) T := by
    change (S ρ a * J (I := I) (X : Matrix K K ℂ)) * scalarTensor (Q*T) = _
    rw [scalarTensor_mul]
    change (S ρ a * J (I := I) (X : Matrix K K ℂ)) * (J (X : Matrix K K ℂ) * scalarTensor T) = _
    rw [← mul_assoc,mul_assoc (S ρ a),J_sq,mul_one]
  let _ := isStarNormal_of_mem_unitary (mul_mem (S_unitary (K := K) ρ a) (scalarTensor_mem_unitary (A := A) hT))
  let _ := isStarNormal_of_mem_unitary (mul_mem (S_unitary (K := K) ρ a) (J_unitary (I := I) X))
  let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) (mul_mem hQ hT))
  have hsub := phase_mul_le U V hU hV
  change KervaireMatrix.phase (S ρ a * scalarTensor (A := A) T) ≤ _
  have hsub' : KervaireMatrix.phase (S ρ a * scalarTensor (A := A) T) ≤
      KervaireMatrix.phase (S ρ a * J (I := I) (X : Matrix K K ℂ)) +
      KervaireMatrix.phase (scalarTensor (A := A) (Q*T)) := by
    simpa only [hUV] using hsub
  rw [phase_SJ] at hsub'
  have hc : (2 : ℝ) * Fintype.card K ≤ fixedDim (Q*T) := by exact_mod_cast hfix
  simp only [Slot,Fintype.card_prod,Fintype.card_sum,Nat.cast_mul,Nat.cast_add] at hb
  linarith
end KervaireMixing

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireMixing
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
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
attribute [local instance] OAI.KervaireMixing.instDecidableEqSlot


theorem solution : type_of% @_root_.OAI.KervaireMixing.phase_upper_of_fixed := @_root_.OAI.KervaireMixing.phase_upper_of_fixed
