-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeDropPresentation.central_no_character
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:33:51.430978+00:00
-- url     : https://prove2.me/submissions/48824ec1-71ba-4b5d-ab98-cc46f66b786d

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr013
import Definitions.Def_OAIB3Kr014
import Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_Channels_finite_control

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_NormUltrapower
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]


open Filter Topology BoundedContinuousFunction

universe uQuot

namespace KirchbergRordam
namespace NormUltrapower

variable {A : Type*} [CStarAlgebra A]


theorem mem_central_iff (ω : Ultrafilter ℕ) (z : Algebra A ω) :
    z ∈ centralSubalgebra ω ↔ ∀ a : A, diagonal ω a * z = z * diagonal ω a := by
  change z ∈ StarSubalgebra.centralizer ℂ (Set.range (diagonal ω)) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h (diagonal ω a) ⟨a, rfl⟩).1
  · intro h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨h a, by simpa only [map_star] using h (star a)⟩


end NormUltrapower
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_InductiveLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PrimeDropPresentation.instSeparableSpaceObjSystem _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


open scoped TensorProduct CStarAlgebra


namespace KirchbergRordam.CStarInductiveLimit
section
universe u


attribute [instance] System.cstar


variable {C : Type*} [CStarAlgebra C]


theorem induction_on (S : System) {P : Algebra S → Prop} (x : Algebra S)
    (hclosed : IsClosed {x | P x}) (hof : ∀ n x, P (of S n x)) : P x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih x =>
    refine DirectLimit.induction S.map ?_ x
    exact hof


theorem denseRange_of (S : System) :
    DenseRange (fun p : Σ n, S.obj n => of S p.1 p.2) := by
  intro x
  exact induction_on S x isClosed_closure
    (fun n x => subset_closure ⟨⟨n,x⟩,rfl⟩)


instance instSeparableSpaceAlgebraOfObj (S : System) [∀ n, TopologicalSpace.SeparableSpace (S.obj n)] :
    TopologicalSpace.SeparableSpace (Algebra S) :=
  (denseRange_of S).separableSpace (continuous_sigma fun n => map_continuous (of S n))

end

universe u


attribute [instance] Chain.cstar


end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder

theorem matrixUnit_mul_self {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    matrixUnit i j * matrixUnit i j = 0 := by
  unfold matrixUnit
  rw [← map_mul, Matrix.single_mul_single_of_ne (1 : ℂ) i j i h.symm (1 : ℂ), map_zero]

theorem leftCone_mul_self (a : M2) (ha : a * a = 0) :
    leftCone a * leftCone a = 0 := by
  apply drop_ext
  intro t
  change ((1 - ((t : ℝ) : ℂ)) • leftMatrix a) *
    ((1 - ((t : ℝ) : ℂ)) • leftMatrix a) = 0
  rw [smul_mul_smul, ← map_mul, ha, map_zero, smul_zero]

theorem rightCone_mul_self (a : M3) (ha : a * a = 0) :
    rightCone a * rightCone a = 0 := by
  apply drop_ext
  intro t
  change (((t : ℝ) : ℂ) • rightMatrix a) *
    (((t : ℝ) : ℂ) • rightMatrix a) = 0
  rw [smul_mul_smul, ← map_mul, ha, map_zero, smul_zero]

theorem matrixUnit_two_diagonal :
    matrixUnit (0 : Fin 2) 0 + matrixUnit 1 1 = 1 := by
  apply CStarMatrix.ext
  intro i j
  change Matrix.single (0 : Fin 2) 0 (1 : ℂ) i j + Matrix.single 1 1 1 i j =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single, Fin.ext_iff]

theorem matrixUnit_three_diagonal :
    matrixUnit (0 : Fin 3) 0 + matrixUnit 1 1 + matrixUnit 2 2 = 1 := by
  apply CStarMatrix.ext
  intro i j
  change Matrix.single (0 : Fin 3) 0 (1 : ℂ) i j + Matrix.single 1 1 1 i j +
    Matrix.single 2 2 1 i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single, Fin.ext_iff]

theorem drop_left_identity :
    leftCone (matrixUnit 0 1) * leftCone (matrixUnit 1 0) +
      leftCone (matrixUnit 1 0) * leftCone (matrixUnit 0 1) = (1 - dropCoordinate) ^ 2 := by
  apply drop_ext
  intro t
  let z : ℂ := (t : ℝ)
  change ((1-z) • leftMatrix (matrixUnit 0 1)) * ((1-z) • leftMatrix (matrixUnit 1 0)) +
    ((1-z) • leftMatrix (matrixUnit 1 0)) * ((1-z) • leftMatrix (matrixUnit 0 1)) =
      ((1 : M6) - z • 1) ^ 2
  rw [smul_mul_smul, smul_mul_smul, ← map_mul, ← map_mul,
    matrixUnit_mul, matrixUnit_mul, ← smul_add, ← map_add,
    matrixUnit_two_diagonal, map_one]
  have h : (1 : M6) - z • 1 = (1-z) • (1 : M6) := by rw [sub_smul, one_smul]
  rw [h, pow_two, smul_mul_smul, mul_one]

theorem drop_right_identity :
    rightCone (matrixUnit 0 1) * rightCone (matrixUnit 1 0) +
      rightCone (matrixUnit 1 0) * rightCone (matrixUnit 0 1) +
      rightCone (matrixUnit 2 0) * rightCone (matrixUnit 0 2) = dropCoordinate ^ 2 := by
  apply drop_ext
  intro t
  let z : ℂ := (t : ℝ)
  change (z • rightMatrix (matrixUnit 0 1)) * (z • rightMatrix (matrixUnit 1 0)) +
    (z • rightMatrix (matrixUnit 1 0)) * (z • rightMatrix (matrixUnit 0 1)) +
    (z • rightMatrix (matrixUnit 2 0)) * (z • rightMatrix (matrixUnit 0 2)) =
      (z • (1 : M6)) ^ 2
  rw [smul_mul_smul, smul_mul_smul, smul_mul_smul, ← map_mul, ← map_mul, ← map_mul,
    matrixUnit_mul, matrixUnit_mul, matrixUnit_mul, ← smul_add, ← smul_add,
    ← map_add, ← map_add, matrixUnit_three_diagonal, map_one,
    pow_two, smul_mul_smul, mul_one]


theorem dimensionDrop23_no_ringhom : IsEmpty (DimensionDrop23 →+* ℂ) := by
  refine ⟨fun f => ?_⟩
  have kill {x : DimensionDrop23} (hx : x * x = 0) : f x = 0 := by
    apply eq_zero_of_mul_self_eq_zero
    rw [← map_mul, hx, map_zero]
  have hL (i j : Fin 2) (h : i ≠ j) : f (leftCone (matrixUnit i j)) = 0 :=
    kill (leftCone_mul_self _ (matrixUnit_mul_self i j h))
  have hR (i j : Fin 3) (h : i ≠ j) : f (rightCone (matrixUnit i j)) = 0 :=
    kill (rightCone_mul_self _ (matrixUnit_mul_self i j h))
  have hl : f (1 - dropCoordinate) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [← map_pow, ← drop_left_identity]
    simp only [map_add, map_mul, hL 0 1 (by decide), hL 1 0 (by decide), zero_mul, add_zero]
  have hr : f dropCoordinate = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [← map_pow, ← drop_right_identity]
    simp only [map_add, map_mul, hR 0 1 (by decide), hR 1 0 (by decide),
      hR 2 0 (by decide), zero_mul, add_zero]
  apply one_ne_zero (α := ℂ)
  simpa only [map_sub, map_one, hr, sub_zero] using hl


end KirchbergRordam


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MultiplicativeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.MultiplicativeChannel
open scoped CStarAlgebra ComplexOrder
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}
variable {C : Type*} [CStarAlgebra C]
lemma no_character_of_pair (φ ψ : Channel DimensionDrop23 B) (h : φ 1+ψ 1=1) :
    IsEmpty (B →⋆ₐ[ℂ] ℂ) := by
  refine ⟨fun χ => ?_⟩
  have hs := congrArg χ h
  simp only [_root_.map_add,_root_.map_one] at hs
  by_cases hφ : χ (φ 1)=0
  · have hψ : χ (ψ 1)≠0 := by rw [hφ,zero_add] at hs; rw [hs]; exact one_ne_zero
    exact dimensionDrop23_no_ringhom.false (normalized ψ χ hψ)
  · exact dimensionDrop23_no_ringhom.false (normalized φ χ hφ)

end KirchbergRordam.MultiplicativeChannel
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.MultiplicativeChannel
open Filter Topology TopologicalSpace
open scoped CStarAlgebra ComplexOrder
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]

lemma sequence_central [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) (φ : ℕ → Channel D A)
    (hφ : ∀ i d, Tendsto (fun n => ‖φ n d*denseSeq A i-denseSeq A i*φ n d‖) atTop (𝓝 0)) :
    ∀ d, postcompose (sequence φ) (NormUltrapower.quotientMap ω) d∈NormUltrapower.centralSubalgebra ω := by
  intro d
  rw [NormUltrapower.mem_central_iff]
  intro a
  let z := NormUltrapower.quotientMap ω (sequence φ d)
  change NormUltrapower.diagonal ω a*z=z*NormUltrapower.diagonal ω a
  refine (denseRange_denseSeq A).induction_on a
    (p := fun a => NormUltrapower.diagonal ω a*z=z*NormUltrapower.diagonal ω a)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro i
  have hz := (hφ i d).mono_left (by simpa only [Nat.cofinite_eq_atTop] using hω)
  have he : sequence φ d*NormUltrapower.constantSeq (denseSeq A i)-
      NormUltrapower.constantSeq (denseSeq A i)*sequence φ d∈NormUltrapower.nullIdeal ω :=
    (NormUltrapower.mem_nullIdeal ω _).mpr hz
  have heq := Ideal.Quotient.eq.mpr he
  exact heq.symm


theorem no_central_character_of_finite_channels [TopologicalSpace.SeparableSpace A]
    (H : ∀ (F : Finset A) (ε : ℝ), 0<ε →
      ∃ φ ψ : Channel DimensionDrop23 A, φ 1+ψ 1=1 ∧
        ∀ a∈F, ∀ d : DimensionDrop23,
          ‖φ d*a-a*φ d‖≤ε*‖d‖ ∧ ‖ψ d*a-a*ψ d‖≤ε*‖d‖)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ) := by
  classical
  choose φ ψ hu hc using fun n : ℕ =>
    H ((Finset.range n).image (denseSeq A)) (1/((n:ℝ)+1)) (by positivity)
  have hz (r : ℕ → Channel DimensionDrop23 A)
      (hr : ∀ n i, i<n → ∀ d, ‖r n d*denseSeq A i-denseSeq A i*r n d‖≤(1/((n:ℝ)+1))*‖d‖) :
      ∀ i d, Tendsto (fun n => ‖r n d*denseSeq A i-denseSeq A i*r n d‖) atTop (𝓝 0) := by
    intro i d
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (g := fun n : ℕ => (1/((n:ℝ)+1))*‖d‖)
    · filter_upwards [eventually_gt_atTop i] with n hn
      exact hr n i hn d
    · simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖d‖
  have hl := sequence_central ω hω φ (hz φ (fun n i hi d =>
    (hc n (denseSeq A i) (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)) d).1))
  have hr := sequence_central ω hω ψ (hz ψ (fun n i hi d =>
    (hc n (denseSeq A i) (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)) d).2))
  let l := centralize ω (postcompose (sequence φ) (NormUltrapower.quotientMap ω)) hl
  let r := centralize ω (postcompose (sequence ψ) (NormUltrapower.quotientMap ω)) hr
  apply no_character_of_pair l r
  apply Subtype.ext
  change NormUltrapower.quotientMap ω (sequence φ 1)+NormUltrapower.quotientMap ω (sequence ψ 1)=1
  rw [←_root_.map_add,←_root_.map_one (NormUltrapower.quotientMap ω)]
  congr 1
  ext n
  exact hu n
end KirchbergRordam.MultiplicativeChannel
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
instance instSeparableSpaceAlgebra : TopologicalSpace.SeparableSpace S.Algebra := inferInstanceAs (TopologicalSpace.SeparableSpace (CStarInductiveLimit.Algebra S.system))
end KirchbergRordam.PrimeDropPresentation
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open Filter
variable (S : PrimeDropPresentation)


theorem central_no_character_oai (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra S.Algebra ω →⋆ₐ[ℂ] ℂ) :=
  MultiplicativeChannel.no_central_character_of_finite_channels
    (Channels.finite_control S) ω hω


end KirchbergRordam.PrimeDropPresentation
end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.PrimeDropPresentation.central_no_character_oai := @OAI.KirchbergRordam.PrimeDropPresentation.central_no_character_oai
