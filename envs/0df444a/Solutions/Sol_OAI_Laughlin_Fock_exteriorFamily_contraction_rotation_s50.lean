-- Prove2me | solution 1 for OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:13:53.852175+00:00
-- url     : https://prove2.me/submissions/90654baa-9c55-4d28-b294-e97a494e3e91

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_exteriorRotation_unitary_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbitalRotation_mul (Q : ℕ) (g h : SourceSU2) :
    (orbitalRotation Q g).comp (orbitalRotation Q h) = orbitalRotation Q (g*h) := by
  apply LinearMap.ext
  intro v
  funext i
  change (sourceSpinRepresentation Q g *ᵥ (sourceSpinRepresentation Q h *ᵥ v)) i = _
  rw [Matrix.mulVec_mulVec,← map_mul]
  rfl

theorem orbitalRotation_one (Q : ℕ) : orbitalRotation Q 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  simp [orbitalRotation]

theorem exteriorRotation_mul (Q : ℕ) (g h : SourceSU2) (x : Space Q) :
    exteriorRotation Q g (exteriorRotation Q h x) = exteriorRotation Q (g*h) x := by
  change ((ExteriorAlgebra.map (orbitalRotation Q g)).comp
    (ExteriorAlgebra.map (orbitalRotation Q h))) x = _
  rw [ExteriorAlgebra.map_comp_map,orbitalRotation_mul]
  rfl

theorem exteriorRotation_one (Q : ℕ) (x : Space Q) : exteriorRotation Q 1 x = x := by
  unfold exteriorRotation
  rw [orbitalRotation_one,ExteriorAlgebra.map_id]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_FamilyCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem occupationInner_basis_left (Q : ℕ) (A : Finset (Fin (Q+1))) (x : Space Q) :
    occupationInner Q (occupationBasis Q A) x = (occupationBasis Q).repr x A := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem occupationInner_ext_right (Q : ℕ) (x y : Space Q)
    (h : ∀ z, occupationInner Q z x = occupationInner Q z y) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  simpa only [occupationInner_basis_left] using h (occupationBasis Q A)

theorem occupationInner_rotation_left (Q : ℕ) (g : SourceSU2) (x y : Space Q) :
    occupationInner Q (exteriorRotation Q g⁻¹ x) y =
      occupationInner Q x (exteriorRotation Q g y) := by
  have h := exteriorRotation_unitary_s50 Q g (exteriorRotation Q g⁻¹ x) y
  rw [exteriorRotation_mul,mul_inv_cancel,exteriorRotation_one] at h
  exact h.symm

theorem exteriorFamily_contraction_rotation_s50_oai {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (v : I → Space Q) (minus : I → Module.End ℂ (Space Q))
    (ha : ∀ i x y, occupationInner Q (v i*x) y = occupationInner Q x (minus i y))
    (hv : ∀ g i, exteriorRotation Q g (v i) = ∑ j, ρ g j i • v j)
    (g : SourceSU2) (i : I) (x : Space Q) :
    minus i (exteriorRotation Q g x) = ∑ j, ρ g i j • exteriorRotation Q g (minus j x) := by
  apply occupationInner_ext_right Q
  intro y
  rw [← ha,← occupationInner_rotation_left,map_mul,hv]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,occupationInner_smul_left,
    ha,hρ,Matrix.conjTranspose_apply,star_star,occupationInner_sum_right,occupationInner_smul_right,
    occupationInner_rotation_left]

end Laughlin.Fock

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50_oai.{u_1} := @OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50_oai.{u_1}
