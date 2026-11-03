-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:27:31.628876+00:00
-- url     : https://prove2.me/submissions/08d4691c-0810-4be5-a067-a4f86a5ef67d

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_contractionForm_haar_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourcePairEnd_rotation_s50
import Theorems.Thm_OAI_Laughlin_Rotation_source_spin_haar_schur_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TensorAction
attribute [-instance] _root_.OAI.Laughlin.Rotation.sourceSU2_borelSpace _root_.OAI.Laughlin.Rotation.sourceSU2_compactSpace _root_.OAI.Laughlin.Rotation.sourceSU2_continuousInv _root_.OAI.Laughlin.Rotation.sourceSU2_measurableSpace _root_.OAI.Laughlin.Rotation.sourceSU2_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem tensorMatrix_conjTranspose (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix N Aᴴ = (tensorMatrix N A)ᴴ := by
  ext a b
  simp [tensorMatrix,Matrix.conjTranspose_apply]

theorem tensorMatrix_unitary (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorMatrix N A ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose,← tensorMatrix_conjTranspose,← tensorMatrix_mul]
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h,tensorMatrix_one]

 theorem sourceTensorRepresentation_unitary (Q : ℕ) (g : SourceSU2) :
    sourceTensorRepresentation Q g ∈ Matrix.unitaryGroup (Fin Q → Fin 2) ℂ :=
  tensorMatrix_unitary Q g.val g.property.1

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Compact
attribute [-instance] _root_.OAI.Laughlin.Rotation.sourceSU2_borelSpace _root_.OAI.Laughlin.Rotation.sourceSU2_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem sourceTensorRepresentation_continuous (Q : ℕ) (a b : Fin Q → Fin 2) :
    Continuous (fun g : SourceSU2 => sourceTensorRepresentation Q g a b) := by
  change Continuous (fun g : SourceSU2 => ∏ i, g.val (a i) (b i))
  exact continuous_finsetProd _ (fun i hi => (continuous_apply (b i)).comp
    ((continuous_apply (a i)).comp continuous_subtype_val))

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem sourceSpinRepresentation_unitary (Q : ℕ) (g : SourceSU2) :
    sourceSpinRepresentation Q g ∈ Matrix.unitaryGroup (Fin (Q+1)) ℂ := by
  have he := congrArg (fun M => Mᴴ*M) (tensor_spin_intertwining Q g)
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceTensorRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  simp only [Matrix.conjTranspose_mul] at he
  have hleft : (sourceSpinMatrix Q g)ᴴ*(symmetricTensorInclusion Q)ᴴ*
      (symmetricTensorInclusion Q*sourceSpinMatrix Q g) = (sourceSpinMatrix Q g)ᴴ*sourceSpinMatrix Q g := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc (symmetricTensorInclusion Q)ᴴ,
      symmetricTensorInclusion_isometry,Matrix.one_mul]
  have hright : (symmetricTensorInclusion Q)ᴴ*(sourceTensorRepresentation Q g)ᴴ*
      (sourceTensorRepresentation Q g*symmetricTensorInclusion Q) = 1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc (sourceTensorRepresentation Q g)ᴴ,hu,
      Matrix.one_mul,symmetricTensorInclusion_isometry]
  rw [hleft,hright] at he
  exact Matrix.mem_unitaryGroup_iff'.mpr he

 theorem sourceSpinRepresentation_continuous (Q : ℕ) (p q : Fin (Q+1)) :
    Continuous (fun g => sourceSpinRepresentation Q g p q) := by
  change Continuous (fun g : SourceSU2 =>
    ((symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*symmetricTensorInclusion Q) p q)
  simp only [Matrix.mul_apply]
  have h := sourceTensorRepresentation_continuous Q
  fun_prop

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Disjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix ComplexOrder

 theorem sourceSpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    sourceSpinRepresentation Q g⁻¹=(sourceSpinRepresentation Q g)ᴴ := by
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  calc
    _ = 1*sourceSpinRepresentation Q g⁻¹ := by rw [Matrix.one_mul]
    _ = ((sourceSpinRepresentation Q g)ᴴ*sourceSpinRepresentation Q g)*sourceSpinRepresentation Q g⁻¹ := by rw [hu]
    _ = _ := by rw [Matrix.mul_assoc,← map_mul,mul_inv_cancel,map_one,Matrix.mul_one]

end Laughlin.Rotation

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

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_EnergyRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourceFockEnergy_eq_fin (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    sourceFockEnergy Q x = ∑ p : Fin (2*Q-2+1), occupationNormSq Q (sourcePairEnd Q p.val x) := by
  unfold sourceFockEnergy
  rw [show 2*Q-1=2*Q-2+1 by omega]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_Certificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate


theorem eta_numerator : (rows.map (fun r => r.2.1 ^ 2)).sum = 93527408868499 := by
  decide

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_smul {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (c : ℂ) (M : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (c • M) x = c * contractionForm Q minus M x := by
  simp only [contractionForm,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem pair_contractionForm_one (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) 1 x =
      (sourceFockEnergy Q x : ℂ) := by
  rw [sourceFockEnergy_eq_fin Q hQ]
  simp [contractionForm,Matrix.one_apply,occupationInner_self,Complex.ofReal_sum]

theorem physical_pairFock_haar (Q : ℕ) (hQ : 0 < Q)
    (M : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) (x : Space Q) :
    (∫ g, contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) M
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      (Matrix.trace M/(2*Q-2+1 : ℕ)) * (sourceFockEnergy Q x : ℂ) := by
  rw [contractionForm_haar_s50 Q (sourceSpinRepresentation (2*Q-2))
    (sourceSpinRepresentation_inv (2*Q-2)) (sourceSpinRepresentation_continuous (2*Q-2))
    _ (sourcePairEnd_rotation_s50 Q hQ),source_spin_haar_schur_s50,contractionForm_smul,
    pair_contractionForm_one Q hQ]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TwoBodyCertificateHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem physicalTwoBodyMatrix_trace (Q : ℕ) (hQ : 5 ≤ Q) :
    Matrix.trace (physicalTwoBodyMatrix Q) = (93527408868499/10^14 : ℂ) := by
  have htr (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows) :
      Matrix.trace (physicalPairRowMatrix Q row) =
      ((row.2.1 : ℂ)/10^7)^2 := by
    have ht : row.1 ≤ 7 := (show ∀ row ∈ Certificate.rows, row.1 ≤ 7 from by decide) row hr
    let p : Fin (2*Q-2+1) := ⟨row.1,by omega⟩
    have he (i : Fin (2*Q-2+1)) : i.val=row.1 ↔ i=p := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; subst i; rfl
    simp only [Matrix.trace,Matrix.diag,physicalPairRowMatrix,he,and_self,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hsum (l : List (Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ)) :
      Matrix.trace l.sum = (l.map Matrix.trace).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.sum_cons,List.map_cons,Matrix.trace_add,ih]
  rw [physicalTwoBodyMatrix,hsum,List.map_map]
  have he : Certificate.rows.map (fun row => Matrix.trace (physicalPairRowMatrix Q row)) =
      Certificate.rows.map (fun row => ((row.2.1 : ℂ)/10^7)^2) := List.map_congr_left htr
  change (Certificate.rows.map (fun row => Matrix.trace (physicalPairRowMatrix Q row))).sum = _
  rw [he]
  have hl (l : List (ℕ × ℤ × List (ℕ × ℕ × ℤ))) :
      (l.map (fun row => ((row.2.1 : ℂ)/10^7)^2)).sum =
        ((l.map (fun row => row.2.1^2)).sum : ℤ)/(10^14 : ℂ) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,Int.cast_add,Int.cast_pow,ih]
      ring
  rw [hl,Certificate.eta_numerator]
  norm_num

theorem physical_twoBody_certificate_haar_s50_oai (Q : ℕ) (hQ : 5 ≤ Q) (x : Space Q) :
    ((2*Q-2+1 : ℕ) : ℂ) * (∫ g, contractionForm Q
      (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) (physicalTwoBodyMatrix Q)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      (93527408868499/10^14 : ℂ) * (sourceFockEnergy Q x : ℂ) := by
  rw [physical_pairFock_haar Q (by omega),physicalTwoBodyMatrix_trace Q hQ]
  have hd : ((2*Q-2+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2*Q-2)
  field_simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50_oai := @OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50_oai
