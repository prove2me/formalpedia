-- Prove2me | solution 1 for OAI.Laughlin.Fock.physicalLimitGram_eq_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:53:25.737199+00:00
-- url     : https://prove2.me/submissions/4301184e-659f-4055-9cf7-82e2df63c406

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L008
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_occupation_coefficient_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Scaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem copyWeight_nonneg (D : ℕ) (i : Fin ((D+1)/2)) : 0 ≤ (copyWeight D i : ℝ) := by
  unfold copyWeight
  positivity

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Matrix Topology
open Filter

theorem sourceCopyWeight_certificate (D : ℕ) (i : Fin ((D+1)/2)) :
    sourceCopyWeight D (Certificate.copyLabel i) = (Certificate.copyWeight D i : ℝ) := by
  simp [sourceCopyWeight,Certificate.copyWeight]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_OccupationCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourColumn_gram_occupation (Q r s D : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) :
    occupationInner Q (limitFourColumn Q r D) (limitFourColumn Q s D) =
      ((∑ A : Finset (Fin (Q+1)), fourOccupationCoefficient Q r D A *
        fourOccupationCoefficient Q s D A : ℝ) : ℂ) := by
  simp [occupationInner,limitFourColumn_occupation_coefficient_s50 Q r D hr hor,
    limitFourColumn_occupation_coefficient_s50 Q s D hs hos]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Quadruples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

private theorem quadTail_nodup (D a b : ℕ) : (quadTail D a b).Nodup := by
  apply List.Nodup.filterMap _ List.nodup_range
  intro c c' t hc hc'
  dsimp only at hc hc'
  split_ifs at hc with h
  · split_ifs at hc' with h'
    · simp only [Option.mem_def,Option.some.injEq] at hc hc'
      have he := hc.trans hc'.symm
      exact congrArg (fun u : ℕ×ℕ×ℕ×ℕ => u.2.2.1) he
    · simp at hc'
  · simp at hc

theorem quadruples_nodup (D : ℕ) : (quadruples D).Nodup := by
  change ((List.range (D+2)).flatMap
    (fun a => (List.range (D+2)).flatMap (quadTail D a))).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro a ha
    apply List.nodup_flatMap.mpr
    constructor
    · intro b hb; exact quadTail_nodup D a b
    · apply List.nodup_range.imp
      intro b b' hne t ht ht'
      obtain ⟨x,y,z,w⟩ := t
      have h := (mem_quadTail D a b x y z w).mp ht
      have h' := (mem_quadTail D a b' x y z w).mp ht'
      exact hne (h.2.1.symm.trans h'.2.1)
  · apply List.nodup_range.imp
    intro a a' hne t ht ht'
    obtain ⟨b,hb,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b',hb',ht'⟩ := List.mem_flatMap.mp ht'
    obtain ⟨x,y,z,w⟩ := t
    have h := (mem_quadTail D a b x y z w).mp ht
    have h' := (mem_quadTail D a' b' x y z w).mp ht'
    exact hne (h.1.symm.trans h'.1)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_FourOccupationEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_fourOccupations (Q D : ℕ) (hQ : D+1 ≤ Q) (f : (ℕ×ℕ×ℕ×ℕ) → ℝ) :
    ∑ A : FourOccupation Q D, f (occupationQuadruple Q D A).val =
      ((Certificate.quadruples D).map f).sum := by
  classical
  let : Fintype {t : ℕ×ℕ×ℕ×ℕ // t ∈ Certificate.quadruples D} :=
    Fintype.ofFinset (Certificate.quadruples D).toFinset (by intro t; change t ∈ (Certificate.quadruples D).toFinset ↔ t ∈ Certificate.quadruples D; simp)
  rw [← List.sum_toFinset f (Certificate.quadruples_nodup D)]
  rw [Finset.sum_subtype (p := fun t => t ∈ Certificate.quadruples D) (Certificate.quadruples D).toFinset (by simp)]
  exact (fourOccupationEquiv Q D hQ).sum_comp (fun t => f t.val)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Spin

private theorem sqrt_weight_product (u v f : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hf : 0 ≤ f) :
    Real.sqrt (u/f)*Real.sqrt (v/f) = Real.sqrt (u*v)/f := by
  rw [Real.sqrt_div hu,Real.sqrt_div hv]

  rw [div_mul_div_comm,Real.mul_self_sqrt hf,← Real.sqrt_mul hu]

private theorem fourOccupation_product (Q r s D : ℕ) (A : FourOccupation Q D) :
    fourOccupationCoefficient Q r D A.val * fourOccupationCoefficient Q s D A.val =
      let t := (occupationQuadruple Q D A).val
      Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
        ((Certificate.L D r t : ℝ)*(Certificate.L D s t : ℝ) /
          ((t.1.factorial : ℝ)*t.2.1.factorial*t.2.2.1.factorial*t.2.2.2.factorial)) := by
  simp only [fourOccupationCoefficient,dite_eq_left A.property.1,ite_eq_left A.property.2,occupationQuadruple]
  have hr : 0 ≤ sourceCopyWeight D r := by unfold sourceCopyWeight; positivity
  have hs : 0 ≤ sourceCopyWeight D s := by unfold sourceCopyWeight; positivity
  have hf : 0 ≤ (((occupationFourLabels Q A.val A.property.1 0).val.factorial : ℝ) *
    (occupationFourLabels Q A.val A.property.1 1).val.factorial *
    (occupationFourLabels Q A.val A.property.1 2).val.factorial *
    (occupationFourLabels Q A.val A.property.1 3).val.factorial) := by positivity
  rw [show ∀ a b c d : ℝ, (a*b)*(c*d)=(a*c)*(b*d) from by intros; ring,
    sqrt_weight_product _ _ _ hr hs hf]
  ring

theorem source_fourBody_physical_Gram (Q r s D : ℕ) (hQ : D+1 ≤ Q)
    (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s) :
    occupationInner Q (limitFourColumn Q r D) (limitFourColumn Q s D) =
      ((Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
        (Certificate.Z D r s : ℝ) : ℝ) : ℂ) := by
  classical
  rw [limitFourColumn_gram_occupation Q r s D hr hs hor hos]
  congr 1
  let P := fun A : Finset (Fin (Q+1)) => A.card=4 ∧ (∑ i ∈ A, i.val)=D+1
  let f := fun A => fourOccupationCoefficient Q r D A * fourOccupationCoefficient Q s D A
  have hsum : ∑ A, f A = ∑ A ∈ Finset.univ.filter P, f A := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn
    by_cases hc : A.card=4
    · have hw : (∑ i ∈ A, i.val) ≠ D+1 := by intro hw; exact hn ⟨hc,hw⟩
      simp [f,fourOccupationCoefficient,hc,hw]
    · simp [f,fourOccupationCoefficient,hc]
  change ∑ A, f A = _
  rw [hsum,Finset.sum_subtype (p := P) (Finset.univ.filter P) (by simp)]
  change (∑ A : FourOccupation Q D, fourOccupationCoefficient Q r D A.val *
    fourOccupationCoefficient Q s D A.val) = _
  simp_rw [fourOccupation_product]
  rw [← Finset.mul_sum,sum_fourOccupations Q D hQ (fun t =>
    (Certificate.L D r t : ℝ)*(Certificate.L D s t : ℝ) /
      ((t.1.factorial : ℝ)*t.2.1.factorial*t.2.2.1.factorial*t.2.2.2.factorial))]
  simp only [Certificate.Z]
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  rfl

theorem source_fourBody_physical_scaledGram (Q D : ℕ) (hQ : D+1 ≤ Q)
    (i j : Fin ((D+1)/2)) :
    occupationInner Q (limitFourColumn Q (Certificate.copyLabel i) D)
      (limitFourColumn Q (Certificate.copyLabel j) D) =
      (Certificate.scaledGram D i j : ℂ) := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hj : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  rw [source_fourBody_physical_Gram Q _ _ D hQ hi hj
    ⟨i.val,by unfold Certificate.copyLabel; omega⟩ ⟨j.val,by unfold Certificate.copyLabel; omega⟩,
    sourceCopyWeight_certificate,sourceCopyWeight_certificate,
    Real.sqrt_mul (Certificate.copyWeight_nonneg D i)]
  simp only [Certificate.scaledGram,Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Certificate.gramRational,Rat.coe_castHom]
  push_cast
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix

theorem physicalLimitGram_eq_s50_oai (Q D : ℕ) (hQ : D+1 ≤ Q) :
    physicalLimitGram Q D = Certificate.scaledGram D := by
  ext i j
  simp [physicalLimitGram,source_fourBody_physical_scaledGram Q D hQ]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physicalLimitGram_eq_s50_oai := @OAI.Laughlin.Fock.physicalLimitGram_eq_s50_oai
