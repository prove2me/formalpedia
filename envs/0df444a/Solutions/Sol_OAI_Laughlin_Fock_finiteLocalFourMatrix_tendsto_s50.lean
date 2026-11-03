-- Prove2me | solution 1 for OAI.Laughlin.Fock.finiteLocalFourMatrix_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:16:05.82296+00:00
-- url     : https://prove2.me/submissions/44af98c7-0871-492c-ad0e-a3efeb03135d

import Mathlib
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Spin_fourErrorEntry_tendsto_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_coefficient_tendsto_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_error_matrix_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FactorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem modeFactor_sq_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range x, (1/1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) 0 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x) := by
    filter_upwards [eventually_ge_atTop x] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : (Q : ℝ)^x = ∏ _i ∈ Finset.range x, (Q : ℝ) := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ Q)]
      congr 1 <;> ring
  simpa using hp.congr' he

theorem pairFactor_inv_sq_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range p, (2/2 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(2+(i : ℝ))) 0 2 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p) := by
    filter_upwards [eventually_ge_atTop (p+2)] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : ((2 : ℝ)*Q)^p = ∏ _i ∈ Finset.range p, (2 : ℝ)*Q := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
      push_cast
      congr 1 <;> ring
  simpa using hp.congr' he

theorem modeFactor_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => modeFactor Q x) atTop (𝓝 1) := by
  simpa [modeFactor] using (modeFactor_sq_tendsto x).sqrt

theorem pairFactor_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairFactor Q p) atTop (𝓝 1) := by
  have h := ((pairFactor_inv_sq_tendsto p).inv₀ (by norm_num)).sqrt
  simpa [pairFactor, inv_div] using h

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physical_list_sum_tendsto {I : Type*} (l : List I) (f : ℕ → I → ℝ) (g : I → ℝ)
    (h : ∀ i ∈ l, Tendsto (fun Q => f Q i) atTop (𝓝 (g i))) :
    Tendsto (fun Q => (l.map (f Q)).sum) atTop (𝓝 ((l.map g).sum)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

theorem source_rows_admissible : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2,
    row.1 ≤ e.1+e.2.1 := by decide

theorem physicalFourError_tendsto (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D) :
    Tendsto (fun Q => physicalFourError Q D r s) atTop (𝓝 (limitFourError D r s)) := by
  apply Filter.Tendsto.neg
  apply physical_list_sum_tendsto
  intro row hrow
  apply physical_list_sum_tendsto
  intro e he
  apply physical_list_sum_tendsto
  intro f hf
  exact fourErrorEntry_tendsto_s50 D r s row.1 e f hr hs
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)

end Laughlin.Spin

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

theorem physicalFourError_certificate_tendsto (D : ℕ) (i j : Fin ((D+1)/2)) :
    Tendsto (fun Q => physicalFourError Q D (Certificate.copyLabel i) (Certificate.copyLabel j))
      atTop (𝓝 (Certificate.scaledError D i j)) := by
  rw [← source_fourBody_error_matrix_s50 D i j]
  apply physicalFourError_tendsto D
  · unfold Certificate.copyLabel; have := i.isLt; omega
  · unfold Certificate.copyLabel; have := j.isLt; omega

end Laughlin.Spin

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

theorem physicalLimitError_eq (D : ℕ) : physicalLimitError D = Certificate.scaledError D := by
  ext i j
  exact Spin.source_fourBody_error_matrix_s50 D i j

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MiddleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix Topology
open Filter Spin

theorem fourDimensionRatio_tendsto (D : ℕ) : Tendsto (fun Q => fourDimensionRatio Q D) atTop (𝓝 2) := by
  have hi : Tendsto (fun Q : ℕ => (Q : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hn := (tendsto_const_nhds (x := (4 : ℝ))).sub (hi.const_mul (1+2*(D : ℝ)))
  have hd := (tendsto_const_nhds (x := (2 : ℝ))).sub hi
  have hh := hn.div hd (by norm_num : (2 : ℝ)-0 ≠ 0)
  have he : (fun Q : ℕ => fourDimensionRatio Q D) =ᶠ[atTop]
      (fun Q => (4-(1+2*(D : ℝ))*(Q : ℝ)⁻¹)/(2-(Q : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop 1] with Q hQ
    have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    unfold fourDimensionRatio
    field_simp
    ring
  apply Tendsto.congr' he.symm
  norm_num at hh
  apply hh.congr
  intro Q
  rfl

theorem finiteFourMiddle_tendsto (D : ℕ) (i j : Fin ((D+1)/2)) :
    Tendsto (fun Q => finiteFourMiddle Q D i j) atTop (𝓝 (limitFourMiddle D i j)) := by
  have he := physicalFourError_certificate_tendsto D i j
  rw [← physicalLimitError_eq D] at he
  unfold finiteFourMiddle limitFourMiddle
  apply Tendsto.sub _ he
  by_cases hij : i=j
  · subst j
    by_cases hi : Certificate.copyLabel i=1
    · simpa [Matrix.diagonal_apply,hi,Certificate.certificateDiagonal,Matrix.map_apply] using
        (fourDimensionRatio_tendsto D).add_const (3/10^6 : ℝ)
    · simp [hi,Certificate.certificateDiagonal,Matrix.map_apply]
  · simp [hij,Certificate.certificateDiagonal,Matrix.map_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TransferConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem physicalFourBeta_tendsto (r D : ℕ) (hrD : r ≤ D) (b : LocalFourIndex D) :
    Tendsto (fun Q => physicalFourBeta Q r D b) atTop
      (𝓝 (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val)) := by
  have hs := source_fourBody_coefficient_tendsto_s50 r D D b.val.1.val b.val.2.1.val b.val.2.2.val
    hrD (le_refl _) b.property.1
  have hp := pairFactor_tendsto b.val.1.val
  have hj := modeFactor_tendsto b.val.2.1.val
  have hk := modeFactor_tendsto b.val.2.2.val
  have hh := (hs.mul hp).div (hj.mul hk) (by norm_num)
  simp only [mul_one,div_one] at hh
  apply hh.congr
  intro Q
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TransferCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem finiteLocalFourMatrix_tendsto_s50_oai (D : ℕ) (a b : LocalFourIndex D) :
    Tendsto (fun Q => finiteLocalFourMatrix Q D a b) atTop (𝓝 (limitLocalFourMatrix D a b)) := by
  unfold finiteLocalFourMatrix limitLocalFourMatrix copyQuadraticMatrix
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  have hiD : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hjD : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  exact ((finiteFourMiddle_tendsto D i j).mul (physicalFourBeta_tendsto _ D hiD a)).mul
    (physicalFourBeta_tendsto _ D hjD b)

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.finiteLocalFourMatrix_tendsto_s50_oai := @OAI.Laughlin.Fock.finiteLocalFourMatrix_tendsto_s50_oai
