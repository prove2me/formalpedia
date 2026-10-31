-- Prove2me | solution 1 for OAI.Generator.single_generation_of_II1_separable_predual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:49:32.12698+00:00
-- url     : https://prove2.me/submissions/28f8ce25-852d-4774-b63f-db1921297c78

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G016
import Theorems.Thm_OAI_Generator_Tracial_exists_commuting_matrix_extension_q129
import Theorems.Thm_OAI_Generator_Tracial_represented_four_selfAdjoint_generators_q129
import Theorems.Thm_OAI_Generator_Tracial_traceOrbit_isSeparable_of_separablePredual_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator.MatrixEncoding

/-! Algebraic encoding of four corner operators by two self-adjoint matrices. -/
section
variable {R : Type*} [Ring R] [StarRing R]
local notation "Mat" => Matrix (Fin 2) (Fin 2) R

theorem encodeA_selfAdjoint {a₁ a₂ C : R}
    (h₁ : IsSelfAdjoint a₁) (h₂ : IsSelfAdjoint a₂) (hC : IsSelfAdjoint C) :
    IsSelfAdjoint (encodeA a₁ a₂ C) := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [encodeA, h₁.star_eq, h₂.star_eq, hC.star_eq]

theorem encodeB_selfAdjoint {a₃ a₄ : R}
    (h₃ : IsSelfAdjoint a₃) (h₄ : IsSelfAdjoint a₄) :
    IsSelfAdjoint (encodeB a₃ a₄) := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [encodeB, h₃.star_eq, h₄.star_eq]

omit [StarRing R] in
theorem complement : (1 : Mat) - E11 = E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, E22]

theorem star_E12 : star (E12 : Mat) = E21 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E12, E21, Matrix.star_apply]

omit [StarRing R] in
theorem cut_offDiagonal (a₃ a₄ : R) : E11 * encodeB a₃ a₄ * E22 = E12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E11, E12, E22, encodeB, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem cut_a₁ (a₁ a₂ C : R) : E11 * encodeA a₁ a₂ C * E11 = corner a₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E11, encodeA, corner, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem cut_a₂ (a₁ a₂ C : R) :
    E12 * encodeA a₁ a₂ C * E21 - corner C = corner a₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E12, E21, encodeA, corner]

omit [StarRing R] in
theorem cut_a₃ (a₃ a₄ : R) : E11 * encodeB a₃ a₄ * E11 = corner a₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E11, encodeB, corner, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem cut_a₄ (a₃ a₄ : R) : E12 * encodeB a₃ a₄ * E21 = corner a₄ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E12, E21, encodeB, corner, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem matrix_reconstruction (X : Mat) :
    X = corner (X 0 0) + corner (X 0 1) * E12 +
      E21 * corner (X 1 0) + E21 * corner (X 1 1) * E12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corner, E12, E21]

variable {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜] [Algebra 𝕜 R] [StarModule 𝕜 R]

theorem matrix_units_mem (NQ : StarSubalgebra 𝕜 Mat) {a₃ a₄ : R} (hE : (E11 : Mat) ∈ NQ)
    (hB : encodeB a₃ a₄ ∈ NQ) :
    (E22 : Mat) ∈ NQ ∧ (E12 : Mat) ∈ NQ ∧ (E21 : Mat) ∈ NQ := by
  have h22 : (E22 : Mat) ∈ NQ := (complement (R := R)) ▸ sub_mem NQ.one_mem hE
  have h12 : (E12 : Mat) ∈ NQ := cut_offDiagonal a₃ a₄ ▸
    NQ.mul_mem (NQ.mul_mem hE hB) h22
  exact ⟨h22, h12, (star_E12 (R := R)) ▸ star_mem h12⟩

theorem encoded_corners_mem (NQ : StarSubalgebra 𝕜 Mat) {a₁ a₂ a₃ a₄ C : R}
    (hE : (E11 : Mat) ∈ NQ) (hA : encodeA a₁ a₂ C ∈ NQ)
    (hB : encodeB a₃ a₄ ∈ NQ) (hC : corner C ∈ NQ) :
    corner a₁ ∈ NQ ∧ corner a₂ ∈ NQ ∧ corner a₃ ∈ NQ ∧ corner a₄ ∈ NQ := by
  obtain ⟨_, h12, h21⟩ := matrix_units_mem NQ hE hB
  exact ⟨cut_a₁ a₁ a₂ C ▸ NQ.mul_mem (NQ.mul_mem hE hA) hE,
    cut_a₂ a₁ a₂ C ▸ sub_mem (NQ.mul_mem (NQ.mul_mem h12 hA) h21) hC,
    cut_a₃ a₃ a₄ ▸ NQ.mul_mem (NQ.mul_mem hE hB) hE,
    cut_a₄ a₃ a₄ ▸ NQ.mul_mem (NQ.mul_mem h12 hB) h21⟩

omit [StarRing R] [StarRing 𝕜] [StarModule 𝕜 R] in
theorem corner_algebraMap (c : 𝕜) :
    corner (algebraMap 𝕜 R c) = c • (E11 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corner, E11, Algebra.algebraMap_eq_smul_one]

/-- The source's shift C 1_N needs no extra corner-membership hypothesis. -/
theorem encoded_corners_mem_scalar (NQ : StarSubalgebra 𝕜 Mat)
    {a₁ a₂ a₃ a₄ : R} (C : 𝕜)
    (hE : (E11 : Mat) ∈ NQ) (hA : encodeA a₁ a₂ (algebraMap 𝕜 R C) ∈ NQ)
    (hB : encodeB a₃ a₄ ∈ NQ) :
    corner a₁ ∈ NQ ∧ corner a₂ ∈ NQ ∧ corner a₃ ∈ NQ ∧ corner a₄ ∈ NQ := by
  apply encoded_corners_mem NQ hE hA hB
  rw [corner_algebraMap]
  exact NQ.smul_mem hE C

theorem eq_top_of_corner_and_units (NQ : StarSubalgebra 𝕜 Mat) (hc : ∀ a : R, corner a ∈ NQ)
    (h12 : (E12 : Mat) ∈ NQ) (h21 : (E21 : Mat) ∈ NQ) : NQ = ⊤ := by
  apply top_unique
  intro X _
  rw [matrix_reconstruction X]
  exact NQ.add_mem (NQ.add_mem (NQ.add_mem (hc _) (NQ.mul_mem (hc _) h12))
    (NQ.mul_mem h21 (hc _))) (NQ.mul_mem (NQ.mul_mem h21 (hc _)) h12)

end

/-! Algebraic diagonal identities used by the analytic gap recovery. -/
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

omit [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem E22_idempotent : (E22 : Matrix (Fin 2) (Fin 2) R)*E22=E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E22]

omit [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem E22_commute_encodeA (a₁ a₂ : R) : Commute E22 (encodeA a₁ a₂ 0) := by
  show E22*encodeA a₁ a₂ 0=encodeA a₁ a₂ 0*E22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E22,encodeA]

omit [StarRing R] [StarModule ℂ R] in
theorem encodeA_scalar_shift (a₁ a₂ : R) (C : ℂ) :
    encodeA a₁ a₂ (algebraMap ℂ R C)=C • E22+encodeA a₁ a₂ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [encodeA,E22,Algebra.algebraMap_eq_smul_one,add_comm]

theorem scalar_shift_selfAdjoint (C : ℝ) : IsSelfAdjoint (algebraMap ℂ R (C : ℂ)) := by
  simp [IsSelfAdjoint,← algebraMap_star_comm]

end Generator.MatrixEncoding

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Target
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wstar_le {s : Set (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : WOTClosed S) (hs : s ⊆ S) : wstar s ≤ S :=
  sInf_le ⟨hS, hs⟩

theorem wstar_mono {s t : Set (H →L[ℂ] H)} (h : s ⊆ t) : wstar s ≤ wstar t := by
  intro x hx
  apply StarSubalgebra.mem_sInf.mpr
  intro S hS
  exact StarSubalgebra.mem_sInf.mp hx S ⟨hS.1, h.trans hS.2⟩

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129UMul _root_.OAI.UltrapowerBridge.q129UOne _root_.OAI.UltrapowerBridge.q129UStar _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem entry_mul_amplify (o i j : ι) (x : A) :
    E.entry i j * E.amplify o x = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.mul_sum,← mul_assoc,E.mul_entry]
  simp [ite_mul]

omit [StarModule ℂ A] in
theorem amplify_mul_entry (o i j : ι) (x : A) :
    E.amplify o x * E.entry i j = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.sum_mul,mul_assoc,E.mul_entry]
  simp [mul_ite]

theorem amplify_mem (o : ι) (x : A) : E.amplify o x ∈ E.commutant := by
  intro i j
  show E.entry i j * E.amplify o x = E.amplify o x * E.entry i j
  rw [E.entry_mul_amplify,E.amplify_mul_entry]

omit [StarModule ℂ A] in
theorem amplify_star (o : ι) (x : A) : star (E.amplify o x)=E.amplify o (star x) := by
  simp only [amplify,star_sum,star_mul,E.star_entry,mul_assoc]

omit [StarModule ℂ A] in
theorem amplify_zero (o : ι) : E.amplify o 0=0 := by simp [amplify]

omit [StarModule ℂ A] in
theorem amplify_corner (o i j : ι) (x : A) :
    E.entry i o*E.amplify o x*E.entry o j = E.entry i o*x*E.entry o j := by
  rw [E.entry_mul_amplify]
  simp only [mul_assoc,E.mul_entry,ite_true, if_true]

omit [StarModule ℂ A] in
theorem amplify_mul (o : ι) (x y : A) :
    E.amplify o x*E.amplify o y=E.amplify o (x*E.entry o o*y) := by
  simp only [amplify,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change (E.entry i o*x*E.entry o i)*E.amplify o y = _
  rw [mul_assoc,E.entry_mul_amplify]
  simp only [mul_assoc]

theorem amplify_compression (o : ι) (x : A) (hx : x ∈ E.commutant) :
    E.amplify o (E.entry o o*x)=x := by
  simp only [amplify]
  calc _ = ∑ i, E.entry i i*x := by
             apply Finset.sum_congr rfl
             intro i hi
             rw [← mul_assoc,E.mul_entry,ite_eq_left rfl,mul_assoc,← (hx o i).eq,
               ← mul_assoc,E.mul_entry,ite_eq_left rfl]
       _ = x := by rw [← Finset.sum_mul,E.total,one_mul]

omit [StarModule ℂ A] in
theorem reconstruct (o : ι) (x : A) :
    (∑ i, ∑ j, E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j)=x := by
  simp only [E.amplify_corner]
  have h (i j : ι) : E.entry i o*(E.entry o i*x*E.entry j o)*E.entry o j=
      E.entry i i*x*E.entry j j := by
    calc _ = (E.entry i o*E.entry o i)*x*(E.entry j o*E.entry o j) := by
               simp only [mul_assoc]
         _ = _ := by simp only [E.mul_entry,ite_true, if_true]
  simp only [h,← Finset.mul_sum,E.total,mul_one,← Finset.sum_mul,one_mul]

/-- The commutant of a full unital matrix algebra in a scalar-center algebra
has scalar center. The finite matrix decomposition is constructed above. -/
theorem commutant_scalar_center (o : ι)
    (hfactor : ∀ c : A, (∀ a : A,a*c=c*a) → ∃ z : ℂ,c=z • (1 : A))
    (c : E.commutant) (hc : ∀ a : E.commutant,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.commutant) := by
  obtain ⟨z,hz⟩ := hfactor c.val (by
    intro x
    have h (i j : ι) : Commute
        (E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j) c.val := by
      have hm : Commute (E.amplify o (E.entry o i*x*E.entry j o)) c.val :=
        congrArg Subtype.val (hc ⟨_,E.amplify_mem o _⟩)
      exact ((c.property i o).mul_left hm).mul_left (c.property o j)
    rw [← E.reconstruct o x]
    simp only [Finset.sum_mul,Finset.mul_sum,(h _ _).eq])
  exact ⟨z,Subtype.ext hz⟩

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_projection (o : ι) : IsStarProjection (E.entry o o) := by
  exact ⟨by show E.entry o o*E.entry o o=E.entry o o; simpa using E.mul_entry o o o o,E.star_entry o o⟩

omit [StarModule ℂ A] in
theorem amplify_projection (o : ι) (q : A) (hq : IsStarProjection q)
    (hs : q*E.entry o o=q) : IsStarProjection (E.amplify o q) := by
  constructor
  · show E.amplify o q*E.amplify o q=E.amplify o q
    rw [E.amplify_mul,hs,hq.isIdempotentElem.eq]
  · show star (E.amplify o q)=E.amplify o q
    rw [E.amplify_star,hq.isSelfAdjoint.star_eq]

theorem commutant_diffuse (o : ι)
    (hdiff : ∀ p : A,IsStarProjection p → p ≠ 0 →
      ∃ q : A,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.commutant) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.commutant,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  have hpA : IsStarProjection p.val := hp.map E.commutant.subtype
  let r : A := E.entry o o*p.val
  have hr : IsStarProjection r := (E.diagonal_projection o).mul hpA (p.property o o)
  have hr0 : r ≠ 0 := by
    intro h
    have he := E.amplify_compression o p.val p.property
    rw [show E.entry o o*p.val=0 from h,E.amplify_zero] at he
    exact hp0 (Subtype.ext he.symm)
  obtain ⟨q,hq,hq0,hqr,hrq,hqr'⟩ := hdiff r hr hr0
  have hqs : q*E.entry o o=q := by
    have hre : r*E.entry o o=r := by
      dsimp [r]
      rw [mul_assoc,← (p.property o o).eq,← mul_assoc,
        (E.diagonal_projection o).isIdempotentElem.eq]
    calc q*E.entry o o = (q*r)*E.entry o o := by rw [hqr']
         _ = q*r := by rw [mul_assoc,hre]
         _ = q := hqr'
  have hsq : E.entry o o*q=q := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,E.star_entry] using congrArg star hqs
  let Q : E.commutant := ⟨E.amplify o q,E.amplify_mem o q⟩
  have hQ : IsStarProjection Q := by
    constructor
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isIdempotentElem.eq
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isSelfAdjoint.star_eq
  have hrec : E.entry o o*Q.val*E.entry o o=q := by
    change E.entry o o*E.amplify o q*E.entry o o=q
    rw [E.amplify_corner,hsq,hqs]
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro h
    have hz : Q.val=0 := congrArg Subtype.val h
    rw [hz,mul_zero,zero_mul] at hrec
    exact hq0 hrec.symm
  · intro h
    have hz : Q.val=p.val := congrArg Subtype.val h
    rw [hz,mul_assoc,← (p.property o o).eq,← mul_assoc,
      (E.diagonal_projection o).isIdempotentElem.eq] at hrec
    exact hqr hrec.symm
  · apply Subtype.ext
    change p.val*E.amplify o q=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul]
    congr 1
    rw [mul_assoc,hsq]
    exact hrq
  · apply Subtype.ext
    change E.amplify o q*p.val=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul,hqs]
    exact congrArg (E.amplify o) hqr'

open scoped BigOperators
variable {ι κ A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B]
variable (E : MatrixUnitSystem ι A)

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

theorem coefficientHom_single (i j : ι) (a : E.commutant) :
    E.coefficientHom (Matrix.single i j a)=a.val*E.entry i j := by
  change E.coefficientEval (Matrix.single i j a)=_
  simp [coefficientEval,Matrix.single,apply_ite,ite_mul,ite_and]

theorem coefficientHom_surjective (o : ι) : Function.Surjective E.coefficientHom := by
  intro x
  let a : Matrix ι ι E.commutant := fun i j =>
    ⟨E.amplify o (E.entry o i*x*E.entry j o),E.amplify_mem o _⟩
  refine ⟨a,?_⟩
  change (∑ i,∑ j,E.amplify o (E.entry o i*x*E.entry j o)*E.entry i j)=x
  calc (∑ i,∑ j,E.amplify o (E.entry o i*x*E.entry j o)*E.entry i j) =
      ∑ i,∑ j,E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (a i j).val*E.entry i j=E.entry i o*(a i j).val*E.entry o j
        rw [((a i j).property i o).eq,mul_assoc,E.mul_entry,ite_eq_left rfl]
    _ = x := E.reconstruct o x

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

theorem relative_scalar_center (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.relativeVonNeumann.toStarSubalgebra) := by
  obtain ⟨z,hz⟩ := E.commutant_scalar_center o hfactor (E.relativeEquiv.symm c) (by
    intro a
    apply E.relativeEquiv.injective
    change E.relativeEquiv (a*E.relativeEquiv.symm c)=
      E.relativeEquiv (E.relativeEquiv.symm c*a)
    rw [map_mul,map_mul,E.relativeEquiv.apply_symm_apply]
    exact hc (E.relativeEquiv a))
  refine ⟨z,?_⟩
  have h := congrArg E.relativeEquiv hz
  simpa only [StarAlgEquiv.apply_symm_apply,map_smul,map_one] using h

theorem relative_diffuse (o : ι)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.relativeVonNeumann.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.relativeVonNeumann.toStarSubalgebra,
      IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := E.commutant_diffuse o hdiff
    (E.relativeEquiv.symm p) (hp.map E.relativeEquiv.symm) (by
      intro h
      apply hp0
      simpa using congrArg E.relativeEquiv h)
  refine ⟨E.relativeEquiv q,?_,?_,?_,?_,?_⟩
  · exact hq.map E.relativeEquiv.toStarAlgHom
  · intro h
    apply hq0
    exact E.relativeEquiv.injective (h.trans (map_zero E.relativeEquiv).symm)
  · intro h
    apply hqp
    exact E.relativeEquiv.injective (h.trans (E.relativeEquiv.apply_symm_apply p).symm)
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hpq
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hqp'

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/

open UltrapowerBridge Tracial

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129Neg _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! A separated idempotent is recovered from commutation with a norm-small
perturbation. This is an elementary substitute for the spectral-cut step. -/
section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem offDiagonal_eq_zero_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : p*x*(1-p)=0 := by
  let y := p*x*(1-p)
  have hleft : p*(a • p+t) = a • p+p*t := by
    rw [mul_add,mul_smul_comm,hp]
  have hright : (a • p+t)*(1-p)=t*(1-p) := by
    rw [add_mul,smul_mul_assoc,mul_sub,mul_one,hp,sub_self,smul_zero,zero_add]
  have he := congrArg (fun z : A => p*z*(1-p)) hx.eq
  have hy : a • y = y*t-t*y := by
    have ht : t*(1-p)=(1-p)*t := by
      rw [mul_sub,sub_mul,mul_one,one_mul,hpt.eq]
    have h : a • y+t*y=y*t := by
      calc a • y+t*y = (p*(a • p+t))*x*(1-p) := by
             rw [hleft,add_mul,add_mul,smul_mul_assoc,smul_mul_assoc]
             dsimp [y]
             rw [hpt.eq]
             simp only [mul_assoc]
        _ = p*((a • p+t)*x)*(1-p) := by simp only [mul_assoc]
        _ = p*(x*(a • p+t))*(1-p) := he
        _ = y*t := by
          simp only [mul_assoc]
          rw [hright,ht]
          simp only [y,mul_assoc]
    exact eq_sub_of_add_eq' (by simpa only [add_comm] using h)
  have han : 0 ≤ a := (mul_nonneg (by norm_num) (norm_nonneg t)).trans ha.le
  have hn : a*‖y‖ ≤ 2*‖t‖*‖y‖ := by
    calc a*‖y‖ = ‖a • y‖ := by rw [norm_smul,Real.norm_of_nonneg han]
      _ = ‖y*t-t*y‖ := congrArg norm hy
      _ ≤ ‖y*t‖+‖t*y‖ := norm_sub_le _ _
      _ ≤ ‖y‖*‖t‖+‖t‖*‖y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2*‖t‖*‖y‖ := by ring
  have hz : ‖y‖=0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp hz

theorem commute_projection_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : Commute p x := by
  have h₁ := offDiagonal_eq_zero_of_gap p t x hp hpt a ha hx
  have hcp : (1-p)*(1-p)=1-p := by noncomm_ring [hp]
  have hcpt : Commute (1-p) (-t) := ((Commute.one_left t).sub_left hpt).neg_right
  have hcx : Commute (a • (1-p)+ -t) x := by
    have he : a • (1-p)+ -t = a • (1 : A)-(a • p+t) := by
      rw [smul_sub]; abel
    rw [he]
    exact ((Commute.one_left x).smul_left a).sub_left hx
  have h₂ := offDiagonal_eq_zero_of_gap (1-p) (-t) x hcp hcpt a
    (by simpa only [norm_neg] using ha) hcx
  simp only [sub_sub_cancel] at h₂
  show p*x=x*p
  have h₁' : p*x=p*x*p := by simpa only [mul_sub,mul_one,sub_eq_zero] using h₁
  have h₂' : x*p=p*x*p := by simpa only [sub_mul,one_mul,sub_eq_zero] using h₂
  exact h₁'.trans h₂'.symm

end

/-! Countably many commuting projections have one self-adjoint generator.
We use coefficients 3*4^(-(n+1)), whose strict gap admits direct norm recovery
through the double commutant. No trace, tensor model, or uniqueness is used. -/

/-! The spectral separation step as an exact membership theorem for literal W*. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem idempotent_mem_wstar_of_gap (p t : H →L[ℂ] H) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a) : p ∈ wstar {a • p+t} := by
  let S := wstar {a • p+t}
  change p ∈ (S : Set (H →L[ℂ] H))
  rw [← wotClosed_bicommutant S (wstar_closed _)]
  intro x hx
  exact (commute_projection_of_gap p t x hp hpt a ha
    (hx _ (subset_wstar _ rfl))).eq.symm

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_AmplificationEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! One arbitrary operator and a pair of self-adjoint operators generate the same weakly closed star algebra. -/
open scoped ComplexStarModule
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "Op" => H →L[ℂ] H

theorem realPart_mem (S : StarSubalgebra ℂ Op) {x : Op} (hx : x ∈ S) :
    (ℜ x : Op) ∈ S := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  exact S.smul_mem (add_mem hx (star_mem hx)) _

theorem imaginaryPart_mem (S : StarSubalgebra ℂ Op) {x : Op} (hx : x ∈ S) :
    (ℑ x : Op) ∈ S := by
  rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
  exact S.smul_mem (S.smul_mem (sub_mem hx (star_mem hx)) _) _

theorem mem_iff_parts_mem (S : StarSubalgebra ℂ Op) (x : Op) :
    x ∈ S ↔ (ℜ x : Op) ∈ S ∧ (ℑ x : Op) ∈ S := by
  refine ⟨fun hx => ⟨realPart_mem S hx, imaginaryPart_mem S hx⟩, ?_⟩
  rintro ⟨hr, hi⟩
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem hr (S.smul_mem hi _)

theorem wstar_singleton_eq_parts (x : Op) :
    wstar {x} = wstar {(ℜ x : Op), (ℑ x : Op)} := by
  apply le_antisymm
  · apply wstar_le (wstar_closed _)
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    apply (mem_iff_parts_mem _ x).mpr
    exact ⟨subset_wstar _ (by simp), subset_wstar _ (by simp)⟩
  · apply wstar_le (wstar_closed _)
    intro y hy
    have hx := subset_wstar {x} (Set.mem_singleton x)
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact realPart_mem _ hx
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact imaginaryPart_mem _ hx

theorem realPart_pack {a b : Op} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    (ℜ (a + Complex.I • b) : Op) = a := by
  simp only [map_add, realPart_I_smul, hb.imaginaryPart, neg_zero, add_zero]
  exact ha.coe_realPart

theorem imaginaryPart_pack {a b : Op} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    (ℑ (a + Complex.I • b) : Op) = b := by
  simp only [map_add, ha.imaginaryPart, imaginaryPart_I_smul, zero_add]
  exact hb.coe_realPart

theorem wstar_pack {a b : Op} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    wstar {a + Complex.I • b} = wstar {a, b} := by
  rw [wstar_singleton_eq_parts, realPart_pack ha hb, imaginaryPart_pack ha hb]

end

/-! Two self-adjoint generators for an actual two-by-two amplification
whose actual commutant has four self-adjoint generators. Spectral separation
is proved, and the final generation uses the surjective coefficient map. -/
open scoped BigOperators
namespace MatrixUnitSystem
open MatrixEncoding
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem (Fin 2) M.toStarSubalgebra)

theorem coefficient_corner (a : E.commutant) :
    E.concreteCoefficientHom (corner a)=a.val.val*(E.entry 0 0).val := by
  have he : corner a=Matrix.single 0 0 a := by ext i j; fin_cases i <;> fin_cases j <;> simp [corner,Matrix.single]
  change (E.coefficientHom (corner a)).val=_
  rw [he,E.coefficientHom_single]
  rfl

theorem coefficient_diagonal (a : E.commutant) :
    E.concreteCoefficientHom (corner a+E21*corner a*E12)=a.val.val := by
  have he : corner a+E21*corner a*E12=Matrix.diagonal (fun _ : Fin 2 => a) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [corner,E21,E12,Matrix.diagonal]
  rw [he]
  change (E.coefficientEval (Matrix.diagonal (fun _ : Fin 2 => a))).val=a.val.val
  congr 1
  simp [coefficientEval,Matrix.diagonal,apply_ite,ite_mul,← Finset.mul_sum,E.total]

theorem two_generators_of_four_commutant_generators (a₁ a₂ a₃ a₄ : E.commutant)
    (h₁ : IsSelfAdjoint a₁) (h₂ : IsSelfAdjoint a₂)
    (h₃ : IsSelfAdjoint a₃) (h₄ : IsSelfAdjoint a₄)
    (hgen : wstar {a₁.val.val,a₂.val.val,a₃.val.val,a₄.val.val}=E.relativeVonNeumann.toStarSubalgebra) :
    ∃ A ∈ M,∃ B ∈ M,IsSelfAdjoint A ∧ IsSelfAdjoint B ∧ wstar {A,B}=M.toStarSubalgebra := by
  let f := E.concreteCoefficientHom
  let t := f (encodeA a₁ a₂ 0)
  let q := f E22
  let C : ℝ := 2*‖t‖+1
  let A := f (encodeA a₁ a₂ (algebraMap ℂ E.commutant (C : ℂ)))
  let B := f (encodeB a₃ a₄)
  have hA : A ∈ M := (E.coefficientHom _).property
  have hB : B ∈ M := (E.coefficientHom _).property
  have hsa : IsSelfAdjoint A :=
    (encodeA_selfAdjoint h₁ h₂ (scalar_shift_selfAdjoint C)).map f
  have hsb : IsSelfAdjoint B := (encodeB_selfAdjoint h₃ h₄).map f
  have hq : q*q=q :=
    (map_mul f E22 E22).symm.trans (congrArg f E22_idempotent)
  have hqt : Commute q t := (E22_commute_encodeA a₁ a₂).map f
  have hsplit : A=C • q+t := by
    change f _=C • f E22+f (encodeA a₁ a₂ 0)
    exact (congrArg f (encodeA_scalar_shift a₁ a₂ C)).trans
      ((map_add f _ _).trans (congrArg (fun x => x + f (encodeA a₁ a₂ 0))
        ((map_smul f (C : ℂ) E22).trans (Complex.coe_smul C (f E22)))))
  let Q := wstar {A,B}
  let S := Q.comap f
  have hAm : encodeA a₁ a₂ (algebraMap ℂ E.commutant (C : ℂ)) ∈ S := subset_wstar _ (by simp [A])
  have hBm : encodeB a₃ a₄ ∈ S := subset_wstar _ (by simp [B])
  have h22 : (E22 : Matrix (Fin 2) (Fin 2) E.commutant) ∈ S := by
    change q ∈ wstar {A,B}
    apply (wstar_mono (s := {A}) (t := {A,B}) (by simp))
    rw [hsplit]
    exact idempotent_mem_wstar_of_gap q t hq hqt C (by dsimp [C]; linarith)
  have h11 : (E11 : Matrix (Fin 2) (Fin 2) E.commutant) ∈ S := by
    have he : (1 : Matrix (Fin 2) (Fin 2) E.commutant)-E22=E11 := by rw [← complement]; abel
    rw [← he]
    exact S.sub_mem S.one_mem h22
  obtain ⟨_,h12,h21⟩ := matrix_units_mem S h11 hBm
  obtain ⟨hc₁,hc₂,hc₃,hc₄⟩ := encoded_corners_mem_scalar S (C : ℂ) h11 hAm hBm
  have hcoeff (a : E.commutant) (ha : corner a ∈ S) : a.val.val ∈ Q := by
    rw [← E.coefficient_diagonal a]
    exact S.add_mem ha (S.mul_mem (S.mul_mem h21 ha) h12)
  have hN : E.relativeVonNeumann.toStarSubalgebra ≤ Q := by
    rw [← hgen]
    exact wstar_le (wstar_closed _) (by
      rintro _ (rfl | rfl | rfl | rfl)
      · exact hcoeff a₁ hc₁
      · exact hcoeff a₂ hc₂
      · exact hcoeff a₃ hc₃
      · exact hcoeff a₄ hc₄)
  have hcorner (a : E.commutant) : corner a ∈ S := by
    change f (corner a) ∈ Q
    rw [E.coefficient_corner a]
    apply Q.mul_mem (hN ⟨a,rfl⟩)
    have hp := E.coefficient_corner (1 : E.commutant)
    have he : corner (1 : E.commutant)=E11 := rfl
    rw [he] at hp
    have hp' : f E11=(E.entry 0 0).val := by simpa using hp
    have hh : f E11 ∈ Q := h11
    rwa [hp'] at hh
  have htop : S=⊤ := eq_top_of_corner_and_units S hcorner h12 h21
  refine ⟨A,hA,B,hB,hsa,hsb,le_antisymm ?_ ?_⟩
  · exact wstar_le (Tracial.vonNeumann_wotClosed M) (by rintro _ (rfl | rfl) <;> assumption)
  · intro x hx
    obtain ⟨a,ha⟩ := E.coefficientHom_surjective 0 ⟨x,hx⟩
    have hm : a ∈ S := by rw [htop]; trivial
    change (E.coefficientHom a).val ∈ Q at hm
    rwa [ha] at hm

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Generation
attribute [-instance] _root_.OAI.Generator.FactorTraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Relative generation under represented-factor hypotheses: unitaries in a dense G-delta set satisfy W*(N,u)=M. -/
open Filter
open scoped Topology

/-! Four generators under a faithful normalized vector trace and trace-vector separability. -/
open scoped ComplexStarModule

/-! Single generation for the explicit faithful normalized vector-trace
representation with separable trace-vector range. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem represented_two_selfAdjoint_generators (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ a ∈ M,∃ b ∈ M,IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=M.toStarSubalgebra := by
  obtain ⟨E,_,_,_,_,_⟩ := exists_commuting_matrix_extension_q129 τ
    (FiniteMatrixStage.scalarStage M).units ⟨0,(FiniteMatrixStage.scalarStage M).positive⟩ hfactor hdiff 2 (by norm_num)
  let N := E.relativeVonNeumann
  let τN := restrictedTrace τ E.relativeVonNeumann_le
  have hsepN : TopologicalSpace.IsSeparable (Set.range (baseVector τN)) := by
    apply hsep.mono
    rintro y ⟨a,rfl⟩
    exact ⟨coordinateInclusion E.relativeVonNeumann_le a,rfl⟩
  obtain ⟨a,ha,b,hb,c,hc,d,hd,hsa,hsb,hsc,hsd,hgen⟩ := represented_four_selfAdjoint_generators_q129
    τN (E.relative_scalar_center 0 hfactor) (E.relative_diffuse 0 hdiff) hsepN
  let a' : E.commutant := E.relativeEquiv.symm ⟨a,ha⟩
  let b' : E.commutant := E.relativeEquiv.symm ⟨b,hb⟩
  let c' : E.commutant := E.relativeEquiv.symm ⟨c,hc⟩
  let d' : E.commutant := E.relativeEquiv.symm ⟨d,hd⟩
  have hs (x : H →L[ℂ] H) (hx : x ∈ N) (h : IsSelfAdjoint x) :
      IsSelfAdjoint (E.relativeEquiv.symm ⟨x,hx⟩) :=
    (show IsSelfAdjoint (⟨x,hx⟩ : N.toStarSubalgebra) from Subtype.ext h.star_eq).map E.relativeEquiv.symm
  exact E.two_generators_of_four_commutant_generators a' b' c' d'
    (hs a ha hsa) (hs b hb hsb) (hs c hc hsc) (hs d hd hsd) hgen

theorem represented_single_generator (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    SinglyGenerated M.toStarSubalgebra := by
  obtain ⟨a,ha,b,hb,hsa,hsb,hgen⟩ := represented_two_selfAdjoint_generators τ hfactor hdiff hsep
  exact ⟨a+Complex.I • b,M.add_mem ha (M.smul_mem hb _),(wstar_pack hsa hsb).trans hgen⟩

theorem singlyGenerated_of_tracialRepresentation (hM : IsII1Factor M.toStarSubalgebra)
    (τ : TracialRepresentation M)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    SinglyGenerated M.toStarSubalgebra := by
  apply represented_single_generator τ _ hM.diffuse hsep
  intro c hc
  obtain ⟨z,hz⟩ := hM.factor c hc
  exact ⟨z,by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.FactorTraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/
section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}
  {T : StarSubalgebra ℂ (K →L[ℂ] K)}

/-! Transport of the unchanged finite diffuse factor predicate.
The algebraic fields use the actual star isomorphism; target WOT closedness
is explicit. No trace or separability conclusion is inferred. -/

theorem isII1Factor_of_starAlgEquiv (e : S ≃⋆ₐ[ℂ] T)
    (hS : IsII1Factor S) (hT : WOTClosed T) : IsII1Factor T where
  nonzero := by
    intro h
    have ht : (0 : T) = 1 := Subtype.ext h
    have hs : (0 : S) = 1 := e.injective (by simpa only [map_zero, map_one] using ht)
    exact hS.nonzero (congrArg Subtype.val hs)
  weaklyClosed := hT
  factor := by
    intro x hx
    have hc : ∀ y : S, y * e.symm x = e.symm x * y := by
      intro y
      apply e.injective
      change e (y * e.symm x) = e (e.symm x * y)
      simpa only [map_mul, e.apply_symm_apply] using hx (e y)
    obtain ⟨c, hc⟩ := hS.factor (e.symm x) hc
    refine ⟨c, ?_⟩
    calc x = e (e.symm x) := (e.apply_symm_apply x).symm
         _ = e (algebraMap ℂ S c) := congrArg e hc
         _ = algebraMap ℂ T c := e.toAlgEquiv.commutes c
  finite := by
    intro v hv
    have h : star (e.symm v) * e.symm v = 1 := by
      simpa only [map_mul, map_star, map_one] using congrArg e.symm hv
    have hf := hS.finite (e.symm v) h
    simpa only [map_mul, map_star, map_one, e.apply_symm_apply] using congrArg e hf
  diffuse := by
    intro p hp hp0
    have hsp : IsStarProjection (e.symm p) := hp.map e.symm
    have hsp0 : e.symm p ≠ 0 := by
      intro hz
      apply hp0
      simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
    obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hS.diffuse (e.symm p) hsp hsp0
    refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
    · intro hz
      apply hq0
      apply e.injective
      change e q = e 0
      simpa only [map_zero] using hz
    · intro heq
      apply hqp
      apply e.injective
      change e q = e (e.symm p)
      simpa only [e.apply_symm_apply] using heq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

end

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

local instance traceHilbertTransportOperatorCStar_r0e24cb_1 : CStarAlgebra (K →L[ℂ] K) := {}
attribute [local instance] OAI.Generator.Tracial.traceHilbertTransportClosureCStar
theorem traceFreeHilbertClosure_isII1Factor : IsII1Factor (N).toStarSubalgebra := by
  have hM : IsII1Factor M.toStarSubalgebra := {
    nonzero := fun h => hunit (Subtype.ext h.symm)
    weaklyClosed := traceHilbertVonNeumann_wotClosed M
    factor := by
      intro a ha
      obtain ⟨z,hz⟩ := hfactor a ha
      exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z).symm⟩
    finite := hfinite
    diffuse := hdiff }
  exact isII1Factor_of_starAlgEquiv e hM (traceHilbertVonNeumann_wotClosed N)

theorem traceFreeHilbertClosure_hasSeparablePredual
    (hsep : HasSeparablePredual M.toStarSubalgebra) : HasSeparablePredual (N).toStarSubalgebra := by
  obtain ⟨X,g,s,c,hs,⟨d⟩⟩ := hsep
  exact ⟨X,g,s,c,hs,⟨d.trans (traceFreeHilbertIsometry hfactor hdiff hfinite hunit)⟩⟩

end Tracial

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule
namespace Tracial

/-! Generation pullback for the actual constructed trace representation. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceGenerationTransportCStar
local instance traceGenerationTransportOrder_r0e24cb_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceGenerationTransportStarOrder_r0e24cb_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.Generator.Tracial.traceGenerationTransportOperatorCStar
local instance traceGenerationTransportClosureCStar_r0e24cb_1 : CStarAlgebra (N).toStarSubalgebra := {}
/-- Pull a literal W*-generator back through the constructed representation.
Closed images of the original generated subalgebra replace any unproved
whole-carrier weak-operator continuity assertion. -/
theorem traceFreeHilbert_singlyGenerated_pullback
    (hgen : SinglyGenerated (N).toStarSubalgebra) : SinglyGenerated M.toStarSubalgebra := by
  obtain ⟨b,hb,hgen⟩ := hgen
  let a : M.toStarSubalgebra := (e).symm ⟨b,hb⟩
  let Q := wstar {a.val}
  have hQM : Q ≤ M.toStarSubalgebra :=
    wstar_le (traceHilbertVonNeumann_wotClosed M) (by
      intro c hc
      obtain rfl := Set.mem_singleton_iff.mp hc
      exact a.property)
  let P := (Q.comap M.toStarSubalgebra.subtype).map π
  have hbP : b ∈ P := by
    refine ⟨a,subset_wstar {a.val} (Set.mem_singleton a.val),?_⟩
    exact congrArg Subtype.val ((e).apply_symm_apply ⟨b,hb⟩)
  have hNP : (N).toStarSubalgebra ≤ P := by
    rw [← hgen]
    exact wstar_le (traceFreeSubalgebraImage_wotClosed hfactor hdiff hfinite hunit Q
      (wstar_closed {a.val})) (by
        intro c hc
        obtain rfl := Set.mem_singleton_iff.mp hc
        exact hbP)
  refine ⟨a.val,a.property,le_antisymm hQM ?_⟩
  intro c hc
  obtain ⟨d,hdQ,hd⟩ := hNP (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit ⟨c,hc⟩)
  have hd' : d = (⟨c,hc⟩ : M.toStarSubalgebra) :=
    traceFreeHilbertAction_injective hfactor hdiff hfinite hunit hd
  change d.val ∈ Q at hdQ
  rw [hd'] at hdQ
  exact hdQ

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Main
attribute [-instance] _root_.OAI.Generator.FactorTraceUnitary.instMetricSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! Single generation of a finite diffuse factor with a separable Banach predual,
using its faithful normal trace and given-predual continuity. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem single_generation_of_II1_separable_predual_oai
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S)
    (hsep : HasSeparablePredual S) : SinglyGenerated S := by
  let M := vonNeumannOfWOTClosed S hS.weaklyClosed
  have hf : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    obtain ⟨z, hz⟩ := hS.factor c hc
    exact ⟨z, hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  have hunit : (1 : M.toStarSubalgebra) ≠ 0 := by
    intro h
    exact hS.nonzero (congrArg Subtype.val h).symm
  let E := Tracial.TraceFreePreHilbert hf hS.diffuse hS.finite hunit
  let : NormedAddCommGroup E :=
    Tracial.traceFreePreHilbertNormedAddCommGroup hf hS.diffuse hS.finite hunit
  let : InnerProductSpace ℂ E :=
    Tracial.traceFreePreHilbertInnerProductSpace hf hS.diffuse hS.finite hunit
  let N := Tracial.traceFreeHilbertClosure hf hS.diffuse hS.finite hunit
  let τ := Tracial.traceFreeHilbertClosureTrace hf hS.diffuse hS.finite hunit
  have hN := Tracial.traceFreeHilbertClosure_isII1Factor hf hS.diffuse hS.finite hunit
  have hpre := Tracial.traceFreeHilbertClosure_hasSeparablePredual hf hS.diffuse hS.finite hunit hsep
  have htrace := Tracial.traceOrbit_isSeparable_of_separablePredual_q129 τ hpre
  exact Tracial.traceFreeHilbert_singlyGenerated_pullback hf hS.diffuse hS.finite hunit
    (Tracial.singlyGenerated_of_tracialRepresentation hN τ htrace)

end

end Generator

end OAI
end

theorem solution.{u} : type_of% @OAI.Generator.single_generation_of_II1_separable_predual_oai.{u} := @OAI.Generator.single_generation_of_II1_separable_predual_oai.{u}
