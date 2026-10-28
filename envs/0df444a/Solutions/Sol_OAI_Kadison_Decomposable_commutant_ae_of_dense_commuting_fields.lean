-- Prove2me | solution 1 for OAI.Kadison.Decomposable.commutant_ae_of_dense_commuting_fields
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:35:40.652366+00:00
-- url     : https://prove2.me/submissions/0e78c7cb-d895-40af-be64-105bed940ed8

import Mathlib
import Definitions.Def_OAIQ039C044

section
-- module Solutions.OAIQ039_CM.Commutator_DenseCommutes
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutes_of_dense_contraction_tests (P : VonNeumannAlgebra H)
    (test : ℕ → H →L[ℂ] H)
    (hdense : ∀ A : H →L[ℂ] H,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) ξ) atTop (𝓝 (A ξ)))
    (B : H →L[ℂ] H) (htest : ∀ n,Commute (test n) B)
    (A : H →L[ℂ] H) (hA : A∈P) : Commute A B := by
  let d : ℂ := ((‖A‖+1:ℝ):ℂ)
  have hdR : 0<‖A‖+1 := by positivity
  have hd : d≠0 := by
    dsimp only [d]
    exact_mod_cast (ne_of_gt hdR)
  have hdn : ‖d⁻¹ • A‖≤1 := by
    rw [norm_smul,norm_inv]
    have hnd : ‖d‖=‖A‖+1 := by
      dsimp only [d]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdR]
    rw [hnd]
    have hi : (‖A‖+1)⁻¹*‖A‖=‖A‖/(‖A‖+1) := by ring
    rw [hi]
    exact (div_le_one hdR).mpr (by linarith)
  obtain ⟨k,hk⟩ := hdense (d⁻¹ • A) (P.smul_mem hA d⁻¹) hdn
  have hlim (x y : H) : Tendsto (fun n => inner ℂ (test (k n) x) y) atTop
      (𝓝 (inner ℂ ((d⁻¹ • A) x) y)) := (hk x).inner tendsto_const_nhds
  have hc := WeakOperatorLimit.intertwine hlim B B
    (Eventually.of_forall (fun n => (htest (k n)).eq))
  have h := congrArg (fun C : H →L[ℂ] H => d • C) hc
  change A*B=B*A
  simpa only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_inv_cancel₀ hd,one_smul] using h

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberCommutator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma operator_commutator (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb0 : 0≤b) (hc0 : 0 ≤ c)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    operator μ T hT hb*operator μ S hS hc-operator μ S hS hc*operator μ T hT hb=
    operator μ (fun a => T a*S a-S a*T a) (commutator_measurable μ T S hT hS)
      (commutator_field_bound μ T S hb0 hc0 hb hc) := by
  apply operator_eq_of_ae_apply
  intro f
  filter_upwards [operator_ae μ T hT hb (operator μ S hS hc f),
    operator_ae μ S hS hc (operator μ T hT hb f),operator_ae μ T hT hb f,
    operator_ae μ S hS hc f,
    Lp.coeFn_sub (operator μ T hT hb (operator μ S hS hc f))
      (operator μ S hS hc (operator μ T hT hb f))] with a h1 h2 h3 h4 h5
  change (operator μ T hT hb (operator μ S hS hc f)-operator μ S hS hc (operator μ T hT hb f)) a=_
  rw [h5]
  change operator μ T hT hb (operator μ S hS hc f) a-
    operator μ S hS hc (operator μ T hT hb f) a=_
  rw [h1,h2,h3,h4]
  rfl

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
lemma commutator_ae_bound (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c d : ℝ} (hb0 : 0≤b) (hc0 : 0 ≤ c) (hd : 0≤d)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c)
    (hn : ‖operator μ T hT hb*operator μ S hS hc-operator μ S hS hc*operator μ T hT hb‖≤d) :
    ∀ᵐ a ∂μ,‖T a*S a-S a*T a‖≤d := by
  rw [operator_commutator μ T S hT hS hb0 hc0 hb hc] at hn
  exact (operator_norm_le_iff_ae μ _ _ _ hd).mp hn

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberCommutes
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma commute_ae_of_commuting_fields (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb0 : 0≤b) (hc0 : 0 ≤ c)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c)
    (hcomm : Commute (operator μ T hT hb) (operator μ S hS hc)) :
    ∀ᵐ a ∂μ,Commute (T a) (S a) := by
  have hnorm := commutator_ae_bound μ T S hT hS hb0 hc0 (by norm_num : (0:ℝ)≤0) hb hc
    (by rw [hcomm.eq,sub_self,norm_zero])
  filter_upwards [hnorm] with a ha
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ha (norm_nonneg _)))

theorem commutant_ae_of_dense_commuting_fields_oai
    (Q R : Ω → VonNeumannAlgebra H)
    (T S : ℕ → Ω → H →L[ℂ] H)
    (hT : ∀ n ξ,AEStronglyMeasurable (fun a => T n a ξ) μ)
    (hS : ∀ n ξ,AEStronglyMeasurable (fun a => S n a ξ) μ)
    (hTb : ∀ n,∀ᵐ a ∂μ,‖T n a‖≤1) (hSb : ∀ n,∀ᵐ a ∂μ,‖S n a‖≤1)
    (hcomm : ∀ i j,Commute (operator μ (T i) (hT i) (hTb i))
      (operator μ (S j) (hS j) (hSb j)))
    (hTd : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => T (k n) a ξ) atTop (𝓝 (A ξ)))
    (hSd : ∀ᵐ a ∂μ,∀ B : H →L[ℂ] H,B∈R a → ‖B‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => S (k n) a ξ) atTop (𝓝 (B ξ))) :
    ∀ᵐ a ∂μ,R a≤(Q a).commutant := by
  have ht (i j : ℕ) := commute_ae_of_commuting_fields μ (T i) (S j) (hT i) (hS j)
    (by norm_num) (by norm_num) (hTb i) (hSb j) (hcomm i j)
  filter_upwards [hTd,hSd,ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ht i j))]
    with a hTd hSd hc
  intro B hB
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro A hA
  have hcQ (j : ℕ) : Commute A (S j a) := commutes_of_dense_contraction_tests (Q a)
    (fun i => T i a) hTd (S j a) (fun i => hc i j) A hA
  exact (commutes_of_dense_contraction_tests (R a) (fun j => S j a) hSd A
    (fun j => (hcQ j).symm) B hB).eq.symm

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.Decomposable.commutant_ae_of_dense_commuting_fields_oai.{u_1, u_2} := @OAI.Kadison.Decomposable.commutant_ae_of_dense_commuting_fields_oai.{u_1, u_2}
