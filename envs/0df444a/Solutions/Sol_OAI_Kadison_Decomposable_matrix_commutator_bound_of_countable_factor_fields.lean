-- Prove2me | solution 1 for OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:42.832584+00:00
-- url     : https://prove2.me/submissions/45c87829-8318-4ee2-a21e-43f2b0c64ce7

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C044
import Theorems.Thm_OAI_Kadison_Decomposable_matrix_commutator_bound_of_factor_fields
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_CommutatorPerturbation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutatorSeminorm_le (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ a : H →L[ℂ] H,a∈P → ‖a‖≤1 → ‖Y*a-a*Y‖≤C) :
    commutatorSeminorm P Y≤C := by
  apply csSup_le
  · exact ⟨0,0,P.zero_mem,by simp,by simp⟩
  · rintro r ⟨a,ha,hna,rfl⟩
    exact hC a ha hna

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContractionLimit
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContractionLimit

variable {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

variable {l : Filter ι}

lemma norm_le_of_strong [l.NeBot] (T : ι → H →L[ℂ] G) (Y : H →L[ℂ] G)
    (hstrong : ∀ x,Tendsto (fun i => T i x) l (𝓝 (Y x))) {C : ℝ} (hC : 0≤C)
    (hbound : ∀ᶠ i in l,‖T i‖≤C) : ‖Y‖≤C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply le_of_tendsto (hstrong x |>.norm)
  filter_upwards [hbound] with i hi
  exact ((T i).le_opNorm x).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg x))

end Kadison.StrongContractionLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberCommutator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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

theorem seminorm_ae_le (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (T : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb0 : 0≤b) (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (c : ℕ → Ω → H →L[ℂ] H)
    (hm : ∀ n ξ,AEStronglyMeasurable (fun a => c n a ξ) μ)
    (hc : ∀ n,∀ᵐ a ∂μ,‖c n a‖≤1)
    (hmem : ∀ n,operator μ (c n) (hm n) (hc n)∈P)
    (hdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => c (k n) a ξ) atTop (𝓝 (A ξ))) :
    ∀ᵐ a ∂μ,commutatorSeminorm (Q a) (T a) ≤ commutatorSeminorm P (operator μ T hT hb) := by
  let d := commutatorSeminorm P (operator μ T hT hb)
  have hd : 0≤d := commutatorSeminorm_nonneg P _
  have ht (n : ℕ) : ∀ᵐ a ∂μ,‖T a*c n a-c n a*T a‖≤d := by
    apply commutator_ae_bound μ T (c n) hT (hm n) hb0 (by norm_num) hd hb (hc n)
    exact commutator_bound_unitball P _ (hmem n)
      (operator_norm_le μ (c n) (hm n) (hc n) (by norm_num) (hc n))
  filter_upwards [ae_all_iff.mpr ht,hdense] with a ha hda
  apply commutatorSeminorm_le
  intro A hA hnA
  obtain ⟨k,hk⟩ := hda A hA hnA
  apply StrongContractionLimit.norm_le_of_strong (l:=atTop) (fun n => T a*c (k n) a-c (k n) a*T a) _ _ hd
    (Eventually.of_forall (fun n => ha (k n)))
  intro ξ
  exact ((T a).continuous.tendsto (A ξ) |>.comp (hk ξ)).sub (hk (T a ξ))

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorFieldBound
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

variable {Ω : Type*} {H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem matrix_commutator_bound_of_countable_factor_fields_oai
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (T : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb0 : 0≤b) (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htmem : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (htdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (h : ℕ) (hh : 1≤h) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hX : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {c : Fin h → Fin h → ℝ} (hc0 : ∀ i j,0 ≤ c i j)
    (hc : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖ ≤ c i j)
    (hmem : ∀ᵐ a ∂μ,∀ i j,X i j a∈Q a) :
    ‖diagonalAmplification h (operator μ T hT hb)*
        matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))-
      matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))*
        diagonalAmplification h (operator μ T hT hb)‖≤
      3122*commutatorSeminorm P (operator μ T hT hb)*
        ‖matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))‖ :=
  matrix_commutator_bound_of_factor_fields μ Q hfac T hT hb0
    (commutatorSeminorm_nonneg P _) hb
    (seminorm_ae_le μ P Q T hT hb0 hb test ht htb htmem htdense)
    h hh X hX hc0 hc hmem

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields_oai.{u_1} := @OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields_oai.{u_1}
