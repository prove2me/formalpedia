-- Prove2me | solution 1 for OAI.Kadison.Decomposable.uniform_commutator_in_central_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:37:10.355111+00:00
-- url     : https://prove2.me/submissions/cdbe3494-6871-4793-abec-c0358342045b

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C043
import Definitions.Def_OAIQ039C044
import Theorems.Thm_OAI_Kadison_Decomposable_commutant_ae_of_dense_commuting_fields
import Theorems.Thm_OAI_Kadison_Decomposable_factors_ae_of_central_geometry
import Theorems.Thm_OAI_Kadison_Decomposable_localized_matrix_commutator_bound

section
-- module Solutions.OAIQ039_CM.Commutator_FieldMembership
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

theorem exists_member_field (P : VonNeumannAlgebra (Lp H 2 μ))
    (Q : Ω → VonNeumannAlgebra H)
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈Set.centralizer
        (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htmem : ∀ n,∀ᵐ a ∂μ,test n a∈Q a)
    (htdense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop (𝓝 (A f)))
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) (hA : A∈P) :
    ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
      (hb : ∀ᵐ a ∂μ,‖T a‖≤‖A‖),A=operator μ T hm hb ∧ ∀ᵐ a ∂μ,T a∈Q a := by
  obtain ⟨T,hm,hb,he⟩ := exists_field_of_commutes_indicator μ A
    (fun s hs => (hdiag s hs) A hA)
  refine ⟨T,hm,hb,he,?_⟩
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
  obtain ⟨k,hk⟩ := htdense (d⁻¹ • A) (P.smul_mem hA d⁻¹) hdn
  have hlim : ∀ f,Tendsto
      (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop
      (𝓝 (operator μ (fun a => d⁻¹ • T a) (smul_measurable μ d⁻¹ T hm)
        (smul_field_bound μ d⁻¹ T hb) f)) := by
    intro f
    rw [operator_smul μ d⁻¹ T hm hb,←he]
    exact hk f
  have hmem := mem_ae_of_bounded_strong_limit μ Q
    (fun a => d⁻¹ • T a) (smul_measurable μ d⁻¹ T hm)
    (smul_field_bound μ d⁻¹ T hb) (fun n => test (k n)) (fun n => ht (k n))
    (by norm_num : (0:ℝ)≤1) (fun n => htb (k n)) (fun n => htmem (k n)) hlim
  filter_upwards [hmem] with a ha
  have h := (Q a).smul_mem (r:=d) ha
  change T a∈(Q a).toStarSubalgebra
  simpa only [smul_smul,mul_inv_cancel₀ hd,one_smul] using h

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorModelMain
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

variable {Ω H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem uniform_commutator_in_factor_model
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htP : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (htQ : ∀ n,∀ᵐ a ∂μ,test n a∈Q a)
    (hfiberdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (hglobaldense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop (𝓝 (A f)))
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  choose T hm hb he hq using (fun i j => exists_member_field μ P Q
    (fun s hs => (hdiag s hs).2) test ht htb htQ hglobaldense (X i j) (hX i j))
  have hmem : ∀ᵐ a ∂μ,∀ i j,T i j a∈Q a :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hq i j))
  have hg := localized_matrix_commutator_bound μ P Q hfac hdiag test ht htb htP
    hfiberdense Y h hh T hm (fun i j => norm_nonneg (X i j)) hb hmem
  simpa only [←he] using hg

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralGeometryModel
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

variable {Ω H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem uniform_commutator_in_central_model_oai
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q R : Ω → VonNeumannAlgebra H)
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test cotest : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (hs : ∀ n ξ,AEStronglyMeasurable (fun a => cotest n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (hsb : ∀ n,∀ᵐ a ∂μ,‖cotest n a‖≤1)
    (htP : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (hsP : ∀ n,operator μ (cotest n) (hs n) (hsb n)∈P.commutant)
    (htQ : ∀ n,∀ᵐ a ∂μ,test n a∈Q a)
    (hsR : ∀ n,∀ᵐ a ∂μ,cotest n a∈R a)
    (hfiberdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (hcofiberdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈R a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => cotest (k n) a ξ) atTop (𝓝 (A ξ)))
    (hglobaldense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop (𝓝 (A f)))
    (hcoglobaldense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P.commutant → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (cotest (k n)) (hs (k n)) (hsb (k n)) f) atTop (𝓝 (A f)))
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ B : H →L[ℂ] H,Commute
        (operator μ (fun _ => B) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z)
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  have hPd : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈Set.centralizer
        (P.commutant : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := by
    intro s hs B hB
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hB _ (hdiag s hs).1).symm
  have hPmem : ∀ A,A∈P → FieldMember μ Q A := by
    intro A hA
    obtain ⟨T,hm,hb,he,hmem⟩ := exists_member_field μ P Q (fun s hs => (hdiag s hs).2)
      test ht htb htQ hglobaldense A hA
    exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,hmem⟩
  have hPcmem : ∀ A,A∈P.commutant → FieldMember μ R A := by
    intro A hA
    obtain ⟨T,hm,hb,he,hmem⟩ := exists_member_field μ P.commutant R hPd
      cotest hs hsb hsR hcoglobaldense A hA
    exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,hmem⟩
  have hRQ := commutant_ae_of_dense_commuting_fields μ Q R test cotest ht hs htb hsb
    (fun i j => VonNeumannAlgebra.mem_commutant_iff.mp (hsP j) _ (htP i))
    hfiberdense hcofiberdense
  have hfac := factors_ae_of_central_geometry μ P Q R hPmem hPcmem hRQ hcenter
  exact uniform_commutator_in_factor_model μ P Q hfac hdiag test ht htb htP htQ
    hfiberdense hglobaldense Y h hh X hX

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.Decomposable.uniform_commutator_in_central_model_oai := @OAI.Kadison.Decomposable.uniform_commutator_in_central_model_oai
