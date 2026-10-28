-- Prove2me | solution 1 for OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:37:53.710617+00:00
-- url     : https://prove2.me/submissions/8ca95e62-4974-4db1-b8a0-b1da02e1726a

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C011
import Definitions.Def_OAIQ039C033
import Theorems.Thm_OAI_Kadison_Decomposable_exists_common_tests
import Theorems.Thm_OAI_Kadison_Decomposable_exists_pointwise_starHom
import Theorems.Thm_OAI_Kadison_Decomposable_uniform_commutator_in_central_model
import Theorems.Thm_OAI_Kadison_exists_separable_cstar_bicommutant

section
-- module Solutions.OAIQ039_CM.Commutator_CentralRepresentationModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A B : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

theorem uniform_commutator_in_representation_model
    (P : VonNeumannAlgebra (Lp H 2 μ))
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρc : B →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (σc : Ω → B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hm : ∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ)
    (hmc : ∀ b ξ,AEStronglyMeasurable (fun x => σc x b ξ) μ)
    (hact : ∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x))
    (hactc : ∀ b (f : Lp H 2 μ),ρc b f =ᵐ[μ] fun x => σc x b (f x))
    (hP : NormalGNS.bicommutant ρ.range=P)
    (hPc : NormalGNS.bicommutant ρc.range=P.commutant)
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ C : H →L[ℂ] H,Commute
        (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z)
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨test,ht,hb,htP,htQ,hfd,hgd⟩ := exists_common_tests μ ρ σ hm hact
  obtain ⟨cotest,hs,hc,hsP,hsR,hcfd,hcgd⟩ := exists_common_tests μ ρc σc hmc hactc
  rw [hP] at htP hgd
  rw [hPc] at hsP hcgd
  exact uniform_commutator_in_central_model μ P
    (fun x => NormalGNS.bicommutant (σ x).range)
    (fun x => NormalGNS.bicommutant (σc x).range) hdiag test cotest ht hs hb hc
    htP hsP htQ hsR hfd hcfd hgd hcgd hcenter Y h hh X hX

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ClosedCStarOrder
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.ClosedCStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem starOrderedRing (S : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S:Set (H →L[ℂ] H))] : StarOrderedRing S :=
  StarOrderedRing.of_nonneg_iff' (fun {x y} h z => (show (z : H →L[ℂ] H)+(x : H →L[ℂ] H)≤(z : H →L[ℂ] H)+(y : H →L[ℂ] H) from add_le_add_right (show (x : H →L[ℂ] H)≤(y : H →L[ℂ] H) from h) _)) (by
    intro T
    constructor
    · intro hT
      have hm : CFC.sqrt (T : H →L[ℂ] H)∈S := by
        rw [CFC.sqrt_eq_real_sqrt (T : H →L[ℂ] H) hT]
        exact cfcₙ_mem (𝕜':=ℂ) Real.sqrt T.property
      refine ⟨⟨CFC.sqrt (T : H →L[ℂ] H),hm⟩,?_⟩
      apply Subtype.ext
      change (T : H →L[ℂ] H)=star (CFC.sqrt (T : H →L[ℂ] H))*CFC.sqrt (T : H →L[ℂ] H)
      rw [(CFC.sqrt_nonneg (T : H →L[ℂ] H)).star_eq,CFC.sqrt_mul_sqrt_self (T : H →L[ℂ] H) hT]
    · rintro ⟨T,rfl⟩
      exact (star_mul_self_nonneg (T : H →L[ℂ] H)))

end Kadison.ClosedCStar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralSpectralModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]

theorem uniform_commutator_in_central_spectral_model_nonzero_oai [NeZero μ]
    (P : VonNeumannAlgebra (Lp H 2 μ))
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ C : H →L[ℂ] H,Commute
        (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z)
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨S,hclosedS,hsepS,hSP,hSS⟩ := exists_separable_cstar_bicommutant P
  obtain ⟨T,hclosedT,hsepT,hTP,hTT⟩ := exists_separable_cstar_bicommutant P.commutant
  let : IsClosed (S:Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := hclosedS
  let : IsClosed (T:Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := hclosedT
  let : CStarAlgebra S := StarSubalgebra.cstarAlgebra S
  let : CStarAlgebra T := StarSubalgebra.cstarAlgebra T
  let : StarOrderedRing S := ClosedCStar.starOrderedRing S
  let : StarOrderedRing T := ClosedCStar.starOrderedRing T
  let : TopologicalSpace.SeparableSpace S := hsepS
  let : TopologicalSpace.SeparableSpace T := hsepT
  obtain ⟨σ,hm,hact⟩ := exists_pointwise_starHom μ S.subtype (by
    intro a s hs
    exact (hdiag s hs).2 a (hSP a.property))
  obtain ⟨σc,hmc,hactc⟩ := exists_pointwise_starHom μ T.subtype (by
    intro a s hs
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hTP a.property) _ (hdiag s hs).1).symm)
  have hrS : S.subtype.range=S := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a,ha⟩,rfl⟩
  have hrT : T.subtype.range=T := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a,ha⟩,rfl⟩
  exact uniform_commutator_in_representation_model μ P S.subtype σ T.subtype σc
    hm hmc hact hactc (by rwa [hrS]) (by rwa [hrT]) hdiag hcenter Y h hh X hX

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero_oai := @OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero_oai
