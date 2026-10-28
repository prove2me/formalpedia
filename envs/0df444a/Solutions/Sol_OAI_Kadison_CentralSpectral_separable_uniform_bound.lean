-- Prove2me | solution 1 for OAI.Kadison.CentralSpectral.separable_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:23:45.11155+00:00
-- url     : https://prove2.me/submissions/9e07c58f-5912-4beb-92a1-46c158dc243e

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C061
import Theorems.Thm_OAI_Kadison_CentralSpectral_scalar_indicator_commutes
import Theorems.Thm_OAI_Kadison_CentralSpectral_stable_model_bound
import Theorems.Thm_OAI_Kadison_CyclicSpectral_exists_gelfand_model
import Theorems.Thm_OAI_Kadison_CyclicSpectral_stableUnitary_intertwines
import Theorems.Thm_OAI_Kadison_InfiniteAmplification_separable_space
import Theorems.Thm_OAI_Kadison_IntertwinerCompression_pullback_matrix_commutator_norm_le
import Theorems.Thm_OAI_Kadison_NormalGNS_commutant_range_eq_of_commutative
import Theorems.Thm_OAI_Kadison_NormalRepresentation_exists_stable_gns_model
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg
import Theorems.Thm_OAI_Kadison_matrixOperator_subtype_norm_le

section
-- module Solutions.OAIQ039_CM.Commutator_MaximalAbelianTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma range_of_maximal_conjugate (U : H ≃ₗᵢ[ℂ] G) (σ : A → (H →L[ℂ] H)) (ρ : A → (G →L[ℂ] G))
    (hρ : Set.centralizer (Set.range ρ)=Set.range ρ)
    (hU : ∀ a,U.conjStarAlgEquiv (σ a)=ρ a)
    (T : H →L[ℂ] H) (hT : ∀ a,Commute (σ a) T) : ∃ a,σ a=T := by
  have ht : U.conjStarAlgEquiv T∈Set.centralizer (Set.range ρ) := by
    rintro _ ⟨a,rfl⟩
    rw [←hU,←map_mul,←map_mul]
    exact congrArg U.conjStarAlgEquiv (hT a).eq
  rw [hρ] at ht
  obtain ⟨a,ha⟩ := ht
  exact ⟨a,U.conjStarAlgEquiv.injective ((hU a).trans ha)⟩

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AbelianSpectralIndicators
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma conjugate_eq_of_intertwines {Domain Codomain : Type*}
    [NormedAddCommGroup Domain] [InnerProductSpace ℂ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Codomain] [InnerProductSpace ℂ Codomain] [CompleteSpace Codomain]
    (equiv : Domain ≃ₗᵢ[ℂ] Codomain)
    (first : Domain →L[ℂ] Domain) (second : Codomain →L[ℂ] Codomain)
    (intertwines : ∀ vector,equiv (first vector)=second (equiv vector)) :
    equiv.conjStarAlgEquiv first=second := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,intertwines,equiv.apply_symm_apply]

variable (M : VonNeumannAlgebra H)

variable (τ : (CentralCorner.center M) →ₚ[ℂ] ℂ)

variable (μ : Measure (Spectrum M))

variable (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] τ.GNS)

lemma scalar_conjugate
    (hU : ∀ (a : CentralCorner.center M) (v : Lp ℂ 2 μ),
      U (scalarMultiplier μ (gelfandStarTransform _ a) v)=τ.gnsStarAlgHom a (U v))
    (a : CentralCorner.center M) :
    U.conjStarAlgEquiv (scalarMultiplier μ (gelfandStarTransform _ a))=τ.gnsStarAlgHom a := by
  exact conjugate_eq_of_intertwines (Domain:=Lp ℂ 2 μ) (Codomain:=τ.GNS) U
    (scalarMultiplier μ (gelfandStarTransform _ a)) (τ.gnsStarAlgHom a) (hU a)

theorem indicator_in_scalar_spectral_range
    (hn : NormalGNS.BoundedWOTContinuous (CentralCorner.center M) τ)
    (hU : ∀ (a : CentralCorner.center M) (v : Lp ℂ 2 μ),
      U (scalarMultiplier μ (gelfandStarTransform _ a) v)=τ.gnsStarAlgHom a (U v))
    (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    ∃ a : CentralCorner.center M,
      scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs := by
  exact range_of_maximal_conjugate U
    (fun a : CentralCorner.center M => scalarMultiplier μ (gelfandStarTransform _ a))
    τ.gnsStarAlgHom
    (NormalGNS.commutant_range_eq_of_commutative (CentralCorner.center M) τ
      (fun _ _ => mul_comm _ _) hn)
    (scalar_conjugate M τ μ U hU) (indicatorOperator μ s hs)
    (fun a => scalar_indicator_commutes M μ (gelfandStarTransform _ a) s hs)

end Kadison.CentralSpectral

end

end
end

end OAI
end

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
-- module Solutions.OAIQ039_CM.Commutator_InfiniteCenter
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

local instance infiniteCenterDecidableEq_r4cbfbc_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma map_injective : Function.Injective (map (ι:=ℕ) (H:=H) (G:=H)) := by
  intro S T h
  ext x
  have he := congrArg (fun R : Space ℕ H →L[ℂ] Space ℕ H => R (lp.single 2 0 x) 0) h
  simpa only [map_apply,lp.single_apply,Pi.single_eq_same] using he

lemma map_norm (T : H →L[ℂ] H) : ‖map (ι:=ℕ) T‖=‖T‖ :=
  NonUnitalStarAlgHom.norm_map (diagonal (ι:=ℕ) (H:=H)).toNonUnitalStarAlgHom map_injective T

lemma map_mem_algebra (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) (ha : a∈M) :
    map (ι:=ℕ) a∈algebra M := ⟨⟨a,ha⟩,rfl⟩

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteBoundTransfer
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

open IntertwinerCompression

local instance infiniteBoundTransferDecidableEq_r4cbfbc_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma single0_adjoint : (single0 (H:=H)).toContinuousLinearMap.adjoint=
    lp.evalCLM ℂ (fun _ : ℕ => H) 2 0 := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact (lp.inner_single_right (𝕜:=ℂ) 0 y x).symm

omit [CompleteSpace H] in
lemma single0_intertwines (T : H →L[ℂ] H) :
    (single0 (H:=H)).toContinuousLinearMap.comp T=(map T).comp single0.toContinuousLinearMap := by
  ext x i
  change lp.single (E:=fun _ : ℕ => H) 2 0 (T x) i=T (lp.single (E:=fun _ : ℕ => H) 2 0 x i)
  by_cases hi : i=0 <;> simp [lp.single_apply,hi]

lemma pullback_map (Y : H →L[ℂ] H) :
    transfer (single0 (H:=H)).toContinuousLinearMap.adjoint (map Y)=Y := by
  rw [transfer,ContinuousLinearMap.adjoint_adjoint,single0_adjoint]
  ext x
  change Y (lp.single (E:=fun _ : ℕ => H) 2 0 x 0)=Y x
  simp only [lp.single_apply,Pi.single_eq_same]

lemma seminorm_map_le (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    commutatorSeminorm (algebra M) (map Y) ≤ commutatorSeminorm M Y := by
  apply commutatorSeminorm_le
  rintro _ ⟨a,rfl⟩ ha
  change ‖diagonal (ι:=ℕ) (H:=H) Y*diagonal (ι:=ℕ) (H:=H) a.val-
    diagonal (ι:=ℕ) (H:=H) a.val*diagonal (ι:=ℕ) (H:=H) Y‖≤_
  rw [←map_mul,←map_mul,←map_sub]
  change ‖map (ι:=ℕ) (Y*a.val-a.val*Y)‖≤_
  rw [map_norm]
  exact commutator_bound_unitball M Y a.property (by
    change ‖map (ι:=ℕ) a.val‖≤1 at ha
    rwa [map_norm] at ha)

theorem bound_of_stable_bound (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M)
    {c : ℝ} (hc : 0 ≤ c)
    (hb : ‖diagonalAmplification h (map Y)*matrixOperator h (fun i j => map (ι:=ℕ) (X i j))-
      matrixOperator h (fun i j => map (ι:=ℕ) (X i j))*diagonalAmplification h (map Y)‖≤
      c*commutatorSeminorm (algebra M) (map Y)*‖matrixOperator h (fun i j => map (ι:=ℕ) (X i j))‖) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm M Y*‖matrixOperator h X‖ := by
  let ψ := (diagonal (ι:=ℕ) (H:=H)).comp M.subtype
  have hT : ∀ a : M,single0.toContinuousLinearMap.comp (a:H →L[ℂ] H)=
      (ψ a).comp single0.toContinuousLinearMap := fun a => single0_intertwines a.val
  have hnorm : ‖(single0 (H:=H)).toContinuousLinearMap‖≤1 :=
    (single0 (H:=H)).norm_toContinuousLinearMap_le
  have hp := pullback_matrix_commutator_norm_le (A:=M) (H:=H) (G:=Space ℕ H)
    M.subtype ψ (single0 (H:=H)).toContinuousLinearMap hT
    hnorm h (fun i j => ⟨X i j,hX i j⟩) (map Y)
  rw [pullback_map] at hp
  apply hp.trans (hb.trans ?_)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (seminorm_map_le M Y) hc)
    (matrixOperator_subtype_norm_le M ψ h X hX) (norm_nonneg _)
    (mul_nonneg hc (commutatorSeminorm_nonneg M Y))

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableCentralSpectral
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

theorem exists_stable_center_spectral_model [TopologicalSpace.SeparableSpace H] :
    ∃ μ : Measure (Spectrum M), IsFiniteMeasure μ ∧
      ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ,
        (∀ (a : CentralCorner.center M) (v : Space ℕ H),
          U (map (a : H →L[ℂ] H) v)=
            scalarVectorMultiplier μ (gelfandStarTransform _ a) (U v)) ∧
        (∀ (s : Set (Spectrum M)) (hs : MeasurableSet s),
          ∃ a : CentralCorner.center M,
            scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs) ∧
        TopologicalSpace.SeparableSpace (Lp (Space ℕ ℂ) 2 μ) := by
  obtain ⟨τ,hn,hf,W,hW⟩ := NormalRepresentation.exists_stable_gns_model (CentralCorner.center M)
  obtain ⟨μ,hμ,V,hV⟩ := CyclicSpectral.exists_gelfand_model τ.gnsStarAlgHom
    (TracialGNS.vacuum τ) (by
      have he : (fun a => τ.gnsStarAlgHom a (TracialGNS.vacuum τ))=
          (fun a => TracialGNS.algebraVector τ a) :=
        funext (fun a => TracialGNS.left_vacuum τ a)
      rw [he]
      exact TracialGNS.algebraVector_dense τ)
  let U := stableUnitary μ W V
  refine ⟨μ,hμ,U,?_,?_,?_⟩
  · intro a v
    exact stableUnitary_intertwines μ W V a.val (τ.gnsStarAlgHom a)
      (gelfandStarTransform _ a) (hW a) (hV a) v
  · intro s hs
    exact indicator_in_scalar_spectral_range M τ μ V hn hV s hs
  · let : TopologicalSpace.SeparableSpace (Space ℕ H) := separable_space
    exact U.symm.isometry.isEmbedding.separableSpace

end Kadison.CentralSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableUniversalAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

theorem separable_uniform_bound_oai : SeparableTest.SeparableBound.{0} 9368 := by
  intro H _ _ _ _ M Y h hh X hX
  obtain ⟨μ,hμ,U,hU,hind,hsep⟩ := exists_stable_center_spectral_model M
  let : IsFiniteMeasure μ := hμ
  let : TopologicalSpace.SeparableSpace (Space ℕ ℂ) := separable_space
  let : TopologicalSpace.SeparableSpace (Lp (Space ℕ ℂ) 2 μ) := hsep
  apply bound_of_stable_bound M Y h X hX (by norm_num)
  exact stable_model_bound M μ U hU hind (map Y) h hh (fun i j => map (ι:=ℕ) (X i j))
    (fun i j => map_mem_algebra M _ (hX i j))

end Kadison.CentralSpectral

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.CentralSpectral.separable_uniform_bound_oai := @OAI.Kadison.CentralSpectral.separable_uniform_bound_oai
