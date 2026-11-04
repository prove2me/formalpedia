-- Prove2me | solution 2 for OAI.FreeGroupFactorMain.one_step_from_laurent
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T05:24:10.664987+00:00
-- url     : https://prove2.me/submissions/d0312eec-2798-4c13-a230-81591d389eba

import Mathlib
import Definitions.Def_FreeGroupFactorProof33

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

variable {G : Type uG} [Group G]

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

theorem one_step_from_laurent (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (l : ℤ →₀ ℂ) (hl0 : l 0 = 0)
    (hlS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (Fin n))) l))
    (hln : ‖laurentValue (generatorUnitary (none : Option (Fin n))) l‖ ≤ 2*(Real.pi+1))
    (z : unitary ℂ) (hze : twoNorm (NormedSpace.exp (Complex.I • laurentValue
      (generatorUnitary (none : Option (Fin n))) l) - (z : ℂ) • groupUnitary (FreeGroup.of none)) < ε/2)
    (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n)))
    (hh : coefficientNorm h < (ε/2)/(3*(2*(Real.pi+1))))
    (hw : coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) <
      (ε/2)/(3*(2*(Real.pi+1)))) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  let K : ℝ := 2*(Real.pi+1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨β,hβt,hβn,_hβC,hβgen,hβword⟩ :=
    laurent_flow_displacement (ι := Fin n) (firstCoefficients h) l hl0 hlS K hK.le hln
  obtain ⟨γ,hγt,_hγn,hγi,hγgen,hγC⟩ := gauged_nielsen_iso (ι := Fin n) w z
  have hnormal : @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
      (groupUltraweakTopology (FreeGroup (Option (Fin n)))) (β.trans γ.symm) := by
    let : TopologicalSpace (groupVonNeumann (FreeGroup (Option (Fin n)))) :=
      groupUltraweakTopology (FreeGroup (Option (Fin n)))
    exact hγi.comp hβn
  refine ⟨β.trans γ.symm,?_,hnormal,w,?_,?_⟩
  · intro T
    change canonicalTrace (γ.symm (β T)) = canonicalTrace T
    rw [trace_symm γ hγt,hβt]
  · intro j
    exact one_step_generator_estimate (G := FreeGroup (Option (Fin n))) β γ _ (hγgen j) hK hε (hβgen j)
      ((firstCoefficients_norm_le h j).trans_lt hh)
  · exact one_step_word_estimate (G := FreeGroup (Option (Fin n))) β γ hγt (generatorUnitary (none : Option (Fin n)))
      (groupUnitaryUHom (FreeGroup (Option (Fin n))) (FreeGroup.map Option.some w))
      _ z hγC hK (hβword w) hw hze

end FreeGroupFactorMain

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.one_step_from_laurent := @OAI.FreeGroupFactorMain.one_step_from_laurent
