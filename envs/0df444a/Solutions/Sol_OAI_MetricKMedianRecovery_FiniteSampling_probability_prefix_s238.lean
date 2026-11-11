-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:15:52.355414+00:00
-- url     : https://prove2.me/submissions/909bc46b-1553-4d8d-a3c6-882fd41dd23b

import Mathlib
import Definitions.Def_Q238K002

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

lemma average_equiv (e : Ω ≃ Ξ) (X : Ω → ℝ) (Y : Ξ → ℝ)
    (h : ∀ ω, X ω = Y (e ω)) : average X = average Y :=
  Fintype.expect_equiv e X Y h

end Average

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ProbabilityProd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Ω Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]

lemma average_pi_restrict [DecidableEq I] [Nonempty Ω] (Q : Finset I)
    (X : (↥Q → Ω) → ℝ) :
    average (fun seed : I → Ω => X (fun i => seed i)) = average X := by
  classical
  rw [average_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Q) (fun _ => Ω))
    (fun seed : I → Ω => X (fun i => seed i)) (fun p => X p.1) (fun _ => rfl),average_prod]
  simp

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_AveragePrecomposeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω] [Nonempty Ω]
  [DecidableEq I] [DecidableEq J]

lemma average_precompose_embedding (e : I ↪ J) (X : (I → Ω) → ℝ) :
    average (fun seed : J → Ω => X (fun i => seed (e i))) = average X := by
  classical
  let Q : Finset J := Finset.univ.image e
  let eqv : I ≃ ↥Q :=
    { toFun := fun i => ⟨e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
      invFun := fun j => Classical.choose (Finset.mem_image.mp j.property)
      left_inv := by
        intro i
        apply e.injective
        exact (Classical.choose_spec (Finset.mem_image.mp
          (show e i ∈ Q from Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).2
      right_inv := by
        intro j
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp j.property)).2 }
  let ee : (↥Q → Ω) ≃ (I → Ω) :=
    { toFun := fun seed i => seed (eqv i)
      invFun := fun seed j => seed (eqv.symm j)
      left_inv := by intro s; funext j; simp
      right_inv := by intro s; funext i; simp }
  calc
    _ = average (fun seed : ↥Q → Ω => X (ee seed)) :=
      average_pi_restrict Q (fun seed => X (ee seed))
    _ = average X := average_equiv ee _ X (fun _ => rfl)

lemma probability_precompose_embedding (e : I ↪ J) (E : (I → Ω) → Prop) :
    probability (fun seed : J → Ω => E (fun i => seed (e i))) = probability E := by
  classical
  exact average_precompose_embedding e (fun seed => if E seed then 1 else 0)

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_FairPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma probability_prefix_s238_oai {n N : ℕ} (h : n≤N) (E : (Fin n→Bool)→Prop) :
    probability (fun seed:Fin N→Bool=>E (fun i=>seed (Fin.castLE h i)))=probability E :=
  probability_precompose_embedding ⟨Fin.castLE h,Fin.castLE_injective h⟩ E
end MetricKMedianRecovery.FiniteSampling

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix_s238_oai := @OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix_s238_oai
