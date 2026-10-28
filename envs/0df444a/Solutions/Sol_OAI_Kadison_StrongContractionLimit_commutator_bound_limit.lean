-- Prove2me | solution 1 for OAI.Kadison.StrongContractionLimit.commutator_bound_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:07:53.863915+00:00
-- url     : https://prove2.me/submissions/677f6314-dc23-4ba1-ac1a-aa89e023e83e

import Mathlib
import Definitions.Def_UniformCommutator

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContractionLimit
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
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedStrongLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open Filter

namespace Kadison.StrongContractionLimit

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {l : Filter ι}

omit [CompleteSpace H] in
lemma piLp_tendsto {κ : Type*} [Fintype κ] (u : ι → PiLp 2 (fun _ : κ => H))
    (x : PiLp 2 (fun _ : κ => H)) (hu : ∀ k,Tendsto (fun i => u i k) l (𝓝 (x k))) :
    Tendsto u l (𝓝 x) := by
  have h := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => H)).symm.continuous.tendsto
    (fun k => x k)
  exact h.comp (tendsto_pi_nhds.mpr hu)

omit [CompleteSpace H] in
lemma diagonal_tendsto (P : ι → H →L[ℂ] H) (Y : H →L[ℂ] H)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Y x)))
    (h : ℕ) (x : PiLp 2 (fun _ : Fin h => H)) :
    Tendsto (fun i => diagonalAmplification h (P i) x) l (𝓝 (diagonalAmplification h Y x)) := by
  apply piLp_tendsto
  intro k
  exact hstrong (x k)

omit [CompleteSpace H] in
lemma commutator_tendsto (P : ι → H →L[ℂ] H) (Y : H →L[ℂ] H)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Y x)))
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : Fin h => H)) :
    Tendsto (fun i => (diagonalAmplification h (P i)*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h (P i)) x) l
      (𝓝 ((diagonalAmplification h Y*matrixOperator h X-
        matrixOperator h X*diagonalAmplification h Y) x)) := by
  exact (diagonal_tendsto P Y hstrong h (matrixOperator h X x)).sub
    (((matrixOperator h X).continuous.tendsto (diagonalAmplification h Y x)).comp
      (diagonal_tendsto P Y hstrong h x))

omit [CompleteSpace H] in
lemma commutator_bound_limit_oai [l.NeBot] (P : ι → H →L[ℂ] H) (Y : H →L[ℂ] H)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Y x)))
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ᶠ i in l,‖diagonalAmplification h (P i)*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h (P i)‖≤C) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤C :=
  norm_le_of_strong _ _ (commutator_tendsto P Y hstrong h X) hC hbound

end Kadison.StrongContractionLimit

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.StrongContractionLimit.commutator_bound_limit_oai.{u_1, u_2} := @OAI.Kadison.StrongContractionLimit.commutator_bound_limit_oai.{u_1, u_2}
