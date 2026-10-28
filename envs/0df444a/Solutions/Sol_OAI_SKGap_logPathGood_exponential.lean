-- Prove2me | solution 1 for OAI.SKGap.logPathGood_exponential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:44:35.836909+00:00
-- url     : https://prove2.me/submissions/269731d6-2de3-4a96-a256-a13a2a30ee77

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_path_all_good_exponential

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LogDetIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logPathGood_exponential_oai [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA : 0 < A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hs : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | goeMatrix (j/(Fintype.card ι:ℝ)) g ∉
        logPathGood (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
          ((j/(Fintype.card ι:ℝ))*∑ b,a b) a} ≤ 3*Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
  apply (measureReal_mono (s₂ := {g | ∃ z ∈ Icc (0:ℝ) 1, g ∉ truncationGoodSet (j/(Fintype.card ι:ℝ))
        (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
        (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))}) ?_ (measure_ne_top _ _)).trans
    (path_all_good_exponential hj hA ha haA hs herr)
  intro g hg
  by_contra hcontra
  change ¬(∃ z ∈ Icc (0:ℝ) 1, _) at hcontra
  push Not at hcontra
  apply hg
  constructor
  · exact (hcontra 0 (by constructor <;> norm_num)).1.le
  · intro z hz
    exact ⟨(hcontra z hz).2.1.le,(hcontra z hz).2.2.le⟩

end SKGap
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKGap.logPathGood_exponential_oai.{u_1} := @OAI.SKGap.logPathGood_exponential_oai.{u_1}
