-- Prove2me | solution 1 for Kyprianou.Ch03.levy_rightGerm_le_natFiltr_join_shiftedGerm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:14:30.491806+00:00
-- url     : https://prove2.me/submissions/5706fb5c-4442-4a14-86e1-6e7f79b70d63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_le_join_germSigma

open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
Structural shift identity for the raw natural right germ.

Proved here:
* `X(t+u) = Y_u + X_t` ⇒ `comap X(t+u) ≤ natFiltr_t ⊔ pastSigma Y ε`
* hence `natFiltr X (t+ε) ≤ natFiltr X t ⊔ pastSigma Y ε`
* hence right germ `≤ ⨅_{ε>0} (natFiltr_t ⊔ pastSigma Y ε)`

Open child:
* `iInf_join_pastSigma_le_join_germSigma` — `⨅ (G ⊔ H_ε) ≤ G ⊔ H_{0+}`
-/

namespace Kyprianou.Ch03

variable {Omega : Type} [MeasurableSpace Omega]

private lemma comap_add_le_sup (f g : Omega → Real) :
    MeasurableSpace.comap (fun ω => f ω + g ω) (inferInstance : MeasurableSpace Real) ≤
      MeasurableSpace.comap f inferInstance ⊔ MeasurableSpace.comap g inferInstance := by
  have hf : @Measurable _ _ (MeasurableSpace.comap f inferInstance ⊔
      MeasurableSpace.comap g inferInstance) _ f :=
    measurable_iff_comap_le.2 le_sup_left
  have hg : @Measurable _ _ (MeasurableSpace.comap f inferInstance ⊔
      MeasurableSpace.comap g inferInstance) _ g :=
    measurable_iff_comap_le.2 le_sup_right
  exact measurable_iff_comap_le.1 (hf.add hg)

private lemma comap_X_t_le_natFiltr (X : NNReal → Omega → Real) (t : NNReal) :
    MeasurableSpace.comap (X t) inferInstance ≤ PerfCorrMSQ.natFiltr X t :=
  le_iSup₂_of_le t le_rfl le_rfl

private lemma comap_shift_le_past (X : NNReal → Omega → Real) (t ε u : NNReal) (hu : u ≤ ε) :
    MeasurableSpace.comap (fun ω => X (t + u) ω - X t ω) inferInstance ≤
      pastSigma (fun v ω => X (t + v) ω - X t ω) ε :=
  le_iSup₂_of_le u hu le_rfl

private lemma comap_X_add_le_join (X : NNReal → Omega → Real) (t ε u : NNReal) (hu : u ≤ ε) :
    MeasurableSpace.comap (X (t + u)) inferInstance ≤
      PerfCorrMSQ.natFiltr X t ⊔
        pastSigma (fun v ω => X (t + v) ω - X t ω) ε := by
  have hEq : X (t + u) = fun ω => (X (t + u) ω - X t ω) + X t ω := by
    funext ω; ring
  rw [hEq]
  refine (comap_add_le_sup _ _).trans (sup_le ?_ ?_)
  · exact (comap_shift_le_past X t ε u hu).trans le_sup_right
  · exact (comap_X_t_le_natFiltr X t).trans le_sup_left

private lemma natFiltr_le_join_past (X : NNReal → Omega → Real) (t ε : NNReal) :
    PerfCorrMSQ.natFiltr X (t + ε) ≤
      PerfCorrMSQ.natFiltr X t ⊔
        pastSigma (fun v ω => X (t + v) ω - X t ω) ε := by
  refine iSup₂_le fun u hu => ?_
  by_cases hle : u ≤ t
  · exact (le_iSup₂_of_le u hle (le_rfl :
      MeasurableSpace.comap (X u) inferInstance ≤ MeasurableSpace.comap (X u) inferInstance)).trans
        le_sup_left
  · have htu : t ≤ u := le_of_not_ge hle
    have hvu : u - t ≤ ε := tsub_le_iff_left.mpr (by simpa [add_comm] using hu)
    have hu' : t + (u - t) = u := add_tsub_cancel_of_le htu
    rw [← hu']
    exact comap_X_add_le_join X t ε (u - t) hvu

private lemma rightGerm_le_join_past (X : NNReal → Omega → Real) (t ε : NNReal) (hε : 0 < ε) :
    (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
      PerfCorrMSQ.natFiltr X t ⊔
        pastSigma (fun v ω => X (t + v) ω - X t ω) ε := by
  have hle :
      (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
        PerfCorrMSQ.natFiltr X (t + ε) :=
    iInf₂_le (t + ε) (lt_add_of_pos_right t hε)
  exact hle.trans (natFiltr_le_join_past X t ε)

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X : NNReal -> Omega -> Real)
    (t : NNReal) :
    (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
      PerfCorrMSQ.natFiltr X t ⊔
        germSigma (fun u : NNReal => fun omega : Omega => X (t + u) omega - X t omega) := by
  have hBound :
      (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
        (⨅ ε : NNReal, ⨅ (_ : 0 < ε),
          PerfCorrMSQ.natFiltr X t ⊔
            pastSigma (fun v ω => X (t + v) ω - X t ω) ε) :=
    le_iInf₂ fun ε hε => rightGerm_le_join_past X t ε hε
  exact hBound.trans
    (iInf_join_pastSigma_le_join_germSigma (PerfCorrMSQ.natFiltr X t)
      (fun u ω => X (t + u) ω - X t ω))
