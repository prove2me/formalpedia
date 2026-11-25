-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.denseRange_algebraMap_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:29.1858+00:00
-- url     : https://prove2.me/submissions/bb88de68-9589-48ae-a4b1-f8e792e9be39

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Theorems.Thm_GroundTheory_Global_SemiLocal_exists_sub_mem_pow_of_injective
import Theorems.Thm_GroundTheory_Global_SemiLocal_norm_algebraMap_le_of_mem_pow
import Theorems.Thm_GroundTheory_Global_SemiLocal_toNNReal_exp_neg_one_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter
noncomputable section
open GroundTheory.Global.SemiLocal
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by
  classical
  have := Fintype.ofFinite ι
  let f : L →+* ((i : ι) → (w i).adicCompletion L) := RingHom.pi fun i ↦ algebraMap L _
  let S : Subring ((i : ι) → (w i).adicCompletion L) := f.range.topologicalClosure
  have hδ : ∀ i, Pi.single i 1 ∈ S := by
    intro i
    choose a ha using fun n ↦ exists_sub_mem_pow_of_injective w hw i n
    refine mem_closure_of_tendsto (b := atTop) (f := fun n ↦ f (algebraMap (𝓞 L) L (a n))) ?_
      (Eventually.of_forall fun n ↦ ⟨_, rfl⟩)
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _)
        (toNNReal_exp_neg_one_lt_one (w j)))
    have h := norm_algebraMap_le_of_mem_pow (w j) _ n (ha n j)
    refine le_of_eq_of_le ?_ h
    congr 1
    by_cases hji : j = i
    · subst hji
      simp [f, ← IsScalarTower.algebraMap_apply]
    · simp [f, hji, ← IsScalarTower.algebraMap_apply]
  have hE : ∀ y : ι → L, (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ∈ S := by
    intro y
    have : (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) =
        ∑ i, Pi.single i 1 * f (y i) := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, f, RingHom.pi_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [this]
    exact S.sum_mem fun i _ ↦ S.mul_mem (hδ i) (f.range.le_topologicalClosure ⟨y i, rfl⟩)
  have hdense : DenseRange (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) :=
    DenseRange.piMap fun i ↦ HeightOneSpectrum.denseRange_algebraMap L (w i)
  have hsub : Set.range (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ⊆
      closure (Set.range f) := by
    rintro _ ⟨y, rfl⟩
    exact hE y
  exact dense_closure.1 (hdense.mono hsub)
end GroundTheory.Global.SemiLocal
