-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.continuous_finiteCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:16.781628+00:00
-- url     : https://prove2.me/submissions/d0b764b5-fd56-46ec-b7bc-0d949c8befe3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_localCoord
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_localCoord_mem
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (i : ι) : Continuous (finiteCoord b i) := by
  refine (RestrictedProduct.continuous_dom
    (R := fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (A := fun w ↦ (w.adicCompletionIntegers L : Set (w.adicCompletion L)))).2 fun S hS ↦ ?_
  set T : Set (HeightOneSpectrum (𝓞 L)) := Sᶜ ∪ {w | algebraMap L (w.adicCompletion L)
    (traceDual b i) ∉ w.adicCompletionIntegers L} with hTdef
  have hT : T.Finite := by
    refine Set.Finite.union ?_ ?_
    · exact le_principal_iff.1 hS
    · exact Filter.eventually_cofinite.1
        (algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)).2
  have hS' : cofinite ≤ 𝓟 (below K '' T)ᶜ := by
    rw [le_principal_iff, mem_cofinite, compl_compl]
    exact hT.image _
  let g : Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]_[𝓟 S] →
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [v.adicCompletion K, v.adicCompletionIntegers K]_[𝓟 (below K '' T)ᶜ] :=
    fun y ↦ ⟨fun v ↦ localCoord b v i (fun w ↦ y w.1), by
      rw [eventually_principal]
      intro v hv
      refine localCoord_mem b v i _ fun w ↦ ?_
      have hw : w.1 ∉ T := fun hw ↦ hv ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩
      simp only [hTdef, Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq] at hw
      exact mul_mem (eventually_principal.1 y.2 _ hw.1) hw.2⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal_iff_forall.2 fun v ↦
    (continuous_localCoord b v i).comp
      (continuous_pi fun w ↦ RestrictedProduct.continuous_eval w.1)
  exact (RestrictedProduct.continuous_inclusion hS').comp hg
end GroundTheory.Global.AdeleBaseChange
