-- Prove2me | solution 1 for GroundTheory.Global.denseRange_units_prod_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:48.822801+00:00
-- url     : https://prove2.me/submissions/bf597262-471b-4ec2-bdb6-60a5803caef6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
import Theorems.Thm_GroundTheory_Global_denseRange_algebraMap_prod_pi


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
open IsDedekindDomain NumberField Topology
variable {K : Type*} [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
namespace GroundTheory.Global
theorem _root_.solution :
    DenseRange (fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a))) := by
  classical
  set f := fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a)) with hf
  set E : ((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ) →
      ((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion) :=
    Prod.map (Pi.map fun _ ↦ Units.val) (Pi.map fun _ ↦ Units.val) with hE
  have hEi : IsInducing E :=
    (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing).prodMap
      (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing)
  let W : Set (((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion)) :=
    {z | (∀ v, z.1 v ≠ 0) ∧ ∀ w, z.2 w ≠ 0}
  have hW : IsOpen W := by
    have : W = (⋂ v, {z | z.1 v ≠ 0}) ∩ ⋂ w, {z | z.2 w ≠ 0} := by
      ext z; simp [W]
    rw [this]
    exact (isOpen_iInter_of_finite fun v ↦
      isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const).inter
      (isOpen_iInter_of_finite fun w ↦
        isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ ↦ ?_
  obtain ⟨V, hV, rfl⟩ := hEi.isOpen_iff.1 hU
  have hEu : E u ∈ W := ⟨fun v ↦ (u.1 v).ne_zero, fun w ↦ (u.2 w).ne_zero⟩
  obtain ⟨x, hxV, hxW⟩ := (denseRange_algebraMap_prod_pi S T).exists_mem_open (hV.inter hW)
    ⟨E u, hu, hEu⟩
  by_cases hx : x = 0
  · have hS : IsEmpty S := ⟨fun v ↦ hxW.1 v (by rw [hx]; exact map_zero _)⟩
    have hT : IsEmpty T := ⟨fun w ↦ hxW.2 w (by rw [hx]; exact map_zero _)⟩
    refine ⟨f 1, ?_, 1, rfl⟩
    show E (f 1) ∈ V
    convert hxV using 1
    exact Prod.ext (funext fun v ↦ isEmptyElim v) (funext fun w ↦ isEmptyElim w)
  · refine ⟨f (Units.mk0 x hx), ?_, _, rfl⟩
    exact hxV
end GroundTheory.Global
