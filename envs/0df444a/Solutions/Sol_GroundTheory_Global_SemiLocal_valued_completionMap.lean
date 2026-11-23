-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.valued_completionMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:07.940803+00:00
-- url     : https://prove2.me/submissions/0adc53a6-9e34-473c-9ec3-48f8ba16edbf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap

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
open IsDedekindDomain NumberField
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  have hK : ∀ k : K, Valued.v (completionMap v w (algebraMap K _ k)) =
      Valued.v (algebraMap K (v.adicCompletion K) k) ^ e := by
    intro k
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [he, ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
      HeightOneSpectrum.valuation_liesOver L v w]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hclosed : IsClosed
      {x : v.adicCompletion K | Valued.v (completionMap v w x) = Valued.v x ^ e} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x0 hx0
    have h0 : x0 ≠ 0 := by
      rintro rfl
      simp [zero_pow he0] at hx0
    have h1 : Valued.v x0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (completionMap v w x0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (completionMap v w).injective).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_completionMap v w).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with x hx hx'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hx hx' hx0 ⊢
    rwa [hx, hx']
  exact (HeightOneSpectrum.denseRange_algebraMap K v).induction_on x hclosed hK
end GroundTheory.Global.SemiLocal
