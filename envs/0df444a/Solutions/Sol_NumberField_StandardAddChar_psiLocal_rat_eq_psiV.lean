-- Prove2me | solution 1 for NumberField.StandardAddChar.psiLocal_rat_eq_psiV
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1f0f07f9-500e-597a-9e78-525f9023f32e

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.StandardAddChar NumberField.AdelicTrace NumberField.AdelicBox Rat.HeightOneSpectrum

namespace LanglandsTunnell
namespace TateLocal
namespace LevelRat
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

private theorem algebraMap_trace_int (a : 𝓞 ℚ) :
    algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 ℚ) a) = a := by
  obtain ⟨n, rfl⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) a
  rw [Algebra.trace_algebraMap, RingOfIntegers.rank ℚ, Module.finrank_self, one_smul]

private theorem traceInt_rat : traceInt ℚ = AddMonoidHom.id _ := by
  symm
  refine eq_traceInt ℚ continuous_id fun a => ?_
  rw [traceInt_diag, algebraMap_trace_int, AddMonoidHom.id_apply, diag_eq]

private theorem traceFinHom_rat_apply (x : FiniteAdeleRing (𝓞 ℚ) ℚ) : traceFinHom ℚ x = x := by
  obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 ℚ) ℚ x
  let w : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ :=
    fun v => ⟨(algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x) v, hk v⟩
  have hsm : RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
        (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite w
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x :=
    RestrictedProduct.ext _ _ fun v => rfl
  have h1 : traceFinHom ℚ (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x := by
    rw [← hsm, traceFinHom_structureMap, traceInt_rat, AddMonoidHom.id_apply]
  have h2 : traceFinHom ℚ (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := by
    rw [traceFinHom_algebraMap]
    congr 1
    exact trace_rat_apply k
  rw [map_add, h2] at h1
  exact add_left_cancel h1

private theorem psiLocal_rat_apply (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    psiLocal ℚ v x = psiV v x := by
  rw [psiLocal_apply, show stdAddChar ℚ = (adelicTraceData ℚ).psiK from rfl,
    AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  change psiArch ((adelicTraceData ℚ).traceInf 0)
      * psiFin (traceFinHom ℚ (finAdeleSingleAt ℚ v x)) = psiV v x
  rw [map_zero, AddChar.map_zero_eq_one, one_mul, traceFinHom_rat_apply, psiFin_apply]
  rw [finprod_eq_single (fun w => psiV w (finAdeleSingleAt ℚ v x w)) v (fun w hw => by
    show psiV w (finAdeleSingleAt ℚ v x w) = 1
    rw [finAdeleSingleAt_apply_of_ne ℚ v x hw]
    exact AddChar.map_zero_eq_one _)]
  show psiV v (finAdeleSingleAt ℚ v x v) = psiV v x
  rw [finAdeleSingleAt_apply_self]

end LanglandsTunnell.TateLocal.LevelRat

end

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem solution
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    psiLocal ℚ v = psiV v :=
  AddChar.ext _ _ (LanglandsTunnell.TateLocal.LevelRat.psiLocal_rat_apply v)

end S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
end P2MW
export P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV (solution)
