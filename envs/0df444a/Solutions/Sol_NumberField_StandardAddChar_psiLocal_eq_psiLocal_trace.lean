-- Prove2me | solution 1 for NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3e8254d6-9332-5005-9096-6153c39bf5c4

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.NumberField IsDedekindDomain NumberField.StandardAddChar P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.NumberField.StandardAddChar"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place AdelicTrace.traceFinHom_apply_eq_sum_trace"
namespace StandardAddChar
p2m_export "NumberField.StandardAddChar" "finAdeleSingleAt finAdeleSingleAt_apply_self finAdeleSingleAt_apply_of_ne psiLocal psiLocal_apply traceFinHom adelicTraceData traceInfHom AdelicTraceData AdelicTraceData.adelicTrace_apply psiV psiFin psiFin_apply psiArch psiQ psiQ_apply"
namespace LocalTraceCompat
p2m_open "NumberField.StandardAddChar NumberField"

section oneField

variable (L : Type) [Field L] [NumberField L]

private theorem psiLocal_eq_psiFin (u : HeightOneSpectrum (𝓞 L)) (x : u.adicCompletion L) :
    psiLocal L u x = psiFin (traceFinHom L (finAdeleSingleAt L u x)) := by
  rw [psiLocal_apply]
  change psiQ ((adelicTraceData L).adelicTrace ((0 : InfiniteAdeleRing L), finAdeleSingleAt L u x)) = _
  rw [AdelicTraceData.adelicTrace_apply, psiQ_apply]
  change psiArch (traceInfHom L 0) * psiFin (traceFinHom L (finAdeleSingleAt L u x)) = _
  rw [map_zero, AddChar.map_zero_eq_one, one_mul]

private theorem psiLocal_eq_psiV_trace (p : HeightOneSpectrum (𝓞 ℚ)) (u : p.Extension (𝓞 L))
    (x : u.1.adicCompletion L) :
    psiLocal L u.1 x = psiV p (Algebra.trace (p.adicCompletion ℚ) (u.1.adicCompletion L) x) := by
  rw [psiLocal_eq_psiFin, psiFin_apply]
  rw [finprod_eq_single _ p (fun q hq => ?_)]
  · congr 1
    rw [NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace L (finAdeleSingleAt L u.1 x) p]
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ L (𝓞 L) p
    rw [Finset.sum_eq_single u]
    · rw [finAdeleSingleAt_apply_self]
    · intro w _ hw
      rw [finAdeleSingleAt_apply_of_ne L u.1 _ (fun h => hw (Subtype.ext h)), map_zero]
    · intro h
      exact absurd (Finset.mem_univ u) h
  · rw [NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace L (finAdeleSingleAt L u.1 x) q]
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ L (𝓞 L) q
    rw [Finset.sum_eq_zero (fun w _ => ?_), AddChar.map_zero_eq_one]
    have hne : w.1 ≠ u.1 := fun h => hq (by rw [← w.2, ← u.2, h])
    rw [finAdeleSingleAt_apply_of_ne L u.1 _ hne, map_zero]

end oneField

section tower

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

private theorem ringHom_ratInt_ext {R : Type*} [Ring R] (f g : 𝓞 ℚ →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) := by
    have h := (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom (Rat.ringOfIntegersEquiv x)).symm
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply] at h
    exact h.symm
  rw [hx, map_intCast, map_intCast]

private theorem under_rat_eq : w.1.under (𝓞 ℚ) = v.under (𝓞 ℚ) := by
  apply HeightOneSpectrum.ext
  have hv : v.asIdeal = Ideal.under (𝓞 K) w.1.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (congrArg HeightOneSpectrum.asIdeal w.2).symm
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, hv,
    Ideal.under_def, Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
    ringHom_ratInt_ext ((algebraMap (𝓞 K) (𝓞 L)).comp (algebraMap (𝓞 ℚ) (𝓞 K))) (algebraMap (𝓞 ℚ) (𝓞 L))]

private def pQ : HeightOneSpectrum (𝓞 ℚ) := v.under (𝓞 ℚ)

private def vp : (pQ K v).Extension (𝓞 K) := ⟨v, rfl⟩

private def wp : (pQ K v).Extension (𝓞 L) := ⟨w.1, under_rat_eq K L v w⟩

local notation "ℚp" => HeightOneSpectrum.adicCompletion ℚ (pQ K v)
local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

@[reducible] private def algQK : Algebra ℚp Kv := inferInstanceAs (Algebra ℚp ((vp K v).1.adicCompletion K))
@[reducible] private def algQL : Algebra ℚp Lw := inferInstanceAs (Algebra ℚp ((wp K L v w).1.adicCompletion L))

attribute [local instance] algQK algQL

private theorem finiteDimensional_QK : FiniteDimensional ℚp Kv :=
  inferInstanceAs (FiniteDimensional ℚp ((vp K v).1.adicCompletion K))
private theorem finiteDimensional_QL : FiniteDimensional ℚp Lw :=
  inferInstanceAs (FiniteDimensional ℚp ((wp K L v w).1.adicCompletion L))

attribute [local instance] finiteDimensional_QK finiteDimensional_QL

private theorem tower_apply (y : ℚp) :
    algebraMap Kv Lw (algebraMap ℚp Kv y) = algebraMap ℚp Lw y := by
  have hKL : Continuous (algebraMap Kv Lw) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K L w
  have hQK : Continuous (algebraMap ℚp Kv) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ K (vp K v)
  have hQL : Continuous (algebraMap ℚp Lw) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ L (wp K L v w)
  refine DenseRange.induction_on (HeightOneSpectrum.denseRange_algebraMap ℚ (pQ K v)) y
    (isClosed_eq (hKL.comp hQK) hQL) (fun q => ?_)
  change (w.adicCompletionSemialgHom K L) (((vp K v).adicCompletionSemialgHom ℚ K) (algebraMap ℚ ℚp q))
    = ((wp K L v w).adicCompletionSemialgHom ℚ L) (algebraMap ℚ ℚp q)
  have h1 : ((vp K v).adicCompletionSemialgHom ℚ K) (algebraMap ℚ ℚp q) = algebraMap K Kv (algebraMap ℚ K q) :=
    SemialgHom.commutes _ _
  have h2 : (w.adicCompletionSemialgHom K L) (algebraMap K Kv (algebraMap ℚ K q))
      = algebraMap L Lw (algebraMap K L (algebraMap ℚ K q)) :=
    SemialgHom.commutes _ _
  have h3 : ((wp K L v w).adicCompletionSemialgHom ℚ L) (algebraMap ℚ ℚp q) = algebraMap L Lw (algebraMap ℚ L q) :=
    SemialgHom.commutes _ _
  rw [h1, h2, h3, eq_ratCast (algebraMap ℚ K) q, eq_ratCast (algebraMap ℚ L) q, map_ratCast]

private theorem isScalarTower_QKL : IsScalarTower ℚp Kv Lw :=
  IsScalarTower.of_algebraMap_eq fun y => (tower_apply K L v w y).symm

attribute [local instance] isScalarTower_QKL

private theorem trace_tower (x : Lw) :
    Algebra.trace ℚp Kv (Algebra.trace Kv Lw x) = Algebra.trace ℚp Lw x :=
  Algebra.trace_trace x

end tower

private theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) := by
  have hL := psiLocal_eq_psiV_trace L (pQ K v) (wp K L v w) x
  have hK := psiLocal_eq_psiV_trace K (pQ K v) (vp K v)
    (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x)
  have ht := trace_tower K L v w x
  change psiLocal L w.1 x = _ at hL
  change psiLocal K v _ = _ at hK
  rw [hL, hK]
  exact congrArg (psiV (pQ K v)) ht.symm

end NumberField.StandardAddChar.LocalTraceCompat

end

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L))
    (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) :=
  NumberField.StandardAddChar.LocalTraceCompat.main K L v w x

end S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace
end P2MW
export P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace (solution)
