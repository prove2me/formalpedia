-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResDisc.isUnit_discr_of_isMaximal_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:42.282042+00:00
-- url     : https://prove2.me/submissions/59f52691-b225-4637-8064-3512fded3285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResDisc
open IsLocalRing
namespace GlobalTheory.UnitLemma.Unr.ResDisc
theorem _root_.solution {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Finite (ResidueField R)] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
    (hmax : (Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal) :
    IsUnit (Algebra.discr R b) := by
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI : Module.Finite R S := Module.Finite.of_basis b
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field (Ideal.map (algebraMap R S) (maximalIdeal R))
  haveI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    Module.Finite.of_basis (basisQuotient b)
  haveI : Algebra.IsSeparable (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    inferInstance
  have h1 : Ideal.Quotient.mk (maximalIdeal R) (Algebra.discr R b) =
      Algebra.discr (R ⧸ maximalIdeal R) (basisQuotient b) := by
    rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, basisQuotient_apply, ← map_mul, Algebra.trace_quotient_mk]
  have h2 := Algebra.discr_not_zero_of_basis (R ⧸ maximalIdeal R) (basisQuotient b)
  rw [← h1] at h2
  by_contra h
  exact h2 (Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal _).2 h))
end GlobalTheory.UnitLemma.Unr.ResDisc
