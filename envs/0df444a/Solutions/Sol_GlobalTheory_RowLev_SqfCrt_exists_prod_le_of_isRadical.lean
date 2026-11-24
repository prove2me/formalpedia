-- Prove2me | solution 1 for GlobalTheory.RowLev.SqfCrt.exists_prod_le_of_isRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:31.133579+00:00
-- url     : https://prove2.me/submissions/91c446f2-da0e-4204-8a8d-fd57fde243f6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsProdLeOfIsRadical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.SqfCrt
namespace GlobalTheory.RowLev.SqfCrt
theorem _root_.solution {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) : ∃ T : Finset (HeightOneSpectrum R), (∀ u ∈ T, 𝔞 ≤ u.asIdeal) ∧
      ∏ u ∈ T, u.asIdeal ≤ 𝔞 := by
  have hfin := Ideal.finite_factors h0
  refine ⟨hfin.toFinset, fun u hu => Ideal.le_of_dvd ((Set.Finite.mem_toFinset hfin).1 hu), ?_⟩
  intro x hx
  apply hr
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  have hP0 : P ≠ ⊥ := fun hb => h0 (le_bot_iff.1 (hb ▸ hle))
  let v : HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have hv : v ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 (Ideal.dvd_iff_le.2 hle)
  exact (Ideal.prod_le_inf.trans (Finset.inf_le hv)) hx
end GlobalTheory.RowLev.SqfCrt
