-- Prove2me | solution 1 for GlobalTheory.RowLev.Inhab.ker_eq_extId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:21:17.928519+00:00
-- url     : https://prove2.me/submissions/19b12d88-3e89-411b-add1-e9f3c0a782f4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_Inhab_exists_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Inhab
namespace GlobalTheory.RowLev.Inhab
theorem _root_.solution {I : AutInst} {p : ℕ} (hp : p ≠ 0) {w : HeightOneSpectrum (𝓞 I.E)}
    (r : IntAf I.F I.E →+* ZMod p) (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) :
    RingHom.ker r = extId I w.asIdeal := by
  apply le_antisymm
  · intro s h
    rw [RingHom.mem_ker] at h
    obtain ⟨b, t, e⟩ := exists_approx hp s
    rw [← map_natCast (psi I.F I.E)] at e
    have hpr : r (psi I.F I.E (p : 𝓞 I.E)) = 0 := by rw [map_natCast, map_natCast, ZMod.natCast_self]
    have hb : r (psi I.F I.E b) = 0 := by
      rw [e, map_add, _root_.map_mul, hpr, zero_mul, add_zero] at h
      exact h
    rw [e]
    exact add_mem (Ideal.subset_span ⟨b, (hr b).1 hb, rfl⟩)
      (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, (hr _).1 hpr, rfl⟩))
  · rw [extId, Ideal.span_le]
    rintro ⟨z, hz⟩ ⟨b, hb, rfl⟩
    exact (hr b).2 hb
end GlobalTheory.RowLev.Inhab
