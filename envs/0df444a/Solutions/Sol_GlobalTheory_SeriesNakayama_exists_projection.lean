-- Prove2me | solution 1 for GlobalTheory.SeriesNakayama.exists_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:33.519803+00:00
-- url     : https://prove2.me/submissions/96c42828-4522-4880-8ca2-145964aff245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama
namespace GlobalTheory.SeriesNakayama
theorem _root_.solution {O K : Type*} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) :
    ∃ (μ : K →+ K) (l : K → O), (∀ a, f (l a) = μ a) ∧ (∀ a o, μ (a * f o) = μ a * f o) ∧
      ∀ o, μ (f o) = f o := by
  let φ : IsLocalRing.ResidueField O →+* K :=
    Ideal.Quotient.lift _ f fun a ha => by rwa [← hf] at ha
  have hφ : ∀ o, φ (IsLocalRing.residue O o) = f o := fun _ => rfl
  letI := φ.toAlgebra
  obtain ⟨r, hr⟩ := (Algebra.linearMap (IsLocalRing.ResidueField O) K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 φ.injective)
  choose l hl using fun a => IsLocalRing.residue_surjective (R := O) (r a)
  refine ⟨φ.toAddMonoidHom.comp r.toAddMonoidHom, l, fun a => ?_, fun a o => ?_, fun o => ?_⟩
  · change _ = φ (r a)
    rw [← hl, hφ]
  · change φ (r _) = φ (r a) * _
    have : a * f o = IsLocalRing.residue O o • a := mul_comm _ _
    rw [this, map_smul, smul_eq_mul, map_mul, hφ, mul_comm]
  · change φ (r _) = _
    have : r (f o) = IsLocalRing.residue O o := LinearMap.congr_fun hr (IsLocalRing.residue O o)
    rw [this, hφ]
end GlobalTheory.SeriesNakayama
