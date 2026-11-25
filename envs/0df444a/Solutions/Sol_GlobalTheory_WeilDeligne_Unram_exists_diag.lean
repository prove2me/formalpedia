-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.Unram.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:02:01.049569+00:00
-- url     : https://prove2.me/submissions/46b6fff8-7db4-4320-adf3-25045269495e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_exists_eigenbasis
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_mk_eq_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.Unram
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne.Unram
theorem _root_.solution {x : WD h} (hx : x.unr) :
    ∃ (n : ℕ) (c : Fin n → ℂˣ), x = WD.mk (WDRep.diag h c) := by
  induction x using WD.ind with
  | hP n a =>
    obtain ⟨b, c, hc⟩ := exists_eigenbasis (a.semisimple (frob h))
    have h0 : ∀ i, c i ≠ 0 := by
      intro i hi
      have := congrArg (a.ρ (frob h)⁻¹) (hc i)
      rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply, hi, zero_smul,
        map_zero] at this
      exact b.ne_zero i this
    exact ⟨_, fun i => Units.mk0 (c i) (h0 i), mk_eq_diag ((WD.unr_mk a).mp hx) b _ hc⟩
end GlobalTheory.WeilDeligne.Unram
