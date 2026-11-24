-- Prove2me | solution 1 for GlobalTheory.CotUniv.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:07.001663+00:00
-- url     : https://prove2.me/submissions/80c67071-d53b-4675-9956-963f693cad0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
import Theorems.Thm_GlobalTheory_CotUniv_lhom_ext
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_fst
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_snd



set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O A : LAlg R₀} {p g : ℕ}
  {sO : LHom O A} {ε : LHom A O} {y : B.G A} {w : Fin g → B.gg}
variable {M : Type} [AddCommGroup M] [Module (O : Type) M]
namespace GlobalTheory.CotUniv
theorem _root_.solution (hε : ε.comp sO = LHom.id O) (d : (A : Type) →+ M)
    (h1 : ∀ o f, d (sO.1 o * f) = o • d f)
    (h2 : ∀ f f', d (f * f') = ε.1 f • d f' + ε.1 f' • d f) :
    ∃ φ : LHom A (sqAlg O M), φ.comp sO = sqIncl O M ∧ (sqProj O M).comp φ = ε ∧
      ∀ f, SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) = d f := by
  have d1 : d 1 = 0 := by
    have h := h2 1 1
    simp only [mul_one, map_one, one_smul] at h
    simpa using h
  have dO : ∀ o, d (sO.1 o) = 0 := fun o => by
    have h := h1 o 1
    rwa [mul_one, d1, smul_zero] at h
  refine ⟨sqLift ε d h2 (fun r => by rw [← sO.1.commutes, dO]), lhom_ext fun o => ?_,
    lhom_ext fun _ => rfl, fun _ => rfl⟩
  exact SqExt.ext (O := (O : Type)) (M := M) (congrArg (fun ψ => ψ.1 o) hε) (dO o)
end GlobalTheory.CotUniv
