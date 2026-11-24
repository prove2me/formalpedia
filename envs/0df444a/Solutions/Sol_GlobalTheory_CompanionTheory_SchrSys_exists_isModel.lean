-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchrSys.exists_isModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:12:33.561807+00:00
-- url     : https://prove2.me/submissions/be512dc6-9273-4429-b8a7-81a1a5dae0e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Theorems.Thm_GlobalTheory_CompanionTheory_SchrSys_pair_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_SchrSys_pair_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_law
import Theorems.Thm_GlobalTheory_CompanionTheory_SchrLaw_schr_law


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrSys
namespace GlobalTheory.CompanionTheory.SchrSys
theorem _root_.solution : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) , GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ S : Sys W (SB (κ → R)), IsModel ψ d μ S := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ hψ hμ
  have law := fun w w' φ φ' => GlobalTheory.CompanionTheory.SchrLaw.schr_law ψ O u d μ w w' φ φ' hψ hμ
  have hc : @IsFiniteMeasureOnCompacts _ (borel _) _ μ := hμ.toIsFiniteMeasureOnCompacts
  have ho : @Measure.IsOpenPosMeasure _ _ (borel _) μ := hμ.toIsOpenPosMeasure
  let rho : W → SB (κ → R) →ₗ[ℂ] SB (κ → R) := fun w =>
    { toFun := fun φ => ⟨d.rho ψ w φ, (law w 0 φ 0).2.2.1 φ.2⟩
      map_add' := fun φ φ' => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_add]
      map_smul' := fun a φ => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_left_comm] }
  refine ⟨{ c := fun w w' => ψ (⅟(2 : R) * B w w')
            rho := rho
            B := pairForm μ hc
            c_add_left := ?_
            c_add_right := ?_
            c_self := ?_
            c_norm := fun _ _ => hψ.norm_one _
            rho_zero := fun φ => Subtype.ext (law 0 0 φ 0).2.1
            rho_rho := fun w w' φ => Subtype.ext (law w w' φ 0).1
            B_conj := fun φ φ' => pair_conj μ φ φ'
            B_pos := fun φ hφ => pair_pos μ hc ho φ hφ
            B_rho := fun w φ φ' => (law w 0 φ φ').2.2.2 },
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro x x' y
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x y y'
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x
    simp [d.form]
end GlobalTheory.CompanionTheory.SchrSys
