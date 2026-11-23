-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:59:43.294637+00:00
-- url     : https://prove2.me/submissions/bd89f098-ee69-4f48-9273-a6214eb1365f

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_finite_endpoint
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_cadlag_clock
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_integrability
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_set_integral_mono
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_height_law_normalized
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
private lemma tps {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x d : ℝ) (ω : Ω) :
    tauPlus (shifted X x) (x + d) ω = tauPlus X d ω := by
  unfold tauPlus shifted ; congr 1
  ext t ; constructor <;> rintro ⟨u, hu0, hut, hlt⟩ <;> exact ⟨u, hu0, hut, by simpa using hlt⟩
private lemma tms {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x : ℝ) (ω : Ω) :
    tauMinus (shifted X x) 0 ω = tauMinus X (-x) ω := by
  unfold tauMinus shifted ; congr 1
  ext t ; constructor <;> rintro ⟨u, hu0, hut, hlt⟩ <;> exact ⟨u, hu0, hut, by linarith⟩
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ) (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      Real.exp (-(d * (Phi ψ q + (n (Set.Ici l)).toReal))) ≤
        upBeforeDownExpectation P D.X q l (l + d) := by
  intro l d hl hd
  let U : Ω → ℝ≥0∞ := fun ω => tauPlus D.X d ω
  let V : Ω → ℝ≥0∞ := fun ω => tauMinus D.X (-l) ω
  have hAE : ∀ᵐ ω ∂P, NoDrawdownBeforeUpcrossing D.X d l ω → U ω = ⊤ ∨ U ω < V ω := by
    filter_upwards [D.levy.cadlag_ae] with ω hcad
    intro hND
    by_cases ht : U ω = ⊤
    · exact Or.inl ht
    · right
      dsimp [U, V] at ht ⊢
      exact Kyprianou.Ch08.StageB.scale_slice_lower_hy4_cadlag_clock D hl hd hcad hND ht
  have hU : AEMeasurable U P := by
    have heq : U = fun ω => (tauPlus (shifted D.X l) (l + d) ω : ℝ≥0∞) :=
      funext fun ω => (tps D.X l d ω).symm
    rw [heq]
    exact (Kyprianou.Ch08.StageB.source_result81_strict_exit_clocks_aemeasurable Ω P D l (l + d)).1
  have hV : AEMeasurable V P := by
    have heq : V = fun ω => (tauMinus (shifted D.X l) 0 ω : ℝ≥0∞) :=
      funext fun ω => (tms D.X l ω).symm
    rw [heq]
    exact (Kyprianou.Ch08.StageB.source_result81_strict_exit_clocks_aemeasurable Ω P D l 0).2
  have hp := Kyprianou.Ch08.StageB.scale_slice_lower_hy4_integrability P U V hU hV q hq
  have hsub : {ω | NoDrawdownBeforeUpcrossing D.X d l ω} ≤ᵐ[P]
      {ω | U ω < V ω ∨ U ω = ⊤} := by
    filter_upwards [hAE] with ω hω hND
    rcases hω hND with ht | hlt
    · exact Or.inr ht
    · exact Or.inl hlt
  have hcmp := Kyprianou.Ch08.StageB.scale_slice_lower_hy4_set_integral_mono P U V hU hV q hp.1 hp.2
    {ω | NoDrawdownBeforeUpcrossing D.X d l ω} hsub
  unfold upBeforeDownExpectation
  simp only [tps, tms]
  change Real.exp (-(d * (Phi ψ q + (n (Set.Ici l)).toReal))) ≤
    ∫ ω, (if U ω < V ω then discountedAt q (U ω) else 0) ∂P
  have hN := Kyprianou.Ch08.StageB.scale_slice_lower_hy4_height_law_normalized P D ψ hψ q n hLaw l d hl hd
  rw [← hN]
  exact hcmp
