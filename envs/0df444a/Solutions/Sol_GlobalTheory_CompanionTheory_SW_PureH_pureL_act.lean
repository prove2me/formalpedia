-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.pureL_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:09:21.851904+00:00
-- url     : https://prove2.me/submissions/ed3a3712-d073-4a04-a832-8e0d4b8065c2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_projInf_consTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_projFin_consTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_projV_consTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_consTup_mem_latV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_prod_union_split
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PureH
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [DecidableEq (HeightOneSpectrum (𝓞 F))]
variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
  (Jp : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
  (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S Sh : Finset (HeightOneSpectrum (𝓞 F)))
include b
namespace GlobalTheory.CompanionTheory.SW.PureH
theorem _root_.solution
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    {n : ℕ} (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf φ (actW (AF F) σ Jp h (consTup X)) =
      pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ Jp ginf (consTup Y)))
        (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ Jp (g v) (consTup Y))
          else (latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup Y))) X := by
  have hP : projInf (actW (AF F) σ Jp h (consTup X)) =
      actW (Ainf F) σ Jp ginf (consTup (projInf X)) := by
    rw [hinf, projInf_consTup]
  have hV : ∀ v, projV v (projFin (actW (AF F) σ Jp h (consTup X))) =
      actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) := fun v => by
    rw [hfin, projFin_consTup, projV_consTup]
  have key : ∀ v, v ∉ S → v ∉ Sh →
      (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v ↔
        projV v (projFin X) ∈ latV b v) := fun v h1 h2 =>
    (hSh v h2 _ _).trans (consTup_mem_latV b v (hS v h1) _)
  have hprod := prod_union_split S Sh
    (fun v => φ v (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))))
    (fun v => ((latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
    (fun v => v ∈ S) (fun _ => Iff.rfl)
  unfold pureL
  by_cases hX : X ∈ intOff b (S ∪ Sh)
  · rw [Set.indicator_of_mem hX, hprod]
    by_cases hA : ∀ v ∈ Sh \ S, actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v
    · have hY : actW (AF F) σ Jp h (consTup X) ∈ intOff b S := by
        intro v hv
        rw [hV]
        by_cases hvh : v ∈ Sh
        · exact hA v (Finset.mem_sdiff.2 ⟨hvh, hv⟩)
        · exact (key v hv hvh).2 (hX v (by simp [hv, hvh]))
      rw [Set.indicator_of_mem hY, hP, Finset.prod_eq_one
        (f := fun v => ((latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
        (fun v hv => by simp [Set.indicator_of_mem (hA v hv)])]
      simp only [mul_one, hV]
    · push Not at hA
      obtain ⟨v, hv, hvl⟩ := hA
      have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
        intro hm
        have := hm v (Finset.mem_sdiff.1 hv).2
        rw [hV] at this
        exact hvl this
      rw [Set.indicator_of_notMem hY, Finset.prod_eq_zero hv (by simp [Set.indicator_of_notMem hvl])]
      simp
  · have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
      intro hm
      apply hX
      intro v hv
      have hv' : v ∉ S ∧ v ∉ Sh := by simpa using hv
      have := hm v hv'.1
      rw [hV] at this
      exact (key v hv'.1 hv'.2).1 this
    rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hY]
end GlobalTheory.CompanionTheory.SW.PureH
