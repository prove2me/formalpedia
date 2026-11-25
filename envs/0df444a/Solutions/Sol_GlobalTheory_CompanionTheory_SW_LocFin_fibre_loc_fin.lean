-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:25:59.925852+00:00
-- url     : https://prove2.me/submissions/c96bfd0f-a2f0-46af-8317-c482a1e58e43

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianLocalContinuousCongruenceSectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFin_null_of_fibres_null
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_fibre_family_basic
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_gram_algebra
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_T_gram_fiber_measures_gl_equivariant
import Theorems.Thm_GlobalTheory_T_hermitian_local_continuous_congruence_section
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_units_open_embedding_local_tensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocFin
namespace GlobalTheory.CompanionTheory.SW.LocFin
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ S : HermR R σ n, IsLocallyFiniteMeasure (m S) ∧ ∀ U : Set (Fin n → Fin M → R ⊗[F] E), IsOpen U → (∃ X ∈ U, gramR R σ J X = S ∧ IsUnit (gramR R σ J X).det) → m S U ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm S
  haveI : IsTopologicalRing R := hR.1
  haveI : LocallyCompactSpace R := hR.2.1
  haveI : SecondCountableTopology R := hR.2.2.1
  haveI : T2Space R := hR.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  obtain ⟨h1, h2, h3, h4, h5⟩ := HermTop.herm_top F E σ hσ R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g, hgc, hg⟩ := h5 M J hJ
  have hKU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hKU.isOpen_range.preimage hdet
  have hUeq : {X | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hg]
  have hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hUeq]
    exact hm
  obtain ⟨hloc, -, -, -⟩ := FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hgc hg _ hBo m hfib
  refine ⟨hloc S, ?_⟩
  rintro U hU ⟨X₀, hX₀U, hX₀S, hX₀⟩ h0
  obtain ⟨κ, -, -, -, hκ⟩ := GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hσ M J hJ R hR n μ ν m hμ hν hm
  have hSdet : IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    rw [← hX₀S]
    exact hX₀
  obtain ⟨B₁, gs, hB₁, hSB₁, hgs, hgs1, hgsS⟩ := GlobalTheory.T.hermitian_local_continuous_congruence_section F E σ hσ R hR n S hSdet
  obtain ⟨a1, a2, a3, -, -⟩ := GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hgX₀ : g X₀ = S := Subtype.ext ((hg X₀).symm.trans hX₀S)
  have hr : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × Matrix (Fin n) (Fin n) (R ⊗[F] E) =>
      rmul R p.1 p.2 := by
    unfold rmul
    refine continuous_pi fun a => continuous_pi fun i => continuous_finset_sum _ fun c _ => ?_
    exact ((continuous_apply_apply c i).comp continuous_fst).mul (continuous_snd.matrix_elem c a)
  let T : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun X =>
    rmul R X (((gs (g X))⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hTc : ContinuousOn T (g ⁻¹' B₁) := by
    refine hr.comp_continuousOn (ContinuousOn.prodMk continuousOn_id ?_)
    exact Units.continuous_val.comp_continuousOn
      ((hgs.comp hgc.continuousOn fun X hX => hX).inv)
  have hU'o : IsOpen (g ⁻¹' B₁ ∩ T ⁻¹' U) := hTc.isOpen_inter_preimage (hB₁.preimage hgc) hU
  have hnull : ∀ S' : HermR R σ n, m S' (g ⁻¹' B₁ ∩ T ⁻¹' U) = 0 := by
    intro S'
    by_cases hS' : S' ∈ B₁
    · have e := hκ (gs S') S S' (hgsS S' hS')
      have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
        (hr.comp (Continuous.prodMk continuous_id continuous_const)).measurable
      rw [e, Measure.smul_apply, Measure.map_apply hmeas hU'o.measurableSet]
      have hsub : (fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U) ⊆
          U ∪ (gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det})ᶜ := by
        intro X hX
        by_cases hXf : X ∈ gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det}
        · left
          have hXS : gramR R σ J X = S := hXf.1
          have hgr : g (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = S' := by
            apply Subtype.ext
            rw [← hg, a1, hXS, ← hgsS S' hS']
          have hT : T (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = X := by
            simp only [T]
            rw [hgr, a2, Units.mul_inv, a3]
          have := hX.2
          simp only [Set.mem_preimage] at this
          rwa [hT] at this
        · exact Or.inr hXf
      have hz : m S ((fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U)) = 0 :=
        measure_mono_null hsub (measure_union_null h0 (hm.1 S))
      rw [hz, smul_zero]
    · refine measure_mono_null ?_ (hm.1 S')
      intro X hX hXf
      have hgX : g X = S' := Subtype.ext ((hg X).symm.trans hXf.1)
      exact hS' (hgX ▸ hX.1)
  have hμ0 := null_of_fibres_null hm hU'o.measurableSet hnull
  have hO : IsOpen ((g ⁻¹' B₁ ∩ T ⁻¹' U) ∩ {X | IsUnit (gramR R σ J X).det}) := by
    rw [hUeq]
    exact hU'o.inter (hBo.preimage hgc)
  refine hO.measure_ne_zero μ ⟨X₀, ⟨?_, ?_⟩, hX₀⟩ hμ0
  · show g X₀ ∈ B₁
    rw [hgX₀]
    exact hSB₁
  · show T X₀ ∈ U
    simp only [T]
    rw [hgX₀, hgs1, inv_one, Units.val_one, a3]
    exact hX₀U
end GlobalTheory.CompanionTheory.SW.LocFin
