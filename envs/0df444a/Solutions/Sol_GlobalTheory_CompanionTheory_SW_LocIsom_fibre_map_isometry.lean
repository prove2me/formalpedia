-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:43:55.256799+00:00
-- url     : https://prove2.me/submissions/907df32b-3a49-4040-8a53-e4a610458348

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsFibreFamilyTransport
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresScalingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresUniqueAeStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresChangeOfForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_gram_algebra
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_isFibreFamily_transport
import Theorems.Thm_GlobalTheory_T_gram_fiber_measures_scaling
import Theorems.Thm_GlobalTheory_T_gram_fiber_measures_unique
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_units_open_embedding_local_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocIsom
namespace GlobalTheory.CompanionTheory.SW.LocIsom
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (μ' : Measure (Fin n → Fin M → R ⊗[F] E)) m', μ'.IsAddHaarMeasure → IsGramFib R σ J' n μ' ν m' → ∀ g : GL (Fin M) (R ⊗[F] E), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ a : ℝ≥0, μ'.map (actTup R g) = a • μ → ∀ S, (m' S).map (actTup R g) = a • m S := by
  intro F E _ _ _ _ _ σ hcm M J hJ J' hJ' R _ _ _ _ _ hR n μ ν m hμ hν hm μ' m' hμ' hm' g hg a ha S
  have hR' := hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR'
  obtain ⟨hK1, hK2, hK3, hK4, -, -, -, hK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := hK8 n M
  obtain ⟨hH1, hH2, hH3, hH4, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R n
  obtain ⟨l, hlc, hl⟩ := hlift M J hJ
  obtain ⟨l', hlc', hl'⟩ := hlift M J' hJ'
  have hact : ∀ X, gramR R σ J (actTup R g X) = gramR R σ J' X :=
    (GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hcm M J hJ R n).2.2.2.2 J' g hg
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  have he : (e : (Fin n → Fin M → R ⊗[F] E) → _) = actTup R g := rfl
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hB : IsOpen B := by
    have hu := (GlobalTheory.T.units_open_embedding_local_tensor F E σ hcm R hR).isOpen_range
    have hd : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have := hu.preimage hd
    convert this using 1
    ext S
    simp [B, IsUnit]
  have hset : {X | IsUnit (gramR R σ J X).det} = l ⁻¹' B := by
    ext X
    simp [B, hl X]
  have hset' : {X | IsUnit (gramR R σ J' X).det} = l' ⁻¹' B := by
    ext X
    simp [B, hl' X]
  have hm'' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ' (gramR R σ J') Subtype.val (l' ⁻¹' B) ν B m' := by
    have := hm'
    unfold IsGramFib at this
    rw [hset'] at this
    exact this
  have hcompat : ∀ X, l (e X) = (Homeomorph.refl _) (l' X) := by
    intro X
    apply Subtype.ext
    show ((l (e X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (l' X : HermR R σ n)
    rw [← hl, ← hl']
    exact hact X
  have hT := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ' ν (gramR R σ J') l' Subtype.val
    Subtype.val_injective hlc' hl' _ (gramR R σ J) l hlc hl e (Homeomorph.refl _) hcompat B hB m' hm''
  have himg : (Homeomorph.refl (HermR R σ n)) '' B = B := by simp
  have hνm : ν.map (Homeomorph.refl (HermR R σ n)) = ν := by
    simp
  rw [himg, hνm, he, ha, ← hset] at hT
  have hfib : IsGramFib R σ J n (a • μ) ν (fun S => (m' S).map (actTup R g)) := hT
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    have h0 : μ' ≠ 0 := by
      intro h
      have := isOpen_univ.measure_pos μ' Set.univ_nonempty
      simp [h] at this
    apply h0
    rw [← he] at ha
    have := congrArg (fun ρ : Measure _ => ρ Set.univ) ha
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rw [Measure.map_apply e.continuous.measurable MeasurableSet.univ] at this
    simpa using this
  have hHaar : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  have h1 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hcm M J hJ R hR n μ ν m hμ hν hm a 1 ha0 one_ne_zero
  rw [one_smul] at h1
  simp only [div_one] at h1
  exact GlobalTheory.T.gram_fiber_measures_unique F E σ hcm M J hJ R hR n (a • μ) ν _ hHaar hν hfib _ h1 S
end GlobalTheory.CompanionTheory.SW.LocIsom
