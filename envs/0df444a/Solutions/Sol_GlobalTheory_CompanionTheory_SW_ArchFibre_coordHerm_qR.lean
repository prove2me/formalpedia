-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArchFibre.coordHerm_qR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:34.046844+00:00
-- url     : https://prove2.me/submissions/049869e1-96f0-41e6-b954-b8bf9d02f8f2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_qR_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_hermScal_qR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_continuous_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_continuous_qR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArchFibre
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
variable [MeasurableSpace R] [BorelSpace R]
namespace GlobalTheory.CompanionTheory.SW.ArchFibre
theorem _root_.solution (h : IsCMExt F E σ) [IsTopologicalRing R] [SecondCountableTopology R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) [SigmaFinite lam] {V : Set R}
    (hV : MeasurableSet V) : coordHerm R σ b lam 1 {S | qR R σ S ∈ V} = lam V := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  haveI : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
    ⟨fun p => by
      have h1 := p.2
      have h2 : p.1.1 = p.1.2 := Subsingleton.elim _ _
      rw [h2] at h1
      exact lt_irrefl _ h1⟩
  set f : HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
    with hf
  set g : (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) → HermR R σ 1 :=
    fun x => hermScal R σ (x.1 0) with hg
  have hgm : Measurable g :=
    (continuous_hermScal R).measurable.comp ((measurable_pi_apply 0).comp measurable_fst)
  have hgf : ∀ S, g (f S) = S := fun S => hermScal_qR R h S
  have hfg : ∀ x, f (g x) = x := by
    intro x
    refine Prod.ext ?_ (funext fun p => isEmptyElim p)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact qR_hermScal R h (x.1 0)
  have himg : ∀ s : Set (HermR R σ 1), f '' s = g ⁻¹' s := by
    intro s
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      simpa [hgf S] using hS
    · intro hx
      exact ⟨g x, hx, hfg x⟩
  have hinj : Function.Injective f := Function.LeftInverse.injective hgf
  have hP : MeasurableSet {S | qR R σ S ∈ V} := (continuous_qR R htr).measurable hV
  have hset : f '' {S | qR R σ S ∈ V} = (Set.pi Set.univ fun _ : Fin 1 => V) ×ˢ Set.univ := by
    rw [himg]
    ext x
    have e : qR R σ (g x) = x.1 0 := qR_hermScal R h (x.1 0)
    simp [e]
  show Measure.comap f _ _ = _
  rw [Measure.comap_apply f hinj (fun s hs => by rw [himg]; exact hgm hs) _ hP, hset,
    Measure.pi_of_empty (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam),
    Measure.prod_prod, Measure.pi_pi]
  simp
end GlobalTheory.CompanionTheory.SW.ArchFibre
