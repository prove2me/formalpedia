-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.HermOne.map_coordHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:14.282796+00:00
-- url     : https://prove2.me/submissions/0d02f67a-6d3e-4ae7-88b2-25dc221f767e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianRankOneHomeomorphBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.HermOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R] [IsTopologicalRing R]
variable [MeasurableSpace R] [BorelSpace R]
namespace GlobalTheory.CompanionTheory.SW.BB.HermOne
theorem _root_.solution (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    [SigmaFinite lam] : (coordHerm R σ b lam 1).map (hermHomeo R hcm) = lam := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  haveI hT : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
    ⟨fun p => by
      have h := p.2
      rw [Subsingleton.elim p.1.1 p.1.2] at h
      exact lt_irrefl _ h⟩
  let ψ : R → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun r => (fun _ => r, fun p => hT.elim p)
  have hψ : MeasurableEmbedding ψ := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun q => q.1 0) ?_ ?_ ?_ ?_
    · refine Measurable.prodMk (measurable_pi_lambda _ fun _ => measurable_id) ?_
      exact measurable_pi_lambda _ fun p => hT.elim p
    · have : Set.range ψ = Set.univ := by
        ext q
        simp only [Set.mem_range, Set.mem_univ, iff_true]
        refine ⟨q.1 0, Prod.ext ?_ (Subsingleton.elim _ _)⟩
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rfl
      rw [this]
      exact MeasurableSet.univ
    · exact (measurable_pi_apply 0).comp measurable_fst
    · intro r
      rfl
  ext s hs
  have hfun : (fun S : HermR R σ 1 =>
      ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} =>
          (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))) = ψ ∘ hermHomeo R hcm := by
    funext S
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  have hemb : MeasurableEmbedding (ψ ∘ hermHomeo R hcm) :=
    hψ.comp (hermHomeo R hcm).measurableEmbedding
  have hpi : Measure.pi (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam) =
      Measure.dirac (fun p => hT.elim p) := Measure.pi_of_empty _ _
  have himg : (ψ ∘ hermHomeo R hcm) '' (hermHomeo R hcm ⁻¹' s) =
      ((fun a : Fin 1 → R => a 0) ⁻¹' s) ×ˢ Set.univ := by
    ext q
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨hS, Set.mem_univ _⟩
    · rintro ⟨hq, -⟩
      refine ⟨(hermHomeo R hcm).symm (q.1 0), ?_, ?_⟩
      · simpa using hq
      · refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp [ψ]
  rw [Measure.map_apply (hermHomeo R hcm).measurable hs, coordHerm, hfun, hemb.comap_apply, hpi, himg,
    Measure.prod_prod, measure_univ, mul_one]
  exact (measurePreserving_funUnique lam (Fin 1)).measure_preimage hs.nullMeasurableSet
end GlobalTheory.CompanionTheory.SW.BB.HermOne
