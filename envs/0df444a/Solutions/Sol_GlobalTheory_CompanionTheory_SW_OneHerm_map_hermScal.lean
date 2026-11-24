-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.OneHerm.map_hermScal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:29.234133+00:00
-- url     : https://prove2.me/submissions/3b0208e5-079d-4d60-a04c-4ca7d2fc22ae

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.OneHerm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
namespace GlobalTheory.CompanionTheory.SW.OneHerm
theorem _root_.solution {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] :
    lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  let P := {p : Fin 1 × Fin 1 // p.1 < p.2}
  let x₀ : P → R ⊗[F] E := isEmptyElim
  let ψ : HermR R σ 1 → (Fin 1 → R) × (P → R ⊗[F] E) := fun S =>
      ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : P => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
  let e : R → (Fin 1 → R) × (P → R ⊗[F] E) := fun s => (fun _ => s, x₀)
  have hHs : MeasurableEmbedding (hermScal R σ) := (hermHomeo R hσ).measurableEmbedding
  have hψe : ∀ S, ψ S = e (hermHalf R σ S) := by
    intro S
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl
  have hemb : MeasurableEmbedding e := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun y => y.1 0) ?_ ?_ ?_ ?_
    · exact (measurable_pi_lambda _ fun _ => measurable_id).prodMk measurable_const
    · have : Set.range e = Set.univ := by
        refine Set.eq_univ_of_forall fun y => ⟨y.1 0, ?_⟩
        refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rfl
      rw [this]
      exact MeasurableSet.univ
    · exact (measurable_pi_apply 0).comp measurable_fst
    · intro s
      rfl
  have hψ : MeasurableEmbedding ψ := by
    have : ψ = e ∘ (hermHomeo R hσ).symm := funext hψe
    rw [this]
    exact hemb.comp (hermHomeo R hσ).symm.measurableEmbedding
  have hprod : (Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : P => coordK R b lam) =
      lam.map e := by
    rw [Measure.pi_of_empty _ x₀, Measure.prod_dirac]
    have h1 : (Measure.pi fun _ : Fin 1 => lam) = lam.map (fun s _ => s) :=
      ((measurePreserving_funUnique lam (Fin 1)).symm (MeasurableEquiv.funUnique (Fin 1) R)).map_eq.symm
    have hm1 : Measurable fun (s : R) (_ : Fin 1) => s := measurable_pi_lambda _ fun _ => measurable_id
    have hm2 : Measurable fun y : Fin 1 → R => (y, x₀) := measurable_id.prodMk measurable_const
    rw [h1, Measure.map_map hm2 hm1]
    rfl
  have hcomp : e = ψ ∘ hermScal R σ := by
    funext s
    rw [Function.comp, hψe, hermHalf_hermScal R hσ]
  have hmap : lam.map e = (lam.map (hermScal R σ)).map ψ := by
    rw [Measure.map_map hψ.measurable hHs.measurable, hcomp]
  change _ = Measure.comap ψ _
  rw [hprod, hmap, hψ.comap_map]
end GlobalTheory.CompanionTheory.SW.OneHerm
