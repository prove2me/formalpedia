-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreRatio.coordHerm_qS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:47.543667+00:00
-- url     : https://prove2.me/submissions/58073cb7-1ba7-406f-8860-0bf1c7831caa

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_qS_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_hermScal_qS
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_continuous_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_continuous_qS
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreRatio
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [Field R] [Algebra F R] [TopologicalSpace R]
variable [MeasurableSpace R] [BorelSpace R]
namespace GlobalTheory.CompanionTheory.SW.FibreRatio
theorem _root_.solution (h : IsCMExt F E σ) [IsTopologicalRing R] [SecondCountableTopology R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) [SigmaFinite lam] {V : Set R}
    (hV : MeasurableSet V) : coordHerm R σ b lam 1 {S | qS R σ S ∈ V} = lam V := by
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
  have hgf : ∀ S, g (f S) = S := fun S => hermScal_qS R h S
  have hfg : ∀ x, f (g x) = x := by
    intro x
    refine Prod.ext ?_ (funext fun p => isEmptyElim p)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact qS_hermScal R h (x.1 0)
  have himg : ∀ s : Set (HermR R σ 1), f '' s = g ⁻¹' s := by
    intro s
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      simpa [hgf S] using hS
    · intro hx
      exact ⟨g x, hx, hfg x⟩
  have hinj : Function.Injective f := Function.LeftInverse.injective hgf
  have hP : MeasurableSet {S | qS R σ S ∈ V} := (continuous_qS R htr).measurable hV
  have hset : f '' {S | qS R σ S ∈ V} = (Set.pi Set.univ fun _ : Fin 1 => V) ×ˢ Set.univ := by
    rw [himg]
    ext x
    have e : qS R σ (g x) = x.1 0 := qS_hermScal R h (x.1 0)
    simp [e]
  show Measure.comap f _ _ = _
  rw [Measure.comap_apply f hinj (fun s hs => by rw [himg]; exact hgm hs) _ hP, hset,
    Measure.pi_of_empty (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam),
    Measure.prod_prod, Measure.pi_pi]
  simp
end GlobalTheory.CompanionTheory.SW.FibreRatio
