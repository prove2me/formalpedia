-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:18:58.141986+00:00
-- url     : https://prove2.me/submissions/b78f9a24-d762-4ab6-8565-75ec50aab198

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_v

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)
namespace GlobalTheory.CompanionTheory.SW.Glue
theorem _root_.solution (Xinf : Fin n → Fin M → Ainf F ⊗[F] E)
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E)
    (h : ∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) :
    ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v := by
  let cf : Fin n → Fin M → Fin d → Af F := fun a i k =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Xv v a i) k, h.mono fun v hv => hv a i k⟩
  let c : Fin n → Fin M → Fin d → AF F := fun a i k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Xinf a i) k) (cf a i k)
  let X : Fin n → Fin M → AF F ⊗[F] E := fun a i => (coH (AF F) b).symm (c a i)
  have hX : ∀ a i k, (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k = c a i k := fun a i k =>
    congrFun ((coH (AF F) b).apply_symm_apply (c a i)) k
  refine ⟨X, ?_, fun v => ?_⟩
  · funext a i
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    rw [crd_inf, hX]
    rfl
  · funext a i
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    rw [crd_v, hX]
    rfl
end GlobalTheory.CompanionTheory.SW.Glue
