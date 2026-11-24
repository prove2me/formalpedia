-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.act_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:58.867725+00:00
-- url     : https://prove2.me/submissions/60b6217d-15d4-4d84-b462-cafeb1c6d243

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_mem_latV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_Lv_sum
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution {M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (hm : ∀ y z : Fv F v ⊗[F] E, y ∈ Lv b v → z ∈ Lv b v → y * z ∈ Lv b v)
    (G : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (hG : ∀ i j, G i j ∈ Lv b v)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) (hX : X ∈ latV b v) :
    (fun a => G.mulVec (X a)) ∈ latV b v := by
  refine (mem_latV b v _).2 fun a i => ?_
  have e : G.mulVec (X a) i = ∑ j, G i j * X a j := by simp [Matrix.mulVec, dotProduct]
  show G.mulVec (X a) i ∈ Lv b v
  rw [e]
  exact Lv_sum b v Finset.univ (fun j => G i j * X a j) fun j _ =>
    hm _ _ (hG i j) ((mem_latV b v X).1 hX a j)
end GlobalTheory.CompanionTheory.SW.HProj
