-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.FixesHalf.base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:33.169654+00:00
-- url     : https://prove2.me/submissions/e509ecf6-d6c9-4a70-8212-3d95632f0b20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_fixMod_smul
import Theorems.Thm_GlobalTheory_DictPinCompare_toFin_smul
import Theorems.Thm_GlobalTheory_DictPinCompare_toFin_mem
import Theorems.Thm_GlobalTheory_DictPinCompare_smul_mem_latAd_one
import Theorems.Thm_GlobalTheory_DictPinCompare_toFin_add
import Theorems.Thm_GlobalTheory_DictPinCompare_toFin_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DictPinCompare
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)
namespace GlobalTheory.DictPinCompare
namespace FixesHalf
theorem _root_.solution {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : FixesHalf fr L0 k M Mh) {u : W} (hu : u ∈ latBase L0 (AA : Submodule (𝓞 E) E)) : ∀ b ∈ Mh,
    toFin F fr (b • u) ∈ fixMod k M (latAd F fr L0 (AA : Submodule (𝓞 E) E) 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hu
    intro b hb
    rw [← algebraMap_smul E b, smul_comm, toFin_smul, toFin_smul]
    exact fixMod_smul _ (fun y hy => smul_mem_latAd_one fr L0 AA ha hy) (h b hb _ (toFin_mem fr L0 hx))
  | zero =>
    intro b _
    rw [smul_zero, toFin_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro b hb
    rw [smul_add, toFin_add]
    exact add_mem (hx b hb) (hy b hb)
  | smul s x _ hx =>
    intro b hb
    rw [smul_smul]
    exact hx _ (Mh.mul_mem_right s hb)
end FixesHalf
end GlobalTheory.DictPinCompare
