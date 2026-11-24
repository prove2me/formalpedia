-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.latAd_eq_of_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:40:44.089741+00:00
-- url     : https://prove2.me/submissions/aa41eb45-ebeb-4d87-b62c-27119fed2c7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_smul_mem_latAd_one

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
omit [IsCMField E]
namespace GlobalTheory.DictPinCompare
theorem _root_.solution {k : GL (Fin n) (Fin𝔸 F ⊗[F] E)}
    (h1 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0)
    (h2 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k⁻¹.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) :
    latAd F fr L0 (AA : Submodule (𝓞 E) E) k = latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 := by
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
  · rintro _ ⟨a, ha, z, hz, rfl⟩
    exact smul_mem_latAd_one fr L0 AA ha (h1 z hz)
  · rintro _ ⟨a, ha, z, hz, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, _, h2 z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
end GlobalTheory.DictPinCompare
