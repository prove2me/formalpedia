-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.latG_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:41:09.276806+00:00
-- url     : https://prove2.me/submissions/c924655f-54d4-4087-b046-b442101cefc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_coord_smul

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
theorem _root_.solution (g : G) : latG F fr L0 AA finHom g =
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 (AA : Submodule (𝓞 E) E) (finHom g)).map (coord fr).toLinearMap := by
  unfold latG GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, v, ⟨z, hz, hv⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (coord fr).surjective v
    exact ⟨a • x, ⟨a, ha, x, ⟨z, hz, hv.symm⟩, rfl⟩, coord_smul fr a x⟩
  · rintro ⟨_, ⟨a, ha, x, ⟨z, hz, hv⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, coord fr x, ⟨z, hz, hv.symm⟩, coord_smul fr a x⟩
end GlobalTheory.DictPinCompare
