-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.latG_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:26:59.242287+00:00
-- url     : https://prove2.me/submissions/05c0e09f-e89e-4356-a8a7-78d3a00cfcba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latHat_eq_hat
import Theorems.Thm_GlobalTheory_DictPinCompare_span_coord
import Theorems.Thm_GlobalTheory_AdLat_hat_rational_points_and_approx
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdelicLatticeBase_latBase_le_latG_one


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
theorem _root_.solution (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (𝔄 : Submodule (𝓞 E) E) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 𝔄 1 = latBase L0 𝔄 := by
  refine le_antisymm (Submodule.span_mono ?_) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latBase_le_latG_one F fr L0 𝔄)
  rintro _ ⟨a, ha, x, ⟨z, hz, hx⟩, rfl⟩
  refine ⟨a, ha, x, ?_, rfl⟩
  rw [Units.val_one, Matrix.one_mulVec] at hx
  rw [← hx, latHat_eq_hat] at hz
  obtain ⟨y, hy, h⟩ := ((GlobalTheory.AdLat.hat_rational_points_and_approx F E n _ (hfg.map _) (span_coord fr L0 hsp)).1
    (coord fr x)).1 hz
  rwa [← (coord fr).injective h]
end GlobalTheory.DictPinCompare
