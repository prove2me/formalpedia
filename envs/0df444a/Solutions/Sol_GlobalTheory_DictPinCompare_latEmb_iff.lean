-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.latEmb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:41.7372+00:00
-- url     : https://prove2.me/submissions/1ce91a0c-362c-493c-a981-b29818f6042d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latG_eq
import Theorems.Thm_GlobalTheory_DictPinCompare_latG_one
import Theorems.Thm_GlobalTheory_DictPinCompare_trace_flip
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



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
theorem _root_.solution {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hherm : ∀ x y, cc (hT x y) = hT y x) (hxi : cc xi0 = -xi0)
    (ι : Dw.La →ₗ[𝓞 E] W) :
    (LatEmb F fr L0 AA finHom ((coord fr).toLinearMap ∘ₗ ι) ∧ LatIsom fr hT xi0 Dw.EF ((coord fr).toLinearMap ∘ₗ ι)) ↔
      IsLatEmb (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 Dw ι := by
  unfold LatEmb LatIsom IsLatEmb
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact (coord fr).injective.of_comp_iff ι
  · rw [latG_eq, map_one, latG_one fr L0 hfg hsp, LinearMap.range_comp]
    exact (Submodule.map_injective_of_injective (coord fr).injective).eq_iff
  · have e : ∀ x, fr.equivFun.symm (((coord fr).toLinearMap ∘ₗ ι) x) = ι x := fun x => fr.equivFun.symm_apply_apply _
    simp only [e, trace_flip hT xi0 hherm hxi]
    constructor <;> rintro ⟨ε, h⟩ <;> refine ⟨-ε, fun x y => ?_⟩ <;> rw [h] <;> simp
end GlobalTheory.DictPinCompare
