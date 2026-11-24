-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.level_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:42.6358+00:00
-- url     : https://prove2.me/submissions/7d6a09cb-cb20-4e84-a4db-84c157c93ec3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_level_elem_iff
import Theorems.Thm_GlobalTheory_DictPinCompare_det_of_unitary

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
theorem _root_.solution {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0) (hnd : (gramOf fr hT).det ≠ 0) (cj : E ≃ₐ[F] E)
    (hU : ∀ g, finHom g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F)) (hGf : ∀ k, k ∈ GfC ↔ infHom k = 1)
    (ι : Dw.La →ₗ[𝓞 E] W) (hι : LinearMap.range ι = latBase L0 (AA : Submodule (𝓞 E) E)) (Kf : Subgroup G) :
    KfHalf F fr L0 finHom GfC Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔
      IsLevelStab F fr L0 (AA : Submodule (𝓞 E) E) l ι infHom finHom Kf := by
  refine forall_congr' fun k => iff_congr Iff.rfl (and_congr (hGf k) ?_)
  exact level_elem_iff fr L0 AA l hfg hsp hA ι hι cj _ (det_of_unitary fr hT cj hnd _ (hU k))
end GlobalTheory.DictPinCompare
