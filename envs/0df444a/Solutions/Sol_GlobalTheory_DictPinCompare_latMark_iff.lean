-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.latMark_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:25:58.84805+00:00
-- url     : https://prove2.me/submissions/c767486a-93de-49ec-b5b8-68d95652d11e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_finVec_coord
import Theorems.Thm_GlobalTheory_DictPinCompare_latGHat_eq
import Theorems.Thm_GlobalTheory_DictPinCompare_mem_latG_iff

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
theorem _root_.solution {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hr : n = r)
    (ι : Dw.La →ₗ[𝓞 E] W) (X : Data E r) (mk : Dw.La → X.Λ) (g : G) :
    (((X.Λ : Set (Fin r → E)) =
        (fun v : Fin n → E => v ∘ Fin.cast hr.symm) '' (latG F fr L0 AA finHom g : Set _)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ latGHat F fr L0 AA finHom g,
        finVec F ((mk a : Fin r → E) ∘ Fin.cast hr) -
          (finHom g).1.mulVec (finVec F (((coord fr).toLinearMap ∘ₗ ι) a)) = (l.M : ℕ) • w) ↔
      LatMark F hr fr L0 (AA : Submodule (𝓞 E) E) l ι X mk (finHom g) := by
  subst hr
  refine and_congr ?_ (forall₂_congr fun a _ => ?_)
  · have e : (fun v : Fin n → E => v ∘ Fin.cast (rfl : n = n).symm) = id := rfl
    rw [e, Set.image_id, SetLike.coe_set_eq, SetLike.ext_iff, (coord fr).surjective.forall]
    exact forall_congr' fun v => iff_congr Iff.rfl (mem_latG_iff fr L0 AA finHom g v)
  · have e : toFin F fr (vec rfl fr (mk a : Fin n → E)) = finVec F ((mk a : Fin n → E) ∘ Fin.cast rfl) := by
      have : vec rfl fr (mk a : Fin n → E) = fr.equivFun.symm (mk a : Fin n → E) := (fr.equivFun_symm_apply _).symm
      rw [this, ← finVec_coord]
      exact congrArg _ (fr.equivFun.apply_symm_apply _)
    unfold CongrAt
    rw [e, latGHat_eq]
    rfl
end GlobalTheory.DictPinCompare
