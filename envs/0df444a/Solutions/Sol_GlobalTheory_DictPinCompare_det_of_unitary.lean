-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.det_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:02:27.897683+00:00
-- url     : https://prove2.me/submissions/03e55fd8-fb93-4eda-8c99-75a87eba240f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_mem_unitaryOver_iff

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
theorem _root_.solution (cj : E ≃ₐ[F] E) (hnd : (gramOf fr hT).det ≠ 0) (A : Type) [CommRing A] [Algebra F A]
    {g : GL (Fin n) (A ⊗[F] E)} (hg : g ∈ unitaryOver F cj fr (flipForm hT) A) :
    g.1.det * GlobalTheory.AdLat.sg A cj g.1.det = 1 := by
  have h := congrArg Matrix.det ((mem_unitaryOver_iff fr cj _ A g).1 hg)
  have hB : (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)) =
      (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom.mapMatrix (gramOf fr hT)ᵀ := rfl
  have hu : IsUnit (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)).det := by
    rw [hB, ← RingHom.map_det, Matrix.det_transpose]
    exact (IsUnit.mk0 _ hnd).map _
  have hs : (g.1.map (GlobalTheory.AdLat.sg A cj)).det = GlobalTheory.AdLat.sg A cj g.1.det :=
    (RingHom.map_det (GlobalTheory.AdLat.sg A cj).toRingHom g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs] at h
  refine hu.mul_left_cancel ?_
  rw [mul_one]
  linear_combination h
end GlobalTheory.DictPinCompare
