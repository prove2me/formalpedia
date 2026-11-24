-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.mul_inv_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:43:01.8785+00:00
-- url     : https://prove2.me/submissions/eb93354a-b896-4695-a14c-4587a7457a09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latHat_eq_hat

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
theorem _root_.solution {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹)
    {z : Fin n → Fin𝔸 F ⊗[F] E} (hz : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) :
    ad F (a * b) • z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  have hab : a * b ∈ I * I⁻¹ := FractionalIdeal.mul_mem_mul ha hb
  rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hab
  obtain ⟨s, hs⟩ := hab
  rw [latHat_eq_hat] at hz ⊢
  rw [← hs]
  exact GlobalTheory.AdLat.Translate.hat_smul_ring _ s hz
end GlobalTheory.DictPinCompare
