-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.mem_of_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:22:07.710106+00:00
-- url     : https://prove2.me/submissions/9756ade8-fff3-4b1b-aa82-0e3208b3f4f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff

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
theorem _root_.solution {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E)}
    {z : Fin n → Fin𝔸 F ⊗[F] E} (h : ∀ a ∈ I, ∀ b ∈ I⁻¹, ad F (a * b) • z ∈ P) : z ∈ P := by
  have key : ∀ c ∈ I * I⁻¹, ad F c • z ∈ P := fun c hc =>
    FractionalIdeal.mul_induction_on hc h fun x y hx hy => by
      rw [ad, TensorProduct.tmul_add, add_smul]; exact add_mem hx hy
  have := key 1 (by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _)
  rwa [ad, ← Algebra.TensorProduct.one_def, one_smul] at this
end GlobalTheory.DictPinCompare
