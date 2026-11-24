-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.FixesHalf.mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:20.168533+00:00
-- url     : https://prove2.me/submissions/20b2afa9-bac8-48a8-9cb8-968067008664

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_ad_mul
import Theorems.Thm_GlobalTheory_DictPinCompare_mem_of_mul_inv
import Theorems.Thm_GlobalTheory_DictPinCompare_mul_inv_smul_mem

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
    (h : FixesHalf fr L0 k M Mh) (hM : (M : 𝓞 E) ∈ Mh) (hM0 : M ≠ 0) :
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  have hI : (Mh : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => hM0 (by rw [h0, Ideal.mem_bot] at hM; exact_mod_cast hM)
  intro z hz
  refine mem_of_mul_inv hI fun a ha b hb => ?_
  obtain ⟨a', ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  obtain ⟨y, hy, e⟩ := h a' ha' z hz
  have eM : ad F (algebraMap (𝓞 E) E (M : 𝓞 E)) = (M : Fin𝔸 F ⊗[F] E) := by
    rw [map_natCast]
    exact map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] Fin𝔸 F ⊗[F] E) M
  have e' : ad F (algebraMap (𝓞 E) E a' * b) • k *ᵥ z =
      ad F (algebraMap (𝓞 E) E a' * b) • z + ad F (algebraMap (𝓞 E) E (M : 𝓞 E) * b) • y := by
    rw [Matrix.mulVec_smul, sub_eq_iff_eq_add'] at e
    rw [mul_comm _ b, mul_comm _ b, ad_mul, ad_mul, mul_smul, mul_smul, mul_smul, ← smul_add, e, eM,
      Nat.cast_smul_eq_nsmul]
  rw [e']
  exact add_mem (mul_inv_smul_mem fr L0 hI ha hb hz)
    (mul_inv_smul_mem fr L0 hI (FractionalIdeal.mem_coeIdeal_of_mem _ hM) hb hy)
end FixesHalf
end GlobalTheory.DictPinCompare
