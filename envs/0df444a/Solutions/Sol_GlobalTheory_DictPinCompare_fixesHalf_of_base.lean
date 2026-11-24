-- Prove2me | solution 1 for GlobalTheory.DictPinCompare.fixesHalf_of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:08.681557+00:00
-- url     : https://prove2.me/submissions/699e54ab-5b81-4cd2-84ca-de5a355812ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
import Theorems.Thm_GlobalTheory_DictPinCompare_latHat_eq_hat
import Theorems.Thm_GlobalTheory_DictPinCompare_fixMod_smul
import Theorems.Thm_GlobalTheory_DictPinCompare_ad_mul
import Theorems.Thm_GlobalTheory_DictPinCompare_mem_of_mul_inv
import Theorems.Thm_GlobalTheory_DictPinCompare_toFin_smul
import Theorems.Thm_GlobalTheory_DictPinCompare_inv_smul_mem_latHat
import Theorems.Thm_GlobalTheory_AdLat_Translate_gen_eq
import Theorems.Thm_GlobalTheory_AdLat_Translate_hat_smul_int


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
theorem _root_.solution (hA : AA ≠ 0) {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : ∀ u ∈ latBase L0 (AA : Submodule (𝓞 E) E), ∀ b ∈ Mh,
      toFin F fr (b • u) ∈ fixMod k M (latAd F fr L0 (AA : Submodule (𝓞 E) E) 1)) : FixesHalf fr L0 k M Mh := by
  intro b hb z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨t, ht, x, hx, rfl⟩ := hz
    have e : (fun i => t ⊗ₜ[F] fr.repr x i) = (t ⊗ₜ[F] (1 : E) : Fin𝔸 F ⊗[F] E) • toFin F fr x :=
      GlobalTheory.AdLat.Translate.gen_eq t (coord fr x)
    rw [e, smul_comm]
    refine fixMod_smul (P := GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) _ (fun y hy => ?_)
      (mem_of_mul_inv hA fun a ha a' ha' => ?_)
    · rw [latHat_eq_hat] at hy ⊢
      exact GlobalTheory.AdLat.Translate.hat_smul_int ht hy
    · have h5 := h (a • x) (Submodule.subset_span ⟨a, ha, x, hx, rfl⟩) b hb
      rw [← algebraMap_smul E b, smul_comm, toFin_smul, toFin_smul] at h5
      rw [mul_comm, ad_mul, mul_smul]
      exact fixMod_smul _ (fun y hy => inv_smul_mem_latHat fr L0 AA hA ha' hy) h5
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end GlobalTheory.DictPinCompare
