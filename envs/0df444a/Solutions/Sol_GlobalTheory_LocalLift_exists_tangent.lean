-- Prove2me | solution 1 for GlobalTheory.LocalLift.exists_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:10.530188+00:00
-- url     : https://prove2.me/submissions/b5976de9-f9a0-489f-859a-f675299d71c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Theorems.Thm_GlobalTheory_LocalLift_hol_eventually_mem
import Theorems.Thm_GlobalTheory_LocalLift_hol_differentiableAt
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_top_le_preimage_iff
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b
import Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
import Theorems.Thm_P2M_GlobalTheory_valAt__zero_f075fc9dd23d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin
noncomputable section
open GlobalTheory GlobalTheory.LocalLift
variable {Y : Scheme.{0}}
namespace GlobalTheory.LocalLift
theorem _root_.solution {n : ℕ} (s : Y ⟶ Sp ℂ) {W : Set (Fin n → ℂ)} (hW : 0 ∈ W) {p : (Fin n → ℂ) → (Sp ℂ ⟶ Y)}
    (hp : IsHolTo W p) (hps : ∀ w, p w ≫ s = 𝟙 _) {U : Y.Opens} (hU : IsAffineOpen U) (h0 : ⊤ ≤ p 0 ⁻¹ᵁ U)
    (u : Fin n → ℂ) :
    ∃ (v : Sp (DualNumber ℂ) ⟶ Y) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) ∧
      spMap fstC ≫ v = p 0 ∧ ∀ f, (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (p z) U f) 0 u := by
  have hd := hol_differentiableAt hp hW h0
  have hconst : ∀ a, fderiv ℂ (fun z => valAt' (p z) U (constFn s U a)) 0 = 0 := by
    intro a
    have : (fun z => valAt' (p z) U (constFn s U a)) =ᶠ[𝓝 0] fun _ => a := by
      filter_upwards [hol_eventually_mem hp hW h0] with z hz
      exact valAt'_constFn _ s (hps z) U a hz.2
    rw [this.fderiv_eq]; simp
  let J : Γ(Y, U) →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (valAt' (p 0) U f) +
        TrivSqZeroExt.inr (fderiv ℂ (fun z => valAt' (p z) U f) 0 u)
      map_one' := by
        have := hconst 1
        rw [show constFn s U 1 = 1 by simp [constFn]] at this
        ext <;> simp [this, valAt'_one _ h0]
      map_zero' := by
        ext <;> simp [valAt'_zero]
      map_add' := fun f f' => by
        ext <;> simp [valAt'_add, fderiv_fun_add (hd f) (hd f')]
      map_mul' := fun f f' => by
        ext <;> simp [valAt'_mul, fderiv_fun_mul (hd f) (hd f'), mul_comm] }
  obtain ⟨v, hv, hve⟩ := exists_evalPt_eq hU J
  refine ⟨v, hv, ?_, ?_, fun f => ?_⟩
  · refine eq_spMap_of_evalPt _ _ fun a => ?_
    rw [← evalPt_constFn s v U hv, hve]
    ext <;> simp [J, hconst, valAt'_constFn _ s (hps 0) U a h0, TrivSqZeroExt.algebraMap_eq_inl]
  · refine ext_evalPt hU ((top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp fstC v U hv _ f).trans ?_
    rw [hve, ← valAt'_eq_evalPt]
    simp [J]
  · rw [hve]; simp [J]
end GlobalTheory.LocalLift
