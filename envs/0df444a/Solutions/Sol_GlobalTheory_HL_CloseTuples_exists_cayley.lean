-- Prove2me | solution 1 for GlobalTheory.HL.CloseTuples.exists_cayley
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:11.916827+00:00
-- url     : https://prove2.me/submissions/3c01217c-011e-40f3-9dd4-9249a826d1a0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuples
import Theorems.Thm_GlobalTheory_HL_CloseTuples_one_add_onto
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_l
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CloseTuples
open GlobalTheory.HL.Eichler GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.HL.CloseTuples
theorem _root_.solution {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (hp' : L.cj p = p)
    (Z : (Fin n → E) →ₗ[E] (Fin n → E)) (hZ : ∀ v ∈ Λ, Z v ∈ Λ)
    (hsk : ∀ v w, hf L Hm (Z v) w = - hf L Hm v (Z w)) :
    ∃ g ∈ isomG L Hm, (∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = (p : E) • w) ∧
      ∀ x y, (p : E) • Z (x + y) = y - x → g x = y := by
  obtain ⟨b1, -⟩ := one_add_onto hΛ p hp Z hZ
  obtain ⟨b2, o2⟩ := one_add_onto hΛ p hp (-Z) fun v hv => Λ.neg_mem (hZ v hv)
  let g := (LinearEquiv.ofBijective _ b1).trans (LinearEquiv.ofBijective _ b2).symm
  have hg : ∀ x y, x + (p : E) • Z x = y - (p : E) • Z y → g x = y := fun x y e => by
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    change x + (p : E) • Z x = y + (p : E) • (-Z y)
    rw [e]; module
  have hg' : ∀ u, g (u + (p : E) • (-Z u)) = u + (p : E) • Z u := fun u => hg _ _ (by
    simp only [map_add, map_smul, map_neg]; module)
  refine ⟨g, fun v w => ?_, fun v hv => ?_, fun x y e => hg x y ?_⟩
  · obtain ⟨v, rfl⟩ := b2.2 v
    obtain ⟨w, rfl⟩ := b2.2 w
    change hf L Hm (g (v + (p : E) • (-Z v))) (g (w + (p : E) • (-Z w)))
      = hf L Hm (v + (p : E) • (-Z v)) (w + (p : E) • (-Z w))
    rw [hg', hg']
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, hf_neg_l, hf_neg_r, hp', hsk v w]
    ring
  · obtain ⟨u, hu, rfl⟩ := o2 v hv
    refine ⟨Z u + Z u, Λ.add_mem (hZ u hu) (hZ u hu), ?_⟩
    change g (u + (p : E) • (-Z u)) - (u + (p : E) • (-Z u)) = _
    rw [hg']; module
  · rw [map_add, smul_add] at e
    linear_combination (exp := 1) e
end GlobalTheory.HL.CloseTuples
