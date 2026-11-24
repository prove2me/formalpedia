-- Prove2me | solution 1 for GlobalTheory.SympMod.exists_stdSymp_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:07.440561+00:00
-- url     : https://prove2.me/submissions/58de743e-d105-428f-b47a-bd7672733719

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
import Theorems.Thm_GlobalTheory_SympMod_exists_isSymplecticFamily
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SympMod
open ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.SympMod
theorem _root_.solution {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (hB : B.IsAlt) (hN : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // d • x = 0} = d ^ (2 * g)) :
    ∃ v : Fin (2 * g) → V, ∀ i k, B (v i) (v k) = (stdSymp g i k : ℤ) := by
  obtain ⟨e, f, hs, -, -⟩ := exists_isSymplecticFamily hB g ⊤ (fun x _ h => hN x fun y => h y trivial)
    (fun d hd => by simpa using hc d hd)
  let σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  refine ⟨Sum.elim e f ∘ σ, fun i k => ?_⟩
  obtain ⟨a, rfl⟩ := σ.symm.surjective i
  obtain ⟨b, rfl⟩ := σ.symm.surjective k
  simp only [Function.comp, Equiv.apply_symm_apply, stdSymp]
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a := fun _ => rfl
  rcases a with a | a <;> rcases b with b | b <;> have := a.2 <;> have := b.2 <;>
    simp only [l, r, Sum.elim_inl, Sum.elim_inr, hs.left_left, hs.right_right, hs.left_right, hs.right_left hB,
      Fin.ext_iff] <;> split_ifs <;> first | omega | simp
end GlobalTheory.SympMod
