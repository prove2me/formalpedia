-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.idealSheaf_stable_iff_exists_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:27.848804+00:00
-- url     : https://prove2.me/submissions/93f4dddc-cb0a-4cd9-9381-a633c66c94d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Theorems.Thm_GlobalTheory_GaloisDescent_idealSheaf_comap_map_of_stable
import Theorems.Thm_GlobalTheory_GaloisDescent_idealSheaf_comap_injective
import Theorems.Thm_GlobalTheory_GaloisDescent_twist_fst
import Theorems.Thm_GlobalTheory_GaloisDescent_twist_snd
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_quotientEquivOfMapEq_tmul
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul
attribute [local simp] GlobalTheory.GaloisDescent.mem_rationalPart
attribute [local simp] GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


attribute [reassoc (attr := simp)] GlobalTheory.GaloisDescent.twist_fst
attribute [reassoc (attr := simp)] GlobalTheory.GaloisDescent.twist_snd

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs
universe u
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}
include H
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (I : Y.IdealSheafData) :
    (∀ g, I.comap (twist H (s g)) ≤ I) ↔ ∃! J : X.IdealSheafData, J.comap π = I := by
  constructor
  · intro hI
    have h1 := idealSheaf_comap_map_of_stable H (fun g => (s g).toRingHom) hs
      (fun g => twist H (s g)) (fun g => twist_fst H _) (fun g => twist_snd H _) I hI
    exact ⟨_, h1, fun J hJ => idealSheaf_comap_injective H (hJ.trans h1.symm)⟩
  · rintro ⟨J, rfl, -⟩ g
    rw [← Scheme.IdealSheafData.comap_comp, twist_fst]
end GlobalTheory.GaloisDescent
