-- Prove2me | solution 1 for GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:54.806384+00:00
-- url     : https://prove2.me/submissions/41c3ecc3-aec8-4ceb-8d8d-fcfce9b74caa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetOneCochainToCechCochainCoboundary
import Theorems.Thm_GlobalTheory_CechCmp_NE_set_pair
import Theorems.Thm_GlobalTheory_CechCmp_NE_set_single
import Theorems.Thm_GlobalTheory_CechCmp_cap_pair
import Theorems.Thm_GlobalTheory_CechCmp_cap_single
import Theorems.Thm_GlobalTheory_CechCmp_cv_mp
import Theorems.Thm_GlobalTheory_CechCmp_toCech_apply
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_KS_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_rsT_sub
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
noncomputable section
open GlobalTheory GlobalTheory.CechCmp
namespace GlobalTheory.CechCmp
theorem _root_.solution : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  intro I _ X R _ s U hU hinf g
  refine ⟨fun i => rsT (cv s U hU hinf (op (NE.single i)) (g (op (NE.single i)))) (U i), fun i j => ?_⟩
  have hp : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  have key : ∀ k, k ∈ ({i, j} : Set I) →
      rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (cap U (NE.pair i j))) (U i ⊓ U j) =
        rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (U k)) (U i ⊓ U j) := by
    intro k hk
    have hk' : U i ⊓ U j ≤ U k := by
      rcases hk with rfl | hk
      · exact inf_le_left
      · rw [Set.mem_singleton_iff.1 hk]; exact inf_le_right
    rw [GlobalTheory.KS.rsT_rsT (cap_mono U (a := NE.pair i j) (b := NE.single k) (NE.le_iff.2 (by rw [NE.set_single, NE.set_pair]; exact Set.singleton_subset_iff.2 hk))) hp,
      GlobalTheory.KS.rsT_rsT (cap_single U k).ge hk']
  rw [toCech_apply, amitsur_d0_apply, amitsur_d0_apply, map_sub, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sub]
  have e1 := key i (Set.mem_insert i {j})
  have e2 := key j (Set.mem_insert_of_mem i rfl)
  simp only [unop_op] at e1 e2 ⊢
  rw [e1, e2]
  abel
end GlobalTheory.CechCmp
