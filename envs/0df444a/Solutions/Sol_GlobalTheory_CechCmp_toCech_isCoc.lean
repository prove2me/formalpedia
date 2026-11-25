-- Prove2me | solution 1 for GlobalTheory.CechCmp.toCech_isCoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:57:22.584029+00:00
-- url     : https://prove2.me/submissions/a7356222-bd39-4be3-96ff-37a1c1b7ad7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCocyclePosetOneCochainToCechCochain
import Theorems.Thm_GlobalTheory_CechCmp_toCech_cocycle_read
import Theorems.Thm_GlobalTheory_CechCmp_cap_pair
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechCmp
variable {I : Type} [Finite I] {X : Scheme.{0}} {R : Type} [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
namespace GlobalTheory.CechCmp
theorem _root_.solution (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf)) :
    IsCoc U (toCech s U hU hinf f) := by
  intro i j k
  let K : NE I := OrderDual.toDual ⟨{i, j, k}, Set.insert_nonempty i {j, k}⟩
  have hi : i ∈ K.set := Set.mem_insert i _
  have hj : j ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert j _)
  have hk : k ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert_of_mem j rfl)
  have sgl : ∀ {a : I}, a ∈ K.set → K ≤ NE.single a := fun ha => NE.le_iff.2 (Set.singleton_subset_iff.2 ha)
  have pr : ∀ {a b : I}, a ∈ K.set → b ∈ K.set → K ≤ NE.pair a b :=
    fun ha hb => NE.le_iff.2 (Set.insert_subset ha (Set.singleton_subset_iff.2 hb))
  have hW : U i ⊓ U j ⊓ U k ≤ cap U K := le_iInf₂ fun x hx => by
    rcases hx with rfl | rfl | rfl
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have hij : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have hjk : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hik : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  simp only [toCech_apply, GlobalTheory.KS.rsT_sub]
  rw [GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij, GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij,
    GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk, GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk,
    GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik, GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik]
  rw [toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hj) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hi hj) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hj hk) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hj hk) (sgl hk) _ hW,
    toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hk) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hi hk) (sgl hk) _ hW]
  abel
end GlobalTheory.CechCmp
