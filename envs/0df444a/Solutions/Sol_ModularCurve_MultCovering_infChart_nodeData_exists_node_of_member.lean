-- Prove2me | solution 1 for ModularCurve.MultCovering.infChart_nodeData_exists_node_of_member
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/42cebab4-20cb-5960-b633-674a06ea0f61

import Definitions.Def_ModularCurve_MultCoveringFamily
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_goodFamily
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member

set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC MultCovering.infChart_residue_goodFamily ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "ssPolyBar FamCtx goodFamily jBar mAnnuli ChartCtx infChart chart ssValue ssValue_injective nodeTgt infChart_residue_goodFamily"
namespace FamProj
p2m_open "ModularCurve.MultCovering ModularCurve"

theorem ord_finset_prod {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem jBar_sub_algebraMap_ne_zero (k : Type) [Field k] [DecidableEq k] (c : k) :
    jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c ≠ 0 := by
  intro h
  have := ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k c c
  rw [show ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) = jBar k from rfl, h,
    Place.ord_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem hX (k : Type) [Field k] : ratFuncEquivCharLOneC k RatFunc.X = jBar k := by
  apply Subtype.ext
  show ((ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = jqModC k
  rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)

theorem ord_charLGeomPlaceOfPoint_aeval_jBar (k : Type) [Field k] [DecidableEq k] (a : k) (Q : Polynomial k)
    (hQ : Q ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord (Polynomial.aeval (jBar k) Q) = Polynomial.rootMultiplicity a Q := by
  have halg : algebraMap (Polynomial k) (RatFunc k) Q = Polynomial.aeval (RatFunc.X : RatFunc k) Q := by
    have h : (IsScalarTower.toAlgHom k (Polynomial k) (RatFunc k)) = Polynomial.aeval (RatFunc.X : RatFunc k) := by
      apply Polynomial.algHom_ext
      simp [RatFunc.algebraMap_X]
    exact DFunLike.congr_fun h Q
  have h1 : Polynomial.aeval (jBar k) Q =
      (ratFuncEquivCharLOneC k).toRingEquiv (algebraMap (Polynomial k) (RatFunc k) Q) := by
    rw [halg, ← hX]
    exact (Polynomial.aeval_algHom_apply (ratFuncEquivCharLOneC k).toAlgHom RatFunc.X Q)
  rw [h1, show charLGeomPlaceOfPoint k a = Place.congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
      (fun x => (ratFuncEquivCharLOneC k).commutes x) (RationalFunctionField.placeOfPoint k a) from rfl,
    Place.ord_congrRingEquiv, RationalFunctionField.ord_placeOfPoint_algebraMap a hQ]

theorem aeval_jBar_injective (k : Type) [Field k] :
    Function.Injective (Polynomial.aeval (R := k) (jBar k)) := by
  have htr : Transcendental k (jBar k) :=
    (transcendental_algebraMap_iff
      (algebraMap (↥(modularFunctionFieldC k 1)) (LaurentSeries k)).injective).mp (transcendental_jqModC k)
  exact transcendental_iff_injective.mp htr

section PerA
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ssPolyBar_eq_aeval :
    ssPolyBar Γ = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e))) := by
  rw [ssPolyBar, map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

theorem ssPolyX_monic : (∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e))).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun e _ => Polynomial.monic_X_sub_C _

theorem ssPolyX_natDegree :
    (∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e))).natDegree = mAnnuli p := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun e _ => Polynomial.monic_X_sub_C _)]
  simp

theorem ssPolyBar_ne_zero : ssPolyBar Γ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun e _ => jBar_sub_algebraMap_ne_zero _ _

theorem ord_nodeTgt_ssPolyBar (e : Fin (mAnnuli p)) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord (ssPolyBar Γ) = 1 := by
  rw [ssPolyBar, ord_finset_prod _ _ _ (fun e' _ => jBar_sub_algebraMap_ne_zero _ _)]
  simp_rw [show ∀ c : (IsLocalRing.ResidueField ↥A), jBar (IsLocalRing.ResidueField ↥A) - algebraMap _ _ c
      = (⟨jqModC (IsLocalRing.ResidueField ↥A), jqModC_mem (IsLocalRing.ResidueField ↥A) 1⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) - algebraMap _ _ c
      from fun _ => rfl,
    ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap, (ssValue_injective Γ).eq_iff]
  simp [Finset.sum_ite_eq']

noncomputable def ssMulAeval : Polynomial (IsLocalRing.ResidueField ↥A) →ₗ[(IsLocalRing.ResidueField ↥A)] ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  (LinearMap.mulLeft (IsLocalRing.ResidueField ↥A) (ssPolyBar Γ)).comp (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A))).toLinearMap

theorem ssMulAeval_apply (Q : Polynomial (IsLocalRing.ResidueField ↥A)) :
    ssMulAeval Γ Q = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q := rfl

theorem ssMulAeval_injective : Function.Injective (ssMulAeval Γ) := by
  intro Q Q' h
  rw [ssMulAeval_apply, ssMulAeval_apply] at h
  exact aeval_jBar_injective _ (mul_left_cancel₀ (ssPolyBar_ne_zero Γ) h)

end PerA

end ModularCurve.MultCovering.FamProj

open ModularCurve.MultCovering.FamProj

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers,
      ∀ l : Fin r, 1 ≤ (l : ℕ) → ∃ e : Fin (mAnnuli p),
        (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩) = 1 := by
  classical
  obtain ⟨hint, -, P, hP, hli, -⟩ := ModularCurve.MultCovering.infChart_residue_goodFamily p A hA Γ Φ
  refine ⟨hint, fun l hl1 => ?_⟩
  have hPl : P l ≠ 0 := hli.ne_zero ⟨l, hl1⟩
  have h2 : Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) ≠ 0 :=
    (map_ne_zero_iff _ (aeval_jBar_injective (IsLocalRing.ResidueField ↥A))).mpr hPl
  by_contra hne
  push_neg at hne

  have hroots : ∀ e, (P l).IsRoot (ssValue Γ e) := by
    intro e
    by_contra hev
    apply hne e
    show (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord _ = _
    rw [(hP l hl1).2, (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord_mul (ssPolyBar_ne_zero Γ) h2,
      ord_nodeTgt_ssPolyBar, ord_charLGeomPlaceOfPoint_aeval_jBar _ _ _ hPl,
      Polynomial.rootMultiplicity_eq_zero hev]
    simp

  have hsub : Finset.univ.image (ssValue Γ) ⊆ (P l).roots.toFinset := by
    intro a ha
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp ha
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPl).mpr (hroots e))
  have hcard : mAnnuli p ≤ (P l).natDegree := by
    calc mAnnuli p = (Finset.univ.image (ssValue Γ)).card := by
          rw [Finset.card_image_of_injective _ (ssValue_injective Γ), Finset.card_univ, Fintype.card_fin]
      _ ≤ (P l).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (P l).roots.card := Multiset.toFinset_card_le _
      _ ≤ (P l).natDegree := Polynomial.card_roots' _
  have := (hP l hl1).1
  omega

end S_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member
end P2MW
export P2MW.S_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member (solution)
