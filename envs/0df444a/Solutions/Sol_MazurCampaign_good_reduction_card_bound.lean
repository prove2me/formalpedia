-- Prove2me | solution 1 for MazurCampaign.good_reduction_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T10:34:54.47121+00:00
-- url     : https://prove2.me/submissions/217cf717-7b3d-4349-8283-5580d70b3238

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Theorems.Thm_MazurReduction_rational_torsion_kernel_zero
import Theorems.Thm_MazurReduction_rational_residue_field_equiv
import Definitions.Def_MazurReduction_PointTransport
import Definitions.Def_MazurCampaign_group_constraints

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Finite (MazurCampaign.RationalTorsion (W.map (Int.castRingHom ℚ))) ∧
      Nat.card (MazurCampaign.RationalTorsion (W.map (Int.castRingHom ℚ))) ∣
        Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  classical
  let v := Rat.padicValuation p
  let A := v.valuationSubring
  let F := ResidueField A
  let WA := W.map (Int.castRingHom A)
  let E := W.map (Int.castRingHom ℚ)
  have hWq : WA.map A.subtype = E := by
    ext <;> simp [WA, E, WeierstrassCurve.map]
  letI : (WA.map A.subtype).IsElliptic := hWq.symm ▸ inferInstance
  have hval : v ((WA.Δ : A) : ℚ) = 1 := by
    dsimp only [WA]
    rw [WeierstrassCurve.map_Δ]
    change Rat.padicValuation p (W.Δ : ℚ) = 1
    rw [Rat.padicValuation_cast, Int.padicValuation_eq_one_iff]
    exact hgood
  have hunit : IsUnit WA.Δ := by
    exact (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one.mpr hval
  have hΔ : (WA.map (residue A)).Δ ≠ 0 :=
    (WeierstrassCurve.map_residue_Δ_ne_zero_iff WA).mpr hunit
  obtain ⟨e⟩ := MazurReduction.rational_residue_field_equiv p
  let σ : F ≃ₐ[ℤ] ZMod p := AlgEquiv.ofRingEquiv (f := e) (by intro z; simp)
  let eF : (WA.map (residue A)).toAffine.Point ≃+
      (W.map (Int.castRingHom (ZMod p))).toAffine.Point :=
    (MazurReduction.curvePointCongr (by
      ext <;> simp [WA, WeierstrassCurve.map, WeierstrassCurve.Affine.baseChange])).trans
      ((MazurReduction.pointBaseChangeEquiv W.toAffine σ).trans
        (MazurReduction.curvePointCongr (by
          ext <;> simp [WeierstrassCurve.map, WeierstrassCurve.Affine.baseChange])))
  let eQ : (E⁄ℚ).Point ≃+ (WA.map A.subtype).toAffine.Point :=
    MazurReduction.curvePointCongr (by
      rw [hWq]
      ext <;> simp [WeierstrassCurve.Affine.baseChange, WeierstrassCurve.map])
  let f : MazurCampaign.RationalTorsion E →+ (WA.map (residue A)).toAffine.Point :=
    (WeierstrassCurve.reduceHom hΔ).comp
      (eQ.toAddMonoidHom.comp (AddCommGroup.torsion (E⁄ℚ).Point).subtype)
  have hf : Function.Injective f := by
    intro P Q hPQ
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply eQ.injective
    rw [map_zero]
    apply MazurReduction.rational_torsion_kernel_zero p hp WA hΔ
    · exact eQ.toAddMonoidHom.isOfFinAddOrder (P - Q).property
    · change f (P - Q) = 0
      rw [map_sub, hPQ, sub_self]
  letI : Finite (WA.map (residue A)).toAffine.Point :=
    Finite.of_equiv (W.map (Int.castRingHom (ZMod p))).toAffine.Point eF.symm.toEquiv
  refine ⟨Finite.of_injective f hf, ?_⟩
  rw [← Nat.card_congr eF.toEquiv]
  exact AddSubgroup.card_dvd_of_injective f hf

#print axioms solution
