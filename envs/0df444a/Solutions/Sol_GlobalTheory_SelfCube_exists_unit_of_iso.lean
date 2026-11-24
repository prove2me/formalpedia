-- Prove2me | solution 1 for GlobalTheory.SelfCube.exists_unit_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:55:43.681368+00:00
-- url     : https://prove2.me/submissions/59a752ee-5aac-4c5d-8393-6f1a409ef4ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Theorems.Thm_GlobalTheory_SelfCube_exists_glue
import Theorems.Thm_P2M_GlobalTheory_SelfCube_differentiableOn_prod__64b63bfab2b1
import Theorems.Thm_GlobalTheory_SelfCube_val_div
import Theorems.Thm_GlobalTheory_SelfCube_exists_chart
import Theorems.Thm_GlobalTheory_CubeValues_comp_psum
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_CubeValues_val_gen
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
open GlobalTheory.CubeValues
namespace GlobalTheory.SelfCube
theorem _root_.solution (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]
    {L : LB A.left} (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) {n : ℕ} (y : Fin n → (A ⟶ A))
    (Y : Fin n → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hY : ∀ k, ∀ l ∈ u.Λ, Y k l ∈ u.Λ)
    (hy : ∀ k z, u.ex z ≫ y k = u.ex (Y k z))
    (a : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (ha : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l z * u.fr i (z + l))
    (hiso : LBIso L (cubeLB A y L)) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ (∀ z, ψ z ≠ 0) ∧ ∀ z, ∀ l ∈ u.Λ,
      ψ (z + l) * a l z = (∏ I : ULift.{0} (Finset (Fin n)),
        a (∑ k ∈ I.down, Y k l) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) * ψ z := by
  classical
  obtain ⟨w, hw⟩ := hiso
  have hpt : ∀ z (I : ULift.{0} (Finset (Fin n))),
      (u.ex z).left ≫ (psum A y I.down).left = (u.ex (∑ k ∈ I.down, Y k z)).left := fun z I => by
    rw [← Over.comp_left, comp_psum u (u.ex z) y (fun k => Y k z) (fun k => hy k z)]
  have hMc : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j ↔
        ∀ I : ULift.{0} (Finset (Fin n)), ⊤ ≤ (u.ex (∑ k ∈ I.down, Y k z)).left ⁻¹ᵁ L.U (j I) :=
    fun z j => by
      have h1 := le_preimage_wchart (u.ex z).left L
        (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left) j
      simp only [hpt] at h1
      exact h1
  have hMg : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' →
      valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j') ((cubeLB A y L).g j j').val =
        ∏ I : ULift.{0} (Finset (Fin n)), valAt' (u.ex (∑ k ∈ I.down, Y k z)).left
          (L.U (j I) ⊓ L.U (j' I)) (L.g (j I) (j' I)).val ^ ((-1 : ℤ) ^ (n - I.down.card)) :=
    fun z j j' hj hj' => by
      have h1 := val_linComb (u.ex z).left hv L
        (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left)
        (fun I => (-1 : ℤ) ^ (n - I.down.card)) j j' hj hj'
      simp only [hpt] at h1
      exact h1
  obtain ⟨Fc, hFc⟩ : ∃ Fc : (ULift.{0} (Finset (Fin n)) → L.ι) → (Fin g → ℂ) → ℂ,
      Fc = fun j z => ∏ I : ULift.{0} (Finset (Fin n)),
        u.fr (j I) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card)) := ⟨_, rfl⟩
  have hFc_ne : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → Fc j z ≠ 0 := fun z j hj => by
    simp only [hFc]
    exact Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (u.fr_ne _ _ ((hMc z j).1 hj I))
  have hFc_g : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' →
      Fc j z = valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j')
        ((cubeLB A y L).g j j').val * Fc j' z := fun z j j' hj hj' => by
    rw [hMg z j j' hj hj']
    simp only [hFc]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [← mul_zpow, ← u.fr_compat _ _ _
      ((le_preimage_inf _ _ _).2 ⟨(hMc z j).1 hj I, (hMc z j').1 hj' I⟩)]
  have hdiv : ∀ z (p : (LB.div (cubeLB A y L) L).ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p ↔
        ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U p.1 ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2 :=
    fun z p => le_preimage_inf _ _ _
  have hex : ∀ z l, l ∈ u.Λ → u.ex (z + l) = u.ex z := fun z l hl => by
    rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  obtain ⟨G, hG⟩ : ∃ G : (LB.div (cubeLB A y L) L).ι → (Fin g → ℂ) → ℂ,
      G = fun p z => valAt' (u.ex z).left ((LB.div (cubeLB A y L) L).U p) (w.s p).val *
        u.fr p.2 z / Fc p.1 z := ⟨_, rfl⟩
  have hG_ne : ∀ p z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p → G p z ≠ 0 := by
    intro p z hz
    have h2 := (hdiv z p).1 hz
    simp only [hG]
    exact div_ne_zero (mul_ne_zero (val_unit_ne_zero _ hv hz _) (u.fr_ne _ _ h2.2))
      (hFc_ne z _ h2.1)
  have hcov : ∀ z, ∃ p, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := fun z => by
    obtain ⟨i, hi⟩ := exists_chart hv hL u z
    choose j hj using fun I : ULift.{0} (Finset (Fin n)) => exists_chart hv hL u (∑ k ∈ I.down, Y k z)
    exact ⟨(j, i), (hdiv z (j, i)).2 ⟨(hMc z j).2 hj, hi⟩⟩
  have hopen : ∀ p, IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} :=
    fun p => (u.hol _ (w.s p).val).1
  have hYd : ∀ I : ULift.{0} (Finset (Fin n)), Differentiable ℂ (fun z => ∑ k ∈ I.down, Y k z) :=
    fun I => by
      have h : ∀ k, Differentiable ℂ (Y k) := fun k => by
        simpa using (LinearMap.toContinuousLinearMap (Y k)).differentiable
      have h2 : ∀ s : Finset (Fin n), Differentiable ℂ (fun z => ∑ k ∈ s, Y k z) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact differentiable_const 0
        | insert b s hb ih => simp only [Finset.sum_insert hb]; exact (h b).add ih
      exact h2 I.down
  have hGd : ∀ p, DifferentiableOn ℂ (G p)
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := fun p => by
    have hsub2 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} ⊆
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2} := fun z hz => ((hdiv z p).1 hz).2
    have hF : DifferentiableOn ℂ (Fc p.1)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := by
      simp only [hFc]
      refine differentiableOn_prod' Finset.univ fun I => ?_
      have hc : DifferentiableOn ℂ (fun z => u.fr (p.1 I) (∑ k ∈ I.down, Y k z))
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} :=
        (u.fr_hol (p.1 I)).comp (hYd I).differentiableOn
          (fun z hz => (hMc z p.1).1 ((hdiv z p).1 hz).1 I)
      rcases neg_one_pow_eq_or ℤ (n - I.down.card) with h | h
      · simp only [h, zpow_one]; exact hc
      · simp only [h, _root_.zpow_neg_one]
        exact hc.inv fun z hz => u.fr_ne _ _ ((hMc z p.1).1 ((hdiv z p).1 hz).1 I)
    simp only [hG, div_eq_mul_inv]
    exact (((u.hol _ (w.s p).val).2).mul ((u.fr_hol p.2).mono hsub2)).mul
      (hF.inv fun z hz => hFc_ne z _ ((hdiv z p).1 hz).1)
  have hcompat : ∀ p q z, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} →
      z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U q} → G p z = G q z := by
    intro p q z hp hq
    have hp' := (hdiv z p).1 hp
    have hq' := (hdiv z q).1 hq
    have hpq : ⊤ ≤ (u.ex z).left ⁻¹ᵁ
        ((LB.div (cubeLB A y L) L).U p ⊓ (LB.div (cubeLB A y L) L).U q) :=
      (le_preimage_inf _ _ _).2 ⟨hp, hq⟩
    have hL2 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2) :=
      (le_preimage_inf _ _ _).2 ⟨hp'.2, hq'.2⟩
    have e1 := val_gen (u.ex z).left hv w hw p q hp hq
    have e2 := val_div hv (u.ex z).left (cubeLB A y L) L p q hp hq
    have e3 := u.fr_compat p.2 q.2 z hL2
    have e4 := hFc_g z p.1 q.1 hp'.1 hq'.1
    have n1 := val_unit_ne_zero _ hv hpq ((LB.div (cubeLB A y L) L).g p q)
    have n2 := val_unit_ne_zero _ hv hL2 (L.g p.2 q.2)
    have n3 := hFc_ne z q.1 hq'.1
    simp only [hG]
    rw [e1, e3, e4, ← e2]
    field_simp
  obtain ⟨F, hFd, hFG⟩ := exists_glue
    (fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}) G hopen hcov hGd hcompat
  refine ⟨F, hFd, fun z => ?_, fun z l hl => ?_⟩
  · obtain ⟨p, hp⟩ := hcov z
    rw [hFG p z hp]
    exact hG_ne p z hp
  · obtain ⟨p, hp⟩ := hcov z
    have hp' := (hdiv z p).1 hp
    have hpl : z + l ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := by
      rw [Set.mem_ofPred_eq, hex z l hl]
      exact hp
    rw [hFG p z hp, hFG p (z + l) hpl]
    simp only [hG]
    rw [hex z l hl]
    have e1 := ha l hl p.2 z hp'.2
    have hSl : ∀ I : ULift.{0} (Finset (Fin n)), ∑ k ∈ I.down, Y k l ∈ u.Λ :=
      fun I => Submodule.sum_mem _ fun k _ => hY k l hl
    have e2 : Fc p.1 z = (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l)
        (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) * Fc p.1 (z + l) := by
      simp only [hFc]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← mul_zpow, ha _ (hSl I) (p.1 I) _ ((hMc z p.1).1 hp'.1 I)]
      rw [show ∑ k ∈ I.down, Y k (z + l) = ∑ k ∈ I.down, Y k z + ∑ k ∈ I.down, Y k l by
        simp only [map_add, Finset.sum_add_distrib]]
    have n0 := hFc_ne z p.1 hp'.1
    have n1 : Fc p.1 (z + l) ≠ 0 := hFc_ne (z + l) p.1 (by rw [hex z l hl]; exact hp'.1)
    have n2 : (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l)
        (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) ≠ 0 := fun h => n0 (by
      rw [e2, h, zero_mul])
    rw [e1, e2]
    field_simp
end GlobalTheory.SelfCube
