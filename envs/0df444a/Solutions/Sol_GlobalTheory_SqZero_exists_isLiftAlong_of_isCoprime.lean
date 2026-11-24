-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_isLiftAlong_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:10.283027+00:00
-- url     : https://prove2.me/submissions/add5390c-c042-407d-8565-f33b9585c2dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_IsLiftAlong_mul
import Theorems.Thm_GlobalTheory_SqZero_IsLiftAlong_mul_inv_mem
import Theorems.Thm_GlobalTheory_SqZero_isLiftAlong_of_away
import Theorems.Thm_GlobalTheory_SqZero_exists_add_eq_of_isCoprime
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_agree_of_isAway
import Theorems.Thm_GlobalTheory_SqZero_away_glue
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_expBij
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
import Theorems.Thm_GlobalTheory_SqZero_lieExp_add
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_GlobalTheory_SqZero_lieExp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_map_sq
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
section Hom
variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {m : ℕ}
  {w : Fin m → (epsR R ⟶ H)} (f : G ⟶ H) [IsMonHom f]
variable [IsCommMonObj H]
end Hom
variable [Smooth G.hom]
section Surjective
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
private theorem ideal_map_map_le_map_comp {P Q S : Type} [CommRing P] [CommRing Q] [CommRing S] [Algebra R P]
    [Algebra R Q] [Algebra R S] (I : Ideal P) (p : P →ₐ[R] Q) (q : Q →ₐ[R] S) :
    (I.map p).map q ≤ I.map (q.comp p) :=
  Ideal.map_le_iff_le_comap.2 (Ideal.map_le_iff_le_comap.2 fun _ hx =>
    Ideal.mem_comap.2 (Ideal.mem_comap.2 (Ideal.mem_map_of_mem (q.comp p) hx)))
end Surjective
end GlobalTheory.SqZero
namespace GlobalTheory
open SqZero
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥)
    {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G} {φ : A →ₐ[R] T} {f g : T} (hfg : IsCoprime f g)
    {y₁ : sp (R₀ := R) (Localization.Away f) ⟶ G} {y₂ : sp (R₀ := R) (Localization.Away g) ⟶ G}
    (hy₁ : IsLiftAlong y₀ ((awayHom R f).comp φ) y₁)
    (hy₂ : IsLiftAlong y₀ ((awayHom R g).comp φ) y₂) : ∃ y, IsLiftAlong y₀ φ y := by
  have hfu : IsUnit (awayHom R (f * g) f * awayHom R (f * g) g) := by
    rw [← map_mul]; exact (isAway_awayHom (R := R) (f * g)).unit
  obtain ⟨a, ha⟩ := (isAway_awayHom (R := R) f).lift (awayHom R (f * g)) (isUnit_of_mul_isUnit_left hfu)
  obtain ⟨b, hb⟩ := (isAway_awayHom (R := R) g).lift (awayHom R (f * g)) (isUnit_of_mul_isUnit_right hfu)
  have hK : (J.map ((awayHom R (f * g)).comp φ)) ^ 2 = ⊥ := map_sq hJ _
  have hy₁' : IsLiftAlong y₀ ((awayHom R (f * g)).comp φ) (spMap a ≫ y₁) := by
    have := hy₁.map a; rwa [← AlgHom.comp_assoc, ha] at this
  have hy₂' : IsLiftAlong y₀ ((awayHom R (f * g)).comp φ) (spMap b ≫ y₂) := by
    have := hy₂.map b; rwa [← AlgHom.comp_assoc, hb] at this
  have hmem := hy₁'.mul_inv_mem hy₂'
  obtain ⟨-, hsurj⟩ := expBij (Localization.Away (f * g)) hv (J.map ((awayHom R (f * g)).comp φ)) hK
  obtain ⟨c, hc, hcJ, hcy⟩ := hsurj _ hmem
  have hcJ' : ∀ i, c i ∈ (J.map φ).map (awayHom R (f * g)) := fun i => by
      have h0 : J.map ((awayHom R (f * g)).comp φ) ≤ (J.map φ).map (awayHom R (f * g)) :=
        Ideal.map_le_iff_le_comap.2 fun _ hx => Ideal.mem_comap.2 (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem φ hx))
      exact h0 (hcJ i)
  choose z₁ hz₁ z₂ hz₂ hz using fun i => exists_add_eq_of_isCoprime (R := R) hfg (isAway_awayHom (R := R) f)
    (isAway_awayHom (R := R) g) (isAway_awayHom (R := R) (f * g)) ha hb (hcJ' i)
  have E1 : ∀ i, z₁ i ∈ J.map ((awayHom R f).comp φ) := fun i => ideal_map_map_le_map_comp J φ _ (hz₁ i)
  have E2 : ∀ i, z₂ i ∈ J.map ((awayHom R g).comp φ) := fun i => ideal_map_map_le_map_comp J φ _ (hz₂ i)
  have H1 : ((J.map φ).map (awayHom R f)).map a ≤ J.map ((awayHom R (f * g)).comp φ) := by
    refine (ideal_map_map_le_map_comp _ _ _).trans ?_
    rw [ha]; exact ideal_map_map_le_map_comp _ _ _
  have H2 : ((J.map φ).map (awayHom R g)).map b ≤ J.map ((awayHom R (f * g)).comp φ) := by
    refine (ideal_map_map_le_map_comp _ _ _).trans ?_
    rw [hb]; exact ideal_map_map_le_map_comp _ _ _
  have ma : ∀ i, a (z₁ i) ∈ J.map ((awayHom R (f * g)).comp φ) := fun i => H1 (Ideal.mem_map_of_mem a (hz₁ i))
  have mb : ∀ i, b (z₂ i) ∈ J.map ((awayHom R (f * g)).comp φ) := fun i => H2 (Ideal.mem_map_of_mem b (hz₂ i))
  have hL₁ : lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i)) ∈
      redKer G (J.map ((awayHom R f).comp φ)) := lieExp_mem_redKer hv.1 _ E1 _
  have hL₂ : lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i)) ∈
      redKer G (J.map ((awayHom R g).comp φ)) := lieExp_mem_redKer hv.1 _ E2 _
  have hl₁ := hy₁.mul (inv_mem hL₁)
  have hl₂ := hy₂.mul hL₂
  have e1 : lieExp v c hc = (spMap a ≫ lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i))) *
      (spMap b ≫ lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i))) := by
    rw [comp_lieExp, comp_lieExp, ← lieExp_add hv.1 _ _ _ _ (fun i => mul_eq_zero_of_sq hK (ma i) (mb i))
      (fun i => mul_eq_zero_of_sq hK (add_mem (ma i) (mb i)) (add_mem (ma i) (mb i)))]
    exact lieExp_congr v (fun i => hz i) _ _
  have key : spMap a ≫ ((lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i)))⁻¹ * y₁) =
      spMap b ≫ (lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i)) * y₂) := by
    rw [← ptsMap_apply G a, ← ptsMap_apply G b, map_mul, map_mul, map_inv, ptsMap_apply, ptsMap_apply,
      ptsMap_apply, ptsMap_apply]
    have : spMap a ≫ y₁ = (spMap a ≫ lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i))) *
        (spMap b ≫ lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i))) * (spMap b ≫ y₂) := by
      rw [← e1, ← hcy, inv_mul_cancel_right]
    rw [this, mul_assoc, inv_mul_cancel_left]
  have hs : Ideal.span (Set.range fun i : Bool => cond i f g) = ⊤ := by
    obtain ⟨u, w, huw⟩ := hfg
    refine (Ideal.eq_top_iff_one _).2 ?_
    rw [← huw]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨true, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨false, rfl⟩))
  obtain ⟨z, hzz⟩ := away_glue (X := G) hs (fun i => awayHom R (cond i f g)) (fun i => isAway_awayHom _)
    (fun i => Bool.rec (motive := fun i => sp (R₀ := R) (Localization.Away (cond i f g)) ⟶ G)
      (lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i)) * y₂)
      ((lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i)))⁻¹ * y₁) i)
    (by
      intro i j T₀ _ _ a' b' e
      cases i <;> cases j
      · have := (isAway_awayHom (R := R) g).ext e; subst this; rfl
      · exact (agree_of_isAway (isAway_awayHom (R := R) g) (isAway_awayHom (R := R) f) (hb.trans ha.symm)
          (by rw [hb, mul_comm]; exact isAway_awayHom _) key.symm T₀ a' b' e)
      · exact (agree_of_isAway (isAway_awayHom (R := R) f) (isAway_awayHom (R := R) g) (ha.trans hb.symm)
          (by rw [ha]; exact isAway_awayHom _) key T₀ a' b' e)
      · have := (isAway_awayHom (R := R) f).ext e; subst this; rfl)
  refine ⟨z, isLiftAlong_of_away hs fun i => ?_⟩
  rw [hzz i]
  cases i
  · exact hl₂
  · exact hl₁
end GlobalTheory.SqZero
