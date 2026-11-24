-- Prove2me | solution 1 for GlobalTheory.SqZero.reduction_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:14.95684+00:00
-- url     : https://prove2.me/submissions/d64f4a3c-5854-459d-9c30-93c22aae5168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_isLiftAlong_of_quotient
import Theorems.Thm_GlobalTheory_SqZero_exists_isLiftAlong_of_isCoprime
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_away_ext
import Theorems.Thm_GlobalTheory_SqZero_exists_local_chart
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
import Theorems.Thm_GlobalTheory_SqZero_map_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_smooth_of_chart
import Theorems.Thm_GlobalTheory_SqZero_span_eq_top_of_forall_maximal
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
theorem _root_.solution (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥) :
    Function.Surjective (pointsMap G (Ideal.Quotient.mkₐ R J)) := by
  intro y₀
  have hzero : ∃ y : sp (Localization.Away (0 : A)) ⟶ G, IsLiftAlong y₀ (awayHom R 0) y := by
    refine ⟨1, fun T₀ _ _ q q₀ _ => ?_⟩
    have h01 : (0 : Localization.Away (0 : A)) = 1 := by
      have := (isAway_awayHom (R := R) (0 : A)).unit
      rw [map_zero] at this
      exact isUnit_zero_iff.1 this
    have : Subsingleton T₀ := subsingleton_of_zero_eq_one (by rw [← map_zero q, h01, map_one])
    have hs : Ideal.span (Set.range fun i : Empty => i.elim) = (⊤ : Ideal T₀) :=
      (Ideal.eq_top_iff_one _).2 (by rw [Subsingleton.elim (1 : T₀) 0]; exact zero_mem _)
    exact away_ext (X := G) (B := fun _ => T₀) hs (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
  have hmul : ∀ c f : A, (∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y) →
      ∃ y : sp (Localization.Away (c * f)) ⟶ G, IsLiftAlong y₀ (awayHom R (c * f)) y := by
    rintro c f ⟨y, hy⟩
    have hu : IsUnit (awayHom R (c * f) c * awayHom R (c * f) f) := by
      rw [← map_mul]; exact (isAway_awayHom (R := R) (c * f)).unit
    obtain ⟨ψ, hψ⟩ := (isAway_awayHom (R := R) f).lift (awayHom R (c * f)) (isUnit_of_mul_isUnit_right hu)
    exact ⟨spMap ψ ≫ y, by have := hy.map ψ; rwa [hψ] at this⟩
  have hadd : ∀ f g : A, (∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y) →
      (∃ y : sp (Localization.Away g) ⟶ G, IsLiftAlong y₀ (awayHom R g) y) →
      ∃ y : sp (Localization.Away (f + g)) ⟶ G, IsLiftAlong y₀ (awayHom R (f + g)) y := by
    rintro f g ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
    have hu : IsUnit (awayHom R (f + g) (f + g)) := (isAway_awayHom (R := R) (f + g)).unit
    have hcop : IsCoprime (awayHom R (f + g) f) (awayHom R (f + g) g) :=
      ⟨↑hu.unit⁻¹, ↑hu.unit⁻¹, by rw [← mul_add, ← map_add]; exact hu.val_inv_mul⟩
    obtain ⟨ψ₁, hψ₁⟩ := (isAway_awayHom (R := R) f).lift
      ((awayHom R (awayHom R (f + g) f)).comp (awayHom R (f + g))) (isAway_awayHom (R := R) (awayHom R (f + g) f)).unit
    obtain ⟨ψ₂, hψ₂⟩ := (isAway_awayHom (R := R) g).lift
      ((awayHom R (awayHom R (f + g) g)).comp (awayHom R (f + g))) (isAway_awayHom (R := R) (awayHom R (f + g) g)).unit
    have h1 : IsLiftAlong y₀ ((awayHom R (awayHom R (f + g) f)).comp (awayHom R (f + g))) (spMap ψ₁ ≫ y₁) := by
      have := hy₁.map ψ₁; rwa [hψ₁] at this
    have h2 : IsLiftAlong y₀ ((awayHom R (awayHom R (f + g) g)).comp (awayHom R (f + g))) (spMap ψ₂ ≫ y₂) := by
      have := hy₂.map ψ₂; rwa [hψ₂] at this
    exact exists_isLiftAlong_of_isCoprime hv hJ hcop h1 h2
  have hmax : ∀ m : Ideal A, m.IsMaximal →
      ∃ f ∈ {f : A | ∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y}, f ∉ m := by
    intro m hm
    have := hm.isPrime
    have hJm : RingHom.ker (Ideal.Quotient.mkₐ R J) ≤ m := by
      intro x hx
      have hxJ : x ∈ J := by simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hx
      have h2 : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hxJ 2
      rw [hJ, Ideal.mem_bot] at h2
      exact hm.isPrime.mem_of_pow_mem 2 (h2 ▸ m.zero_mem)
    have hm' : (m.map (Ideal.Quotient.mkₐ R J)).IsPrime :=
      Ideal.map_isPrime_of_surjective (Ideal.Quotient.mkₐ_surjective R J) hJm
    obtain ⟨fb, hfb, B, _, _, j, hj, hchart⟩ := exists_local_chart y₀ _ hm'
    have := hj
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J fb
    refine ⟨f, ?_, fun hf => hfb (Ideal.mem_map_of_mem _ hf)⟩
    have hI : (J.map (awayHom R f)) ^ 2 = ⊥ := map_sq hJ _
    obtain ⟨ψ₀, hψ₀⟩ := hchart (Localization.Away f ⧸ J.map (awayHom R f))
      (Ideal.quotientMapₐ (J.map (awayHom R f)) (awayHom R f) Ideal.le_comap_map)
      ((isAway_awayHom (R := R) f).unit.map (Ideal.Quotient.mkₐ R (J.map (awayHom R f))))
    have := smooth_of_chart j
    refine ⟨spMap (Algebra.FormallySmooth.lift (J.map (awayHom R f)) ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩ ψ₀) ≫ j,
      isLiftAlong_of_quotient ?_⟩
    rw [hψ₀, ← Category.assoc, spMap_comp]
    congr 2
    ext x
    exact Algebra.FormallySmooth.mk_lift _ _ _ x
  have hspan := span_eq_top_of_forall_maximal hmax
  have h1 : (1 : A) ∈ Ideal.span {f : A | ∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y} :=
    hspan ▸ Submodule.mem_top
  have hL1 : ∃ y : sp (Localization.Away (1 : A)) ⟶ G, IsLiftAlong y₀ (awayHom R 1) y :=
    Submodule.span_induction (p := fun x _ => ∃ y : sp (Localization.Away x) ⟶ G, IsLiftAlong y₀ (awayHom R x) y)
      (fun x hx => hx) hzero (fun x y _ _ hx hy => hadd x y hx hy) (fun c x _ hx => hmul c x hx) h1
  obtain ⟨y1, hy1⟩ := hL1
  have hy1' : IsLiftAlong y₀ ((awayHom R (1 : A)).comp (AlgHom.id R A)) y1 := by rw [AlgHom.comp_id]; exact hy1
  obtain ⟨y, hy⟩ := exists_isLiftAlong_of_isCoprime hv hJ isCoprime_one_left hy1' hy1'
  refine ⟨y, ?_⟩
  have := hy (A ⧸ J) (Ideal.Quotient.mkₐ R J) (AlgHom.id R _) (by rw [AlgHom.comp_id, AlgHom.id_comp])
  rw [ptsMap_apply, this, spMap_id, Category.id_comp]
end GlobalTheory.SqZero
