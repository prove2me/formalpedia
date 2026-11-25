-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:30:02.250578+00:00
-- url     : https://prove2.me/submissions/6bbdc474-17cc-4cd1-ba10-b0d0230085bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
import Theorems.Thm_GlobalTheory_LevCover_exists_spMap
import Theorems.Thm_P2M_GlobalTheory_LevCover_spMap_inj__60b6352f6bfd
import Theorems.Thm_P2M_GlobalTheory_LevCover_spMap_comp___b854f9bdcdc0
import Theorems.Thm_GlobalTheory_LevCover_map_fnOn
import Theorems.Thm_GlobalTheory_LevCover_datum_free
import Theorems.Thm_GlobalTheory_LevCover_act_nsmul
import Theorems.Thm_GlobalTheory_LevCover_ClopenCond_and
import Theorems.Thm_GlobalTheory_LevCover_ClopenCond_forall_of_finite
import Theorems.Thm_GlobalTheory_LevCover_RepTors_clopenCond
import Theorems.Thm_GlobalTheory_LevCover_add_map_nsmul
import Theorems.Thm_GlobalTheory_LevCover_exists_finite_mod
import Theorems.Thm_GlobalTheory_LevCover_exists_sub
import Theorems.Thm_GlobalTheory_LevCover_finiteEtale_tensor
import Theorems.Thm_GlobalTheory_LevelTwist_twist_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LevelTwist.twist_ev



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution (t : SAB H S) {B L : Type} [Field B] [CharZero B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (s : S ⟶ Sp B) {N : ℕ} (hN : 0 < N) {ξ : Lˣ} (hξ : ξ ^ N = 1)
    {Z : Over S} {et : D.La → (Z ⟶ t.G)} (R : RepTors t.G N D.La Z et)
    (hW : ∀ (T : Over S) (x y : T ⟶ t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
      c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs t.G t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (W : Over S) (α : D.La → (W ⟶ t.G)), IsFinite W.hom ∧ Etale W.hom ∧ (∀ a c, α (a + c) = α a * α c) ∧
      (∀ a, α a ^ N = 1) ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
        ∀ α' : D.La → (Over.mk x ⟶ t.G), (∀ a c, α' (a + c) = α' a * α' c) → (∀ a, α' a ^ N = 1) →
          ((∃ w : Over.mk x ⟶ W, ∀ a, w ≫ α a = α' a) ↔ ∃ β' : L →+* k, β'.comp (algebraMap B L) = β ∧
            (∀ (c : 𝓞 E) a, α' (c • a) = α' a ≫ t.act.act c) ∧
            ∀ a b, Out.WeilIs t.G t.PP.L N (α' a) (α' b) (unitOn (Units.map β'.toMonoidHom ξ ^ D.EF a b))) := by
  obtain ⟨hfree, hfin⟩ := datum_free D
  have hLf : IsFinite (spMap (algebraMap B L)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hLe : Etale (spMap (algebraMap B L)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
    have : Algebra.FinitePresentation B L := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  let C : Over S := Over.mk (pullback.fst s (spMap (algebraMap B L)))
  have hC1 : IsFinite C.hom := inferInstanceAs (IsFinite (pullback.fst s (spMap (algebraMap B L))))
  have hC2 : Etale C.hom := inferInstanceAs (Etale (pullback.fst s (spMap (algebraMap B L))))
  have := R.1
  have := R.2.1
  obtain ⟨hY1, hY2⟩ := finiteEtale_tensor Z C
  let g : (Z ⊗ C).left ⟶ Sp L := (snd Z C).left ≫ pullback.snd s (spMap (algebraMap B L))
  have hg : g ≫ spMap (algebraMap B L) = (Z ⊗ C).hom ≫ s := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ s) (Over.w (snd Z C))
  let y : D.La → (Z ⊗ C ⟶ t.G) := fun a => fst Z C ≫ et a
  have yadd : ∀ a c, y (a + c) = y a * y c := fun a c => by simp only [y, R.2.2.1, MonObj.comp_mul]
  have ypow : ∀ a, y a ^ N = 1 := fun a => by simp only [y]; rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one]
  have ymod : ∀ a c, y (a + N • c) = y a := fun a c => by rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap B L).injective
  have hu : IsUnit (N : Γ((Z ⊗ C).left, ⊤)) := by
    have := (IsUnit.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')).map (fnOn g)
    rwa [map_natCast] at this
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La hN
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod (𝓞 E) hN
  have c1 : ClopenCond (Z ⊗ C) fun _ h => ∀ (c : 𝓞 E) a, h ≫ y (c • a) = h ≫ y a ≫ t.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := t.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ t.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := t.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, t.act.add, MonObj.comp_mul, act_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond (Z ⊗ C) fun _ h => ∀ p : D.La × D.La, Out.WeilIs t.G t.PP.L N (h ≫ y p.1) (h ≫ y p.2)
      (Units.map (h.left.appTop).hom.toMonoidHom (Units.map (fnOn g).toMonoidHom (ξ ^ D.EF p.1 p.2))) := by
    refine ClopenCond.forall_of_finite (Prod.map q q) (fun p => hW _ _ _ _ hu (ypow _) (ypow _) ?_)
      fun p p' e T' h Hc => ?_
    · rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow, map_one]
    · obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := p'
      obtain ⟨c, rfl⟩ := hq a a' (congrArg Prod.fst e)
      obtain ⟨d, rfl⟩ := hq b b' (congrArg Prod.snd e)
      have : ξ ^ D.EF (a + N • c) (b + N • d) = ξ ^ D.EF a b := by
        have : D.EF (a + N • c) (b + N • d) = D.EF a b + N * (D.EF a d + D.EF c (b + N • d)) := by
          simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
          ring
        rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, _root_.mul_one]
      dsimp only at Hc ⊢
      rwa [ymod, ymod, this]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, -, Hi⟩ := exists_sub U hU
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, ypow, MonObj.comp_one], fun k _ x β hx α' hadd hpow => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨h1, h2⟩ := (HU _ (w ≫ i)).2 ((Hi _ _).2 ⟨w, rfl⟩)
    obtain ⟨β', hβ'⟩ := exists_spMap (A := k) ((w ≫ i).left ≫ g)
    refine ⟨β', spMap_inj' ?_, fun c a => ?_, fun a b => ?_⟩
    · rw [← spMap_comp'', ← hβ', ← hx, Category.assoc, hg, ← Category.assoc]
      exact congrArg (· ≫ s) (Over.w (w ≫ i))
    · rw [← hw, ← hw, ← Category.assoc, h1]
      simp only [Category.assoc]
    · have := h2 (a, b)
      rw [map_fnOn g _ β' hβ', map_zpow, Category.assoc, Category.assoc, hw, hw] at this
      exact this
  · rintro ⟨β', hβ', h1, h2⟩
    obtain ⟨z, hz, -⟩ := R.2.2.2.2 _ α' hadd hpow
    let c : Over.mk x ⟶ C := Over.homMk (pullback.lift x (spMap β') (by rw [hx, spMap_comp'', hβ']))
      (pullback.lift_fst _ _ _)
    have hy : ∀ a, lift z c ≫ y a = α' a := fun a => by simp only [y]; rw [lift_fst_assoc, hz]
    have hg' : (lift z c).left ≫ g = spMap β' := by
      simp only [g]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact pullback.lift_snd _ _ _
    obtain ⟨w, hw⟩ := (Hi _ (lift z c)).1 ((HU _ _).1 ⟨fun c a => by rw [hy, ← Category.assoc, hy, h1], fun p => by
      rw [map_fnOn g _ β' hg', map_zpow, hy, hy]
      exact h2 _ _⟩)
    exact ⟨w, fun a => by rw [← Category.assoc, hw, hy]⟩
end GlobalTheory.LevCover
