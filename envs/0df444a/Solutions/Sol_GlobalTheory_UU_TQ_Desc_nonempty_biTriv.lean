-- Prove2me | solution 1 for GlobalTheory.UU.TQ.Desc.nonempty_biTriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:11.46508+00:00
-- url     : https://prove2.me/submissions/e26c46f2-3bdf-4396-92cf-5abdba6cc5d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
import Theorems.Thm_GlobalTheory_UU_TQ_comp_i_q
import Theorems.Thm_GlobalTheory_UU_TQ_Desc_cubV_torus
import Theorems.Thm_GlobalTheory_CubTransport_exists_pmaps
import Theorems.Thm_GlobalTheory_CubTransport_val_pmaps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
private theorem comp_one_uniformization {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (x : T ⟶ T') :
    x ≫ (1 : T' ⟶ G) = 1 := by
  show x ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit _)]
private theorem one_comp_of_isMonHom' {S : Scheme.{0}} {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) [IsMonHom q]
    {T : Over S} : (1 : T ⟶ G) ≫ q = 1 := by
  show (toUnit _ ≫ η) ≫ q = toUnit _ ≫ η
  rw [Category.assoc, IsMonHom.one_hom]
private theorem oneGen_isGen_uniformization {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  unfold LB.Gen.IsGen
  simp [LB.oneGen]
  intro i j
  unfold LB.LinComb
  simp
end GlobalTheory.UU
end
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
namespace TQ.Desc
theorem _root_.solution {Q : TQ G X} {P : CP G} (D : Q.Desc P) : Nonempty (BiTriv P.c Q.i) := by
  have hi := Q.i_hom
  have hq := Q.q_hom
  have hw : PGen D.w := (isGen_iff D.w).1 D.map.gen
  have hOe : (Oε : Fin 4 → ℤ) = ![1, -1, -1, 1] := rfl
  let φ : Fin 4 → ((splitTorus S X ⊗ G).left ⟶ Q.B.left) := ![(snd (splitTorus S X) G ≫ Q.q).left,
    (1 : splitTorus S X ⊗ G ⟶ Q.B).left, (snd (splitTorus S X) G ≫ Q.q).left, (1 : splitTorus S X ⊗ G ⟶ Q.B).left]
  have hF : FormEq (K := PEmpty) (K' := Fin 4) PEmpty.elim PEmpty.elim φ Oε := by
    intro U _ h
    simp [Fin.prod_univ_four, hOe, φ]
  obtain ⟨t, ht, htv⟩ := exists_gen D.M.L.isLB hF (LB.oneGen D.M.L.L) (oneGen_isGen_uniformization _)
  have hc : ∀ k, lamφ Q.i k ≫ Q.q.left = 𝟙 _ ≫ φ k := by
    intro k
    fin_cases k
    · show ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left ≫ Q.q.left =
        𝟙 _ ≫ (snd (splitTorus S X) G ≫ Q.q).left
      rw [Category.id_comp, ← Over.comp_left, MonObj.mul_comp, TQ.comp_i_q, _root_.one_mul]
    · show (fst (splitTorus S X) G ≫ Q.i).left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⊗ G ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left, TQ.comp_i_q]
    · show (snd (splitTorus S X) G).left ≫ Q.q.left = 𝟙 _ ≫ (snd (splitTorus S X) G ≫ Q.q).left
      rw [Category.id_comp, Over.comp_left]
    · show (1 : splitTorus S X ⊗ G ⟶ G).left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⊗ G ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left, one_comp_of_isMonHom']
  obtain ⟨a, ha, hpm⟩ := CubTransport.exists_pmaps hw D.M.L.isLB P.L.isLB (𝟙 _) hc t ht
  have key : ∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left)
      (J : (T.left ⟶ Q.B.left) → D.M.L.L.ι) (J' : (T.left ⟶ G.left) → P.L.L.ι), Good D.M.L.L z J →
      Good P.L.L z J' → val a (lift t x).left z J' =
        (gw D.w ((t ≫ Q.i) * x).left z (J (((t ≫ Q.i) * x).left ≫ Q.q.left)) (J' ((t ≫ Q.i) * x).left) *
          (gw D.w (t ≫ Q.i).left z (J ((t ≫ Q.i).left ≫ Q.q.left)) (J' (t ≫ Q.i).left))⁻¹ *
          (gw D.w x.left z (J (x.left ≫ Q.q.left)) (J' x.left))⁻¹ *
          gw D.w (1 : T ⟶ G).left z (J ((1 : T ⟶ G).left ≫ Q.q.left)) (J' (1 : T ⟶ G).left))⁻¹ := by
    intro T t x z J J' hJ hJ'
    have e1 := CubTransport.val_pmaps hc hpm (lift t x).left hJ hJ'
    rw [htv _ _ _ _ hJ, val_one] at e1
    simp only [Fin.prod_univ_four] at e1
    have k0 : (lift t x).left ≫ lamφ Q.i 0 = ((t ≫ Q.i) * x).left := by
      show (lift t x).left ≫ ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left = _
      rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
    have k1 : (lift t x).left ≫ lamφ Q.i 1 = (t ≫ Q.i).left := by
      show (lift t x).left ≫ (fst (splitTorus S X) G ≫ Q.i).left = _
      rw [← Over.comp_left, lift_fst_assoc]
    have k2 : (lift t x).left ≫ lamφ Q.i 2 = x.left := by
      show (lift t x).left ≫ (snd (splitTorus S X) G).left = _
      rw [← Over.comp_left, lift_snd]
    have k3 : (lift t x).left ≫ lamφ Q.i 3 = (1 : T ⟶ G).left := by
      show (lift t x).left ≫ (1 : splitTorus S X ⊗ G ⟶ G).left = _
      rw [← Over.comp_left, comp_one_uniformization]
    have o0 : Oε 0 = 1 := rfl
    have o1 : Oε 1 = -1 := rfl
    have o2 : Oε 2 = -1 := rfl
    have o3 : Oε 3 = 1 := rfl
    rw [k0, k1, k2, k3, o0, o1, o2, o3] at e1
    simp only [zpow_one, zpow_neg_one, Category.comp_id] at e1
    exact eq_inv_of_mul_eq_one_right e1.symm
  refine ⟨⟨a, ha, ?_, ?_⟩⟩
  · intro T t t' x z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hv := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.2 (t ≫ Q.i) (t' ≫ Q.i) x
    rw [TQ.Desc.cubV_torus D hJ _ t (t' ≫ Q.i) x, _root_.one_mul] at hv
    rw [key T (t * t') x z J J' hJ hJ', key T t x z J J' hJ hJ', key T t' x z J J' hJ hJ', MonObj.mul_comp]
    rw [eq_inv_mul_of_mul_eq hv.symm]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro T t x x' z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hv := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.2 (t ≫ Q.i) x x'
    rw [TQ.Desc.cubV_torus D hJ _ t x x', _root_.one_mul] at hv
    rw [key T t (x * x') z J J' hJ hJ', key T t x z J J' hJ hJ', key T t x' z J J' hJ hJ',
      show (t ≫ Q.i) * (x * x') = (t ≫ Q.i) * x * x' from (_root_.mul_assoc _ _ _).symm]
    rw [eq_inv_mul_of_mul_eq hv.symm]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end TQ.Desc
end GlobalTheory.UU
