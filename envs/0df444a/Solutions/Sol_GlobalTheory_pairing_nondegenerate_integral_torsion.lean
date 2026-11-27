-- Prove2me | solution 1 for GlobalTheory.pairing_nondegenerate_integral_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:08.364928+00:00
-- url     : https://prove2.me/submissions/e0683f7e-177a-48ca-9950-49d843279db9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingNondegenerateIntegralTorsion
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_PGsh_a1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
section Transfer
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)
private theorem pfTie_prod1 {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift (x * x') y).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x' y).left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2) = CartesianMonoidalCategory.lift (x * x') y := by
    rw [comp_lift]
    congr 1
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
    · simp [x3]
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2) = CartesianMonoidalCategory.lift x' y := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]
private theorem pfTie_prod2 {T : Over S} (x y y' : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift x (y * y')).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x y').left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2)) = CartesianMonoidalCategory.lift x (y * y') := by
    rw [comp_lift]
    congr 1
    · simp [x3]
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y' := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]
private theorem pfTie_gen {T : Over S} (x y : T ⟶ G) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb P (K := Fin 4) ![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] ![1, -1, -1, 1]), t.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        val t ρ.left z J = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  induction n with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ 0) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ 0)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen P (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun T' ρ z J hJ => ((hv _ _ z J hJ).trans (val_one _)).trans (by simp)⟩
  | succ n ih =>
    obtain ⟨t, ht, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ (n + 1)) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left,
        (CartesianMonoidalCategory.lift x (y ^ (n + 1))).left, (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := ULift.{0} (Fin 3) ⊕ ULift.{0} (Fin 3)) (U := U) _
          (c := ∏ i, h ((![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
            (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] : Fin 4 → _) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i) rfl
          (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := ULift.{0} (Fin 3)) (U := U) _ (pfTie_prod1 (x ^ n) x y h)
            (DVR.prod_neg _ _ (pfTie_prod2 x (y ^ n) y h)))).trans ?_
        rw [pow_succ x, pow_succ y]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
        abel)
      (LB.mulGen P _ _ _ _ t (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left)
        (LB.invGen P _ _ (LB.pullGen P _ _ β.law2 (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left))))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))))
    refine ⟨t', ht', fun T' ρ z J hJ => ?_⟩
    have p₁ : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n := map_pow (preHom ρ) _ _
    have p₂ : ρ ≫ (y ^ n) = (ρ ≫ y) ^ n := map_pow (preHom ρ) _ _
    have q₁ : ρ.left ≫ (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left = (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ n) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₁]
    have q₂ : ρ.left ≫ (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left = (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ n) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₂]
    refine ((hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T' ρ z J hJ)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (congrArg (val β.law1 · z J) q₁))
        ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans (congrArg (val β.law2 · z J) q₂))))))))).trans ?_
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_inv, _root_.mul_mul_mul_comm]
private theorem pfTie_unit {T : Over S} (x y : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        gm ρ.left z ⊤ a = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  obtain ⟨u, hu, hw⟩ := pfTie_gen β x y n
  obtain ⟨t, -, hv⟩ := exists_gen β.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      rw [hx, hy]
      simp [Fin.prod_univ_succ]) u hu
  have le : (⊤ : T.left.Opens) ≤ LB.wchart P (PEmpty.elim : PEmpty → (T.left ⟶ (G ⊗ G).left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun T' ρ z J hJ => ?_⟩
  rw [← hw T' ρ z J hJ, ← hv _ _ z J hJ, val_of t ρ.left z J PEmpty.elim (fun k => k.elim)]
  exact gm_res ρ.left z le trivial _
private theorem pfTie_local (R : Type) [CommRing R] [IsLocalRing R] (a : Γ(Spec (CommRingCat.of R), ⊤)ˣ)
    (h : gm (𝟙 (Spec (CommRingCat.of R))) (IsLocalRing.closedPoint R) ⊤ a = 1) : a = 1 := by
  apply Units.ext
  have e := congrArg (fun u => (stalkClosedPointIso (CommRingCat.of R)).hom.hom (Units.val u)) h
  have g := congrArg (fun q => q.hom a.val) (germ_stalkClosedPointIso_hom (CommRingCat.of R))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at g
  have e' : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a.val = 1 :=
    g.symm.trans ((congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gm_val (𝟙 _) _ ⊤ trivial a)).symm.trans
      (e.trans (map_one _)))
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (e'.trans (map_one _).symm)
end Transfer
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (b : ∀ R x y, B.P R x y)
    (J : ∀ R : LAlg R₀, ((sp (R₀ := R₀) (R : Type)).left ⟶ (G ⊗ G).left) → P.1),
    (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    (∀ R : LAlg R₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P (Z := (sp (R₀ := R₀) (R : Type)).left) (IsLocalRing.closedPoint (R : Type)) (J R)) →
    (∀ (R : LAlg R₀) x x' y, B.add1 (b R x y) (b R x' y) =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R (x + x') y)) →
    (∀ (R : LAlg R₀) x y y', B.add2 (b R x y) (b R x y') =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R x (y + y'))) →
    ∀ (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), p ≠ 0 → v.Integers (O : Type) → Smooth G.hom →
    IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := R₀) C) ≫ x) (fst G (sp (R₀ := R₀) C))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : B.G O, p • x = 0 → (∀ y : B.G O, p • y = 0 → B.IsPairing p x y 1) → x = 0) := by
  intro FRM PFF TORS BIV R₀ _ G _ _ P β B e b J hb hadd _ hJ h1 h2 O C _ _ _ v _ _ _ p hp hv hsm hfin hfl hsurj hnd x hx H
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := Nat.exists_eq_succ_of_ne_zero hp
  have e0 : e O 0 = 1 := by
    have := hadd O 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have en : ∀ (k : ℕ) (w : B.G O), e O (k • w) = e O w ^ k := fun k w => by
    induction k with
    | zero => rw [zero_nsmul, pow_zero, e0]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  obtain ⟨j, hj⟩ : ∃ j : sp (R₀ := R₀) C ⟶ sp (R₀ := R₀) (O : Type), j = spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) :=
    ⟨_, rfl⟩
  have T := (TORS G O C v (N + 1) hv hfin hsurj).2
  rw [← hj] at T
  have hxp : e O x ^ (N + 1) = 1 := by rw [← en, hx, e0]
  have j1 : j ≫ (1 : sp (R₀ := R₀) (O : Type) ⟶ G) = 1 := map_one (preHom j)
  have key : j ≫ e O x = 1 := by
    refine PFF _ G P β C (Spec.map (CommRingCat.ofHom (algebraMap R₀ C))) (N + 1) (Nat.cast_ne_zero.2 hp) hsm hfin hfl
      hsurj hnd (j ≫ e O x) ((map_pow (preHom j) _ _).symm.trans ((congrArg (j ≫ ·) hxp).trans j1))
      (fun y hy z Jc hJc => ?_)
    obtain ⟨y₀, ⟨hy₀, rfl⟩, -⟩ := T y hy
    obtain ⟨y', rfl⟩ := (hb O).2 y₀
    have hy' : (N + 1) • y' = 0 := (hb O).1 (by rw [en, hy₀, e0])
    have F := (((FRM B b _ _ h1 h2).1 O N x y' 1).1 (H y' hy')).2.2
    obtain ⟨a₁, -, a₂, -, -⟩ := BIV _ G P β (sp (R₀ := R₀) (O : Type)) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    have b₁ := a₁ 1 1 (e O x) (e O y')
    have b₂ := a₂ (e O x) 1 1 (e O y')
    simp only [_root_.one_mul] at b₁ b₂
    have c₁ := mul_left_cancel b₁
    have c₂ := mul_left_cancel b₂
    obtain ⟨a, ha⟩ := pfTie_unit β (e O x) (e O y') (N + 1) hxp hy₀
    have a1 : a = 1 := by
      apply pfTie_local (O : Type) a
      have g := ha _ (𝟙 _) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      refine Eq.trans g ?_
      simp only [Category.id_comp]
      rw [Finset.prod_range_succ', Finset.prod_range_succ', pow_zero, pow_zero, ← c₁, ← c₂, mul_inv_eq_one]
      simp only [en, e0] at F
      rw [← map_prod, ← map_prod, ← map_mul, ← map_mul, eq_comm, div_eq_one] at F
      have inj := Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of (O : Type))).hom.hom.toMonoidHom)
        (stalkClosedPointIso (CommRingCat.of (O : Type))).commRingCatIsoToRingEquiv.injective F
      exact (mul_comm _ _).trans (inj.trans (mul_comm _ _))
    have g := ha _ j z Jc hJc
    rw [a1, map_one, eq_comm, mul_inv_eq_one] at g
    exact g
  obtain ⟨w, -, hw⟩ := T 1 (one_pow _)
  exact (hb O).1 (((hw _ ⟨hxp, key⟩).trans (hw 1 ⟨one_pow _, j1⟩).symm).trans e0.symm)
end GlobalTheory
