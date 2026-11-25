-- Prove2me | solution 1 for GlobalTheory.UU.exists_isCPMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:48.891225+00:00
-- url     : https://prove2.me/submissions/0fbca90f-9d8a-44a7-ad1a-427f46778277

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_GlobalTheory_UU_one_left_comp
import Theorems.Thm_GlobalTheory_UU_inv_left_comp
import Theorems.Thm_GlobalTheory_UU_sym_cub_alg
import Theorems.Thm_GlobalTheory_CubTransport_exists_pmaps
import Theorems.Thm_GlobalTheory_CubTransport_isCub_of_twist
import Theorems.Thm_GlobalTheory_CubTransport_val_pmaps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
namespace GlobalTheory.UU
theorem _root_.solution (P : CP G)
    (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (L' : LB G'.left) (hL' : L'.IsLB) (w : LB.Iso L' (P.L.L.pull F)) (hg : w.IsGen) :
    ∃ (rig : LB.Gen (L'.pull (eSec G'))) (hr : rig.IsGen) (c : CubicalStr G' ⟨L', rig, hL', hr⟩) (s : _) (h₁ : _)
      (h₂ : _) (h₃ : _), IsCPMap ⟨⟨L', rig, hL', hr⟩, c, s, h₁, h₂, h₃⟩ P f F hw w := by
  have hw' : PGen w := (isGen_iff w).1 hg
  have hL := P.L.isLB
  have he : eSec G' ≫ F = f ≫ eSec G := by
    have h1 := one_left_comp mul (𝟙_ (Over S'))
    rw [one_left] at h1
    simpa using h1
  obtain ⟨rig, hr, hrm⟩ := CubTransport.exists_pmaps hw' hL hL' (φ' := fun _ : PUnit => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) f (fun _ => he) P.L.rig P.L.rigGen
  have hc2 : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := by
    have h0 : ((𝟙 G' : G' ⟶ G').left ≫ (ι[G']).left) ≫ F = ((𝟙 G' : G' ⟶ G').left ≫ F) ≫ (ι[G]).left :=
      inv_left_comp mul (𝟙 G')
    intro k
    fin_cases k
    · simpa using h0
    · simp
  obtain ⟨s, hs, hsm⟩ := CubTransport.exists_pmaps hw' hL hL' (φ' := ![(ι[G']).left, 𝟙 G'.left])
    (φ := ![(ι[G]).left, 𝟙 G.left]) (ε := ![1, -1]) F hc2 P.sym P.sym_gen
  let σ : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
    lift (toBase hw (x3 G' 0)) (lift (toBase hw (x3 G' 1)) (toBase hw (x3 G' 2)))
  have hσ : ∀ i, σ ≫ x3 G i = toBase hw (x3 G' i) := by
    intro i
    fin_cases i <;> simp [σ, x3]
  have hc3 : ∀ I : thK, thφ G' (x3 G') I ≫ F = σ.left ≫ thφ G (x3 G) I := by
    intro I
    have e1 : toBase hw (psum G' (x3 G') I.down) = psum G (fun i => toBase hw (x3 G' i)) I.down :=
      psum_hom (toBaseHom mul (G3 G')) (x3 G') I.down
    have e2 : σ ≫ psum G (x3 G) I.down = psum G (fun i => σ ≫ x3 G i) I.down := psum_hom (preHom σ) (x3 G) I.down
    simp only [hσ] at e2
    have e3 := congrArg Over.Hom.left (e1.trans e2.symm)
    show (psum G' (x3 G') I.down).left ≫ F = σ.left ≫ (psum G (x3 G) I.down).left
    simpa [toBase] using e3
  obtain ⟨t', ht', htm⟩ := CubTransport.exists_pmaps hw' hL hL' (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G))
    (ε := thε) σ.left hc3 P.c.t P.c.isGen
  have key1 : ∀ (T : Over S') (z : T.left) (J0 : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ G'.left) → L'.ι),
      Good P.L.L z J0 → Good L' z J →
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ f) z J0 =
        gw w (1 : T ⟶ G').left z (J0 ((1 : T ⟶ G').left ≫ F)) (J (1 : T ⟶ G').left) * val rig T.hom z J := by
    intro T z J0 J hJ0 hJ
    rw [CubTransport.val_pmaps (fun _ => he) hrm T.hom hJ0 hJ, one_left]
    simp only [Fintype.prod_unique, zpow_one]
  have key2 : ∀ (T : Over S') (z : T.left) (J0 : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ G'.left) → L'.ι),
      Good P.L.L z J0 → Good L' z J → ∀ a : T ⟶ G',
      val P.sym (a.left ≫ F) z J0 = gw w (a⁻¹).left z (J0 ((a⁻¹).left ≫ F)) (J (a⁻¹).left) *
        (gw w a.left z (J0 (a.left ≫ F)) (J a.left))⁻¹ * val s a.left z J := by
    intro T z J0 J hJ0 hJ a
    rw [CubTransport.val_pmaps hc2 hsm a.left hJ0 hJ, prod_sym a (fun ψ => gw w ψ z (J0 (ψ ≫ F)) (J ψ))]
  have key3 : ∀ (T : Over S') (z : T.left) (J0 : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ G'.left) → L'.ι),
      Good P.L.L z J0 → Good L' z J → ∀ a b c : T ⟶ G',
      cubV P.c z J0 (toBase hw a) (toBase hw b) (toBase hw c) =
        gw w (a * b * c).left z (J0 ((a * b * c).left ≫ F)) (J (a * b * c).left) *
        (gw w (a * b).left z (J0 ((a * b).left ≫ F)) (J (a * b).left))⁻¹ *
        (gw w (a * c).left z (J0 ((a * c).left ≫ F)) (J (a * c).left))⁻¹ *
        (gw w (b * c).left z (J0 ((b * c).left ≫ F)) (J (b * c).left))⁻¹ *
        gw w a.left z (J0 (a.left ≫ F)) (J a.left) * gw w b.left z (J0 (b.left ≫ F)) (J b.left) *
        gw w c.left z (J0 (c.left ≫ F)) (J c.left) *
        (gw w (1 : T ⟶ G').left z (J0 ((1 : T ⟶ G').left ≫ F)) (J (1 : T ⟶ G').left))⁻¹ *
        val (φ := thφ G' (x3 G')) (ε := thε) t' (lift a (lift b c)).left z J := by
    intro T z J0 J hJ0 hJ a b c
    let ρ : Over.mk (T.hom ≫ f) ⟶ Over.mk ((G3 G').hom ≫ f) := Over.homMk (lift a (lift b c)).left (by
      show (lift a (lift b c)).left ≫ (G3 G').hom ≫ f = T.hom ≫ f
      rw [← Category.assoc, Over.w])
    have q : ∀ (i : Fin 3) (d : T ⟶ G'), lift a (lift b c) ≫ x3 G' i = d → toBase hw d = ρ ≫ toBase hw (x3 G' i) := by
      intro i d hd
      ext
      show d.left ≫ F = (lift a (lift b c)).left ≫ ((x3 G' i).left ≫ F)
      rw [← Category.assoc, ← Over.comp_left, hd]
    have hl : lift (toBase hw a) (lift (toBase hw b) (toBase hw c)) = ρ ≫ σ := by
      simp only [σ, comp_lift]
      rw [← q 0 a (by simp [x3]), ← q 1 b (by simp [x3]), ← q 2 c (by simp [x3])]
    have e' : cubV P.c z J0 (toBase hw a) (toBase hw b) (toBase hw c) =
        val (φ := thφ G (x3 G)) (ε := thε) P.c.t ((lift a (lift b c)).left ≫ σ.left) z J0 := by
      show val (φ := thφ G (x3 G)) (ε := thε) P.c.t (lift (toBase hw a) (lift (toBase hw b) (toBase hw c))).left z J0 = _
      rw [hl]
      rfl
    rw [e', CubTransport.val_pmaps hc3 htm (lift a (lift b c)).left hJ0 hJ]
    congr 1
    exact prod_cub a b c (fun ψ => gw w ψ z (J0 (ψ ≫ F)) (J ψ))
  have hcub : ∀ (T : Over S') (z : T.left) (J : (T.left ⟶ G'.left) → L'.ι), Good L' z J →
      IsCub (CubTransport.thV (L := ⟨L', rig, hL', hr⟩) t' z J) := by
    intro T z J hJ
    obtain ⟨J0, hJ0⟩ := exists_good_pt hL z
    exact CubTransport.isCub_of_twist (isCub_cubV (T := Over.mk (T.hom ≫ f)) P.c hJ0) (toBaseHom mul T)
      (fun a => gw w a.left z (J0 (a.left ≫ F)) (J a.left)) (fun a b c => key3 T z J0 J hJ0 hJ a b c)
  let c : CubicalStr G' ⟨L', rig, hL', hr⟩ := CubTransport.cubicalOfVal t' ht' hcub
  have hsr : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s (eSec G')) (LB.oneGen L') := by
    refine corr_of_val hL' fun y J hJ => ?_
    rw [val_pull hJ, val_one]
    obtain ⟨J0, hJ0⟩ := exists_good_pt hL y
    have k := key2 (𝟙_ (Over S')) y J0 J hJ0 hJ 1
    have one1 : (1 : 𝟙_ (Over S') ⟶ G').left = (𝟙_ (Over S')).hom ≫ eSec G' := one_left G' (𝟙_ (Over S'))
    rw [inv_one, _root_.mul_inv_cancel, _root_.one_mul, one1] at k
    have r1 : val P.sym (((𝟙_ (Over S')).hom ≫ f) ≫ eSec G) y J0 = 1 :=
      (val_pull hJ0 P.sym (eSec G) ((𝟙_ (Over S')).hom ≫ f)).symm.trans ((val_corr hJ0 P.sym_rig _).trans (val_one _))
    show val s ((𝟙_ (Over S')).hom ≫ eSec G') y J = 1
    rw [← k, Category.assoc, he, ← Category.assoc, r1]
  have hsc : ∀ (T : Over S') (x y u : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → L'.ι), Good L' z J →
      cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J =
        cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
    intro T x y u z J hJ
    obtain ⟨J0, hJ0⟩ := exists_good_pt hL z
    exact sym_cub_alg (toBaseHom mul T) (fun a => gw w a.left z (J0 (a.left ≫ F)) (J a.left))
      (θ := cubV (T := Over.mk (T.hom ≫ f)) P.c z J0) (θ' := cubV c z J) (σ := fun a => val P.sym a.left z J0) (σ' := fun a => val s a.left z J)
      (fun a b d => key3 T z J0 J hJ0 hJ a b d) (fun a => key2 T z J0 J hJ0 hJ a)
      (P.sym_cub (Over.mk (T.hom ≫ f)) (toBase hw x) (toBase hw y) (toBase hw u) z J0 hJ0)
  refine ⟨rig, hr, c, s, hs, hsr, hsc, mul, hg, ?_⟩
  intro T z J' J hJ' hJ W hW
  dsimp only
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [key1 T z J J' hJ hJ', hW]
  · rw [key2 T z J J' hJ hJ' x, hW, hW]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hc' : cubV c z J' x y u = val (φ := thφ G' (x3 G')) (ε := thε) t' (lift x (lift y u)).left z J' := rfl
    rw [id_eq, key3 T z J J' hJ hJ' x y u, hc']
    simp only [hW]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end GlobalTheory.UU
