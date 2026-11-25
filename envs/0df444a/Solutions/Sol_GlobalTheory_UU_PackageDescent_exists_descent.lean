-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.exists_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:55.777184+00:00
-- url     : https://prove2.me/submissions/e835487e-9cfb-4c08-bd0c-39e779e580d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
import Theorems.Thm_GlobalTheory_UU_PackageDescent_exists_descend_through
import Theorems.Thm_GlobalTheory_UU_PackageDescent_exists_val_cover
import Theorems.Thm_P2M_GlobalTheory_UU_PackageDescent_exists_lift_cover__77a38d08e648
import Theorems.Thm_P2M_GlobalTheory_UU_PackageDescent_diff__swap__0641a273d81f
import Theorems.Thm_P2M_GlobalTheory_UU_PackageDescent_diff__swap__a8f34ce6eb6c
import Theorems.Thm_GlobalTheory_AbelianQuotient_flat_tensorHom
import Theorems.Thm_GlobalTheory_AbelianQuotient_quasiCompact_tensorHom
import Theorems.Thm_GlobalTheory_AbelianQuotient_surjective_tensorHom
import Theorems.Thm_GlobalTheory_CubTransport_isCub_of_twist
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_cub_alg
import Theorems.Thm_GlobalTheory_UU_sym_cub_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G B : Over S} (q : G ⟶ B) [Flat q.left] [Surjective q.left]
variable [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] [IsMonHom q] [QuasiCompact q.left]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution (P : CP G) {M : LB B.left} (hM : M.IsLB) (w : LB.Iso P.L.L (M.pull q.left)) (hw : w.IsGen)
    (hcub : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x x' y u : T ⟶ G, x ≫ q = x' ≫ q →
      diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u = diff₃ (isoV q w z I J) x' y u * cubV P.c z J x' y u)
    (hsym : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x x' : T ⟶ G, x ≫ q = x' ≫ q →
      isoV q w z I J x⁻¹ * (isoV q w z I J x)⁻¹ * val P.sym x.left z J =
        isoV q w z I J x'⁻¹ * (isoV q w z I J x')⁻¹ * val P.sym x'.left z J)
    (hq : q.left ≫ B.hom = G.hom ≫ 𝟙 S) :
    ∃ (N : CP B) (w' : _), IsCPMap P N (𝟙 S) q.left hq w' := by
  have hp := (isGen_iff w).1 hw
  have hL := P.L.isLB
  let β : ∀ T : Over S, (T ⟶ G) →* (T ⟶ B) := fun T => MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q

  have he : eSec G ≫ q.left = 𝟙 _ ≫ eSec B := by
    rw [Category.id_comp, eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨rig, hr, vr⟩ := exists_descend_through hp hM hL (𝟙 _) (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec B) (ε := fun _ => 1) (fun _ => he) P.L.rig P.L.rigGen fun Z g₁ g₂ z I J _ _ e => by
      rw [Category.comp_id, Category.comp_id] at e
      rw [e]

  have hc₂ : ∀ k : Fin 2, ![(ι[G]).left, 𝟙 G.left] k ≫ q.left = q.left ≫ ![(ι[B]).left, 𝟙 B.left] k := fun k => by
    fin_cases k
    · exact congrArg (fun q => q.left) (GrpObj.inv_hom q)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  have ps : ∀ (T : Over S) (z : T.left) (I J) (x : T ⟶ G),
      (∏ k : Fin 2, gw w (x.left ≫ ![(ι[G]).left, 𝟙 G.left] k) z (I ((x.left ≫ ![(ι[G]).left, 𝟙 G.left] k) ≫ q.left))
        (J (x.left ≫ ![(ι[G]).left, 𝟙 G.left] k)) ^ (![1, -1] : Fin 2 → ℤ) k) * val P.sym x.left z J =
      isoV q w z I J x⁻¹ * (isoV q w z I J x)⁻¹ * val P.sym x.left z J := fun T z I J x =>
    congrArg₂ (· * ·) (prod_sym x (fun r => gw w r z (I (r ≫ q.left)) (J r))) rfl
  obtain ⟨s, hs, vs₀⟩ := exists_descend_through hp hM hL q.left hc₂ P.sym P.sym_gen fun Z g₁ g₂ z I J hI hJ e => by
    let T : Over S := Over.mk (g₂ ≫ G.hom)
    let k₂ : T ⟶ G := Over.homMk g₂ rfl
    let k₁ : T ⟶ G := Over.homMk g₁ (by
      change g₁ ≫ G.hom = g₂ ≫ G.hom
      rw [← Over.w q, reassoc_of% e])
    exact (ps T z I J k₁).trans ((hsym T z I J hI hJ k₁ k₂ (Over.OverMorphism.ext e)).trans (ps T z I J k₂).symm)
  have vs : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x : T ⟶ G,
      val s (x ≫ q).left z I = isoV q w z I J x⁻¹ * (isoV q w z I J x)⁻¹ * val P.sym x.left z J :=
    fun T z I J hI hJ x => (vs₀ _ x.left z I J hI hJ).trans (ps T z I J x)

  have := AbelianQuotient.flat_tensorHom q q
  have := AbelianQuotient.surjective_tensorHom q q
  have := AbelianQuotient.quasiCompact_tensorHom q q
  have := AbelianQuotient.flat_tensorHom q (q ⊗ₘ q)
  have := AbelianQuotient.surjective_tensorHom q (q ⊗ₘ q)
  have := AbelianQuotient.quasiCompact_tensorHom q (q ⊗ₘ q)
  let π : G3 G ⟶ G3 B := q ⊗ₘ q ⊗ₘ q
  have hπ : ∀ {T : Over S} (x y u : T ⟶ G),
      lift x (lift y u) ≫ π = lift (x ≫ q) (lift (y ≫ q) (u ≫ q)) := fun x y w => by
    simp [π, lift_map]
  have hφ : ∀ I, thφ G (x3 G) I ≫ q.left = π.left ≫ thφ B (x3 B) I := fun I =>
    congrArg (fun q => q.left) ((psum_hom (β (G3 G)) (x3 G) I.down).trans
      ((congrArg (fun q => psum B q I.down) (funext fun i => by
        fin_cases i <;> simp [β, π, preHom, x3])).trans (psum_hom (preHom π) (x3 B) I.down).symm))
  have pc : ∀ (T : Over S) (z : T.left) (I J) (x y u : T ⟶ G),
      (∏ k, gw w ((lift x (lift y u)).left ≫ thφ G (x3 G) k) z
        (I (((lift x (lift y u)).left ≫ thφ G (x3 G) k) ≫ q.left)) (J ((lift x (lift y u)).left ≫ thφ G (x3 G) k)) ^
          thε k) * val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t (lift x (lift y u)).left z J =
      diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u := fun T z I J x y u =>
    congrArg₂ (· * ·) (prod_cub x y u (fun r => gw w r z (I (r ≫ q.left)) (J r))) rfl
  obtain ⟨t, ht, vt₀⟩ := exists_descend_through hp hM hL π.left hφ (ε := thε) P.c.t P.c.isGen
    fun Z g₁ g₂ z I J hI hJ e => by
      let T : Over S := Over.mk (g₂ ≫ (G3 G).hom)
      let k₂ : T ⟶ G3 G := Over.homMk g₂ rfl
      let k₁ : T ⟶ G3 G := Over.homMk g₁ (by
        change g₁ ≫ (G3 G).hom = g₂ ≫ (G3 G).hom
        rw [← Over.w π, reassoc_of% e])
      have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
      obtain ⟨x, y, u, h₁⟩ : ∃ x y u, k₁ = lift x (lift y u) :=
        ⟨k₁ ≫ fst _ _, k₁ ≫ snd _ _ ≫ fst _ _, k₁ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
      obtain ⟨x', y', u', h₂⟩ : ∃ x y u, k₂ = lift x (lift y u) :=
        ⟨k₂ ≫ fst _ _, k₂ ≫ snd _ _ ≫ fst _ _, k₂ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
      rw [h₁, h₂, hπ, hπ] at e'
      have ex : x ≫ q = x' ≫ q := by simpa using e' =≫ fst _ _
      have ey : y ≫ q = y' ≫ q := by simpa using e' =≫ snd _ _ ≫ fst _ _
      have eu : u ≫ q = u' ≫ q := by simpa using e' =≫ snd _ _ ≫ snd _ _
      have a₁ : g₁ = (lift x (lift y u)).left := congrArg (fun q => q.left) h₁
      have a₂ : g₂ = (lift x' (lift y' u')).left := congrArg (fun q => q.left) h₂
      have C := isCub_cubV P.c (T := T) hJ
      have s01 : ∀ a b d : T ⟶ G, diff₃ (isoV q w z I J) a b d * cubV P.c z J a b d =
          diff₃ (isoV q w z I J) b a d * cubV P.c z J b a d := fun a b d => by
        rw [C.s01 a, diff₃_swap₁ _ a]
      have s12 : ∀ a b d : T ⟶ G, diff₃ (isoV q w z I J) a b d * cubV P.c z J a b d =
          diff₃ (isoV q w z I J) a d b * cubV P.c z J a d b := fun a b d => by
        rw [C.s12 a, diff₃_swap₂ _ a]
      have key : diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u =
          diff₃ (isoV q w z I J) x' y' u' * cubV P.c z J x' y' u' := by
        rw [hcub T z I J hI hJ x x' y u ex, s01, hcub T z I J hI hJ y y' x' u ey, s12, s01,
          hcub T z I J hI hJ u u' y' x' eu, s01, s12, s01]
      clear_value k₁ k₂
      have f := (pc T z I J x y u).trans (key.trans (pc T z I J x' y' u').symm)
      rw [← a₁, ← a₂] at f
      exact f
  let M₁ : RigLB B := ⟨M, rig, hM, hr⟩
  have vt : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x y u : T ⟶ G,
      CubTransport.thV (L := M₁) t z I (x ≫ q) (y ≫ q) (u ≫ q) =
        diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u := fun T z I J hI hJ x y u => by
    have e := (vt₀ _ (lift x (lift y u)).left z I J hI hJ).trans (pc T z I J x y u)
    rw [← Over.comp_left, hπ] at e
    exact e
  have vt' : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x y u : T ⟶ G,
      cubV P.c z J x y u = diff₃ (fun a => (isoV q w z I J a)⁻¹) x y u *
        CubTransport.thV (L := M₁) t z I (x ≫ q) (y ≫ q) (u ≫ q) := fun T z I J hI hJ x y u => by
    rw [vt T z I J hI hJ, diff₃, diff₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have cover : ∀ (T : Over S) (z : T.left) (I), Good M z I → ∀ x y u v : T ⟶ B,
      ∃ (T' : Over S) (z' : T'.left) (I' : _) (J : _) (ρ : (T ⟶ B) →* (T' ⟶ B))
        (e : (T.left.presheaf.stalk z)ˣ →* (T'.left.presheaf.stalk z')ˣ) (x' y' u' v' : T' ⟶ G),
        Good M z' I' ∧ Good P.L.L z' J ∧ Function.Injective e ∧ ρ x = β _ x' ∧ ρ y = β _ y' ∧ ρ u = β _ u' ∧
        ρ v = β _ v' ∧ (∀ a b d, e (CubTransport.thV (L := M₁) t z I a b d) =
          CubTransport.thV (L := M₁) t z' I' (ρ a) (ρ b) (ρ d)) ∧
        ∀ a, e (val s a.left z I) = val s (ρ a).left z' I' := by
    intro T z I hI x y u v
    obtain ⟨T', ρ, x', y', u', v', _, _, e₁, e₂, e₃, e₄⟩ := exists_lift_cover₄ q x y u v
    obtain ⟨z', I', e, hI', ei, ev⟩ := exists_val_cover hM ρ.left z I hI
    obtain ⟨J, hJ⟩ := exists_good_pt hL z'
    refine ⟨T', z', I', J, preHom ρ, e, x', y', u', v', hI', hJ, ei, e₁.symm, e₂.symm, e₃.symm, e₄.symm,
      fun a b d => ?_, fun a => (ev s a.left).symm⟩
    refine (ev (φ := thφ B (x3 B)) (ε := thε) t (lift a (lift b d)).left).symm.trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
  have up : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J →
      IsCub (fun a b d : T ⟶ G => CubTransport.thV (L := M₁) t z I (β _ a) (β _ b) (β _ d)) :=
    fun T z I J hI hJ => CubTransport.isCub_of_twist (isCub_cubV P.c hJ) (MonoidHom.id _)
      (fun a => (isoV q w z I J a)⁻¹) (vt' T z I J hI hJ)
  let c : CubicalStr B M₁ := CubTransport.cubicalOfVal t ht fun T z I hI => by
    refine ⟨fun x y => ?_, fun x y u => ?_, fun x y u => ?_, fun x y u v => ?_⟩
    · obtain ⟨T', z', I', J, ρ, e, x', y', -, -, hI', hJ, ei, e₁, e₂, -, -, ec, -⟩ := cover T z I hI x y x x
      apply ei
      rw [ec, map_one, map_one, e₁, e₂, ← map_one (β T')]
      exact (up T' z' I' J hI' hJ).face x' y'
    · obtain ⟨T', z', I', J, ρ, e, x', y', u', -, hI', hJ, ei, e₁, e₂, e₃, -, ec, -⟩ := cover T z I hI x y u x
      apply ei
      rw [ec, ec, e₁, e₂, e₃]
      exact (up T' z' I' J hI' hJ).s01 x' y' u'
    · obtain ⟨T', z', I', J, ρ, e, x', y', u', -, hI', hJ, ei, e₁, e₂, e₃, -, ec, -⟩ := cover T z I hI x y u x
      apply ei
      rw [ec, ec, e₁, e₂, e₃]
      exact (up T' z' I' J hI' hJ).s12 x' y' u'
    · obtain ⟨T', z', I', J, ρ, e, x', y', u', v', hI', hJ, ei, e₁, e₂, e₃, e₄, ec, -⟩ := cover T z I hI x y u v
      apply ei
      rw [map_mul, map_mul, ec, ec, ec, ec, map_mul, map_mul, e₁, e₂, e₃, e₄, ← map_mul (β T'), ← map_mul (β T')]
      exact (up T' z' I' J hI' hJ).coc x' y' u' v'
  refine ⟨⟨M₁, c, s, hs, corr_of_val hM fun y I hI => ?_, fun T x y u z I hI => ?_⟩, w,
    toBase_mul_of_isMonHom q hq, hw, fun T z J I hJ hI W hW => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt hL y
    have e := vs (𝟙_ _) y I J hI hJ 1
    rw [inv_one, mul_inv_cancel, _root_.one_mul, P.val_sym_one hJ, MonObj.one_comp, one_left] at e
    exact (val_pull hI _ _ _).trans (e.trans (val_one _).symm)
  · obtain ⟨T', z', I', J, ρ, e, x', y', u', -, hI', hJ, ei, e₁, e₂, e₃, -, ec, es⟩ := cover T z I hI x y u x
    apply ei
    have ec' : ∀ a b d, e (cubV c z I a b d) = CubTransport.thV (L := M₁) t z' I' (ρ a) (ρ b) (ρ d) := ec
    simp only [map_mul, ec', es, map_inv, e₁, e₂, e₃]
    simp only [← map_mul, ← map_inv]
    exact sym_cub_alg (MonoidHom.id _) (fun a => (isoV q w z' I' J a)⁻¹) (θ := cubV P.c z' J)
      (θ' := fun a b d => CubTransport.thV (L := M₁) t z' I' (β _ a) (β _ b) (β _ d))
      (σ := fun a => val P.sym a.left z' J) (σ' := fun a => val s (β _ a).left z' I') (vt' T' z' I' J hI' hJ)
      (fun a => by
        refine Eq.trans ?_ (congrArg (_ * ·) (vs T' z' I' J hI' hJ a)).symm
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, MonoidHom.id_apply]
        abel) (P.sym_cub T' x' y' u' z' J hJ)
  · obtain rfl : W = isoV q w z I J := funext hW
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · have e := vr _ T.hom z I J hI hJ
      rw [Fintype.prod_unique, zpow_one, ← one_left] at e
      exact e
    · refine (congrArg (· * _) (vs T z I J hI hJ x)).trans ?_
      rw [mul_right_comm, inv_mul_cancel_right]
    · let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
      have e : ∀ a : T ⟶ G, toBase hq a = ρ ≫ a ≫ q := fun a => Over.OverMorphism.ext (Category.id_comp _).symm
      have e' : (lift (toBase hq x) (lift (toBase hq y) (toBase hq u))).left =
          (lift (x ≫ q) (lift (y ≫ q) (u ≫ q))).left := by
        rw [e, e, e, ← comp_lift, ← comp_lift]; exact Category.id_comp _
      exact cub_alg ((congrArg (fun r => val (L := M) (φ := thφ B (x3 B)) (ε := thε) t r z I) e').trans
        (vt T z I J hI hJ x y u))
end GlobalTheory.UU.PackageDescent
