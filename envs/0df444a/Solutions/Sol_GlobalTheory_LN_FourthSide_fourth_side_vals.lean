-- Prove2me | solution 1 for GlobalTheory.LN.FourthSide.fourth_side_vals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:01:36.780561+00:00
-- url     : https://prove2.me/submissions/ae09a791-1819-4251-b88f-1f28e07b2fe6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourthSideRespectsRigSymmetryCube
import Theorems.Thm_GlobalTheory_LN_FourthSide_mul_left_congr
import Theorems.Thm_GlobalTheory_LN_FourthSide_cubV_congr
import Theorems.Thm_GlobalTheory_LN_FourthSide_cube_alg
import Theorems.Thm_GlobalTheory_LN_FourthSide_sym_alg
import Theorems.Thm_GlobalTheory_LN_FourthSide_rig_alg
import Theorems.Thm_GlobalTheory_LN_FourthSide_pG_mul
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_toBase_mul_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.FourthSide
set_option maxHeartbeats 1000000
namespace GlobalTheory.LN.FourthSide
theorem _root_.solution : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  intro hG R V _ _ _ _ I I' φ hle D D' A G _ _ G' _ _ U P' F hF wL hwL β hβ v hv e g' h hh hp w' hsq T z JG J hJG hJ W hW
  have hpow : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hle _
  obtain ⟨σ, hσ⟩ : ∃ σ : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
      σ ≫ thick R I e = thick V I' e ≫ spMap φ :=
    ⟨spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hpow), by rw [← Spec.map_comp, ← Spec.map_comp]; rfl⟩
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have := Cmp.mono_fstG I e G
  have hb : (T.hom ≫ σ) ≫ thick R I e = (T.hom ≫ thick V I' e) ≫ spMap φ := by
    rw [Category.assoc, hσ, Category.assoc]
  let a := toBaseHom (toBase_mul_pullback G' (thick V I' e)) T
  let b := toBaseHom (pG_mul g') T
  have ha : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (fstG I e G).left = (a x).left ≫ F := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hh).trans (Category.assoc _ _ _).symm)
  have hq : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (U.gt e).pG.left = (b x).left ≫ β := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hp.symm).trans (Category.assoc _ _ _).symm)
  have hs : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (thickObj R I e G).hom = T.hom ≫ σ := fun x => by
    rw [← cancel_mono (thick R I e), hb, Category.assoc]
    refine (congrArg ((x.left ≫ h) ≫ ·) (Over.w (fstG I e G)).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (ha x)).trans ?_)
    exact Over.w (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
  let n₀ : (T ⟶ thickObj V I' e G') → (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) :=
    fun x => Over.homMk (x.left ≫ h) (hs x)
  let n : (T ⟶ thickObj V I' e G') →* (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) := MonoidHom.mk' n₀ fun x y => by
    refine Over.OverMorphism.ext ((cancel_mono (fstG I e G).left).1 ((ha (x * y)).trans ?_))
    rw [map_mul]
    refine (congrArg (fun q => q.left) (hwL.mul _ (a x) (a y))).trans (Eq.trans ?_
      (congrArg (fun q => q.left) (toBase_mul_pullback G (thick R I e) _ (n₀ x) (n₀ y))).symm)
    exact mul_left_congr (ha x).symm (ha y).symm
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨J₀, hJ₀⟩ := exists_good_pt D.P.isLB z
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x =
    gw (U.w e) x.left z (J₀ (x.left ≫ (U.gt e).pG.left)) (fun _ => K (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : (Over.mk (T.hom ≫ thick V I' e) ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ x, W₁ x =
    gw wL x.left z (K (x.left ≫ F)) (JG x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : (Over.mk (T.hom ≫ thick V I' e) ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₂ x =
    gw v x.left z (J₀ (x.left ≫ β)) (J x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨p₁, p₂, p₃⟩ := U.w_vals e (Over.mk (T.hom ≫ σ)) z K J₀ hK hJ₀ W₀ hW₀
  obtain ⟨q₁, q₂, q₃⟩ := hwL.vals (Over.mk (T.hom ≫ thick V I' e)) z JG K hJG hK W₁ hW₁
  obtain ⟨r₁, r₂, r₃⟩ := hv.vals (Over.mk (T.hom ≫ thick V I' e)) z J J₀ hJ hJ₀ W₂ hW₂
  have sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x) := fun x => by
    have k := hsq _ x.left z _ _ _ _ (hJ₀ ((b x).left ≫ β)) (hJ (b x).left) (hK ((a x).left ≫ F)) (hJG (a x).left)
    have k₀ : W₀ (n x) = gw (U.w e) (x.left ≫ h) z (J₀ ((b x).left ≫ β)) (fun _ => K ((a x).left ≫ F)) := by
      rw [← ha, ← hq]
      exact hW₀ (n x)
    rw [k₀, hW, hW₁, hW₂]
    exact k
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · have k := sq 1
    rw [map_one, map_one, map_one] at k
    have p : val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
        ((T.hom ≫ σ) ≫ thick R I e) z J₀ = W₀ 1 * val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1)
          U.P.L.rig ((T.hom ≫ σ) ≫ thick R I e) z K := p₁
    rw [hb] at p
    exact rig_alg k p q₁ r₁
  · have p : val D.sym ((x.left ≫ h) ≫ (U.gt e).pG.left) z J₀ * W₀ (n x) =
        W₀ (n x)⁻¹ * val U.P.sym ((x.left ≫ h) ≫ (fstG I e G).left) z K := p₂ (n x)
    rw [ha, hq] at p
    have q : val U.P.sym ((x.left ≫ (fstG I' e G').left) ≫ F) z K * W₁ (a x) =
        W₁ (a x)⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG := q₂ (a x)
    have r : val D.sym ((x.left ≫ g'.pG.left) ≫ β) z J₀ * W₂ (b x) =
        W₂ (b x)⁻¹ * val D'.sym (x.left ≫ g'.pG.left) z J := r₂ (b x)
    exact sym_alg n a b sq x p q r
  · let C : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z J₀
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b u))
    let E : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z K
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a u))
    let C' : (T.left.presheaf.stalk z)ˣ := cubV D'.cub (T := Over.mk (T.hom ≫ thick V I' e)) z J (b x) (b y) (b u)
    let E' : (T.left.presheaf.stalk z)ˣ := cubV P'.c (T := Over.mk (T.hom ≫ thick V I' e)) z JG (a x) (a y) (a u)
    let C₀ : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z J₀
      ((Over.map (thick R I e)).map (n x) ≫ (U.gt e).pG) ((Over.map (thick R I e)).map (n y) ≫ (U.gt e).pG)
      ((Over.map (thick R I e)).map (n u) ≫ (U.gt e).pG)
    let E₀ : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z K
      ((Over.map (thick R I e)).map (n x) ≫ fstG I e G) ((Over.map (thick R I e)).map (n y) ≫ fstG I e G)
      ((Over.map (thick R I e)).map (n u) ≫ fstG I e G)
    have hC : C₀ = C := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      D.cub z J₀ (hq x) (hq y) (hq u)
    have hE : E₀ = E := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      U.P.c z K (ha x) (ha y) (ha u)
    have p : C₀ * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E₀ := p₃ (n x) (n y) (n u)
    have q : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E' := q₃ (a x) (a y) (a u)
    have r : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C' := r₃ (b x) (b y) (b u)
    rw [hC, hE] at p
    have k := cube_alg n a b sq x y u p q r
    have hC' : C' = cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J
        ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG)
        ((Over.map (thick V I' e)).map u ≫ g'.pG) :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) D'.cub z J rfl rfl rfl
    have hE' : E' = cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG
        ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G')
        ((Over.map (thick V I' e)).map u ≫ fstG I' e G') :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) P'.c z JG rfl rfl rfl
    rw [hC', hE'] at k
    exact k
end GlobalTheory.LN.FourthSide
