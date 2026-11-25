-- Prove2me | solution 1 for GlobalTheory.IsoDesc.quot_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:38:15.435062+00:00
-- url     : https://prove2.me/submissions/a6d94a05-52c8-446d-8eda-d535f13aa084

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_trans
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_exists_ratio
import Theorems.Thm_GlobalTheory_IsoDesc_eqns_quot
import Theorems.Thm_GlobalTheory_IsoDesc_Eqns_ker
import Theorems.Thm_GlobalTheory_IsoDesc_factor_alg
import Theorems.Thm_GlobalTheory_IsoDesc_exists_char
import Theorems.Thm_GlobalTheory_IsoDesc_char_eq_zero
import Theorems.Thm_GlobalTheory_IsoDesc_mul_comp_q
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G : Over S'} {B : Over S}
  [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] [GrpObj B] [IsCommMonObj B] {Q : TQ G X} {P : CP G}
  {M' : CP Q.B} {M : CP B} {β : Q.B.left ⟶ B.left} {hβ : β ≫ B.hom = Q.B.hom ≫ f}
namespace GlobalTheory.IsoDesc
theorem _root_.solution (mul : ∀ (T : Over S') (x y : T ⟶ Q.B), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {hq : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S'} {hw : (Q.q.left ≫ β) ≫ B.hom = G.hom ≫ f} {u w}
    (Hu : IsCPMap P M' (𝟙 S') Q.q.left hq u) (Hw : IsCPMap P M f (Q.q.left ≫ β) hw w) {s} (hs : IsQuot u w s)
    {Z : Over S'} (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G) (z : Z.left) (j i)
    (hz : Q.q.left (g.left z) ∈ dom M'.L.L M.L.L β j i) :
    gm ((t ≫ Q.i) * g).left z _ (s j i) = gm g.left z _ (s j i) := by
  have := Q.i_hom
  obtain ⟨a, ha⟩ := hs.exists_ratio P.L.isLB M'.L.isLB M.L.isLB ((isGen_iff _).1 Hu.gen) ((isGen_iff _).1 Hw.gen)
    ((fst (splitTorus S' X) G ≫ Q.i) * snd (splitTorus S' X) G).left (snd (splitTorus S' X) G).left
    (congrArg (fun k => k.left) (mul_comp_q (Q := Q) (fst (splitTorus S' X) G) (snd (splitTorus S' X) G)))
  obtain ⟨A, hA⟩ : ∃ A : ∀ {Z : Over S'} (z : Z.left), (Z ⟶ splitTorus S' X) → (Z ⟶ G) → (Z.left.presheaf.stalk z)ˣ,
    ∀ {Z : Over S'} (z : Z.left) (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G), gm (lift t g).left z ⊤ a = A z t g := ⟨_, fun _ _ _ => rfl⟩
  have hr : ∀ {Z : Over S'} (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G) (z : Z.left) (j i),
      Q.q.left (g.left z) ∈ dom M'.L.L M.L.L β j i →
      gm ((t ≫ Q.i) * g).left z _ (s j i) = A z t g * gm g.left z _ (s j i) := fun t g z j i hz => by
    have e : (lift t g).left ≫ (snd (splitTorus S' X) G).left = g.left := by rw [← Over.comp_left, lift_snd]
    have := ha _ (lift t g).left z j i (by
      have e' : (snd (splitTorus S' X) G).left ((lift t g).left z) = g.left z := congrArg (fun k => k z) e
      rw [e']; exact hz)
    rwa [e, hA, ← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd] at this
  have alg : ∀ {Z : Over S'} (z : Z.left),
      (∀ t t' u, A z (t * t') u * (A z (t * t') 1)⁻¹ = A z t u * (A z t 1)⁻¹ * (A z t' u * (A z t' 1)⁻¹)) ∧
      (∀ t t', A z (t * t') 1 = A z t (t' ≫ Q.i) * A z t' 1) ∧ ∀ t, A z t⁻¹ 1 = A z t 1 := fun {Z} z => by
    obtain ⟨I, hI⟩ := exists_good_pt M'.L.isLB z
    obtain ⟨J, hJ⟩ := exists_good_pt M.L.isLB z
    refine factor_alg (MonoidHom.mk' (fun t : Z ⟶ splitTorus S' X => t ≫ Q.i) fun _ _ => MonObj.mul_comp _ _ _)
      (fun x => gm x.left z _ (s (J ((x ≫ Q.q).left ≫ β)) (I (x ≫ Q.q).left))) (A z) (fun t g => ?_) fun t =>
      (eqns_quot (hβ := hβ) Hu Hw hs hI hJ).ker mul hI hJ ?_
    · show gm ((t ≫ Q.i) * g).left z _ (s (J ((((t ≫ Q.i) * g) ≫ Q.q).left ≫ β)) (I (((t ≫ Q.i) * g) ≫ Q.q).left)) = _
      rw [mul_comp_q]
      exact hr t g z _ _ ⟨mem_pull.2 (hJ ((g ≫ Q.q).left ≫ β)), hI (g ≫ Q.q).left⟩
    · have := mul_comp_q (Q := Q) t 1
      have _ := Q.q_hom
      rwa [_root_.mul_one, MonObj.one_comp] at this
  obtain ⟨χ, hχ⟩ := exists_char G (a * (Units.map (lift (fst (splitTorus S' X) G) (1 : _ ⟶ G)).left.appTop.hom.toMonoidHom a)⁻¹)
    (fun Z t t' y z => by
      have e : ∀ t : Z ⟶ splitTorus S' X, gm (lift t y).left z ⊤
          (Units.map (lift (fst (splitTorus S' X) G) (1 : _ ⟶ G)).left.appTop.hom.toMonoidHom a) = A z t 1 := fun t => by
        refine (gm_pull _ _ z ⊤ trivial a).trans ?_
        rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one, hA]
      simp only [map_mul, map_inv, e]
      rw [hA, hA, hA]
      exact (alg z).1 t t' y)
  have c : ∀ {Z : Over S'} (z : Z.left) t g, A z t g = A z t 1 := fun {Z} z t g => by
    have e : ∀ y : Z ⟶ G, gm (lift t y).left z ⊤
        (Units.map (lift (fst (splitTorus S' X) G) (1 : _ ⟶ G)).left.appTop.hom.toMonoidHom a) = A z t 1 := fun y => by
      refine (gm_pull _ _ z ⊤ trivial a).trans ?_
      rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one, hA]
    have := (hχ Z t g z).trans (hχ Z t 1 z).symm
    simp only [map_mul, map_inv, e] at this
    rw [hA, hA] at this
    exact mul_right_cancel this
  obtain ⟨ψ, hψ⟩ := exists_char G a (fun Z t t' y z => by
    rw [hA, hA, hA, c z _ y, c z _ y, c z _ y, (alg z).2.1, c z t])
  have h2 : ψ + ψ = 0 := char_eq_zero G fun Z t _ z => by
    have := (alg z).2.2 t
    rw [← hA, ← hA, hψ, hψ, chV_inv, map_inv] at this
    rw [chV_add, map_mul]
    exact (congrArg (· * _) this.symm).trans (inv_mul_cancel _)
  have h0 : ψ = 0 := by
    rw [← two_smul ℤ ψ] at h2
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hr t g z j i hz, ← hA, hψ, h0, chV_zero, map_one, _root_.one_mul]
end GlobalTheory.IsoDesc
